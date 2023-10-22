include "result.mc"
include "error.mc"

include "./ast_gen.mc"
include "./ast.mc"
include "./pprint.mc"
include "./error-print.mc"

lang DAEParseAnalysis = DAEAst + DAEParsePrettyPrint
  type Res a = Result ErrorSection ErrorSection a

  sem daeParse : String -> String -> Res DAEProg
  sem daeParse filename =| prog ->
    switch parseDAEParse filename prog
    case Right prog then result.ok prog
    case Left errs then
      foldl1
        result.withAnnotations
        (map
           (lam e. result.err { errorDefault with msg = e.1, info = e.0 })
           errs)
    end

  sem daeParseExn : String -> String -> DAEProg
  sem daeParseExn filename =| prog ->
    switch result.consume (daeParse filename prog)
    case (ws, Right prog) then
      (if not (null ws) then errorWarn (errorMsg  ws {single = "", multi = ""})
       else ());
      prog
    case (ws, Left errs) then
      (if not (null ws) then errorWarn (errorMsg  ws {single = "", multi = ""})
       else ());
      errorDie (errorMsg  errs {single = "", multi = ""})
    end

  sem daeProgWellFormed : all a. DAEProg -> Res DAEProg
  sem daeProgWellFormed =
  | prog & ProgDAEProg r ->
    result.withAnnotations
      (result.withAnnotations
         (foldl daeVarWellFormed (setEmpty nameCmp, result.ok ()) r.vars).1
         (result.mapM daeInitWellFormed r.ieqns))
      (foldl1 result.withAnnotations
         [
           smapM_DAEProg_DAETop daeTopWellFormed prog,
           smapM_DAEProg_DAEEqn
             (smapM_DAEEqn_DAEExpr daeExprAllowPrimWellFormed) prog
         ])

  sem daeVarWellFormed : all a. (Set Name, Res ()) -> DAEVar -> (Set Name, Res ())
  sem daeVarWellFormed acc =
  | vars & VarsDAEVar r ->
    foldl
      (lam acc. lam name.
        match acc with (names, res) in
        let newres =
          if setMem name.v names then
            result.err {
              errorDefault with
              msg = strJoin "\n" [
                "Duplicate dependent variable declaration:",
                daeVarToString vars
              ],
              info = name.i
            }
          else result.ok ()
        in
        (setInsert name.v names, result.withAnnotations res newres))
      acc
      r.names

  sem daeTopWellFormed : all a. DAETop -> Res DAETop
  sem daeTopWellFormed =
  | top -> smapM_DAETop_DAEExpr daeExprWellFormed top

  sem daeInitWellFormed : all a. DAEEqn -> Res DAEEqn
  sem daeInitWellFormed =
  | eqn & EqnDAEEqn r ->
    switch (r.left, r.right)
    case
      ((VarDAEExpr _, _) | (_, VarDAEExpr _))
    | ((PrimDAEExpr _, _) | (_, PrimDAEExpr _))
    then result.ok eqn
    case _ then result.err {
      errorDefault with
      msg = strJoin "\n" [
        "Non-explicit initial equation:", daeEqnToString eqn
      ],
      info = r.info
    }
    end

  sem daeExprWellFormed : all a. DAEExpr -> Res DAEExpr
  sem daeExprWellFormed =
  | expr & PrimDAEExpr r ->
    result.err {
      errorDefault with
      msg = strJoin "\n" ["Invalid use of \':", daeExprToString expr],
      info = r.info
    }
  | expr -> smapM_DAEExpr_DAEExpr daeExprWellFormed expr

  sem daeExprAllowPrimWellFormed : all a. DAEExpr -> Res DAEExpr
  sem daeExprAllowPrimWellFormed =
  | expr & PrimDAEExpr r ->
    recursive let recur = lam expr.
      switch expr
      case VarDAEExpr _ then true
      case PrimDAEExpr r then recur r.left
      case _ then false
      end
    in
    if recur r.left then result.ok expr
    else
      result.err {
        errorDefault with
        msg = strJoin "\n" ["Invalid use of \':", daeExprToString expr],
        info = r.info
      }
  | expr -> smapM_DAEExpr_DAEExpr daeExprAllowPrimWellFormed expr
end
