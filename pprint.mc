include "mexpr/pprint.mc"
include "mexpr/free-vars.mc"

include "./ast_gen.mc"
include "./ast.mc"

let seqToString =
  lam elToString. lam seq. join ["[", strJoin ", " (map elToString seq), "]"]

let mapToString = lam kToString. lam vToString. lam map.
  join [
    "{",
    strJoin ", "
      (map
         (lam x. strJoin " " [kToString x.0, "->", vToString x.1])
         (mapBindings map)),
    "}"
  ]

let setToString = lam elToString. lam set.
  join ["{", strJoin ", " (map elToString (setToSeq set)), "}"]

let tupleToString2 = lam elToString0. lam elToString1. lam x.
  join ["(", elToString0 x.0, ", ", elToString1 x.1, ")"]

lang DAEParsePrettyPrintBase = IdentifierPrettyPrint + ProgDAEProgAst
  type DAEPPCtx = {
    env : PprintEnv,
    indent : Int,
    cols : Int,
    multiline : Bool
  }

  sem daePPCtxEmpty : () -> DAEPPCtx
  sem daePPCtxEmpty =| _ -> {
    env = pprintEnvEmpty,
    indent = 0,
    cols = 0,
    multiline = false
  }

  sem daePPKeyword : DAEPPCtx -> String -> (DAEPPCtx, String)
  sem daePPKeyword ctx =| kw ->
    ({ ctx with cols = addi (length kw) ctx.cols, multiline = false }, kw)

  -- Interface
  sem daeTypeToString : DAEType -> String
  sem daeTypeToString =| ty ->
    match daeTypeToStringH (daePPCtxEmpty ()) ty with (_, str) in str

  sem daeConstToString : DAEConst -> String

  sem daePatToString : DAEPat -> String
  sem daePatToString =| pat ->
    match daePatToStringH (daePPCtxEmpty ()) pat with (_, str) in str

  sem daeExprToString : DAEExpr -> String
  sem daeExprToString =| expr ->
    match daeExprToStringH (daePPCtxEmpty ()) expr with (_, str) in str

  sem daeVarToString : DAEVar -> String
  sem daeVarToString =| model ->
    match daeVarToStringH (daePPCtxEmpty ()) model with (_, str) in str

  sem daeEqnToString : DAEEqn -> String
  sem daeEqnToString =| equation ->
    match daeEqnToStringH (daePPCtxEmpty ()) equation with (_, str) in str

  sem daeTopToString : DAETop -> String
  sem daeTopToString =| top ->
    match daeTopToStringH (daePPCtxEmpty ()) top with (_, str) in str

  sem daeProgToString : DAEProg -> String
  sem daeProgToString =| prog ->
    match daeProgToStringH (daePPCtxEmpty ()) prog with (_, str) in str

  -- Helpers
  sem daeVarNameToString : DAEPPCtx -> Name -> (DAEPPCtx, String)
  sem daeVarNameToString ctx =
  | name ->
    match pprintEnvGetStr ctx.env name with (env,str) in
    ({ ctx with env = env }, str)

  sem daePPGroup : DAEPPCtx -> String -> (DAEPPCtx, String)
  sem daePPGroup ctx =| str ->
    ({ ctx with cols = addi ctx.cols 2 }, join ["(", str, ")"])

  sem daePPMaybeGroup : Bool -> DAEPPCtx -> String -> (DAEPPCtx, String)
  sem daePPMaybeGroup group ctx =| str ->
    if group then daePPGroup ctx str else (ctx, str)

  sem daeProgToStringH : DAEPPCtx -> DAEProg -> (DAEPPCtx, String)
  sem daeProgToStringH ctx =
  | ProgDAEProg r ->
    match
      mapAccumL daeTopToStringH ctx r.tops
      with (ctx, tops)
    in
    match
      mapAccumL daeVarToStringH ctx r.vars
      with (ctx, vars)
    in
    match
      mapAccumL daeEqnToStringH ctx r.ieqns
      with (ctx, ieqns)
    in
    match
      mapAccumL daeEqnToStringH ctx r.eqns
      with (ctx, eqns)
    in
    match
      mapAccumL daeEqnToStringH ctx r.eqns
      with (ctx, eqns)
    in
    match daeExprToStringH ctx r.output with (_, output) in
    (ctx, join [
      strJoin "\n\n" tops,
      "\n\nvariables\n",
      strJoin ";\n" vars,
      "\n\ninit\n",
      strJoin ";\n" ieqns,
      "\n\nequations\n",
      strJoin ";\n" eqns,
      "\n\noutput\n",
      output
    ])

  -- Helpers that should be implemented
  sem daeTypePrecedence : DAEType -> Int
  sem daeExprPrecedence : DAEExpr -> Int
  sem daeTypeToStringH : DAEPPCtx -> DAEType -> (DAEPPCtx, String)
  sem daePatToStringH : DAEPPCtx -> DAEPat -> (DAEPPCtx, String)
  sem daeExprToStringH : DAEPPCtx -> DAEExpr -> (DAEPPCtx, String)
  sem daeEqnToStringH : DAEPPCtx -> DAEEqn -> (DAEPPCtx, String)
  sem daeVarToStringH : DAEPPCtx -> DAEVar -> (DAEPPCtx, String)
  sem daeTopToStringH : DAEPPCtx -> DAETop -> (DAEPPCtx, String)
end


lang DAETypePrettyPrint = DAEParsePrettyPrintBase +
  FloatDAETypeAst + IntDAETypeAst + ArrowDAETypeAst

  sem daeTypePrecedence =
  | FloatDAEType _ | IntDAEType _ -> 1
  | _ -> 0

  sem daeTypeToStringH ctx =
  | FloatDAEType _ -> daePPKeyword ctx "Float"
  | IntDAEType _ -> daePPKeyword ctx "Int"
  | ty & ArrowDAEType r ->
    match daeTypeToStringH ctx r.left with (ctx, left) in
    match
      daePPMaybeGroup
        (leqi (daeTypePrecedence r.left) (daeTypePrecedence ty))
        ctx left with (ctx, left)
    in
    match daeTypeToStringH { ctx with indent = pprintIncr ctx.indent } r.right
      with (ctx, right)
    in
    (ctx, join [left, "->", right])
end


lang DAEConstPrettyPrint = DAEParsePrettyPrintBase +
  FloatDAEConstAst +
  IntDAEConstAst +
  TrueDAEConstAst +
  FalseDAEConstAst +
  PredDAEConstAst

  sem daeConstToString =
  | FloatDAEConst r -> float2string r.val.v
  | IntDAEConst r -> int2string r.val.v
  | TrueDAEConst _ -> "true"
  | FalseDAEConst _ -> "false"
  | PredDAEConst _ -> "pred"
end


lang DAEPatPrettyPrint = DAEParsePrettyPrintBase +
  TupleDAEPatAst

  sem daePatToStringH ctx =
  | TupleDAEPat r ->
    match
      mapAccumL daeVarNameToString ctx (map (lam n. n.v) r.names)
      with (ctx, names)
    in
    (ctx, join ["{", strJoin ", "  names, "}"])
end


lang DAEExprPrettyPrint = DAEParsePrettyPrintBase +
  VarDAEExprAst +
  AbsDAEExprAst +
  AppDAEExprAst +
  TupleDAEExprAst +
  ProjDAEExprAst +
  ConstDAEExprAst +
  AddDAEExprAst +
  SubDAEExprAst +
  MulDAEExprAst +
  DivDAEExprAst +
  LtDAEExprAst +
  LtfDAEExprAst +
  EqDAEExprAst +
  NegDAEExprAst +
  MatchInDAEExprAst +
  IfDAEExprAst +
  LetDAEExprAst +
  RecLetDAEExprAst +
  PrimDAEExprAst

  sem daeExprPrecedence =
  | VarDAEExpr _ | TupleDAEExpr _ | ProjDAEExpr _ | ConstDAEExpr _  -> 7
  | NegDAEExpr _ -> 6
  | AppDAEExpr _ -> 5
  | MulDAEExpr _ | DivDAEExpr _ -> 4
  | AddDAEExpr _ | SubDAEExpr _ -> 3
  | LtDAEExpr _ | LtfDAEExpr _ | EqDAEExpr _ -> 2
  | AbsDAEExpr _ -> 1
  | _ -> 0

  sem daeBindingToString
    : Bool -> DAEPPCtx -> (Name, DAEExpr) -> (DAEPPCtx, String)
  sem daeBindingToString rec ctx =
  | (name, arg) ->
    match daeVarNameToString ctx name with (ctx, name) in
    match daeExprToStringH ctx arg with (ctx, arg) in
    (ctx,
     join [if rec then "reclet " else "let ", name, " = ", arg])

  sem daeBindingInToString
    : Bool -> DAEPPCtx -> (Name, DAEExpr, DAEExpr) -> (DAEPPCtx, String)
  sem daeBindingInToString rec ctx =
  | (name, arg, body) ->
    match daeBindingToString rec ctx (name, arg) with (ctx, binding) in
    match daeExprToStringH ctx body with (ctx, body) in
    (ctx,
     join [binding, " in ", body])

  sem daeBinOpToString
    : DAEPPCtx -> (Int, String, DAEExpr, DAEExpr) -> (DAEPPCtx, String)
  sem daeBinOpToString ctx =
  | (prec, op, left, right) ->
    match daeExprToStringH ctx left with (ctx, leftStr) in
    match
      daePPMaybeGroup (lti (daeExprPrecedence left) prec) ctx leftStr
      with (ctx, left)
    in
    match daeExprToStringH ctx right with (ctx, rightStr) in
    match
      daePPMaybeGroup (lti (daeExprPrecedence right) prec) ctx rightStr
      with (ctx, right)
    in
    (ctx, join [left, op, right])

  sem daeUnOpToString
    : DAEPPCtx -> (Int, String, DAEExpr) -> (DAEPPCtx, String)
  sem daeUnOpToString ctx =
  | (prec, op, right) ->
    match daeExprToStringH ctx right with (ctx, rightStr) in
    match
      daePPMaybeGroup (lti (daeExprPrecedence right) prec) ctx rightStr
      with (ctx, right)
    in
    (ctx, join [op, right])

  sem daeExprToStringH ctx =
  | VarDAEExpr r -> daeVarNameToString ctx r.name.v
  | AbsDAEExpr r ->
    match daeVarNameToString ctx r.name.v with (ctx, name) in
    match daeExprToStringH { ctx with indent = pprintIncr ctx.indent } r.body
      with (ctx, body)
    in
    (ctx, join ["lam ", name, ".", body])
  | expr & AppDAEExpr r ->
    match daeExprToStringH ctx r.fn with (ctx, fn) in
    match
      daePPMaybeGroup
        (lti (daeExprPrecedence r.fn) (daeExprPrecedence expr))
        ctx
        fn
      with (ctx, fn)
    in
    match daeExprToStringH ctx r.arg with (ctx, arg) in
    match
      daePPMaybeGroup
        (leqi (daeExprPrecedence r.arg) (daeExprPrecedence expr))
        ctx
        arg
      with (ctx, arg)
    in
    (ctx, join [fn, " ", arg])
  | TupleDAEExpr r ->

    match mapAccumL daeExprToStringH ctx r.exprs with (ctx, exprs) in
    (ctx, join ["{", strJoin ", " exprs, "}"])
  | expr & ProjDAEExpr r ->
    match daeExprToStringH ctx r.expr with (ctx, exprStr) in
    match
      daePPMaybeGroup
        (lti (daeExprPrecedence r.expr) (daeExprPrecedence expr))
        ctx
        exprStr
      with (ctx, expr) in
    (ctx, join [expr, ".", int2string r.label.v])
  | ConstDAEExpr r -> (ctx, daeConstToString r.val)
  | expr & AddDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "+", r.left, r.right)
  | expr & SubDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "-", r.left, r.right)
  | expr & MulDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "*", r.left, r.right)
  | expr & DivDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "/", r.left, r.right)
  | expr & LtDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "<", r.left, r.right)
  | expr & LtfDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "<.", r.left, r.right)
  | expr & EqDAEExpr r ->
    daeBinOpToString ctx (daeExprPrecedence expr, "==", r.left, r.right)
  | expr & NegDAEExpr r ->
    daeUnOpToString ctx (daeExprPrecedence expr, "-.", r.right)
  | MatchInDAEExpr r ->
    match daeExprToStringH ctx r.target with (ctx, target) in
    match daePatToStringH ctx r.pat with (ctx, pat) in
    match daeExprToStringH ctx r.body with (ctx, body) in
    (ctx, strJoin " " ["match", target, "with", pat, "in", body])
  | IfDAEExpr r ->
    match daeExprToStringH ctx r.pred with (ctx, pred) in
    match daeExprToStringH ctx r.thn with (ctx, thn) in
    match daeExprToStringH ctx r.els with (ctx, els) in
    (ctx, strJoin " " ["if", pred, "then", thn, "else", els])
  | LetDAEExpr r ->
    daeBindingInToString false ctx (r.name.v, r.arg, r.body)
  | RecLetDAEExpr r ->
    daeBindingInToString true ctx (r.name.v, r.arg, r.body)
  | expr & PrimDAEExpr r ->
    match daeExprToStringH ctx r.left with (ctx, left) in
    match
      daePPMaybeGroup
        (lti (daeExprPrecedence r.left) (daeExprPrecedence expr))
        ctx
        left
      with (ctx, left)
    in
    (ctx, join [left, "'"])
end


lang DAEEqnPrettyPrint = DAEParsePrettyPrintBase +
  EqnDAEEqnAst

  sem daeEqnToStringH ctx =
  | EqnDAEEqn r ->
    match daeExprToStringH ctx r.left with (ctx, left) in
    match daeExprToStringH ctx r.right with (ctx, right) in
    (ctx, strJoin " " [left, "=", right])
end

lang DAEVarPrettyPrint = DAEParsePrettyPrintBase + DAEExprPrettyPrint +
  VarsDAEVarAst

  sem daeVarToStringH ctx =
  | VarsDAEVar r ->
    match
      mapAccumL daeVarNameToString ctx (map (lam n. n.v) r.names)
      with (ctx, names)
    in
    match daeTypeToStringH ctx r.ty with (ctx, ty) in
    (ctx, strJoin " " [strJoin ", " names, ":", ty])
end


lang DAETopPrettyPrint = DAEParsePrettyPrintBase + DAEExprPrettyPrint +
  LetDAETopAst + RecLetDAETopAst

  sem daeTopToStringH ctx =
  | LetDAETop r ->
    match daeBindingToString false ctx (r.name.v, r.arg) with (ctx, binding) in
    (ctx, strJoin " " [binding, "end"])
  | RecLetDAETop r ->
    match daeBindingToString true ctx (r.name.v, r.arg) with (ctx, binding) in
    (ctx, strJoin " " [binding, "end"])
end


lang DAEParsePrettyPrint =
  DAETypePrettyPrint +
  DAEConstPrettyPrint +
  DAEPatPrettyPrint +
  DAEExprPrettyPrint +
  DAEVarPrettyPrint +
  DAEEqnPrettyPrint +
  DAETopPrettyPrint
end

mexpr

()
