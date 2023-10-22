include "log.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/type-check.mc"
include "mexpr/boot-parser.mc"
include "mexpr/builtin.mc"

include "./ast_gen.mc"
include "./parse.mc"

lang DAEParseDesugar = DAEAst
  sem daeDesugarType : DAEType -> Type
  sem daeDesugarType =
  | FloatDAEType r -> TyFloat { info = r.info }
  | IntDAEType r -> TyInt { info = r.info }

  sem daeDesugarConst : DAEConst -> Const
  sem daeDesugarConst =
  | FloatDAEConst r -> CFloat { val = r.val.v }
  | IntDAEConst r -> CInt { val = r.val.v }
  | TrueDAEConst _ -> CBool { val = true }
  | FalseDAEConst _ -> CBool { val = false }
  | SinDAEConst _ -> CSin {}
  | CosDAEConst _ -> CCos {}
  | SqrtDAEConst _ -> CSqrt {}
  | ExpDAEConst _ -> CExp {}

  sem daeDesugarPat : DAEPat -> Pat
  sem daeDesugarPat =
  | TupleDAEPat r ->
    let bindings =
      map
        (lam n.
          PatNamed {
            ident = PName n.v,
            info = n.i,
            ty = TyUnknown { info = n.i }
          })
        r.names
    in
    patTuple bindings r.info

  sem daeDesugarBinOp : Info -> Const -> (DAEExpr, DAEExpr) -> Expr
  sem daeDesugarBinOp info c =
  | (left, right) ->
    let ty = TyUnknown { info = info } in
    TmApp {
      lhs = TmApp {
        lhs = TmConst { val = c, info = info, ty = ty },
        rhs = daeDesugarExpr left,
        ty = ty,
        info = info
      },
      rhs = daeDesugarExpr right,
      ty = ty,
      info = info
    }

  sem daeDesugarUnOp : Info -> Const -> DAEExpr -> Expr
  sem daeDesugarUnOp info c =
  | right ->
    let ty = TyUnknown { info = info } in
    TmApp {
      lhs = TmConst { val = c, info = info, ty = ty },
      rhs = daeDesugarExpr right,
      ty = ty,
      info = info
    }

  sem daeDesugarExpr : DAEExpr -> Expr
  sem daeDesugarExpr =
  | VarDAEExpr r ->
    TmVar {
      ident = r.name.v,
      info = r.info,
      ty = TyUnknown { info = r.info },
      frozen = false
    }
  | AbsDAEExpr r ->
    let tyParam = TyUnknown { info = r.name.i } in
    let ty = TyUnknown { info = r.info } in
    TmLam {
      ident = r.name.v,
      tyAnnot = tyParam,
      tyParam = tyParam,
      body = daeDesugarExpr r.body,
      ty = ty,
      info = r.info
    }
  | AppDAEExpr r -> TmApp {
    lhs = daeDesugarExpr r.fn,
    rhs = daeDesugarExpr r.arg,
    ty = TyUnknown { info = r.info },
    info = r.info
  }
  | AppDAEExpr (r & {fn = ConstDAEExpr { val = PredDAEConst _ }}) ->
    let ty = TyUnknown { info = r.info } in
    TmApp {
      lhs = TmApp {
        lhs = TmConst { val = CSubi (), info = r.info, ty = ty },
        rhs = daeDesugarExpr r.arg,
        ty = ty,
        info = r.info
      },
      rhs = TmConst { val = CInt { val = 1 }, info = r.info, ty = ty },
      ty = ty,
      info = r.info
    }
  -- | AppDAEExpr (r & {fn = ConstDAEExpr { val = ExpDAEConst _ }}) ->
  --   let ty = TyUnknown { info = r.info } in
  --   TmApp {
  --     lhs = TmApp {
  --       lhs = TmConst { val = CSubi (), info = r.info, ty = ty },
  --       rhs = daeDesugarExpr r.arg,
  --       ty = ty,
  --       info = r.info
  --     },
  --     rhs = TmConst { val = CInt { val = 1 }, info = r.info, ty = ty },
  --     ty = ty,
  --     info = r.info
  --   }
  | TupleDAEExpr r ->
    tmTuple r.info (TyUnknown { info = r.info }) (map daeDesugarExpr r.exprs)
  | ProjDAEExpr r ->
    let ty = TyUnknown { info = r.info } in
    let x = nameNoSym "x" in
    TmMatch {
      target = daeDesugarExpr r.expr,
      pat = patTuple [
        PatNamed {
          ident =  PName x,
          info = r.info,
          ty = ty
        }] r.info,
      thn = TmVar {
        ident = x,
        info = r.info,
        ty = ty,
        frozen = false
      },
      els = TmNever { info = r.info, ty = ty },
      ty = ty,
      info = r.info
    }
  | ConstDAEExpr r -> TmConst {
    val = daeDesugarConst r.val,
    ty = TyUnknown { info = r.info },
    info = r.info
  }
  | AddDAEExpr r -> daeDesugarBinOp r.info (CAddf ()) (r.left, r.right)
  | SubDAEExpr r -> daeDesugarBinOp r.info (CSubf ()) (r.left, r.right)
  | MulDAEExpr r -> daeDesugarBinOp r.info (CMulf ()) (r.left, r.right)
  | DivDAEExpr r -> daeDesugarBinOp r.info (CDivf ()) (r.left, r.right)
  | LtDAEExpr r -> daeDesugarBinOp r.info (CLti ()) (r.left, r.right)
  | LtfDAEExpr r -> daeDesugarBinOp r.info (CLtf ()) (r.left, r.right)
  | EqDAEExpr r -> daeDesugarBinOp r.info (CEqi ()) (r.left, r.right)
  | NegDAEExpr r -> daeDesugarUnOp r.info (CNegf ()) r.right
  | MatchInDAEExpr r ->
    let ty = TyUnknown { info = r.info } in
    TmMatch {
      target = daeDesugarExpr r.target,
      pat = daeDesugarPat r.pat,
      thn = daeDesugarExpr r.body,
      els = TmNever { info = r.info, ty = ty },
      ty = ty,
      info = r.info
    }
  | IfDAEExpr r ->
    let ty = TyUnknown { info = r.info } in
    TmMatch {
      target = daeDesugarExpr r.pred,
      pat = PatBool { val = true, info = r.info, ty = ty },
      thn = daeDesugarExpr r.thn,
      els = daeDesugarExpr r.els,
      ty = ty,
      info = r.info
    }
  | LetDAEExpr r ->
    let ty = TyUnknown { info = r.info } in
    TmLet {
      ident = r.name.v,
      tyAnnot = ty,
      tyBody = ty,
      body = daeDesugarExpr r.arg,
      inexpr = daeDesugarExpr r.body,
      ty = ty,
      info = r.info
    }
  | RecLetDAEExpr r ->
    let ty = TyUnknown { info = r.info } in
    let binding = {
      ident = r.name.v,
      tyAnnot = ty,
      tyBody = ty,
      body = daeDesugarExpr r.arg,
      info = r.info
    } in
    TmRecLets {
      bindings = [binding],
      inexpr = daeDesugarExpr r.body,
      ty = ty,
      info = r.info
    }
  | PrimDAEExpr r ->
    recursive let recur = lam order. lam expr.
      switch expr
      case VarDAEExpr varr then TmDVar {
        ident = varr.name.v,
        order = order,
        info = r.info,
        ty = TyUnknown { info = r.info }
      }
      case PrimDAEExpr primr then
        recur (succ order) primr.left
      case _ then error "daeDesugarExpr: Undefined"
      end
    in
    recur 1 r.left

  sem daeDesugarTop : DAETop -> Expr
  sem daeDesugarTop =
  | LetDAETop r -> nulet_ r.name.v (daeDesugarExpr r.arg)
  | RecLetDAETop r -> nureclets_ [(r.name.v, daeDesugarExpr r.arg)]

  sem daeDesugarVars : DAEVar -> [(Name, Type)]
  sem daeDesugarVars =
  | VarsDAEVar r ->
    let ty = daeDesugarType r.ty in
    map (lam name. (name.v, ty)) r.names

  sem daeDesugarEqn : DAEEqn -> Expr
  sem daeDesugarEqn =
  | EqnDAEEqn r -> subf_ (daeDesugarExpr r.left) (daeDesugarExpr r.right)

  -- Assumes a well-formed DAE program.
  sem daeDesugarProg : DAEProg -> TmDAERec
  sem daeDesugarProg =
  | ProgDAEProg r ->
    let bindings = bindall_ (snoc (map daeDesugarTop r.tops) unit_) in
    let vars = join (map daeDesugarVars r.vars) in
    let ieqns = map daeDesugarEqn r.ieqns in
    let eqns = map daeDesugarEqn r.eqns in
    let out = daeDesugarExpr r.output in
    {
      bindings = bindings,
      vars = vars,
      ieqns = ieqns,
      eqns = eqns,
      out = out,
      info = r.info
    }

--   sem daeResugarExpr : Expr -> Option DAEExpr
--   sem daeResugarExpr =
--   | TmVar r ->
--     let i = r.info in
--     Some (VarDAEExpr { info = i, name = { i = i, v = r.ident } })
--   | TmLam r ->
--     let i = r.info in
--     optionBind (daeResugarExpr r.body) (lam body.
--       Some
--         (AbsDAEExpr { body = body, info = i, name = { i = i, v = r.ident } }))
--   | TmApp {
--     lhs = TmApp {
--       lhs = TmConst { val = c, info = info },
--       rhs = left
--     },
--     rhs = right,
--     info = info
--   } ->
--     optionBind (daeResugarExpr left) (lam left.
--       optionBind (daeResugarExpr right) (lam right.
--         daeResugarBinOp { info = info, left = left, right = right } c))
--   | TmApp {
--     lhs = TmConst { val = c, info = info },
--     rhs = right,
--     info = info
--   } ->
--     optionBind (daeResugarExpr right) (lam right.
--       daeResugarUnOp { info = info, right = right } c)
--   | TmApp r ->
--     optionBind (daeResugarExpr r.lhs) (lam lhs.
--       optionBind (daeResugarExpr r.rhs) (lam rhs.
--         Some (AppDAEExpr { fn = lhs, arg = rhs, info = r.info })))
--   | TmRecord r ->
--     optionMap
--       (lam exprs. TupleDAEExpr { info = r.info, exprs = exprs })
--       ((optionCompose
--           (optionMapM daeResugarExpr)
--           record2tuple)
--          r.bindings)
--   | TmConst r ->
--     optionBind (daeResugarConst r.info r.val) (lam val.
--       Some (ConstDAEExpr { val = val, info = r.info }))
--   | TmLet r ->
--     let i = r.info in
--     optionBind (daeResugarExpr r.body) (lam arg.
--       optionBind (daeResugarExpr r.inexpr) (lam body.
--         Some
--           (LetDAEExpr {
--             arg = arg,
--             body = body,
--             info = i,
--             name = { i = i, v = r.ident }
--           })))
--   | TmRecLets (r & { bindings = [binding] }) ->
--     optionBind (daeResugarExpr binding.body) (lam arg.
--       optionBind (daeResugarExpr r.inexpr) (lam body.
--         Some
--           (RecLetDAEExpr {
--             arg = arg,
--             body = body,
--             info = r.info,
--             name = { i = r.info, v = binding.ident }
--           })))
--   | TmMatch {
--     info = info,
--     target = target,
--     pat = pat & !(PatBool { val = true }),
--     thn = thn,
--     els = TmNever _
--   } ->
--     optionBind (daeResugarExpr target) (lam target.
--       optionBind (daeResugarPat pat) (lam pat.
--         optionBind (daeResugarExpr thn) (lam body.
--           Some
--             (MatchInDAEExpr {
--               pat = pat,
--               body = body,
--               info = info,
--               target = target}))))
--   | TmMatch {
--     info = info,
--     target = target,
--     pat = pat & PatRecord {bindings = bindings},
--     thn = thn & TmVar {ident = exprName},
--     els = TmNever _
--   } ->
--     optionBind (daeResugarExpr target) (lam target.
--       match matchIsProj bindings exprName with Some fieldLabel then
--         let str = sidToString fieldLabel in
--         if forAll isDigit str then
--           let n = string2int str in
--           Some
--             (ProjDAEExpr {
--               expr = target,
--               label = { v = n, i = info },
--               info = info
--             })
--         else None ()
--       else
--         optionBind (daeResugarPat pat) (lam pat.
--           optionBind (daeResugarExpr thn) (lam body.
--             Some
--               (MatchInDAEExpr {
--                 pat = pat,
--                 body = body,
--                 info = info,
--                 target = target}))))
--   | TmMatch {
--     info = info,
--     target = target,
--     pat = PatBool { val = true },
--     thn = thn,
--     els = els & !TmNever _
--   } ->
--     optionBind (daeResugarExpr target) (lam pred.
--       optionBind (daeResugarExpr thn) (lam thn.
--         optionBind (daeResugarExpr els) (lam els.
--           Some
--             (IfDAEExpr {
--               pred = pred,
--               thn = thn,
--               els = els,
--               info = info}))))
--   | _ -> None ()

--   sem daeResugarUnOp
--     : {info : Info, right : DAEExpr} -> Const -> Option DAEExpr
--   sem daeResugarUnOp r =
--   | CNegf _ ->
--     Some
--       (SubDAEExpr {
--         left = ConstDAEExpr {
--           val = FloatDAEConst { val = { i = r.info, v = 0. }, info = r.info },
--           info = r.info
--         },
--         right = r.right,
--         info = r.info
--       })
--   | CSin _ -> daeResugarElemFunction r.info "sin" r.right
--   | CCos _ -> daeResugarElemFunction r.info "cos" r.right
--   | _ -> None ()

--   sem daeResugarElemFunction : Info -> String -> DAEExpr -> Option DAEExpr
--   sem daeResugarElemFunction info name =| arg ->
--     Some
--       (AppDAEExpr {
--         fn = VarDAEExpr {
--           info = info,
--           name = { i = info, v = nameNoSym name }
--         },
--         arg = arg,
--         info = info
--       })

--   sem daeResugarBinOp
--     : {info : Info, left : DAEExpr, right : DAEExpr} -> Const -> Option DAEExpr
--   sem daeResugarBinOp r =
--   | CAddf _ -> Some (AddDAEExpr r)
--   | CSubf _ -> Some (SubDAEExpr r)
--   | CMulf _ -> Some (MulDAEExpr r)
--   | CDivf _ -> Some (DivDAEExpr r)
--   | _ -> None ()

--   sem daeResugarConst : Info -> Const -> Option DAEConst
--   sem daeResugarConst info =
--   | CFloat r ->
--     Some (FloatDAEConst { val = { i = info, v = r.val }, info = info })
--   | CInt r ->
--     Some (IntDAEConst { val = { i = info, v = r.val }, info = info })
--   | CBool r ->
--     if r.val then
--       Some (TrueDAEConst { info = info })
--     else
--       Some (FalseDAEConst { info = info })
--   | _ -> None ()

--   sem daeResugarPat : Pat -> Option DAEPat
--   sem daeResugarPat =
--   | PatRecord r ->
--     optionMap (lam names. TupleDAEPat { info = r.info, names = names })
--       ((optionCompose
--           (optionMapM
--              (lam p.
--                match p with PatNamed {ident = PName v, info = i} then
--                  Some { i = i, v = v }
--                else None ()))
--           record2tuple)
--          r.bindings)
--   | _ -> None ()
end

lang TestLang = DAEParseAnalysis + DAEParseDesugar end

mexpr

use TestLang in

let parseDAEProg = lam prog.
  let prog = daeParseExn "internal" prog in

  logMsg logLevel.debug
    (lam. strJoin "\n" ["Input program:", daeProgToString prog]);

  prog
in

let parseDAEExprExn = lam prog. typeCheck (symbolize (parseDAEExprExn prog)) in

logSetLogLevel logLevel.error;

let prog = parseDAEProg "
  let mul = lam x. lam y. x*y end
  let pow2 = lam x. mul x x end
  variables
  x, vx, y, vy, h : Float
  init
  x = 1.;
  vy' = 0. - 1.
  equations
  vx = x';
  vy = y';
  vx' = mul x h;
  vy' = mul y h - 1.;
  pow2 x + pow2 y = pow2 1.
  output
  {x, vx, vx'}
  "
in

let expectedExpr = parseDAEExprExn "
  let mul = lam x. lam y. mulf x y in
  let pow2 = lam x. mul x x in

  lam x : Float.
  lam vx : Float.
  lam y : Float.
  lam vy : Float.
  lam h : Float.
  {
    ieqns =
      (subf x 1.,
       subf (prim 1 vy) (subf 0. 1.)),

    eqns =
      (subf vx (prim 1 x),
       subf vy (prim 1 y),
       subf (prim 1 vx) (mul x h),
       subf (prim 1 vy) (subf (mul y h) 1.),
       subf (addf (pow2 x) (pow2 y)) (pow2 1.)),

    out =
      (
        x,
        vx,
        prim 1 vx
      )
  }
  "
in

let daer = daeDesugarProg prog in
match typeCheck (symbolize (TmDAE daer)) with TmDAE daer then
  logSetLogLevel logLevel.error;
  logMsg logLevel.debug
    (lam. strJoin "\n" ["Output program:", expr2str (TmDAE daer)]);
  utest TmDAE daer with TmDAE (_tmToTmDAERec expectedExpr) using eqExpr in
  ()
else error "impossible"
