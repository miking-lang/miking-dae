include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "./ast.mc"

let peadAstBuilder = lam info.
  use DAEAst in
  let tyunknown_ = TyUnknown { info = info } in
  let var_ = lam ty. lam ident.
    TmVar {
      ident = ident,
      ty = ty,
      info = info,
      frozen = false
    }
  in
  let tyfloat_ = TyFloat { info = info } in
  let tytaylorcoef_ = lam n.
    -- tyRecord info (create (succ n) (lam i. (join ["c", int2string i], tyfloat_)))
    tyWithInfo info (tytuple_ (create n (lam. tyfloat_)))
  in
  let tydualnum_ = tytaylorcoef_ 1 in
  let taylorcoef_ = lam ts.
    -- tmRecord info (tytaylorcoef_ (pred (length ts)))
    --   (mapi (lam i. lam t. (join ["c", int2string i], t)) ts)
    tmTuple info (tytaylorcoef_ (pred (length ts))) ts
  in
  let dualnum_ = lam primal. lam tangent. taylorcoef_ [primal, tangent] in
  let record_ = lam ty. lam bindings.
    TmRecord {
      bindings = bindings,
      ty = ty,
      info = info
    } in
  let patrecord_ = lam ty. lam bindings.
    let bindingMapFunc = lam b : (String, Pat). (stringToSid b.0, b.1) in
    PatRecord {
      bindings = mapFromSeq cmpSID (map bindingMapFunc bindings),
      info = info,
      ty = ty
    }
  in
  let recproj_ = lam ty. lam t. lam field.
    let ident = nameSym field in
    TmMatch {
      target = t,
      pat = patrecord_ ty [
        (field, PatNamed { ident = PName ident, info = info, ty = ty })
      ],
      thn = var_ ty ident,
      els = TmNever { info = info, ty = ty },
      info = info,
      ty = ty
    }
  in
  let taylorcoefproj_ = lam t. lam i.
    -- recproj_ tyfloat_ t (join ["c", int2string i])
    tupleproj_ i t
  in
  let primal_ = lam t. taylorcoefproj_ t 0 in
  let tangent_ = lam t. taylorcoefproj_ t 1 in
  let const_ = lam c. lam ty. TmConst {
    val = c,
    info = info,
    ty = ty
  } in
  let float_ = lam val. TmConst {
    val = CFloat { val = val },
    info = info,
    ty = TyFloat { info = info }
  } in
  let int_ = lam val. TmConst {
    val = CInt { val = val },
    info = info,
    ty = TyInt { info = info }
  } in
  let binop_ = lam const. lam x. lam y.
    let ty = TyFloat { info = info } in
    let tyarrow_ = ityarrow_ info in
    TmApp {
      lhs = TmApp {
        lhs = TmConst {
          val = const,
          info = info,
          ty = tyarrow_ ty (tyarrow_ ty ty)
        },
        rhs = x,
        info = info,
        ty = tyarrow_ ty ty
      },
      rhs = y,
      info = info,
      ty = ty
    }
  in
  let binpred_ = lam const. lam x. lam y.
    let ty = TyFloat { info = info } in
    let tyarrow_ = ityarrow_ info in
    TmApp {
      lhs = TmApp {
        lhs = TmConst {
          val = const,
          info = info,
          ty = tyarrow_ ty (tyarrow_ ty (TyBool { info = info }))
        },
        rhs = x,
        info = info,
        ty = tyarrow_ ty (TyBool { info = info })
      },
      rhs = y,
      info = info,
      ty = TyBool { info = info }
    }
  in
  let unop_ = lam const. lam x.
    let ty = TyFloat { info = info } in
    let tyarrow_ = ityarrow_ info in
    TmApp {
      lhs = TmConst {
        val = const,
        info = info,
        ty = tyarrow_ ty ty
      },
      rhs = x,
      ty = ty,
      info = info
    }
  in
  let addf_ = binop_ (CAddf ()) in
  let mulf_ = binop_ (CMulf ()) in
  let subf_ = binop_ (CSubf ()) in
  let divf_ = binop_ (CDivf ()) in
  let negf_ = unop_ (CNegf ()) in
  let eqf_ = binpred_ (CEqf ()) in
  let ltf_ = binpred_ (CLtf ()) in
  let leqf_ = binpred_ (CLeqf ()) in
  let gtf_ = binpred_ (CGtf ()) in
  let geqf_ = binpred_ (CGeqf ()) in
  let neqf_ = binpred_ (CNeqf ()) in
  let sin_ = unop_ (CSin ()) in
  let cos_ = unop_ (CCos ()) in
  let sqrt_ = unop_ (CSqrt ()) in
  let exp_ = unop_ (CExp ()) in
  let let_ = lam id. lam body. lam inexpr.
    let tyAnnot = tyTm body in
    let ty = tyTm inexpr in
    TmLet {
      ident = id,
      tyAnnot = tyunknown_,
      tyBody = tyunknown_,
      body = body,
      inexpr = inexpr,
      ty = ty,
      info = info
    }
  in
  let tmLam = lam id. lam ty. lam body.
    TmLam {
      ident = id,
      tyParam = tyunknown_,
      tyAnnot = tyunknown_,
      body = body,
      ty = tyunknown_,
      info = info
    }
  in
  let liftedbinop_ = lam n. lam x. lam y. lam body.
    tmLam
      x
      (tytaylorcoef_ n)
      (tmLam
         y
         (tytaylorcoef_ n)
         body)
  in
  let liftedunop_ = lam n. lam x. lam body.
    tmLam
      x
      (tytaylorcoef_ n)
      body
  in
  let app = lam f. lam arg.
    TmApp {
      lhs = f,
      rhs = arg,
      ty = tyunknown_,
      info = info
    } in
  let apps = lam f. lam args. foldl app f args in
  let seq_ = lam tms. TmSeq {
    tms = tms,
    ty = TySeq { ty = tyTm (head tms), info = info },
    info = info
  } in
  {
    tyfloat = TyFloat { info = info },
    var = var_,
    tytaylorcoef = tytaylorcoef_,
    tydualnum = tydualnum_,
    taylorcoef = taylorcoef_,
    dualnum = dualnum_,
    record = record_,
    patrecord = patrecord_,
    recordproj = recproj_,
    taylorcoefproj = taylorcoefproj_,
    primal = primal_,
    tangent = tangent_,
    const = const_,
    float = float_,
    int = int_,
    binop = binop_,
    unop = unop_,
    binpred = binpred_,
    addf = addf_,
    mulf = mulf_,
    subf = subf_,
    divf = divf_,
    negf = negf_,
    sin = sin_,
    cos = cos_,
    sqrt = sqrt_,
    exp = exp_,
    eqf_ = eqf_,
    ltf = ltf_,
    leqf = leqf_,
    gtf = gtf_,
    geqf = geqf_,
    neqf = neqf_,
    liftedbinop = liftedbinop_,
    liftedunop = liftedunop_,
    lam_ = tmLam,
    let_ = let_,
    app = app,
    seq = seq_
  }
