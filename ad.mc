include "error.mc"
include "list.mc"
include "log.mc"

include "mexpr/const-types.mc"

include "./ast.mc"
include "./ad-ast-builder.mc"

lang AD = DAEAst + MExprConstType
  type ADEnv = List (Name, Expr)
  type ADCtx = { env : ADEnv }

  sem adCtxEmpty : () -> ADCtx
  sem adCtxEmpty =| _ -> { env = adEnvEmpty () }

  sem adCtxEnvLookup : Name -> ADCtx -> Option Expr
  sem adCtxEnvLookup id =| ctx -> adEnvLookup id ctx.env

  sem adCtxEnvInsert : Name -> Expr -> ADCtx -> ADCtx
  sem adCtxEnvInsert id e =| ctx ->
    { ctx with env = adEnvInsert id e ctx.env }

  sem adEnvEmpty : () -> ADEnv
  sem adEnvEmpty =| _ -> listEmpty

  sem adEnvLookup : Name -> ADEnv -> Option Expr
  sem adEnvLookup id =| env ->
    let p = lam entry. nameEqSymUnsafe id entry.0 in
    match listFind p env with Some (_, e) then Some e else None ()

  sem adEnvInsert : Name -> Expr -> ADEnv -> ADEnv
  sem adEnvInsert id e =| env -> listCons (id, e) env

  sem adType : Int -> Type -> Type
  sem adType n =
  | ty & TyFloat r -> let b = peadAstBuilder r.info in b.tydualnum
  | ty -> smap_Type_Type (adType n) ty


  sem ad : Int -> Expr -> Expr
  sem ad n =| t -> adExpr (adCtxEmpty ()) n t

  sem adExpr : ADCtx -> Int -> Expr -> Expr
  sem adExpr ctx n =| t ->
    if lti n 0 then
      error (join ["adExpr: Invalid invalid input n: ", int2string n])
    else
      if eqi n 0 then t else adExprH ctx n t

  sem adExprH : ADCtx -> Int -> Expr -> Expr
  sem adExprH ctx n =
  | t & TmVar r ->
    switch adCtxEnvLookup r.ident ctx
    case Some t then t
    case None _ then t
      -- errorSingle [r.info]
      --   (join ["Cannot lift ", nameGetStr r.ident])
    end
  | TmDVar r ->
    let b = peadAstBuilder r.info in
    b.taylorcoef
      (create (succ n) (lam i. TmDVar { r with order = addi r.order i }))
  | TmLam r ->
    let b = peadAstBuilder r.info in
    let tyParam = adType n r.tyParam in
    let ctx = adCtxEnvInsert r.ident (b.var tyParam r.ident) ctx in
    let body = adExprH ctx n r.body in
    b.lam_ r.ident tyParam body
  | TmLet r ->
    let b = peadAstBuilder r.info in
    let tyBody = adType n r.tyBody in
    let body = adExprH ctx n r.body in
    let ctx = adCtxEnvInsert r.ident (b.var tyBody r.ident) ctx in
    let inexpr = adExprH ctx n r.inexpr in
    b.let_ r.ident body inexpr
  | TmConst r -> adConst r.info n r.val
  | TmMatch r ->
    let target = adExprH ctx n r.target in
    match adPat ctx n r.pat with (envThn, pat) in
    let thn = adExprH envThn n r.thn in
    let els = adExprH ctx n r.els in
    let ty = adType n r.ty in
    TmMatch { r with
              target = target,
              pat = pat,
              thn = thn,
              els = els,
              ty = ty
    }
  | t ->
    smap_Expr_TypeLabel (adType n)
      (smap_Expr_Type (adType n)
         (smap_Expr_Expr (adExprH ctx n) t))

  sem adPat : ADCtx -> Int -> Pat -> (ADCtx, Pat)
  sem adPat ctx n =
  | PatNamed (r & { ident = PName ident, ty = ty, info = info }) ->
    let b = peadAstBuilder info in
    let ty = adType n ty in
    let ctx = adCtxEnvInsert ident (b.var ty ident) ctx in
    (ctx, PatNamed { r with ty = ty })
  | pat ->
    match smapAccumL_Pat_Pat (lam ctx. adPat ctx n) ctx pat with (ctx, pat) in
    (ctx, withTypePat (adType n (tyPat pat)) pat)

  sem _adBinOp : Info -> Int -> ([[(Expr, Expr)]] -> Expr) -> Expr
  sem _adBinOp info n =| bodyf ->
    let b = peadAstBuilder info in
    let x = nameSym "x" in
    let y = nameSym "y" in
    let xvar = b.var (b.tytaylorcoef n) x in
    let yvar = b.var (b.tytaylorcoef n) y in
    let args =
      create (succ n)
        (lam i.
          create
            (succ i)
            (lam i. (b.taylorcoefproj xvar i, b.taylorcoefproj yvar i)))
    in
    b.liftedbinop n x y (bodyf args)

  sem _adUnOp : Info -> Int -> ([[Expr]] -> Expr) -> Expr
  sem _adUnOp info n =
  | bodyf ->
    let b = peadAstBuilder info in
    let x = nameSym "x" in
    let xvar = b.var (b.tytaylorcoef n) x in
    let args = create (succ n) (lam i. create (succ i) (b.taylorcoefproj xvar)) in
    b.liftedunop n x (bodyf args)

  sem _adSinCos : Bool -> Info -> [[Expr]] -> Expr
  sem _adSinCos sin info =| args ->
    let b = peadAstBuilder info in
    switch args
    case [[arg]] ++ args then
      let n = succ (length args) in
      let ss = create n (lam i. nameSym (join ["s", int2string i])) in
      let cs = create n (lam i. nameSym (join ["c", int2string i])) in
      let bs =
        let map3 = lam f. lam as. lam bs. lam cs.
          zipWith (lam x. uncurry (f x)) as (zip bs cs)
        in
        let mapi2 = lam f. lam xs. map3 f (create (length xs) (lam i. i)) xs in
        let bs  =
          map
            (lam args.
              let f = lam args : [Expr]. lam xs.
                let g = lam i. lam arg. lam x.
                  let v = b.mulf arg (b.var b.tyfloat x) in
                  if gti i 0 then
                    b.mulf (b.float (int2float (succ i))) v
                  else v
                in
                let ts = zip args xs in
                match unzip ts with (args, xs) in
                let v =
                  foldl1 b.addf (mapi2 g (tail args) (reverse (init xs)))
                in
                let x = last xs in
                let k = pred (length ts) in
                if gti k 1 then
                  (x, b.divf v (b.float (int2float k)))
                else
                  (x, v)
              in
              match (f args ss, f args cs) with ((s, ss), (c, cs)) in
              [(s, cs), (c, b.negf ss)])
            args
        in
        let bs = cons ([(head cs, b.cos arg), (head ss, b.sin arg)]) bs in
        let bs = (reverse (join bs)) in
        match bs with [cb, sb] ++ bs then
          if sin then cons sb bs else cons cb bs
        else error "impossible"
      in
      foldl
        (lam inexpr. lam x. b.let_ x.0 x.1 inexpr)
        (b.taylorcoef (map (b.var b.tyfloat) (if sin then ss else cs)))
        bs
    case _ then error "_adSinCos: Invalid input"
    end

  sem adConst : Info -> Int -> Const -> Expr
  sem adConst info n =
  | CFloat r ->
    let b = peadAstBuilder info in
    b.taylorcoef (cons (b.float r.val) (create n (lam. b.float 0.)))
  | CAddf _ ->
    let b = peadAstBuilder info in
    _adBinOp info n
      (lam args.
        b.taylorcoef
          (map (lam arg. match last arg with (x, y) in b.addf x y) args))
  | CMulf _ ->
    let b = peadAstBuilder info in
    _adBinOp info n
      (lam args.
        b.taylorcoef
          (map
             (lam arg.
               let n = length arg in
               match unzip arg with (xs, ys) in
               let terms = zipWith b.mulf xs (reverse ys) in
               let cs = pascalrow (pred n) in
               let terms =
                 zipWith
                   (lam c. lam t.
                     if eqi c 1 then t else b.mulf (b.float (int2float c)) t)
                   cs
                   terms
               in
               foldl1 b.addf terms)
             args))
  | CSubf _ ->
    let b = peadAstBuilder info in
    _adBinOp info n
      (lam args.
        b.taylorcoef
          (map (lam arg. match last arg with (x, y) in b.subf x y) args))
  | CDivf _ ->
    let b = peadAstBuilder info in
    _adBinOp info n
      (lam args.
        let n = length args in
        let vs = create n (lam i. nameSym (join ["v", int2string i])) in
        let vvars = map (b.var b.tyfloat) vs in
        let bs =
          map
            (lam arg.
              match unzip arg with (xs, ys) in
              let terms =  zipWith b.mulf (init vvars) (reverse (tail ys)) in
              let xn = last xs in
              let y0 = head ys in
              if null terms then b.divf xn y0
              else b.divf (b.subf xn (foldl1 b.addf terms)) y0)
            args
        in
        foldl2
          (lam inexpr. lam id. lam body. b.let_ id body inexpr)
          (b.taylorcoef vvars)
          (reverse vs)
          (reverse bs))
  | CNegf _ ->
    let b = peadAstBuilder info in
    _adUnOp info n (lam args. b.taylorcoef (map (lam arg. b.negf (last arg)) args))
  | CSin _ -> _adUnOp info n (_adSinCos true info)
  | CCos _ -> _adUnOp info n (_adSinCos false info)
  | CSqrt _ ->
    let b = peadAstBuilder info in
    _adUnOp info n
      (lam args.
        let n = length args in
        let vs = create n (lam i. nameSym (join ["v", int2string i])) in
        let vvars = map (b.var b.tyfloat) vs in
        let bs =
          map
            (lam arg.
              switch arg
              case [x] then b.sqrt x
              case [x, xp] then b.divf xp (b.mulf (b.float 2.) (head vvars))
              case xs then
                let n = length xs in
                let terms =
                  let vvars = subsequence vvars 1 (subi n 2) in
                  let l = length vvars in
                  let m = if isEven l then divi l 2 else divi (succ l) 2 in
                  let tmp = subsequence vvars 0 m in
                  let mulf2 = b.mulf (b.float 2.) in
                  let sum = foldl1 b.addf in
                  if isEven l then
                    mulf2 (sum (zipWith b.mulf tmp (reverse vvars)))
                  else
                    switch tmp
                    case [vvar] then b.mulf vvar vvar
                    case tmp ++ [vvar] then
                      b.addf
                        (mulf2 (sum (zipWith b.mulf tmp (reverse vvars))))
                        (b.mulf vvar vvar)
                    end
                in
                let xn = last xs in
                let v0 = head vvars in
                let dn = b.mulf (b.float 2.) v0 in
                b.divf (b.subf xn terms) dn
              end)
            args
        in
        foldl2
          (lam inexpr. lam id. lam body. b.let_ id body inexpr)
          (b.taylorcoef vvars)
          (reverse vs)
          (reverse bs))
  | CExp _ ->
    let b = peadAstBuilder info in
    _adUnOp info n
      (lam args.
        let n = length args in
        let vs = create n (lam i. nameSym (join ["v", int2string i])) in
        let vvars = map (b.var b.tyfloat) vs in
        let bs =
          map
            (lam arg.
              switch arg
              case [x] then b.exp x
              case xs then
                let k = pred (length xs) in
                let vvars = (splitAt vvars k).0 in
                let terms =
                  zipWith b.mulf (tail xs) (reverse vvars)
                in
                let terms =
                  mapi
                    (lam i. lam t.
                      if eqi i 0 then t
                      else b.mulf (b.float (int2float (succ i))) t)
                    terms
                in
                let sum = foldl1 b.addf terms in
                if eqi k 1 then sum
                else b.divf sum (b.float (int2float k))
              end)
            args
        in
        foldl2
          (lam inexpr. lam id. lam body. b.let_ id body inexpr)
          (b.taylorcoef vvars)
          (reverse vs)
          (reverse bs))
  | c & (CEqf _ | CLtf _ | CLeqf _ | CGtf _ | CGeqf _ | CNeqf _)->
    let b = peadAstBuilder info in
    let ty = b.tytaylorcoef n in
    let x = nameSym "x" in
    let y = nameSym "y" in
    b.lam_ x ty
      (b.lam_ y ty
         (b.binpred c
            (b.primal (b.var ty x))
            (b.primal (b.var ty y))))
  | c -> TmConst { val = c, info = info, ty = tyConst c }

  sem isDiscreteType : Type -> Bool
  sem isDiscreteType =| ty -> isDiscreteTypeH true ty

  sem isConstantType : Type -> Bool
  sem isConstantType =| ty -> isConstantTypeH true ty

  sem constantAD : Expr -> Expr
  sem constantAD =| t -> constantADH t (tyTm t)

  sem isDiscreteTypeH : Bool -> Type -> Bool
  sem isDiscreteTypeH acc =
  | TyFloat _ -> false
  | ty -> sfold_Type_Type isDiscreteTypeH acc ty

  sem isConstantTypeH : Bool -> Type -> Bool
  sem isConstantTypeH acc =
  | TyArrow r -> and (isDiscreteType r.from) (isDiscreteType r.to)
  | ty -> sfold_Type_Type isConstantTypeH acc ty

  sem constantADH : Expr -> Type -> Expr
  sem constantADH t =
  | ty & TyFloat _ ->
    let b = peadAstBuilder (infoTm t) in
    b.dualnum t (b.float 0.)
  | ty & TyRecord r ->
    let b = peadAstBuilder (infoTm t) in
    let x = nameSym "r" in
    b.let_ x t
      (b.record (adType 1 ty)
         (mapMapWithKey (lam l. lam ty.
           constantADH (b.recordproj ty (b.var ty x) (sidToString l)) ty)
            (r.fields)))
  | ty ->
    if isDiscreteType ty then t
    else
      errorSingle [infoTm t]
        (join ["constantAD undefined for:\n", expr2str t])

  sem adStandardExpr : Expr -> Expr
  sem adStandardExpr =
  | TmConst r -> adConst r.info r.val
  | t ->
    smap_Expr_TypeLabel (adType 1)
      (smap_Expr_Type (adType 1)
         (smap_Expr_Expr adStandardExpr t))

end

lang TestLang = AD + MExprTypeCheck + MExprPrettyPrint + MExprEq end

mexpr

use  TestLang in

let __test = lam n. lam expr.
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "Before ad",
      expr2str expr
    ]);
  let expr = typeCheck (symbolize expr) in
  let expr = ad n expr in
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "After ad",
      expr2str expr
    ]);
  expr
in

let _parse = parseDAEExprExn in

---------------------------
-- Test AD (first-order) --
---------------------------

-- logSetLogLevel logLevel.debug;

let _test = __test 1 in

let prog = _parse "
  1.
" in
utest _test prog with _parse "
(1., 0.)
  "
  using eqExpr in

let prog = _parse "
  lam x:Float. x
" in
utest _test prog with _parse "
  lam x. x"
  using eqExpr in

let prog = _parse "
  addf
" in
utest _test prog with _parse "
lam x. lam y. (addf x.0 y.0, addf x.1 y.1)
  "
  using eqExpr in

let prog = _parse "
  mulf
" in
utest _test prog with _parse "
lam x. lam y.
  (mulf x.0 y.0,
   addf
     (mulf x.0 y.1)
     (mulf x.1 y.0))
  "
  using eqExpr in

let prog = _parse "
  subf
" in
utest _test prog with _parse "
lam x. lam y.
  (subf x.0 y.0, subf x.1 y.1)
  "
  using eqExpr in

let prog = _parse "
  divf
" in
utest _test prog with _parse "
lam x. lam y.
  let v0 = divf x.0 y.0 in
  let v1 = divf
             (subf (x.1) (mulf v0 (y.1)))
             y.0
  in
  (v0, v1)
  "
  using eqExpr in

-- logSetLogLevel logLevel.debug;

let prog = _parse "
  negf
" in
utest _test prog with _parse "
lam x. (negf x.0, negf x.1)
  "
  using eqExpr in

-- logSetLogLevel logLevel.error;

-- logSetLogLevel logLevel.debug;

let prog = _parse "
  ltf
" in
utest _test prog with _parse "
lam x. lam y. ltf x.0 y.0
  "
  using eqExpr in

-- logSetLogLevel logLevel.error;

---------------------------
-- Test AD (third-order) --
---------------------------

let _test = __test 3 in

-- logSetLogLevel logLevel.debug;

let prog = _parse "
  1.
" in
utest _test prog with _parse "
(1., 0., 0., 0.)
  "
  using eqExpr in

-- logSetLogLevel logLevel.error;

let prog = _parse "
  lam x:Float. x
" in
utest _test prog with _parse "
  lam x. x"
  using eqExpr in

let prog = _parse "
  addf
" in
utest _test prog with _parse "
lam x. lam y.
  (addf x.0 y.0, addf x.1 y.1, addf x.2 y.2, addf x.3 y.3)
  "
  using eqExpr in

let prog = _parse "
  mulf
" in
utest _test prog with _parse "
lam x. lam y.
  (mulf x.0 y.0,
   addf (mulf x.0 y.1) (mulf x.1 y.0),
   addf
     (addf (mulf x.0 y.2) (mulf 2. (mulf x.1 y.1)))
     (mulf x.2 y.0),
   addf
     (addf
        (addf (mulf x.0 y.3) (mulf 3. (mulf x.1 y.2)))
        (mulf 3. (mulf x.2 y.1)))
     (mulf x.3 y.0))
  "
  using eqExpr in

let prog = _parse "
  subf
" in
utest _test prog with _parse "
lam x. lam y. (subf x.0 y.0, subf x.1 y.1, subf x.2 y.2, subf x.3 y.3)
  "
  using eqExpr in

let prog = _parse "
  divf
" in
utest _test prog with _parse "
lam x. lam y.
  let v0 = divf x.0 y.0 in
  let v1 = divf (subf x.1 (mulf v0 y.1)) y.0 in
  let v2 =
    divf
      (subf
         x.2
         (addf
            (mulf v0 y.2)
            (mulf v1 y.1)))
      y.0
  in
  let v3 =
    divf
      (subf
         x.3
         (addf
            (addf
               (mulf v0 y.3)
               (mulf v1 y.2))
            (mulf v2 y.1)))
      y.0
  in
  (v0, v1, v2, v3)
  "
  using eqExpr in

let prog = _parse "
  negf
" in
utest _test prog with _parse "
lam x. (negf x.0, negf x.1, negf x.2, negf x.3)
  "
  using eqExpr in

-- logSetLogLevel logLevel.error;

---------------------------------------------
-- Test AD (third-order) Extended builtins --
---------------------------------------------

let prog = _parse "
  sin
" in
utest _test prog with _parse "
lam x.
  let c0 = cos x.0 in
  let s0 = sin x.0 in
  let s1 = mulf x.1 c0 in
  let c1 = negf (mulf x.1 s0) in
  let s2 =
    divf
      (addf
         (mulf x.1 c1)
         (mulf 2. (mulf x.2 c0)))
      2.
  in
  let c2 =
    negf
      (divf
         (addf
            (mulf x.1 s1)
            (mulf 2. (mulf x.2 s0)))
         2.)
  in
  let s3 =
    divf
      (addf
         (addf
            (mulf x.1 c2)
            (mulf 2. (mulf x.2 c1)))
         (mulf 3. (mulf x.3 c0)))
      3.
  in
  (s0, s1, s2, s3)
  "
  using eqExpr in

let prog = _parse "
  cos
" in
utest _test prog with _parse "
lam x.
  let c0 = cos x.0 in
  let s0 = sin x.0 in
  let s1 = mulf x.1 c0 in
  let c1 = negf (mulf x.1 s0) in
  let s2 =
    divf
      (addf
         (mulf x.1 c1)
         (mulf 2. (mulf x.2 c0)))
      2.
  in
  let c2 =
    negf
      (divf
         (addf
            (mulf x.1 s1)
            (mulf 2. (mulf x.2 s0)))
         2.)
  in
  let c3 =
    negf
      (divf
        (addf
           (addf
              (mulf x.1 s2)
              (mulf 2. (mulf x.2 s1)))
           (mulf 3. (mulf x.3 s0)))
        3.)
  in
  (c0, c1, c2, c3)
  "
  using eqExpr in

let prog = _parse "
  sqrt
" in
utest _test prog with _parse "
lam x.
  let v0 = sqrt x.0 in
  let v1 = divf x.1 (mulf 2. v0) in
  let v2 = divf (subf x.2 (mulf v1 v1)) (mulf 2. v0) in
  let v3 =
    divf
      (subf
         x.3
         (mulf 2. (mulf v1 v2)))
      (mulf 2. v0)
  in
  (v0, v1, v2, v3)
  "
  using eqExpr in

let prog = _parse "
  exp
" in
utest _test prog with _parse "
lam x.
  let v0 = exp x.0 in
  let v1 = mulf x.1 v0 in
  let v2 =
    divf
      (addf (mulf x.1 v1) (mulf 2. (mulf x.2 v0)))
      2.
  in
  let v3 =
    divf
      (addf
         (addf (mulf x.1 v2) (mulf 2. (mulf x.2 v1)))
         (mulf 3. (mulf x.3 v0)))
      3.
  in
  (v0, v1, v2, v3)
  "
  using eqExpr in

----------------------
-- Test Constant AD --
----------------------

-- Test predicates on discrete and constant types

utest isDiscreteType (tyfloat_) with false in
utest isDiscreteType (tyint_) with true in
utest isDiscreteType (tyarrow_ tyint_ tyint_) with true in
utest isDiscreteType (tyarrow_ tyfloat_ tyint_) with false in
utest isDiscreteType (tyarrow_ tyint_ tyfloat_) with false in

utest isConstantType (tyfloat_) with true in
utest isConstantType (tyint_) with true in
utest isConstantType (tyarrow_ tyint_ tyint_) with true in
utest isConstantType (tyarrow_ tyfloat_ tyint_) with false in
utest isConstantType (tyarrow_ tyint_ tyfloat_) with false in
utest isConstantType (tytuple_ [tyfloat_, tyfloat_]) with true in
utest isConstantType (tytuple_ [(tyarrow_ tyint_ tyint_), tyfloat_])
  with true
in
utest isConstantType (tytuple_ [(tyarrow_ tyfloat_ tyint_), tyfloat_])
  with false
in
utest isConstantType (tytuple_ [(tyarrow_ tyint_ tyfloat_), tyfloat_])
  with false
in

-- Test constant type-directed lifting

let _test = lam expr.
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "Before constant lift",
      expr2str expr
    ]);
  let expr = typeCheck (symbolize expr) in
  match constantAD expr with expr in
  logMsg logLevel.debug (lam.
    strJoin "\n" [
      "After constant lift",
      expr2str expr
    ]);
  expr
in

let prog = _parse "let x = 1. in x" in
utest _test prog with _parse "
(let x = 1. in x, 0.)
  "
  using eqExpr
in

let prog = _parse "let f = lam x:Int. x in f" in
utest _test prog with _parse "let f = lam x:Int. x in f" using eqExpr in

let prog = _parse "let x = (1.,2.) in x" in
utest _test prog with _parse "
let r =
  let x = (1., 2.) in x
in
((r.0, 0.), (r.1, 0.))
  "
  using eqExpr
in

-- logSetLogLevel logLevel.debug;

let prog = _parse "let x = (lam x:Int. x, 2.) in x" in
utest _test prog with _parse "
let r =
  let x = (lam x1: Int. x1, 2.) in x
in
(r.0, (r.1, 0.))
  "
  using eqExpr
in

()
