include "ad/dualnum-lift.mc"
include "sundials/sundials.mc"
include "vec.mc"
include "mat.mc"

-- Brevity
let num = dualnumNum
let unpack = compose dualnumPrimalDeep dualnumUnpackNum

type DaecoreSolverSession = {
  _idaSession : IdaSession,
  _un : Vector DualNum,
  _v : NvectorSerial,
  _vp : NvectorSerial
}

type DaecoreSolverInitArg = {
  resf
    : DualNum
  -> Vector DualNum
  -> Vector DualNum
  -> Vector DualNum
  -> Vector DualNum
  -> Vector DualNum
  -> (),

  rtol : Float,
  atol : Float,
  t : Float,
  y : Vector Float,
  yp : Vector Float,
  th : Vector Float,
  u : Vector Float,
  isdiff : [Bool]
}

let daecoreSolverInit : DaecoreSolverInitArg -> DaecoreSolverSession
= lam arg.
  if all (lam t. tensorHasRank t 1) [arg.y, arg.yp, arg.th, arg.u] then
    let ny = tensorSize arg.y in   -- number of states
    let nth = tensorSize arg.th in -- number of parameters
    let nu =  tensorSize arg.u in  -- number of inputs
    if and (tensorHasShape arg.yp [ny]) (eqi (length arg.isdiff) ny) then
      -- internal state
      let yn = vecCreate ny (lam i. num (vecGet arg.y i)) in
      let ypn = vecCreate ny (lam i. num (vecGet arg.yp i)) in
      let thn = vecCreate nth (lam i. num (vecGet arg.th i)) in
      let un = vecCreate nu (lam i. num (vecGet arg.u i)) in
      let rn = vecCreate ny (lam. num 0.) in
      let jacn = matCreate (ny, ny) (lam. lam. num 0.) in
      let v = nvectorSerialWrap arg.y in
      let vp = nvectorSerialWrap arg.yp in
      let m = sundialsMatrixDense ny in
      -- residual function
      let resf = lam t. lam y. lam yp. lam r.
        vecMap (lam x. lam. num x) y yn;
        vecMap (lam x. lam. num x) yp ypn;
        arg.resf thn un (num t) yn ypn rn;
        vecMap (lam x. lam. unpack x) rn r;
        ()
      in
      -- Jacobian function
    	let jacf = lam jacargs : IdaJacArgs. lam jac : SundialsMatrixDense.
        let jac = sundialsMatrixDenseUnwrap jac in
        vecMap (lam x. lam. num x) jacargs.y yn;
        vecMap (lam x. lam. num x) jacargs.yp ypn;
        -- compute df[i]/dy[j]
        jacT (lam yn. arg.resf thn un (num jacargs.t) yn ypn) yn jacn;
        vecMap (lam x. lam. unpack x) jacn jac;
        -- compute df[i]/dyp[j]
        jacT (lam ypn. arg.resf thn un (num jacargs.t) yn ypn) ypn jacn;
        matMap
          (lam x1. lam x2. addf (mulf jacargs.c (unpack x1)) x2)
          jacn jac;
        ()
      in
	    let lsolver = idaDlsDense v m in
	    let lsolver = idaDlsSolverJacf jacf lsolver in
	    -- let lsolver = idaDlsSolver lsolver in
      -- construct varid vector
      let varid =
        nvectorSerialWrap (tensorCreateCArrayFloat [ny] (lam. idaVarIdAlgebraic))
      in
      iteri
        (lam i. lam isdiff.
          if isdiff then vecSet varid i idaVarIdDifferential else ())
        arg.isdiff;
      let tol = idaSSTolerances arg.rtol arg.atol in
    	let rootf = lam. lam. lam. lam. () in
	    let idaSession = idaInit lsolver tol resf varid (0, rootf) arg.t v vp in
      { _idaSession = idaSession, _un = un, _v = v, _vp = vp }
    else error "daecoreSolverInit: Invalid input (shape mismatch)"
  else error "daecoreSolverInit: Invalid input (expected rank 1 tensors)"


type DaecoreSolverConsistentIvsArg = {
  tend : Float,
  y : Vector Float,
  yp : Vector Float
}

let daecoreSolverConsistentIvs
  : DaecoreSolverSession -> DaecoreSolverConsistentIvsArg -> ()
= lam s. lam arg.
  idaCalcICYaYd s._idaSession arg.tend s._v s._vp;
  vecBlit (nvectorSerialUnwrap s._v) arg.y;
  vecBlit (nvectorSerialUnwrap s._vp) arg.yp;
  ()

type DaecoreSolverSolveNormalArg = {
  tend : Float,
  y : Vector Float,
  yp : Vector Float,
  u : Vector Float
}

let daecoreSolverSolveNormal
  : DaecoreSolverSession
  -> DaecoreSolverSolveNormalArg
  -> (Float, IdaSolverResult)
= lam s. lam arg.
  vecMap (lam u. lam. num u) arg.u s._un;
	let r = idaSolveNormal s._idaSession arg.tend s._v s._vp in
  vecBlit (nvectorSerialUnwrap s._v) arg.y;
  vecBlit (nvectorSerialUnwrap s._vp) arg.yp;
	match r with (tend, r) then
    (tend, idaSolverResult r)
	else never

mexpr

let resf = lam th. lam. lam t. lam y. lam yp. lam r.
  let k = vecGet th 0 in
  let omega = vecGet th 1 in
  let x = vecGet y 0 in
  let xdot = vecGet yp 0 in
  let v = vecGet y 1 in
  let a = vecGet yp 1 in
  vecSet r 0 (addn a (addn (muln k v) (muln omega x)));
  vecSet r 1 (subn v xdot);
  ()
in

let th = vecOfSeq [1., 1.] in
let u = vecOfSeq [] in
let y = vecOfSeqFloat [1., 0.] in
let yp = vecOfSeqFloat [0., 0.] in
let isdiff = [true, true] in

let s = daecoreSolverInit {
  resf = resf,
  rtol = 1.e-3,
  atol = 1.e-6,
  t = negf 1.e-4,
  y = y,
  yp = yp,
  th = th,
  u = u,
  isdiff = isdiff
} in

daecoreSolverConsistentIvs s { tend = 0., y = y, yp = yp };
let r = daecoreSolverSolveNormal s { tend = 2., y = y, yp = yp, u = u } in
(match r with (tend, r) then
  utest r with IdaSuccess () in
  utest tend with 2. using eqf in
  ()
else never);

()
