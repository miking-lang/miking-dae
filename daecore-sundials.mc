include "string.mc"
include "daecore.mc"
include "sundials/sundials.mc"

----------------------
-- SOLVER INTERFACE --
----------------------

type DaecoreSolverSession = {
  _session : IdaSession,
  _v : NvectorSerial,
  _vp : NvectorSerial,
  _du : Vector (Vector DualNum),
  _t : Ref Float,
  _ds : Vector Int,
  _resf : Float -> Vector Float -> Vector Float -> Vector Float -> (),
	_stateGet : IdOrd -> Float
}

let _unpack = compose dualnumPrimalDeep dualnumUnpackNum

let _hasX : Vector Int -> IdOrd -> Bool =
  lam ds. lam x.
    let i = idOrdId x in
    let n = idOrdOrd x in
    and (lti i (tensorSize ds)) (and (geqi n 0) (leqi n (tget ds [i])))

let daecoreSolverInit
	: DaecoreResidual
  -> {
    rtol : Float,
    atol : Float,
    th : Vector Float,
    t0 : Float,
    ivs : [(IdOrd, Float)],
    u : Vector (Vector Float)
  }
  -> DaecoreSolverSession
= lam res. lam arg.
	let n = res.ny in
	let y = tensorCreateCArrayFloat [n] (lam. 0.) in
	let yp = tensorCreateCArrayFloat [n] (lam. 0.) in
	let v = nvectorSerialWrap y in
	let vp = nvectorSerialWrap yp in
	let m = sundialsMatrixDense n in
	let tol = idaSSTolerances arg.rtol arg.atol in

	-- Dual number states
	let z = tcreate [n] (lam. num 0.) in
	let zp = tcreate [n] (lam. num 0.) in
  let du =
    tcreate
      [tensorSize res.es]
      (lam idx.
        let u = tget arg.u idx in
        tcreate [succ (tget res.es idx)] (lam idx. num (tget u idx)))
  in

  let dth = tcreate [tensorSize arg.th] (lam idx. num (tget arg.th idx)) in
	let dr = tcreate [n] (lam. num 0.) in
	let dm = tcreate [n, n] (lam. num 0.) in

	let resf = lam t. lam y. lam yp. lam r.
		tensorMapExn num y z;
		tensorMapExn num yp zp;
		res.res (num t) z zp du dth dr;
		tensorMapExn _unpack dr r;
		()
	in

	let jacf = lam jacargs : IdaJacArgs. lam m : SundialsMatrixDense.
	  let m = sundialsMatrixDenseUnwrap m in
		tensorMapExn num jacargs.y z;
		tensorMapExn num jacargs.yp zp;

		jacT (lam z. res.res (num jacargs.t) z zp du dth) z dm;
		tensorIteri (lam idx. lam x. tset m idx (_unpack x)) dm;

		jacT (lam zp. res.res (num jacargs.t) z zp du dth) zp dm;
		tensorIteri
			(lam idx. lam x.
				tset m idx (addf (tget m idx) (mulf jacargs.c (_unpack x))))
			dm;

		()
	in

	let lsolver = idaDlsDense v m in
	-- let lsolver = idaDlsSolverJacf jacf lsolver in
	let lsolver = idaDlsSolver lsolver in

	let varid =
		let f = lam x. if x then idaVarIdDifferential else idaVarIdAlgebraic in
		nvectorSerialWrap
			(tensorOfSeqExn tensorCreateCArrayFloat [n] (map f (isdiff res.ds)))
	in

  -- set initial values
  iter
    (lam ivs : (IdOrd, Float).
      if _hasX res.ds ivs.0 then
        res.stateSet y yp ivs.0 ivs.1
      else ())
     arg.ivs;

	let rootf = lam. lam. lam. lam. () in
	let s = idaInit lsolver tol resf varid (0, rootf) arg.t0 v vp in

	{
		_session = s,
		_v = v,
		_vp = vp,
    _du = du,
    _t = ref arg.t0,
    _resf = resf,
    _ds = res.ds,
		_stateGet = res.stateGet y yp
	}

let _printResidual = lam s : DaecoreSolverSession.
  let y = nvectorSerialUnwrap s._v in
  let yp = nvectorSerialUnwrap s._vp in
	let r = tensorCreateCArrayFloat [tensorSize y] (lam. 0.) in
  let t = s._t in
  s._resf t y yp r;
  printLn "y = ";
  printLn (tensorToString float2string y);
  printLn "yp = ";
  printLn (tensorToString float2string yp);
  printLn "r = ";
  printLn (tensorToString float2string r)

let daecoreSolverXOffsets : DaecoreSolverSession -> Vector Int =
  lam s. s._ds

let daecoreSolverHasX : DaecoreSolverSession -> IdOrd -> Bool =
  lam s. _hasX s._ds

let daecoreSolverX : DaecoreSolverSession -> IdOrd -> Float =
  lam s. s._stateGet

let daecoreSolverT : DaecoreSolverSession -> Float =
  lam s. deref (s._t)

let _daecoreSolverSetUs : DaecoreSolverSession -> Vector (Vector Float) -> () =
  lam s. lam u.
    tensorIteri (lam idx. lam t. tensorMapExn num t (tget s._du idx)) u

let daecoreSolverConsistentIvs : DaecoreSolverSession -> Float -> () =
	lam s. lam tend.
		idaCalcICYaYd s._session tend s._v s._vp;
    modref s._t tend

let daecoreSolverSolveNormal
  : DaecoreSolverSession -> Float -> Vector (Vector Float) -> (Float, IdaSolverResult) =
lam s. lam tend. lam u.
  _daecoreSolverSetUs s u;
	let r = idaSolveNormal s._session tend s._v s._vp in
	match r with (tend, r) then
    modref s._t tend;
    (tend, idaSolverResult r)
	else never


-----------------------------
-- SOLVER OUTPUT INTERFACE --
-----------------------------

let _separator = ","
let _freevarlabel = "t"

let daecoreSolverPrintHeader : [(IdOrd, String)] -> () =
lam vs.
  printLn (strJoin _separator (map (lam v : (IdOrd, String). v.1) vs))

let daecoreSolverPrintResult : DaecoreSolverSession -> [IdOrd] -> () =
lam s. lam vs.
  printLn (strJoin _separator (map (lam v. float2string (daecoreSolverX s v)) vs))

mexpr

let runTests = lam residual.
  ----------------------------------
  -- HARMONIC OCCILATOR (INDEX 0) --
  ----------------------------------

  let f = lam xs. lam us. lam ths. lam t.
    let x = tget xs [0] in
    addn (nder 2 x t) (addn (der x t) (x t))
  in
  let xs = [(0, 0), (0, 1), (0, 2)] in
  let us = [] in
  let harmonicOccilator = [(f, xs, us)] in

  let ivs = [((0, 0), 1.)] in
  let th = tcreate [0] (lam. 0.) in
  let u =  tcreate [0] (lam. tcreate [0] (lam. 0.)) in

  let s =
    daecoreSolverInit
      (residual harmonicOccilator)
      { rtol = 1.e-4, atol = 1.e-6, u = u, th = th, t0 = 0., ivs = ivs }
  in

  utest daecoreSolverHasX s (0, 3) with false in
  utest daecoreSolverHasX s (0, 2) with true in
  utest daecoreSolverHasX s (0, 1) with true in
  utest daecoreSolverHasX s (0, 0) with true in

  daecoreSolverConsistentIvs s 1.e-4;
  let r = daecoreSolverSolveNormal s 2. u in

  (match r with (tend, r) then
    utest r with IdaSuccess () in
    utest tend with 2. using eqf in
    ()
  else never);


  ------------------------
  -- PENDULUM (INDEX 3) --
  ------------------------

  let pendulum = testSystems.pendulum.dae in

  let theta = divf pi 4. in
  let ivs =
    let x1   = sin theta in
    let x2   = negf (cos theta) in
    let x3   = negf (cos theta) in
    let d2x1 = mulf x3 x1 in
    let d2x2 = subf (mulf x3 x2) 1. in
  [
    ((0, 0), x1),
    ((0, 2), d2x1),
    ((1, 0), x2),
    ((1, 2), d2x2),
    ((2, 0), x3)
  ]
  in

  let th = tcreate [3] (lam. 1.) in
  let u =  tcreate [2] (lam. tcreate [1] (lam. 0.)) in

  let s =
    daecoreSolverInit
      (residual pendulum)
      { rtol = 1.e-4, atol = 1.e-6, u = u, th = th, t0 = 0., ivs = ivs }
  in
  daecoreSolverConsistentIvs s 1.e-4;
  let r = daecoreSolverSolveNormal s 2. u in

  (match r with (tend, r) then
    utest r with IdaSuccess () in
    utest tend with 2. using eqf in
    ()
  else never);

  ()
in

runTests daecoreResidual;
runTests daecoreResidualStabilized;

()
