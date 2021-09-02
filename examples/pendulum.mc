include "../daecore-sundials.mc"

let pendulum = testSystems.pendulum.dae
let res = daecoreResidualStabilized pendulum

let m = 0.5
let g = 9.81
let l = 1.2

let theta = divf pi 4.
let ivs =
  let x1   = mulf l (sin theta) in
  let x2   = mulf (negf l) (cos theta) in
  let x3   = divf (mulf (mulf m g) x2) l in
  let d2x1 = divf (mulf x3 x1) m in
  let d2x2 = subf (divf (mulf x3 x2) m) g in
[
	((0, 0), x1),
	((0, 2), d2x1),
	((1, 0), x2),
	((1, 2), d2x2),
	((2, 0), x3)
]

let u = tcreate [2] (lam. tcreate [1] (lam. 0.))
let th = tensorOfSeqExn tcreate [3] [m, g, l]

let vs = [(0, 0), (1, 0)]
let labels = ["x", "y"]
let deltat = 0.01

mexpr
let s =
  daecoreSolverInit
    res
    { rtol = 1.e-4, atol = 1.e-6, u = u, th = th, t0 = negf deltat, ivs = ivs }
in

recursive let loop = lam n.
  if leqi n 0 then ()
  else
    daecoreSolverPrintResult s vs;
    let t = daecoreSolverT s in
    let r = daecoreSolverSolveNormal s (addf t deltat) u in
    match r with IdaSuccess _ | IdaRootsFound _ then
      loop (pred n)
    else error "simulation failed"
in

daecoreSolverConsistentIvs s 0.;
daecoreSolverPrintHeader (zip vs labels);
loop 10000;

()
