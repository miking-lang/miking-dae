-- Example showing compilation and simulation of pendulum DAE using the IPM
-- interface.

include "../daecore-ipm.mc"

-- A pendulum in Cartesian coordinates (index-3 DAE).
let pendulum =
  let f1 = lam x. lam u. lam th. lam t.
    let m = vecGet th 0 in
    let u1 = vecGet u 0 in
    let x1 = vecGet x 0 in
    let x3 = vecGet x 2 in
    subn (muln m (nder 2 x1 t)) (addn (muln (x1 t) (x3 t)) (u1 t))
  in
  let xs1 = [(0, 0), (0, 2), (2, 0)] in
  let us1 = [0] in
  let f2 = lam x. lam u. lam th. lam t.
    let m = vecGet th 0 in
    let g = vecGet th 1 in
    let u2 = vecGet u 1 in
    let x2 = vecGet x 1 in
    let x3 = vecGet x 2 in
    addn
      (subn (muln m (nder 2 x2 t)) (addn (muln (x2 t) (x3 t)) (u2 t)))
      (muln m g)
  in
  let xs2 = [(1, 0), (1, 2), (2, 0)] in
  let us2 = [1] in
  let f3 = lam x. lam u. lam th. lam t.
    let l = vecGet th 2 in
    let x1 = vecGet x 0 in
    let x2 = vecGet x 1 in
    subn (addn (muln (x1 t) (x1 t)) (muln (x2 t) (x2 t))) (muln l l)
  in
  let xs3 = [(0, 0), (1, 0)] in
  let us3 = [] in
  [
    { residual = f1, variables = xs1, inputs = us1 },
    { residual = f2, variables = xs2, inputs = us2 },
    { residual = f3, variables = xs3, inputs = us3 }
  ]


-- Physical parameters.
let m = 0.5     -- Pendulum mass [Kg]
let g = 9.81    -- Acceleration of gravity [m/s^2]
let l = 1.2     -- Pendulum arm length [m]

-- Initial values.
let theta = divf pi 4.  -- Angle between the pendulum and the negative y-axis.
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

-- Vector of inputs and their derivatives.
let u = vecCreate 2 (lam. vecCreate 1 (lam. 0.))

-- Vector of parameters.
let th = vecOfSeq [m, g, l]

-- Label the positions.
let ys = [(0, 0), (1, 0)]
let labels = ["x", "y"]

-- Length of transitions.
let dt = 0.01

-- Computation parameters.
let pc = { rtol = 1.e-4, atol = 1.e-6 }

-- Input parameters to the IPM interface. Note that we let the solver find
-- consistent initial values.
let input = { t0 = negf dt, tend = Some 0., th = th, u = u, ivs = ivs }

mexpr

-- Compile the DAE model.
let co : IPMCompileOut = ipmCompile pendulum { stabilize = true } in

-- Initialize the model.
let s = co.init input pc in

-- We simulate until this time.
let tend = 100. in

-- Simulation loop, `t` is the current time.
recursive let loop = lam t.
  if geqf t tend then ()
  else
    -- Output some of the dependent variables and print them stdout.
    let yvals = co.output s input {} ys in
    ipmPrintYvals "," yvals;
    -- Update the input vectors.
    vecSet (vecGet u 0) 0 (sin t);
    -- Transition the dynamics.
    let r =
      co.trans s { { input with tend = Some (addf t dt) } with u = u } pc
    in
    if r then loop (addf t dt)
    else error "simulation failed"
in

-- Print headers to stdout.
ipmPrintHeader "," (zip ys labels);

-- Start the simulation.
loop 0.;

()
