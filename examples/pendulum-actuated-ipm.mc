-- Example showing compilation and simulation of pendulum DAE using the IPM
-- interface.

include "../daecore-ipm.mc"

-- A pendulum in Cartesian coordinates (index-3 DAE).
let dae = {
  residual = lam th. lam u. lam x.
    -- parameters
    let m = th 0 in
    let g = th 1 in
    let l = th 2 in
    -- inputs
    let u1 = u 0 in
    let u2 = u 1 in
    -- states
    let x1 = x 0 in
    let x2 = x 1 in
    let x3 = x 2 in
    -- residual functions
    let f1 = lam t.
      subn (muln m (nder 2 x1 t)) (addn (muln (x1 t) (x3 t)) (u1 t))
    in
    let f2 = lam t.
      addn
        (subn (muln m (nder 2 x2 t)) (addn (muln (x2 t) (x3 t)) (u2 t)))
        (muln m g)
    in
    let f3 = lam t.
      subn (addn (muln (x1 t) (x1 t)) (muln (x2 t) (x2 t))) (muln l l)
    in
    [f1, f2, f3],

  variables =
    let xs1 = [(0, 0), (0, 2), (2, 0)] in
    let xs2 = [(1, 0), (1, 2), (2, 0)] in
    let xs3 = [(0, 0), (1, 0)] in
    [xs1, xs2, xs3],

  inputs =
    let us1 = [0] in
    let us2 = [1] in
    let us3 = [] in
    [us1, us2, us3]
}

-- Physical parameters.
let m = 0.5     -- Pendulum mass [Kg]
let g = 9.81    -- Acceleration of gravity [m/s^2]
let l = 1.2     -- Pendulum arm length [m]

-- Vector of parameters.
let th = vecOfSeq [m, g, l]

-- Initial values.
let phi = divf pi 4.  -- Angle between the pendulum and the negative y-axis.
let ivs =
  let x1   = mulf l (sin phi) in
  let x2   = mulf (negf l) (cos phi) in
  let x3   = divf (mulf (mulf m g) x2) l in
  let d2x1 = divf (mulf x3 x1) m in
  let d2x2 = subf (divf (mulf x3 x2) m) g in
[
	-- ((0, 0), { val = x1, lb = negf inf, ub = inf })
	-- ((0, 2), { val = d2x1, lb = negf inf, ub = inf}),
	-- ((1, 0), { val = x2, lb = negf inf, ub = inf})
	-- ((1, 2), { val = d2x2, lb = negf inf, ub = inf}),
	-- ((2, 0), { val = x3, lb = negf inf, ub = inf})
]

-- Initial value constraints
let g = lam th. lam u. lam t. lam x. lam g.
  let l = th 2 in
  let x1 = x 0 in
  let x2 = x 1 in
  vecSet g 0 (subn (x1 t) (muln l (sinn (num phi))));
  vecSet g 1 (x2 t);
  ()

let constraintsLb = vecOfSeq [0., negf inf]
let constraintsUb = vecOfSeq [0., 0.]

-- Vector of inputs and their derivatives.
let u = vecCreate 2 (lam. vecCreate 1 (lam. 0.))

-- Label the positions.
let ys = [(0, 0), (1, 0)]
let labels = ["x", "y"]

-- Length of transitions.
let dt = 0.01

-- Computation parameters.
let pc = { rtol = 1.e-4, atol = 1.e-6, nlptol = 1.e-6, nlpsoltol = 1.e-6 }

-- Input parameters to the IPM interface.
let doSolveInitialNLP = true -- Solve initial NLP
let doIDACalcIC = false      -- Use IDACalcIC (icopt=IDA_YA_YDP_INIT)

let input = {
  t0 = if doIDACalcIC then negf dt else 0.,
  tend = if doIDACalcIC then Some 0. else None (),
  th = th,
  u = u,
  ivs = ivs,
  solveInitialNLP = doSolveInitialNLP,
  constraintsLb = constraintsLb,
  constraintsUb = constraintsUb
}

mexpr

logSetLogLevel logLevel.info;

-- Compile the DAE model.
let co : IPMCompileOut = ipmCompile (dae, g) { stabilize = true } in

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
