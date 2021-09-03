-- A partial implementation of an Interactive Programmatic Modeling
-- (IPM) interface towards a Differential Algebraic (DAE) solver. The IPM
-- interface is discussed in the journal article "Interactive Programmatic
-- Modeling" https://dl.acm.org/doi/10.1145/3431387 by David Broman.

--Code written by Oscar Eriksson.

include "daecore-sundials.mc"

-- The DAE is given on the form:
--
-- F(x, dxdt, d2xdt, ..., u, th, t) = 0,
--
-- where the vectors x, dxdt, and d2xdt holds the dependent variables and their
-- derivatives, u the inputs, th the parameters, and the scalar t is the free
-- variable.

-- A tuple `(id, ord)` representing a dependent variable `id` at the
-- differentiation order `ord` w.r.t. the free variable. `id` is assumed to be
-- in the range [0, n-1], where n is the size of the DAE problem.
type IdOrd = (Int, Int)

-- A single scalar residual function in a high-index DAE
type Residual =
  Vector (DualNum -> DualNum) ->  -- x, the dependent variables
  Vector (DualNum -> DualNum) ->  -- u, the inputs
  Vector DualNum ->               -- th, the parameters
  DualNum ->                      -- t, the free variable
  DualNum

-- A high index DAE consists of a list of triples, where the first element in
-- the tuple is a residual function, the second element is a list of dependent
-- variables present in this particular residual function, and the third
-- element is a list of inputs appearing in the residual.
type DAE = [(Residual, [IdOrd], [Int])]

-- Computational parameters.
type IPMParamComp = {
  atol : Float, -- Absolute tolerances of the numerical solver
  rtol : Float  -- Relative tolerances of the numerical solver
}

-- The underlying numerical DAE solver is the variable step SUNDIALS IDA solver.
type IPMSession = DaecoreSolverSession

-- Input parameters.
type IPMInput = {
  -- Initial value of the free variable.
  t0 : Float,

  -- INITIALIZATION: If `Some tend` the solver will try to take a step to `tend`
  -- to find consistent initial values. See `IDACalcIC
  -- (icopt=IDA_YA_YDP_INIT)` in the IDA documentation. If `None` initial
  -- values are assumed to be consistent.
  --
  -- TRANSITION: If `Some tend` the solver will transition from the current
  -- value of the free variable to `tend`. If `None` the solver will take a
  -- single step as decided by its internal error control
  -- (currently unimplemented).
  tend : Option Float,

  -- The parameter vector of the DAE.
  th : Vector Float,

  -- A vector of vectors holding the inputs to the DAE. For each element u_i,
  -- u_i[0] holds the value for the i'th input, u_i[1] hold the value for the
  -- derivative of the i'th input w.r.t. to the free variable, u_i[2] hold the
  -- value for the second derivative of the i'th input, and so on.
  u : Vector (Vector Float),

  -- Initial values of the dependent variables and their derivatives, these can
  -- be guesses and/or a partial specification. See INITIALIZATION under
  -- `tend`. If unspecified, the initial value of the dependent variable is
  -- assumed 0. Specifications for variables at differentiation orders not
  -- appearing in the DAE are ignored.
  ivs : [(IdOrd, Float)]
}

-- Output parameters, currently empty.
type IPMParamOut = { }

-- Output from the model compilation function. Later on this should be replaces
-- by code generation.
type IPMCompileOut =  {
  -- Initialization function.
  init : IPMInput -> IPMParamComp -> IPMSession,

  -- Transition function.
  trans : IPMSession -> IPMInput -> IPMParamComp -> Bool,

  -- Output function.
  output : IPMSession -> IPMInput -> IPMParamOut -> [IdOrd] -> [Float]
}

let _init : DaecoreResidual -> IPMInput -> IPMParamComp -> IPMSession =
lam res. lam input. lam pc.
  let s =
    daecoreSolverInit res {
      rtol = pc.rtol,
      atol = pc.atol,
      th = input.th,
      t0 = input.t0,
      ivs = input.ivs,
      u = input.u
  } in
  match input.tend with Some tend then
    daecoreSolverConsistentIvs s tend; s
  else s

let _trans : IPMSession -> IPMInput -> IPMParamComp -> Bool =
lam s. lam input. lam pc.
  match input.tend with Some tend then
    let r = daecoreSolverSolveNormal s tend input.u in
    match r with IdaSuccess _ | IdaRootsFound _ then true
    else false
   else match input.tend with None _ then error "Single step is unimplemented"
   else never

let _output
  : IPMSession -> IPMInput -> IPMParamOut -> [IdOrd] -> [Float] =
lam s. lam input. lam po. lam ys.
  map (daecoreSolverX s) ys

-- Compiles the DAE `model`. If `stabilize` is `true` the DAE is index-reduced
-- and stabilized, if `false` it is naively index-reduced.
let ipmCompile : DAE -> { stablize : Bool } -> IPMCompileOut =
lam model. lam ps.
  let res =
    if ps.stablize then daecoreResidualStabilized model
    else daecoreResidual model
  in
  { init = _init res, trans = _trans, output = _output }

-- Helper function to print `ylabels` on a line separated by `sep` on stdout.
let ipmPrintHeader = lam sep : String. lam ylabels : [(IdOrd, String)].
  let labels =
    map
      (lam y : (IdOrd, String). join ["d", int2string (idOrdOrd y.0), y.1])
      ylabels
  in
  printLn (strJoin sep labels)

-- Helper function to print `yvals` on a line separated by `sep` on stdout.
let ipmPrintYvals = lam sep : String. lam yvals : [(IdOrd, String)].
  printLn (strJoin sep (map float2string yvals))
