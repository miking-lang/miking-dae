-- A partial implementation of an Interactive Programmatic Modeling
-- (IPM) interface towards a Differential Algebraic (DAE) solver. The IPM
-- interface is discussed in the journal article "Interactive Programmatic
-- Modeling" https://dl.acm.org/doi/10.1145/3431387 by David Broman.

--Code written by Oscar Eriksson.

include "daecore.mc"
include "daecore-sundials-ad.mc"

-- Computational parameters.
type IPMParamComp = {
  atol : Float, -- Absolute tolerances of the numerical solver
  rtol : Float  -- Relative tolerances of the numerical solver
}

-- The underlying numerical DAE solver is the variable step SUNDIALS IDA solver.
type IPMSession = {
  _solverSession : DaecoreSolverSession,
  _y : Vector Float,
  _yp : Vector Float,
  _u :  Vector Float,
  _getstate : IdOrd -> Float,
  _structureU : [IdOrd]
}

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

let _populateU =
  lam structureU : [IdOrd]. lam uIn : Vector (Vector Float). lam uOut : Vector Float.
    iteri
      (lam i. lam u. vecSet uOut i (vecGet (vecGet uIn (idOrdId u)) (idOrdOrd u)))
      structureU

let _getstate =
  lam structureY : [IdOrd].
  lam structureYP : [IdOrd].
  lam y : Vector Float.
  lam yp : Vector Float.
    let ymap = mapFromSeq cmpIdOrd (mapi (lam i. lam y. (y, i)) structureY) in
    let ypmap = mapFromSeq cmpIdOrd (mapi (lam i. lam y. (y, i)) structureYP) in
    lam x : IdOrd.
      if mapMem x ymap then vecGet y (mapFindWithExn x ymap)
      else if mapMem x ypmap then vecGet yp (mapFindWithExn x ypmap)
      else error "Invalid Argument: _getstate"

let _init : DaecoreResidual -> IPMInput -> IPMParamComp -> IPMSession =
lam res.
  -- initialize state and input vectors
  let ny = length res.structureY in
  let y = vecCreateFloat ny (lam. 0.) in
  let yp = vecCreateFloat ny (lam. 0.) in
  let u = vecCreateFloat (length res.structureU) (lam. 0.) in
  lam input. lam pc.
    -- populate state and input vectors
    let ivs = mapFromSeq cmpIdOrd input.ivs in
    iteri
      (lam i. lam x.
        if mapMem x ivs then vecSet y i (mapFindWithExn x ivs) else ())
      res.structureY;
    iteri
      (lam i. lam x.
        if mapMem x ivs then vecSet yp i (mapFindWithExn x ivs) else ())
      res.structureYP;
    _populateU res.structureU input.u u;
    -- construct solver session
    let solverSession = daecoreSolverInit {
        resf = res.resf,
        rtol = pc.rtol,
        atol = pc.atol,
        t = input.t0,
        y = y,
        yp = yp,
        th = input.th,
        u = u,
        isdiff = res.isdiff
    } in
    -- try to find consistent initial values of end time is defined
    (match input.tend with Some tend then
      daecoreSolverConsistentIvs solverSession { tend = tend, y = y, yp = yp }
     else ());
    {
      _solverSession = solverSession,
      _y = y,
      _yp = yp,
      _u = u,
      _getstate = _getstate res.structureY res.structureYP y yp,
      _structureU = res.structureU
    }

let _trans : IPMSession -> IPMInput -> IPMParamComp -> Bool =
lam s. lam input. lam pc.
  match input.tend with Some tend then
    -- update internal input vector
    _populateU s._structureU input.u s._u;
    -- solve for the current time interval
    let r = daecoreSolverSolveNormal s._solverSession {
      tend = tend,
      y = s._y,
      yp = s._yp,
      u = s._u
    } in
    match r with IdaSuccess _ | IdaRootsFound _ then true
    else false
   else match input.tend with None _ then error "Single step is unimplemented"
   else never

let _output
  : IPMSession -> IPMInput -> IPMParamOut -> [IdOrd] -> [Float] =
lam s. lam input. lam po. lam ys. map s._getstate ys

-- Compiles the DAE `model`. If `stabilize` is `true` the DAE is index-reduced
-- and stabilized, if `false` it is naively index-reduced. See the definition of
-- `DAE` in `daecore-dae.mc`.
let ipmCompile : [DAE] -> { stabilize : Bool } -> IPMCompileOut =
lam model. lam ps.
  let res =
    if ps.stabilize then daecoreResidualStabilized model
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
