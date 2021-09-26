-- A partial implementation of an Interactive Programmatic Modeling
-- (IPM) interface towards a Differential Algebraic (DAE) solver. The IPM
-- interface is discussed in the journal article "Interactive Programmatic
-- Modeling" https://dl.acm.org/doi/10.1145/3431387 by David Broman.

--Code written by Oscar Eriksson.

include "log.mc"
include "daecore.mc"
include "daecore-sundials-ad.mc"
include "ipopt/ipopt-ad.mc"

-- For brevity
let num = dualnumNum
let logError = lam msg. logError (concat "daecore-ipm." msg)
let logWarning = lam msg. logWarning (concat "daecore-ipm." msg)
let logInfo = lam msg. logInfo (concat "daecore-ipm." msg)
let logDebug = lam msg. logDebug (concat "daecore-ipm." msg)

-- Computational parameters.
type IPMParamComp = {
  atol : Float,                 -- Absolute tolerances of the numerical solver
  rtol : Float,                 -- Relative tolerances of the numerical solver
  nlptol : Float,               -- Tolerance of NLP solver
  nlpsoltol : Float             -- Accepted tolerance of objective function at
                                -- NLP solution
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

type InitialValue = {
  lb : Float,                   -- lower bound
  ub : Float,                   -- upper bound
  val : Float                   -- initial value
}

-- Input parameters.
type IPMInput = {
  -- Initial value of the free variable.
  t0 : Float,

  -- INITIALIZATION: If `Some tend` the solver will try to take a step to `tend`
  -- to find consistent initial values. See `IDACalcIC (icopt=IDA_YA_YDP_INIT)`
  -- in the IDA documentation. If `None` initial values are assumed to be
  -- consistent. This step is performed after solving the inital NLP if
  -- `solveInitialNLP` is `true`.
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
  ivs : [(IdOrd, InitialValue)],

  -- Try to find consistent inital values by solving a constrained non-linear
  -- program.
  solveInitialNLP : Bool,

  -- Lower and upper bounds for the initial value constraints.
  constraintsLb : Vector Float,
  constraintsUb : Vector Float
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
  lam structureU : [IdOrd].
  lam uIn : Vector (Vector Float).
  lam uOut : Vector Float.
    iteri
      (lam i. lam u.
        vecSet uOut i (vecGet (vecGet uIn (idOrdId u)) (idOrdOrd u)))
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

let _init : DaecoreIVP -> IPMInput -> IPMParamComp -> IPMSession =
lam ivp. lam input. lam pc.
  if
    all
      (flip tensorHasRank 1)
      [input.th, input.u, input.constraintsLb, input.constraintsUb]
  then if
    tensorHasSameShape input.constraintsLb input.constraintsUb
  then
    logInfo "_init: start of initialization";
    -- initialize state and input vectors
    let ny = length ivp.structureY in
    let y = vecCreateFloat ny (lam. 0.) in
    let yp = vecCreateFloat ny (lam. 0.) in
    let u = vecCreateFloat (length ivp.structureU) (lam. 0.) in
    -- populate input vector
    _populateU ivp.structureU input.u u;
    -- find consistent inital values by solving NLP
    let ivs = mapFromSeq cmpIdOrd input.ivs in
    let ivs =
      if input.solveInitialNLP then
        logInfo "_init: solving initial NLP";
        let nx = length ivp.structureX in
        let x = vecCreateFloat nx (lam. 0.) in
        let lb = vecCreateFloat nx (lam. negf inf) in
        let ub = vecCreateFloat nx (lam. inf) in
        iteri
          (lam i. lam iv.
            if mapMem iv ivs then
              let iv : InitialValue = mapFindWithExn iv ivs in
              vecSet x i iv.val;
              vecSet lb i iv.lb;
              vecSet ub i iv.ub;
              ()
            else ())
          ivp.structureX;
        logDebug
          (join [
            "_init: structure of nlp variable vector: ",
            "[", strJoin ", " (map idOrdToString ivp.structureX),"]"
          ]);
        logDebug
          (join [
            "_init: initial guess of nlp variable vector: ",
            (vecToString float2string x)
          ]);
        let th = vecCreate (vecLength input.th) (lam i. num (vecGet input.th i)) in
        let u = vecCreate (vecLength u) (lam i. num (vecGet u i)) in
        let p = ipoptAdCreateNLP {
         f = ivp.objf th u (num input.t0),
         g = ivp.g th u (num input.t0),
         lb = lb,
         ub = ub,
         constraintsLb = input.constraintsLb,
         constraintsUb = input.constraintsUb
        } in
        ipoptAddNumOption p "tol" pc.nlptol;
        ipoptAddStrOption p "mu_strategy" "adaptive";
        ipoptAddIntOption p "print_level" 0;
        ipoptAddStrOption p "sb" "yes"; -- supress banner
        match ipoptSolve p x with (SolveSucceeded _, objf) then
          logInfo "_init: found solution to initial NLP";
          (if (gtf objf pc.nlpsoltol) then
            logWarning
              "_init: initial NLP objective function above specified tolerance at solution (this might not be the global minima)"
          else ());
          logDebug
            (join ["_init: solution to initial NLP: ", (vecToString float2string x)]);
          let ivs =
            vecFoldi
              (lam ivs. lam i. lam val.
                snoc ivs { val = val, lb = vecGet lb i, ub = vecGet ub i})
            [] x
          in
          mapFromSeq cmpIdOrd (zip ivp.structureX ivs)
        else
          logError "_init: failed to find a solution to initial NLP";
          ivs
      else ivs
    in
    -- populate state vectors
    iteri
      (lam i. lam iv.
        if mapMem iv ivs then
          let iv : InitialValue = mapFindWithExn iv ivs in
           vecSet y i iv.val
        else ())
      ivp.structureY;
    logDebug
      (join [
        "_init: structure of state vector y: ",
        "[", strJoin ", " (map idOrdToString ivp.structureY),"]"
      ]);
    logDebug
      (join [
        "_init: initial values of state vector y: ",
        (vecToString float2string y)
      ]);
    iteri
      (lam i. lam iv.
        if mapMem iv ivs then
          let iv : InitialValue = mapFindWithExn iv ivs in
          vecSet yp i iv.val
        else ())
      ivp.structureYP;
    logDebug
      (join [
        "_init: structure of state vector y': ",
        "[", strJoin ", " (map idOrdToString ivp.structureYP),"]"
      ]);
    logDebug
      (join [
        "_init: initial values of state vector y': ",
        (vecToString float2string yp)
      ]);
    -- construct solver session
    let solverSession = daecoreSolverInit {
        resf = ivp.resf,
        rtol = pc.rtol,
        atol = pc.atol,
        t = input.t0,
        y = y,
        yp = yp,
        th = input.th,
        u = u,
        isdiff = ivp.isdiff
    } in
    -- try to find consistent initial values using
    -- `IDACalcIC (icopt=IDA_YA_YDP_INIT)` if end time is defined
    (match input.tend with Some tend then
      logInfo
        (join [
          "_init: trying to find consistent initial values using IDACalcIC (icopt=IDA_YA_YDP_INIT) ",
          "from ", float2string input.t0, " to ", float2string tend
        ]);
      daecoreSolverConsistentIvs solverSession { tend = tend, y = y, yp = yp };
      logDebug
        (join [
          "_init: initial values of state vector y: ",
          (vecToString float2string y)
        ]);
      logDebug
        (join [
          "_init: initial values of state vector y': ",
          (vecToString float2string yp)
        ]);
      ()
     else ());
    {
      _solverSession = solverSession,
      _y = y,
      _yp = yp,
      _u = u,
      _getstate = _getstate ivp.structureY ivp.structureYP y yp,
      _structureU = ivp.structureU
    }
  else error "Invalid Argument: _init"
  else error "Invalid Argument: _init"

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

-- Compiles the DAE with initial values constraints function `model`. If
-- `stabilize` is `true` the DAE is index-reduced and stabilized, if `false` it
-- is naively index-reduced. See the definition of `DAE` in `daecore-dae.mc`.
let ipmCompile : (DAE, ConstraintFun) -> { stabilize : Bool } -> IPMCompileOut =
lam model. lam ps.
  match model with (dae, g) then
    let ivp =
      if ps.stabilize then
        logInfo "ipmCompile: compiling stabilized model";
        daecoreIVPStabilized dae g
      else
        logInfo "ipmCompile: compiling naive model";
        daecoreIVP dae g
    in
    { init = _init ivp, trans = _trans, output = _output }
  else never

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
