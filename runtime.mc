include "math.mc"
include "sundials/sundials.mc"
include "sundials/ida.mc"
include "arg.mc"
include "option.mc"
include "ext/array-ext.mc"

let _debug = ref false
let debugPrint = lam msg.
  if deref _debug then
    printError (join ["LOG DEBUG:\t", msg ()]);
    printError "\n";
    flushStderr ()
  else ()

let doLoop : Int -> (Int -> ()) -> ()
  = lam n. lam f.
    recursive let doLoop = lam i.
      if eqi i n then ()
      else f i; doLoop (succ i)
    in
    doLoop 0

type Vec = Tensor[Float]
type Mat = Tensor[Float]

let vget = tensorLinearGetExn
let vset = tensorLinearSetExn
let vlength = lam v. head (tensorShape v)
let viteri = lam f. lam v. tensorIterSlice (lam i. lam v. f i (tensorGetExn v [])) v
let vcreate = lam n. lam f. tensorCreateCArrayFloat [n] (lam idx. f (head idx))
-- let mget = lam m. lam i. lam j. tensorGetExn m [i, j]
let mset = sundialsMatrixDenseSet
let mupdate = sundialsMatrixDenseUpdate

let vecToString = lam name. lam v.
  let n = vlength v in
  join
    (create n
       (lam i.
         join [name, "[", int2string i, "] = ", float2string (vget v i), "\n"]))

let stateToString = lam y. lam yp.
  join [vecToString "y" y, "\n", vecToString "y'" yp]

let usage = lam. strJoin " " ["USAGE:", get argv 0, "interval", "stepsize"]

let errorExit = lam. print (usage ()); print "\n"; exit 1

type DAEInit = ([Float], [Float])
type DAEResf = Array Float -> Array Float -> Tensor[Float] -> ()
type DAEJacVals = [((Int, Int), () -> Float)]
type DAEJacf = Array Float -> Array Float -> (DAEJacVals, DAEJacVals)
type DAEOutf = Array Float -> Array Float -> ()

type Options = {
  interval : Float,
  stepSize : Float,
  rtol : Float,
  atol : Float,
  outputOnlyLast : Bool,
  benchmarkResidual : Option Int,
  benchmarkJacobian : Option Int,
  debug : Bool,
  printStats : Bool,
  seed : Int
}

let defaultOptions = {
  interval = 20.,
  stepSize = 0.1,
  rtol = 1e-4,
  atol = 1e-6,
  outputOnlyLast = false,
  debug = false,
  dumpInfo = false,
  seed = 0
}

let argConfig = [
  ([("--interval", " ", "<value>")],
   "Simulation interval. ",
   lam p. { p.options with interval = argToFloatMin p 0. }),
  ([("--step-size", " ", "<value>")],
   "Interval where to output solution. ",
   lam p. { p.options with stepSize = argToFloatMin p 0. }),
  ([("--rtol", " ", "<value>")],
   "Relative tolerance. ",
   lam p. { p.options with rtol = argToFloatMin p 0. }),
  ([("--atol", " ", "<value>")],
   "Absolute tolerance. ",
   lam p. { p.options with atol = argToFloatMin p 0. }),
  ([("--output-only-last", "", "")],
   "Output only the solution after the last time-step. ",
   lam p. { p.options with outputOnlyLast = true }),
  ([("--debug", "", "")],
   "Debug runtime. ",
   lam p. { p.options with debug = true }),
  ([("--dump-info", "", "")],
   "Dump solver info to stderr. ",
   lam p. { p.options with dumpInfo = true }),
  ([("--seed", " ", "<value>")],
   "Random seed. ",
   lam p. { p.options with seed = argToIntMin p 0 })
]

let usage = lam prog. join [
  "Usage: ", prog, " [OPTION]\n\n",
  "Options:\n",
  argHelpOptions argConfig,
  "\n"
]

let _randState = lam y.
  doLoop (arrayLength y) (lam i.
    arraySet y i (int2float (randIntU 0 10)))

let _benchUsage = lam prog. join [prog, " INTEGER\n"]

let parseArgs = lam n.
  switch argParse defaultOptions argConfig
  case ParseOK r then
    -- Print menu if not exactly n arguments
    if neqi (length r.strings) n then
      print (usage (get argv 0));
      exit 1
    else (r.options, r.strings)
  case result then
    argPrintError result;
    exit 1
  end

let daeRuntimeBenchmarkRes : Int -> DAEResf -> ()
  = lam n. lam resf.
    match parseArgs 1 with (opt, [neval]) then
      -- Set seed
      randSetSeed opt.seed;
      if stringIsInt neval then
        let y = arrayCreateFloat n in
        let r = vcreate n (lam. 0.) in
        let neval = string2int neval in
        let sum = ref 0. in
        let ws = wallTimeMs () in
        doLoop neval (lam.
          _randState y;
          resf y y r;
          doLoop n (lam i.
            modref sum (addf (deref sum) (vget r i))));
        let wt = subf (wallTimeMs ()) ws in
        print (join [
          "Executed the residual ",
          int2string neval,
          " times in ",
          float2string wt,
          " ms, accumulating the residual value ",
          float2string (deref sum),
          "\n"
        ])
      else
        print (_benchUsage (get argv 0)); exit 1
    else
      print (_benchUsage (get argv 0)); exit 1

let daeRuntimeBenchmarkJac : Int -> DAEJacf -> DAEJacf -> ()
  = lam n. lam jacYf. lam jacYpf.
    match parseArgs 1 with (opt, [neval]) then
      -- Set seed
      randSetSeed opt.seed;
      if stringIsInt neval then
        let y = arrayCreateFloat n in
        let neval = string2int neval in
        let sum = ref 0. in
        let ws = wallTimeMs () in
        doLoop neval
          (lam.
            _randState y;
            let jy = iter (lam f. modref sum (addf (deref sum) (f.1 ()))) in
            let fs = jacYf y y in
            jy fs.0;
            jy fs.1;
            let jyp = iter (lam f. modref sum (addf (deref sum) (f.1 ()))) in
            let fs = jacYpf y y in
            jyp fs.0;
            jyp fs.1;
            ());
        let wt = subf (wallTimeMs ()) ws in
        print (join [
          "Executed the Jacobian ",
          int2string neval,
          " times in ",
          float2string wt,
          " ms, accumulating the value ",
          float2string (deref sum),
          "\n"
        ])
      else
        print (_benchUsage (get argv 0)); exit 1
    else
      print (_benchUsage (get argv 0)); exit 1

let daeRuntimeRun
  : Bool -> [Bool] -> DAEInit -> DAEResf -> DAEJacf -> DAEJacf -> DAEOutf -> ()
  = lam numjac. lam varids. lam initVals. lam resf. lam jacYf. lam jacYpf. lam outf.
    match parseArgs 0 with (opt, _) in
    let n = length varids in
    modref _debug opt.debug;
    let resEvalCount = ref 0 in
    let jacEvalCount = ref 0 in
    let resTimeCount = ref 0. in
    let jacTimeCount = ref 0. in
    -- Set seed
    randSetSeed opt.seed;
    -- Initialize
    match initVals with (y0, yp0) in
    let tol = idaSSTolerances opt.rtol opt.atol in
    let y = vcreate n (get y0) in
    let yp = vcreate n (get yp0) in
    -- Pre-allocate residual states
    -- OPT(oerikss, 2023-10-21): We read faster from these compared to BigArrays
    -- (i.e. Tensors)
    let ay = arrayCreateFloat n in
    let ayp = arrayCreateFloat n in
    let resf = lam t. lam y. lam yp. lam r.
      -- gather statistics
      modref resEvalCount (succ (deref resEvalCount));
      -- compute residual
      doLoop n (lam i.
        arraySet ay i (vget y i);
        arraySet ayp i (vget yp i));
      let ws = wallTimeMs () in
      resf ay ayp r;
      let we = wallTimeMs () in
      modref resTimeCount (addf (deref resTimeCount) (subf we ws));
      ()
    in
    let r = vcreate n (lam. 0.) in
    resf y yp r;
    debugPrint
      (lam. strJoin "\n"
            ["Initial residual:", stateToString y yp, vecToString "r" r]);
    let v = nvectorSerialWrap y in
    let vp = nvectorSerialWrap yp in
    let m = sundialsMatrixDense n in
    let nlsolver = sundialsNonlinearSolverNewtonMake v in
    let lsolver =
      if numjac then idaDlsSolver (idaDlsDense v m)
      else
        -- Pre-allocate Jacobian states
        -- OPT(oerikss, 2022-10-21): See the comment for the residiual function
        let ay = arrayCreateFloat n in
        let ayp = arrayCreateFloat n in
        let jacf = lam jacargs : IdaJacArgs. lam m : SundialsMatrixDense.
          -- gather statistics
          modref jacEvalCount (succ (deref jacEvalCount));
          -- compute Jacobian
          doLoop n (lam i.
            arraySet ay i (vget jacargs.y i);
            arraySet ayp i (vget jacargs.yp i));
          -- let m = sundialsMatrixDenseUnwrap m in
          let ws = wallTimeMs () in
          let jy =
            iter
              (lam ijf.
                match ijf with ((i, j), f) in
                -- m is in column-major format
                mset m i j (f ()))
          in
          let fs = jacYf ay ayp in
          jy fs.0;
          jy fs.1;
          let jyp =
            iter
              (lam ijf.
                match ijf with ((i, j), f) in
                -- m is in column-major format
                mupdate m i j (addf (mulf jacargs.c (f ()))))
          in
          let fs = jacYpf ay ayp in
          jyp fs.0;
          jyp fs.1;
          let we = wallTimeMs () in
          modref jacTimeCount (addf (deref jacTimeCount) (subf we ws));
          ()
        in
        idaDlsSolverJacf jacf (idaDlsDense v m)
    in
    let varid =
      nvectorSerialWrap
        (vcreate n
           (lam i. if get varids i then idaVarIdDifferential
                 else idaVarIdAlgebraic))
    in
    let t0 = negf 1.e-4 in
    let s = idaInit {
      tol      = tol,
      nlsolver = nlsolver,
      lsolver  = lsolver,
      resf     = resf,
      varid    = varid,
      roots    = idaNoRoots,
      t        = t0,
      y        = v,
      yp       = vp
    } in
    idaCalcICYaYd s { tend = 0., y = v, yp = vp };
    resf y yp r;
    debugPrint
      (lam. strJoin "\n"
            ["After idaCalcICYaYd:", stateToString y yp, vecToString "r" r]);
    idaSetStopTime s opt.interval;
    -- Solve
    -- Pre-allocate output states
    let ay = arrayCreateFloat n in
    let ayp = arrayCreateFloat n in
    recursive let recur = lam t.
      doLoop n (lam i.
        arraySet ay i (vget y i);
        arraySet ayp i (vget yp i));
      (if opt.outputOnlyLast then () else outf ay ayp);
      if gtf t opt.interval then ()
      else
        switch idaSolveNormal s { tend = addf t opt.stepSize, y = v, yp = vp }
        case (tend, IdaSuccess _) then recur tend
        case (_, IdaStopTimeReached _) then
          (if opt.outputOnlyLast then outf ay ayp else ()); ()
        case (tend, IdaRootsFound _) then
          printError (join ["Roots found at t = ", float2string tend]);
          flushStderr ()
        case (tend, IdaSolveError _) then
          printError (join ["Solver error at t = ", float2string tend]);
          flushStderr ()
        end
    in
    recur 0.;
    (if opt.dumpInfo then
      print (join ["resvals: ", int2string (deref resEvalCount), "\n"]);
      print (join ["jacevals: ", int2string (deref jacEvalCount), "\n"]);
      print (join ["restime: ", float2string (deref resTimeCount), "\n"]);
      print (join ["jactime: ", float2string (deref jacTimeCount), "\n"])
     else ());
    ()

mexpr

-- Hack that allows us to parse this file with dead-code elimination
dprint [
  dprint [daeRuntimeBenchmarkRes],
  dprint [daeRuntimeBenchmarkJac],
  dprint [daeRuntimeRun],
  dprint [sin, cos, exp, sqrt],
  dprint [pow],
  dprint [arrayGet],
  dprint [cArray1Set],
  dprint [sundialsMatrixDenseSet],
  dprint [sundialsMatrixDenseUpdate]
]
