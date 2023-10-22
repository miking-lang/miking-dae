include "sys.mc"
include "option.mc"
include "log.mc"

include "mexpr/ast-builder.mc"
include "mexpr/utils.mc"
include "mexpr/symbolize.mc"
include "mexpr/cse.mc"
include "mexpr/const-transformer.mc"

include "./dae.mc"
include "./desugar.mc"
include "./dae-arg.mc"

let peadaeNameSpace = "PEADAE"

lang DAECompile =
  DAE + PEvalLetInline + MExprFindSym + MExprSubstitute + BootParser + CSE

  sem daeSrcPathExn : () -> String
  sem daeSrcPathExn =| () ->
    optionGetOrElse
      (lam. error
            (strJoin " " [
              peadaeNameSpace,
              "is unset. Please set it to point to the root of PEADAE source"
            ]))
      (sysGetEnv peadaeNameSpace)

  sem daeCompile : Options -> TmDAERec -> Expr
  sem daeCompile options =| daer ->
    let logDebug = lam head. lam msg.
      logDebug (lam. strJoin "\n" [join ["daeCompile:", head, ":"], msg ()])
    in
    match typeCheck (symbolize (TmDAE daer)) with
      TmDAE daer
    then
      -- Setup runtime
      let runtime =
        parseMCoreFile {
          defaultBootParserParseMCoreFileArg with
          eliminateDeadCode = true,
          allowFree = true
        } (join [daeSrcPathExn (), "/runtime.mc"])
      in
      let runtime = symbolize runtime in
      let runtimeNames = [
        "daeRuntimeRun",
        "daeRuntimeBenchmarkRes",
        "daeRuntimeBenchmarkJac",
        "sin",
        "cos",
        "exp",
        "pow",
        "sqrt",
        "arrayGet",
        "cArray1Set",
        "sundialsMatrixDenseSet",
        "sundialsMatrixDenseUpdate"
      ] in
      let runtimeNames =
        foldl2
          (lam runtimeNames. lam str. lam name.
            mapUpdate str (lam. name) runtimeNames)
          (mapEmpty cmpString)
          runtimeNames
          (findNamesOfStrings runtimeNames runtime)
      in
      -- Compile DAE
      let daer = daeAnnotDVars daer in
      let daer = if options.cse then daeCSE daer else daer in
      logDebug "analysis"
        (lam.
          strJoin " " ["number of equations:", int2string (length daer.eqns)]);
      let analysis = daeStructuralAnalysis daer in
      logDebug "analysis"
        (lam. strJoin " " [
          "max equation offset",
          int2string
            (maxOrElse (lam. error "impossible") subi analysis.eqnsOffset)
        ]);
      logDebug "analysis"
        (lam. strJoin " " [
          "number differentiated equations",
          int2string
            (length (filter (neqi 0) analysis.eqnsOffset))
        ]);
      -- let daer = if options.cse then daeDestructiveCSE daer else daer in
      let daer = daeIndexReduce analysis.eqnsOffset daer in
      let state = daeFirstOrderState analysis.varOffset in
      -- logDebug "first-order state"
      --   (lam. strJoin "\n"
      --         (mapi
      --            (lam i. lam y. join [
      --              int2string i, ":",
      --              theseThese
      --                (lam id. nameGetStr (daeID id))
      --                (lam id. nameGetStr (daeID id))
      --                (lam id1. lam id2. join [
      --                  nameGetStr (daeID id1), ",", nameGetStr (daeID id2)
      --                ])
      --                y
      --            ])
      --            state.ys));
      let isdiffvars = daeIsDiffVars state in
      let daer = daeOrderReduce state (nameSym "y") (nameSym "yp") daer in
      let ts = [
        daeGenInitExpr state daer,
        daeGenResExpr daer,
        daeGenOutExpr daer
      ]
      in
      let pevalInlineLets = pevalInlineLets (sideEffectEnvEmpty ()) in
      match
        if options.disablePeval then ts
        else map (lam t. pevalInlineLets (peval t)) ts
        with [iexpr, rexpr, oexpr]
      in
      match
        if options.constantFold then
          (pevalInlineLets iexpr, pevalInlineLets rexpr, pevalInlineLets oexpr)
        else (iexpr, rexpr, oexpr)
        with (iexpr, rexpr, oexpr)
      in
      -- match
      --   if options.cse then
      --     (cse iexpr, cse rexpr, cse oexpr)
      --   else (iexpr, rexpr, oexpr)
      --   with (iexpr, rexpr, oexpr)
      -- in
      let jacSpecThreshold =
        match options.jacSpecThresholdAbsolute with Some n then
          maxf (minf (divf (int2float n) (int2float (length daer.eqns))) 1.) 0.
        else options.jacSpecThreshold
      in
      match
        if options.numericJac then (ulam_ "" never_, ulam_ "" never_)
        else
          if options.disablePeval then
            (daeGenMixedJacY 0. daer, daeGenMixedJacYp 0. daer)
          else
            (daeGenMixedJacY jacSpecThreshold daer,
             daeGenMixedJacYp jacSpecThreshold daer)
        with (jacY, jacYp)
      in
      -- Generate runtime
      let _varids = nameSym "varids" in
      let  _initVals = nameSym "initVals" in
      let _resf = nameSym "resf" in
      let _jacYf = nameSym "jacYf" in
      let _jacYpf = nameSym "jacYpf" in
      let _outf = nameSym "outf" in
      let t =
        let n = length isdiffvars in
        switch (options.benchmarkResidual, options.benchmarkJacobian)
        case (true, false) then
          bind_ (nulet_ _resf rexpr)
            (appSeq_
               (nvar_ (mapFindExn "daeRuntimeBenchmarkRes" runtimeNames))
               [
                 int_ n,
                 (nvar_ _resf)
               ])
        case (false, true) then
          bindall_ [
            nulet_ _jacYf jacY,
            nulet_ _jacYpf jacYp,
            (appSeq_
               (nvar_ (mapFindExn "daeRuntimeBenchmarkJac" runtimeNames))
               [
                 int_ n,
                 (nvar_ _jacYf),
                 (nvar_ _jacYpf)
               ])
          ]
        case (true, true) then error "Unimplemented"
        case (false, false) then
          let t =
            bindall_[
              nulet_ _varids (seq_ (map bool_ isdiffvars)),
              nulet_ _initVals iexpr,
              nulet_ _resf rexpr,
              nulet_ _jacYf jacY,
              nulet_ _jacYpf jacYp,
              nulet_ _outf oexpr,
              appSeq_ (nvar_ (mapFindExn "daeRuntimeRun" runtimeNames))
                (cons
                   (bool_ options.numericJac)
                   (map nvar_
                      [_varids, _initVals, _resf, _jacYf, _jacYpf, _outf]))
            ]
          in
          let env =
            foldl
              (lam env. lam x. match x with (str, c) in
                           mapInsert c (mapFindExn str runtimeNames) env)
              (mapEmpty cmpConst)
              (daeBuiltin ())
          in
          constTransformConstsToVars env t
        end
      in
      -- let t =
      --   substituteIdentifiers
      --     (mapFromSeq
      --        nameCmp
      --        (map
      --           (lam x. (x.1, mapFindExn x.0 runtimeNames))
      --           (concat adBuiltinSymbols (mapBindings daeBuiltins))))
      --     t
      -- in
      bind_ runtime t
    else error "impossible"
end

lang TestLang = DAEParseAnalysis + DAEParseDesugar + DAECompile end

mexpr

use TestLang in

let _parse = lam prog.
  let prog = daeParseExn "internal" prog in
  logMsg logLevel.debug
    (lam. strJoin "\n" ["Input program:", daeProgToString prog]);
  let daer = daeDesugarProg prog in
  match typeCheck (symbolize (TmDAE daer)) with TmDAE daer then
    daer
  else error "impossible"
in

-------------------
-- Test Pendulum --
-------------------

logSetLogLevel logLevel.error;

let dae = _parse "
  let mul = lam x. lam y. x*y end
  let pow2 = lam x. mul x x end
  variables
  x, y, h : Float
  init
  x = 1.;
  x' = 2.;
  y'' = 0. - 1.
  equations
  x'' = mul x h;
  y'' = mul y h - 1.;
  pow2 x + pow2 y = pow2 1.
  output
  {x, x', x''}
  "
in

let t = daeCompile defaultOptions dae in

logMsg logLevel.debug
  (lam. strJoin "\n" ["Output program:", expr2str t]);

utest typeCheck (symbolize t); true with true in

()
