include "arg.mc"

include "./ast.mc"
include "./error-print.mc"
include "./dae-arg.mc"
include "./parse.mc"
include "./desugar.mc"
include "./pprint.mc"
include "./compile.mc"

lang PEADAE =
  DAEAst +
  DAEParseAst +
  DAEParseDesugar +
  DAEParseAnalysis +
  DAECompile
end

mexpr

use PEADAE in

switch argParse defaultOptions argConfig
case ParseOK r then
  -- Print menu if not exactly one file argument
  if neqi (length r.strings) 1 then
    print (usage (get argv 0));
    exit 1
  else
    (if r.options.debug then logSetLogLevel logLevel.debug else ());
    let res =
      let filename = head r.strings in
      logMsg logLevel.debug (lam. strJoin " " ["compiling", filename]);
      let prog = parseDAEParseExn filename (readFile filename) in
      result.bind (daeProgWellFormed prog)
        (lam prog.
          let t = daeCompile r.options (daeDesugarProg prog) in
          printLn (strJoin "\n" ["mexpr", expr2str t]);
          result.ok ())
    in
    consumeWarnErrsExn res
case result then
  argPrintError result;
  exit 1
end
