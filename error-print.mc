include "result.mc"
include "error.mc"

include "mexpr/info.mc"


let errorWarn : (Info, String) -> () = lam msg.
  printError (join ["\n", infoWarningString msg.0 msg.1, "\n"]);
  flushStderr ()

let errorDie : all a. (Info, String) -> a = lam msg.
  printError (join ["\n", infoErrorString msg.0 msg.1, "\n"]);
  flushStderr ();
  exit 1

let consumeWarnErrsExn = lam res.
  switch result.consume res
  case (ws, Right res) then
    (if not (null ws) then
      errorWarn (errorMsg ws {single = "", multi = ""})
     else ());
    res
  case (ws, Left errs) then
    errorWarn (errorMsg ws {single = "", multi = ""});
    errorDie (errorMsg errs {single = "", multi = ""})
  end
