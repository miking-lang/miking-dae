include "option.mc"
include "string.mc"
include "map.mc"
include "tensor.mc"
include "../../daecore-ipm.mc"

let parseNumber = lam n.
  if stringIsInt n then int2float (string2int n)
  else string2float n

let parseLabel = lam l.
  let l = strSplit "der(" l in
  let n = pred (length l) in
  let l = join ((strSplit ")" (join l))) in
  (l, n)

let readIvs = lam file.
  let s = readFile file in
  match strSplit "\n" s with [labels, ivs] ++ _ then
    let labels = map parseLabel (map strTrim (strSplit "," labels)) in
    let ivs = map parseNumber (map strTrim (strSplit "," ivs)) in
    zip labels ivs
  else error "simulate.readIvs: Malformed initial values file"

-- let x = dprint (readIvs "pendulum-3d/ivs.csv")

let simulate = lam arg : {
    dae : DAE,
    ivs : [((String, Int), Float)],
    stabilize : Bool,
    th : Vector Float,
    labels : [String],
    dt : Float,
    tend : Float
  }.
  let u = tcreate [0] (lam. tcreate [0] (lam. 0.)) in
  let ys = mapi (lam i. lam. (i, 0)) arg.labels in
  let t0 = 0. in
  let labelIdxs = mapFromSeq cmpString (mapi (lam i. lam l. (l, i)) arg.labels) in
  let ivs =
    foldl
      (lam acc. lam iv : ((String, Int), Float).
        match iv with ((x, n), v) then
          let i = mapFindWithExn x labelIdxs in
          snoc acc ((i, n), v)
        else never)
      []
      arg.ivs
  in

  let pc = { rtol = 1.e-4, atol = 1.e-6 } in
  let input =
    -- { t0 = subf t0 arg.dt, tend = Some t0, th = arg.th, u = u, ivs = ivs }
    { t0 = t0, tend = None (), th = arg.th, u = u, ivs = ivs }
  in

  let co : IPMCompileOut = ipmCompile arg.dae { stablize = arg.stabilize } in
  let s = co.init input pc in
  print (tensor2string int2string (daecoreSolverXOffsets s));
  recursive let loop = lam t.
    if geqf t arg.tend then ()
    else
      -- _printResidual s;
      let yvals = co.output s input {} ys in
      ipmPrintYvals "," yvals;
      let r = co.trans s { { input
        with tend = Some (addf t arg.dt) }
        with u = u
      } pc in
      if r then loop (addf t arg.dt)
      else error "simulation failed"
  in

  ipmPrintHeader "," (zip ys arg.labels);
  loop 0.
