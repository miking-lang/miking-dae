include "../simulate.mc"
include "model.mc"

mexpr

let ivs = readIvs "ivs.csv" in

simulate {
  dae = dae,
  ivs = ivs,
  stabilize = false,
  th = th,
  labels = labels,
  dt = 0.01,
  tend = 20.
}
