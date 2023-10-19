include "./lib/vec.mc"
include "./lib/mat.mc"

-- A tuple `(id, ord)` representing a dependent variable `id` at the
-- differentiation order `ord` w.r.t. the free variable. `id` is assumed to be
-- in the range [0, n-1], where n is the size of the DAE equation.
type IdOrd = (Int, Int)

let cmpIdOrd = lam x : IdOrd. lam y : IdOrd.
  match (x, y) with ((id1, ord1), (id2, ord2)) in
  if eqi id1 id2 then subi ord1 ord2
  else subi id1 id2

type EqnStructure = {
  -- Variables at the given differential order present in this equation.
  variables : [IdOrd],

  -- Inputs present in this equation
  inputs    : [Int]
}

-- A non-existent incidence in the sigma matrix.
let daecoreSigmaNoEdge = negi 100000

type DAEStructureLowIndex = {
  -- Encodes weighted incidence between variables (columns) and equations
  -- (rows), where the weights are the derivative order of the variable.
  sigma : Matrix Int,

  -- Equation offset vector which indicates the number of times the equation
  -- corresponding to each index needs to be differentiated in order to reduce
  -- the index to one or less.
  c : Vector Int,

  -- Variable offset vector which indicates the highest derivative order of the
  -- variables corresponding to each index.
  d : Vector Int,

  -- Input offset vector which indicated the highest derivative order of the
  -- inputs in the index reduced DAE.
  e : Vector Int,

  -- Indicates a matching between variables (index) and equations (values) in
  -- the index reduced DAE mode.
  varToEq : Vector Int
}

type DAEStructureLowIndexStable = {
  -- see `DAEStructureLowIndexRec`
  d : Vector Int,
  -- see `DAEStructureLowIndexRec`
  e : Vector Int,

  -- A vector indicating algebraic variables substituted for their derivatives.
  lambda : Vector Int,

  -- The number of dummy variables.
  nmu : Int,

  -- Non-differentiated differential equations.
  eqns0d : [Int],

  -- Non-differentiated algebraic equations.
  eqns0a : [Int],

  -- Non-Differentiated constraint equations.
  eqns0c : [Int],

  -- Differentiated constraint equations.
  eqnsNc : [IdOrd]
}
