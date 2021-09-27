include "math.mc"
include "ad/dualnum.mc"
include "maxmatch-tensor.mc"
include "digraph.mc"
include "set.mc"
include "mat.mc"
include "vec.mc"
include "daecore-dae.mc"

-------------------
-- PRELIMINARIES --
-------------------

-- temporary, should be intrinsics or placed in seq.mc
let filteri = lam p.
  recursive let recur = lam acc. lam i. lam xs.
    match xs with [x] ++ xs then
      let acc = if p x then snoc acc i else acc in
      recur acc (addi i 1) xs
    else match xs with [] then
      acc
    else never
  in
  recur [] 0

-- For brevity
let num = dualnumNum

-- Constants
let _neginf = negi (1000000)

-- A sufficiently large negative number representing a non-existant edge in the
-- graph corresponding to the sigma matrix
let sigmaNoEdge = _neginf

-- Short circuit and/or
let or = lam x. lam y. if x then true else y
let and = lam x. lam y. if not x then false else y

------------------
-- TEST SYSTEMS --
------------------

type DaecoreTestSystem = {
  dae : DAE,
  sigma : Matrix Int,
  cs : Vector Int,
  ds : Vector Int,
  es : Vector Int,
  incidenceI : Vector Int,
  incidenceJ : Vector Int,
  blocks : [[Int]],
  assignedVars : [[Int]],
  assignedBlocks : [Int],
  varsInBlock : [[Int]],
  lambdas : Vector Int,
  varIdxOffsets : Vector Int,
  inputIdxOffsets : Vector Int,
  aliases : [(Int, Int)]
}

let testSystems
  : {pendulum : DaecoreTestSystem, linsysOtter : DaecoreTestSystem} =
  let n = sigmaNoEdge in
{
  pendulum = {
    dae = {
      residual = lam th. lam u. lam x.
        -- parameters
        let m = vecGet th 0 in
        let g = vecGet th 1 in
        let l = vecGet th 2 in
        -- inputs
        let u1 = vecGet u 0 in
        let u2 = vecGet u 1 in
        -- states
        let x1 = vecGet x 0 in
        let x2 = vecGet x 1 in
        let x3 = vecGet x 2 in
        -- residual functions
        let f1 = lam t.
          subn (muln m (nder 2 x1 t)) (addn (muln (x1 t) (x3 t)) (u1 t))
        in
        let f2 = lam t.
          addn
            (subn (muln m (nder 2 x2 t)) (addn (muln (x2 t) (x3 t)) (u2 t)))
            (muln m g)
        in
        let f3 = lam t.
          subn (addn (muln (x1 t) (x1 t)) (muln (x2 t) (x2 t))) (muln l l)
        in
        [f1, f2, f3],

      variables =
        let xs1 = [(0, 0), (0, 2), (2, 0)] in
        let xs2 = [(1, 0), (1, 2), (2, 0)] in
        let xs3 = [(0, 0), (1, 0)] in
        [xs1, xs2, xs3],

      inputs =
        let us1 = [0] in
        let us2 = [1] in
        let us3 = [] in
        [us1, us2, us3]
    },


    sigma = matOfSeq (3, 3) [
      2, n, 0,
      n, 2, 0,
      0, 0, n
    ],

    cs = vecOfSeq [0, 0, 2],
    ds = vecOfSeq [2, 2, 0],
    es = vecOfSeq [0, 0],
    incidenceI = vecOfSeq [0, 2, 1],
    incidenceJ = vecOfSeq [0, 2, 1],
    blocks = [[0, 1, 2]],
    assignedVars = [[0, 2, 1]],
    assignedBlocks = [0, 0, 0],
    varsInBlock = [[0, 1, 2]],
    lambdas = vecOfSeq [0, 0, 1],
    varIdxOffsets = vecOfSeq [0, 2, 4],
    inputIdxOffsets = vecOfSeq [0, 1],
    aliases = [(1, 0), (3, 2)]
  },

  linsysOtter = {
    dae = {
      residual = lam th. lam u. lam x.
        -- inputs
        let u1 = vecGet u 0 in
        let u2 = vecGet u 1 in
        let u3 = vecGet u 2 in
        let u4 = vecGet u 3 in
        let u5 = vecGet u 4 in
        let u6 = vecGet u 5 in
        let u7 = vecGet u 6 in
        let u8 = vecGet u 7 in
        -- states
        let x1 = vecGet x 0 in
        let x2 = vecGet x 1 in
        let x3 = vecGet x 2 in
        let x4 = vecGet x 3 in
        let x5 = vecGet x 4 in
        let x6 = vecGet x 5 in
        let x7 = vecGet x 6 in
        let x8 = vecGet x 7 in
        let f1 = lam t.
          addn (u1 t) (addn (x1 t) (x2 t))
        in
        let f2 = lam t.
          addn (u2 t) (addn (x1 t) (subn (x2 t) (subn (x3 t) (der x6 t))))
        in
        let f3 = lam t.
          addn (u3 t) (addn (x1 t) (subn (der x3 t) (x4 t)))
        in
        let f4 = lam t.
          addn (u4 t)
               (addn (muln (num 2.) (nder 2 x1 t))
                     (addn (nder 2 x2 t)
                           (addn (nder 2 x3 t)
                                 (addn (der x4 t)
                                       (nder 3 x6 t)))))
        in
        let f5 = lam t.
          addn (u5 t)
               (addn (muln (num 3.) (nder 3 x1 t))
                     (addn (muln (num 2.) (nder 3 x2 t))
                           (addn (x5 t)
                                 (muln (num 0.1) (x8 t)))))
        in
        let f6 = lam t.
          addn (u6 t)
               (addn (muln (num 2.) (x6 t))
                     (x7 t))
        in
        let f7 = lam t.
          addn (u7 t)
               (addn (muln (num 3.) (x6 t))
                     (muln (num 4.) (x7 t)))
        in
        let f8 = lam t.
          addn (u8 t) (x8 t)
        in
        [f1, f2, f3, f4, f5, f6, f7, f8],

      variables =
        let xs1 = [(0, 0), (1, 0)] in
        let xs2 = [(0, 0), (1, 0), (2, 0), (5, 1)] in
        let xs3 = [(0, 0), (2, 1), (3, 0)] in
        let xs4 = [(0, 2), (1, 2), (2, 2), (3, 1), (5, 3)] in
        let xs5 = [(0, 2), (1, 2), (4, 0), (7, 0)] in
        let xs6 = [(5, 0), (6, 0)] in
        let xs7 = [(5, 0), (6, 0)] in
        let us7 = [6] in
        let xs8 = [(7, 0)] in
        [xs1, xs2, xs3, xs4, xs5, xs6, xs7, xs8],

      inputs = [[0], [1], [2], [3], [4], [5], [6], [7]]
    },

    sigma = matOfSeq (8, 8)
      [0, 0, n, n, n, n, n, n  -- x1 - x2
      ,0, 0, 0, n, n, 1, n, n  -- x1 + x2 - x3 + x6'
      ,0, n, 1, 0, n, n, n, n  -- x1 + x3' - x4
      ,2, 2, 2, 1, n, 3, n, n  -- 2x1'' + x2'' + x3'' + x4' + x6'''
      ,2, 2, n, n, 0, n, n, 0  -- 3x1'' + 2x2'' + x5 + 0.1x8
      ,n, n, n, n, n, 0, 0, n  -- 2x6 + x7
      ,n, n, n, n, n, 0, 0, n  -- 3x6 + 4x7
      ,n, n, n, n, n, n, n, 0],-- x8

    cs = vecOfSeq [2, 2, 1, 0, 0, 3, 3, 0],
    ds = vecOfSeq [2, 2, 2, 1, 0, 3, 3, 0],
    es = vecOfSeq [2, 2, 1, 0, 0, 3, 3, 0],
    incidenceI = vecOfSeq [1, 0, 2, 3, 4, 6, 5, 7],
    incidenceJ = vecOfSeq [1, 0, 2, 3, 4, 6, 5, 7],
    blocks = [[0, 1, 2, 3], [4], [5, 6], [7]],
    assignedVars = [[0, 1, 2, 3], [4], [5, 6], [7]],
    assignedBlocks = [0, 0, 0, 0, 1, 2, 2, 3],
    varsInBlock = [[0, 1, 2, 3, 5], [0, 1, 4, 7], [5, 6], [7]],
    lambdas = vecOfSeq [0, 0, 0, 0, 1, 0, 0, 0],
    varIdxOffsets = vecOfSeq [0, 2, 4, 6, 7, 8, 11, 14],
    inputIdxOffsets = vecCreate 0 (lam. 0),
    aliases = [(1, 0), (3, 2), (5, 4), (9, 8), (10, 9), (12, 11), (13, 12)]
  }
}

------------------
-- SIGMA METHOD --
------------------

-- Constructs the sigma matrix from a sequence `xss`, where each element
-- corresponds to an equation and is a seqence of dependent variables present
-- in that equation.
let sigmaMatrix : [[IdOrd]] -> Matrix Int =
  lam xss.
    let n = length xss in
    let t = matCreate (n, n) (lam. lam. sigmaNoEdge) in
    iteri
      (lam i. lam xs.
        iter
          (lam x.
            let d = maxi (matGet t i (idOrdId x)) (idOrdOrd x) in
            matSet t i (idOrdId x) d)
          xs)
      xss;
    t

utest
  let xs = testSystems.pendulum.dae.variables in
  sigmaMatrix xs
with testSystems.pendulum.sigma
using matEq eqi

utest
  let xs = testSystems.linsysOtter.dae.variables in
  sigmaMatrix xs
with testSystems.linsysOtter.sigma
using matEq eqi


-- Finds equation offset vector `cs` and variable offset vector `ds` given
-- `sigma`. The vector `incidenceI` is the incidence of equations to variables
-- and the vector `incidenceJ` is the incidence of variables to equations in
-- the perfect matching performed as part of the algorithm.
let sigmaIndexReduce
  : Matrix Int
  -> {
        cs : Vector Int,
        ds : Vector Int,
        incidenceI : Vector Int,
        incidenceJ : Vector Int
     }
  = lam sigma.

  let n = (matDim sigma).0 in

  let solverPrimalProblem = maxmatchFindMatch in

  let solveDualProblem = lam incidenceI. lam ds. lam cs.

    let sigmaTr = matTranspose sigma in
    let tmpSigma = matCreate (matDim sigma) (lam. lam. 0) in
    let tmpCs = vecCreate n (lam. 0) in

    recursive let loop = lam.
      vecBlit cs tmpCs;

      -- d[j] <- max_i(sigma[i][j] + c[i])
      matMapi
        (lam. lam j. lam s. lam. addi (vecGet cs j) s)
        sigmaTr
        tmpSigma;

      matIterRow
        (lam j. lam row. vecSet ds j (vecMax subi row))
        tmpSigma;

      -- c[i] <- d[incidenceI[i]] - sigma[i][incidenceI[i]]
      vecMapiInplace
        (lam i. lam.
          let j = vecGet incidenceI i in
          subi (vecGet ds j) (matGet sigma i j))
          cs;

      vecMap subi cs tmpCs;

      if vecAll (eqi 0) tmpCs then ()
      else loop ()
    in
    loop ()
  in

  -- Start of algorithm
  if not (matIsSquareMatrix sigma) then
    error "Invalid argument: daecore.sigmaIndexReduce"
  else
    match solverPrimalProblem sigma with
      { incidenceU = incidenceI, incidenceV = incidenceJ, weight = weight }
    then
      if lti weight 0 then error "Singular matrix: daecore.sigmaIndexReduce"
      else
        let ds = vecCreate n (lam. 0) in
        let cs = vecCreate n (lam. 0) in
        solveDualProblem incidenceI ds cs;
        { cs = cs, ds = ds, incidenceI = incidenceI, incidenceJ = incidenceJ }
    else never

utest (sigmaIndexReduce testSystems.pendulum.sigma).cs
with testSystems.pendulum.cs using vecEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).ds
with testSystems.pendulum.ds using vecEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).incidenceI
with testSystems.pendulum.incidenceI using vecEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).incidenceJ
with testSystems.pendulum.incidenceJ using vecEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).cs
with testSystems.linsysOtter.cs using vecEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).ds
with testSystems.linsysOtter.ds using vecEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).incidenceI
with testSystems.linsysOtter.incidenceI using vecEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).incidenceJ
with testSystems.linsysOtter.incidenceJ using vecEq eqi


-- Columns of `sigma` incident to row `i`.
let sigmaAllIncident : Matrix Int -> Int -> [Int] =
  lam sigma. lam i.
    vecFilteri (lam. lam x. gti x sigmaNoEdge) (matRow sigma i)

utest
  let sigma = testSystems.pendulum.sigma in
  map (sigmaAllIncident sigma) [0, 1, 2]
with [[0, 2], [1, 2], [0, 1]]


let inputOffsets : Vector Int -> [[Int]] -> Vector Int =
lam cs. lam us.
  let nu =
    setSize (foldl setUnion (setEmpty subi) (map (setOfSeq subi) us))
  in
  let uos = vecCreate nu (lam idx. 0) in
  iteri
    (lam i. lam us.
      (iter
        (lam j.
          vecSet uos j (maxi (vecGet cs i) (vecGet uos j)))
        us))
    us;
  uos

utest
  let us = testSystems.pendulum.dae.inputs in
  let cs = testSystems.pendulum.cs in
  inputOffsets cs us
with testSystems.pendulum.es
using vecEq eqi

utest
  let us = testSystems.linsysOtter.dae.inputs in
  let cs = testSystems.linsysOtter.cs in
  inputOffsets cs us
with testSystems.linsysOtter.es
using vecEq eqi

-- Structure of `ds`.
let structure : Vector Int -> [[IdOrd]] = lam ds.
  vecFoldi
    (lam acc. lam i. lam d.
      let ios =
        unfoldr (lam o. if gti o d then None () else Some ((i, o), succ o)) 0
      in
      snoc acc ios)
    []
    ds

-----------------
-- BLT SORTING --
-----------------

let mkDependencyGraph : Matrix Int -> Vector Int -> Digraph Int Int =
lam sigma. lam incidenceJ.
  let n = vecLength incidenceJ in
  let fs = create n (lam i. i) in
  let g = digraphEmpty eqi eqi in
  let g = foldl (lam g. lam f. digraphAddVertex f g) g fs in
  matFoldi
    (lam g. lam f. lam v. lam x.
      let af = vecGet incidenceJ v in
      if and (gti x sigmaNoEdge) (neqi af f) then digraphAddEdge af f x g
      else g)
    g
    sigma

-- Sorts system given by `sigma` and `incidenceJ` into BLT blocks.
let bltSort : Matrix Int -> Vector Int -> [[Int]] =
lam sigma. lam incidenceJ.
  let g = mkDependencyGraph sigma incidenceJ in
  digraphStrongConnects g

utest
  let sigma = testSystems.pendulum.sigma in
  let incidenceJ = testSystems.pendulum.incidenceJ in
  bltSort sigma incidenceJ
with testSystems.pendulum.blocks using eqsetEqual (eqsetEqual eqi)

utest
  let sigma = testSystems.linsysOtter.sigma in
  let incidenceJ = testSystems.linsysOtter.incidenceJ in
  bltSort sigma incidenceJ
with testSystems.linsysOtter.blocks using eqsetEqual (eqsetEqual eqi)


-- Assigned variables in each BLT block (`incidenceJ`, `block`).
let bltAssignedVars : Vector Int -> [[Int]] -> [[Int]] =
  lam incidenceJ. lam blocks.
    map (map (lam eq. vecGet incidenceJ eq)) blocks

utest
  let incidenceJ = testSystems.pendulum.incidenceJ in
  let blocks = testSystems.pendulum.blocks in
  bltAssignedVars incidenceJ blocks
with testSystems.pendulum.assignedVars using eqsetEqual (eqsetEqual eqi)

utest
  let incidenceJ = testSystems.linsysOtter.incidenceJ in
  let blocks = testSystems.linsysOtter.blocks in
  bltAssignedVars incidenceJ blocks
with testSystems.linsysOtter.assignedVars using eqsetEqual (eqsetEqual eqi)


-- BLT block of `blocks` assigned to each variable `xs`
let bltAssigned : [[Int]] -> [Int] -> [Int] =
  lam blocks. lam xs.
    let isAssigned = lam x. lam blocks. any (eqi x) blocks in
    map
      (lam x.
        optionGetOrElse
          (lam. error "Unassigned variable: daecore.bltAssigned")
          (index (isAssigned x) blocks))
      xs

utest
  let blocks = testSystems.pendulum.blocks in
  let vs = create 3 (lam v. v) in
  bltAssigned blocks vs
with testSystems.pendulum.assignedBlocks

utest
  let blocks = testSystems.linsysOtter.blocks in
  let vs = create 8 (lam v. v) in
  bltAssigned blocks vs
with testSystems.linsysOtter.assignedBlocks


-- Variables in each BLT block
let bltVars : Matrix Int -> [[Int]] -> [[Int]] =
  lam sigma. lam blocks.
    let vars = map (map (sigmaAllIncident sigma)) blocks in
    map (lam vars. setToSeq (foldl1 setUnion (map (setOfSeq subi) vars))) vars

utest
  let sigma = testSystems.pendulum.sigma in
  let blocks = testSystems.pendulum.blocks in
  bltVars sigma blocks
with testSystems.pendulum.varsInBlock using eqSeq (eqsetEqual eqi)

utest
  let sigma = testSystems.linsysOtter.sigma in
  let blocks = testSystems.linsysOtter.blocks in
  bltVars sigma blocks
with testSystems.linsysOtter.varsInBlock using eqSeq (eqsetEqual eqi)


----------------------
-- VARIABLE SORTING --
----------------------

-- Variable `v` is algebraic
let isAlgebraic = lam ds. lam lambdas. lam v.
  eqi (addi (vecGet ds v) (vecGet lambdas v)) 0

-- Variable `v` is differential
let isDifferential = lam ds. lam lambdas. lam v. not (isAlgebraic ds lambdas v)

-- The lambda vector, indicating algebraic varaibles to be substituted for their
-- derivative.
let sortFindLambda
  : {
    sigma : Matrix Int,
    ds : Vector Int,
    blocks : [[Int]],
    incidenceJ : Vector Int
  } -> Vector Int =
  lam arg.
  -- Number of variables
  let nvs = vecLength arg.ds in

  -- Number of blocks
  let nblocks = length arg.blocks in

  -- Enumerate variables
  let vs = create nvs (lam v. v) in

  -- Variables assigned to each BLT block
  let assignedVars = bltAssignedVars arg.incidenceJ arg.blocks in

  -- BLT block assigned to each variable
  let blockAssignedToVars =
    vecOfSeq (bltAssigned assignedVars vs)
  in

  let assignedVars =
    vecOfSeq assignedVars
  in

  -- Variables in each BLT block
  let bltVars =
    vecOfSeq (bltVars arg.sigma arg.blocks)
  in

  -- Vector indicating if algebraic variable should be substituted with its
  -- derivative. A 0 means no and a 1 means yes.
  let lambdas = vecCreate nvs (lam. 0) in

  let isAlgebraic = isAlgebraic arg.ds lambdas in
  let isDifferential = isDifferential arg.ds lambdas in

  -- Substitute `v` for its derivative if `v` is algebraic
  let maybeSubstitute =
    lam v. if isAlgebraic v then vecSet lambdas v 1 else ()
  in

  -- Main Algorithm
  recursive let recur = lam us.
    match us with [] then ()
    else match us with [u] ++ us then
      if isAlgebraic u then
        let block = vecGet blockAssignedToVars u in
        let assignedVars = vecGet assignedVars block in
        let blockVars = vecGet bltVars block in
        if or
            (any isDifferential assignedVars)
            (any isDifferential blockVars)
        then
          -- Since this algebraic variable is assigned to a BLT block where
          -- either some assigned variable is differential, and/or not all
          -- variables in this block are algebraic, we need to substitute all
          -- assigned algebraic variables in this BLT block with their
          -- derivatives.
          iter maybeSubstitute assignedVars;
          -- Then we repeat the algorithm from the first variable since the
          -- substitution might affect other BLT blocks.
          recur vs
        else recur us
      else recur us
    else never
  in

  recur vs;
  lambdas

utest
  let sigma = testSystems.pendulum.sigma in
  let ds = testSystems.pendulum.ds in
  let blocks = testSystems.pendulum.blocks in
  let incidenceJ = testSystems.pendulum.incidenceJ in
  sortFindLambda {
    sigma = sigma,
    ds = ds,
    blocks = blocks,
    incidenceJ = incidenceJ
  }
with testSystems.pendulum.lambdas
using vecEq eqi

utest
  let sigma = testSystems.linsysOtter.sigma in
  let ds = testSystems.linsysOtter.ds in
  let blocks = testSystems.linsysOtter.blocks in
  let incidenceJ = testSystems.linsysOtter.incidenceJ in
  sortFindLambda {
    sigma = sigma,
    ds = ds,
    blocks = blocks,
    incidenceJ = incidenceJ
  }
with testSystems.linsysOtter.lambdas
using vecEq eqi


------------------------------------------
-- INDEXING AND FIRST-ORDER FORMULATION --
------------------------------------------

let idxOffsets : Vector Int -> Vector Int =
lam ofs.
  let n = vecLength ofs in
  let t = vecMapCopy (addi 1) ofs in
  vecCumsimiInplace t;
  let idxOfs = vecCreate n (lam. 0) in
  vecBlit
    (vecSub t 0 (pred n))
    (vecSub idxOfs 1 (pred n));
  idxOfs

utest idxOffsets testSystems.pendulum.ds
with vecOfSeq [0, 3, 6]
using vecEq eqi

utest idxOffsets testSystems.linsysOtter.ds
with vecOfSeq [0, 3, 6, 9, 11, 12, 16, 20]
using vecEq eqi


-- The index offset of each variable in a first-order formulation
let idxOffsetsFirstOrder : Vector Int -> Vector Int =
  lam ofs.
    let n = vecLength ofs in
    let t = vecMapCopy (maxi 1) ofs in
    vecCumsimiInplace t;
    let idxOfs = vecCreate n (lam. 0) in
    vecBlit
      (vecSub t 0 (pred n))
      (vecSub idxOfs 1 (pred n));
    idxOfs

utest
  let ofs = idxOffsetsFirstOrder (vecCreate 0 (lam. 0)) in
  vecToSeq ofs
with []

utest idxOffsetsFirstOrder testSystems.pendulum.ds
with testSystems.pendulum.varIdxOffsets
using vecEq eqi

utest idxOffsetsFirstOrder testSystems.linsysOtter.ds
with testSystems.linsysOtter.varIdxOffsets
using vecEq eqi


-- Indexes indicating alias equations of the first-order DAE
let aliases : Vector Int -> [(Int, Int)] =
lam ds.
  let idxOffsets = idxOffsetsFirstOrder ds in
  let idxs = vecFilteri (lam. lam d. gti d 0) ds in
  let f =
    recursive let recur = lam a. lam d. lam i.
      if eqi (vecGet ds i) d then a
      else recur (snoc a (addi (vecGet idxOffsets i) d)) (succ d) i
    in recur [] 0
  in
  let g = lam idxs. zip (tail idxs) (init idxs) in
  join (map (compose g f) idxs)

utest
  let ds = testSystems.pendulum.ds in
  aliases ds
with [(1, 0), (3, 2)]

utest
  let ds = testSystems.linsysOtter.ds in
  aliases ds
with [(1, 0), (3, 2), (5, 4), (9, 8), (10, 9), (12, 11), (13, 12)]


let nVariables : Vector Int -> Int =
  lam ofs. vecFold (lam a. lam d. addi a (maxi 1 d)) 0 ofs

utest nVariables testSystems.pendulum.ds with 5
utest nVariables testSystems.linsysOtter.ds with 15


----------------------
-- EQUATION SORTING --
----------------------

-- Equation sorting
let sortEquations
  : {
    sigma : Matrix Int,
    cs : Vector Int,
    ds : Vector Int,
    incidenceJ : Vector Int,
    blocks : [[Int]],
    lambdas : Vector Int
  } -> {
    -- Non-differentiated differential equations
    eqs0d : [Int],

    -- Non-differentiated algebraic equations
    eqs0a : [Int],

    -- Non-Differentiated constraint equations
    eqs0c : [Int],

    -- Differentiated constraint equations, except at the highest differentation
    -- order.
    eqsNc : [IdOrd]
  } = lam arg.
  let varsInEq = sigmaAllIncident arg.sigma in
  let isAlgebraic = isAlgebraic arg.ds arg.lambdas in
  let isDifferential = isDifferential arg.ds arg.lambdas in
  let isDifferentiated = lam e. gti (vecGet arg.cs e) 0 in

  let neqs = vecLength arg.cs in
  let eqs = create neqs (lam e. e) in
  let nblocks = length arg.blocks in

  let assignedVars =
    vecOfSeq (bltAssignedVars arg.incidenceJ arg.blocks)
  in

  let assignedEqs =
    vecOfSeq (bltAssigned arg.blocks eqs)
  in

  let eqs0d =
    filter
      (lam e.
        let block = vecGet assignedEqs e in
        let assignedVars = vecGet assignedVars block in
        and (not (isDifferentiated e)) (all isDifferential assignedVars))
      eqs
  in

  let eqs0a =
      filter
      (lam e.
        let block = vecGet assignedEqs e in
        let assignedVars = vecGet assignedVars block in
        and (not (isDifferentiated e)) (all isAlgebraic assignedVars))
      eqs
  in

  let eqs0c = filter isDifferentiated eqs in

  let eqsNc =
  foldl
    (lam a. lam i. concat a (map (lam o. (i, o)) (range 1 (vecGet arg.cs i) 1)))
    []
    (filter isDifferentiated eqs)
  in

  { eqs0d = eqs0d, eqs0a = eqs0a, eqs0c = eqs0c, eqsNc = eqsNc }

utest
  sortEquations {
    sigma = testSystems.pendulum.sigma,
    cs = testSystems.pendulum.cs,
    ds = testSystems.pendulum.ds,
    incidenceJ = testSystems.pendulum.incidenceJ,
    blocks = testSystems.pendulum.blocks,
    lambdas = testSystems.pendulum.lambdas
  }
with { eqs0d = [0, 1], eqs0a = [], eqs0c = [2], eqsNc = [(2, 1)] }

utest
  sortEquations {
    sigma = testSystems.linsysOtter.sigma,
    cs = testSystems.linsysOtter.cs,
    ds = testSystems.linsysOtter.ds,
    incidenceJ = testSystems.linsysOtter.incidenceJ,
    blocks = testSystems.linsysOtter.blocks,
    lambdas = testSystems.linsysOtter.lambdas
  }
with {
  eqs0d = [3, 4],
  eqs0a = [7],
  eqs0c = [0, 1, 2, 5, 6],
  eqsNc = [
    (0, 1),
    (1, 1),
    (5, 1), (5, 2),
    (6, 1), (6, 2)
  ]
}


-------------------------
-- SETTERS AND GETTERS --
-------------------------

let offsetGet : Vector Int -> Vector a -> IdOrd -> a =
lam offsets.
  lam y. lam v.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let ofs = vecGet offsets i in
    vecGet y (addi ofs o)

let offsetSet : Vector Int -> Vector a -> IdOrd -> a -> () =
lam offsets.
  lam y. lam v. lam val.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let ofs = vecGet offsets i in
    vecSet y (addi ofs o) val

let offsetGetYYPLambdas
  : { ds : Vector Int, lambdas : Vector Int }
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam arg.
  let idxOffsets = idxOffsetsFirstOrder arg.ds in
  lam y. lam yp. lam v.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let l = vecGet arg.lambdas i in
    let o = addi o l in
    let ofs = vecGet idxOffsets i in
    let dmax = vecGet arg.ds i in

    if or (lti o dmax) (eqi o 0) then
      vecGet y (addi ofs o)
    else if eqi (subi o l) dmax then
      vecGet yp (addi ofs (pred o))
    else
      error "Unknown variable: daecore.offsetGetYYPLambdas"

utest
  let arg = {
    ds = testSystems.pendulum.ds,
    lambdas = testSystems.pendulum.lambdas
  } in
  let y = vecOfSeq (range 0 6 1) in
  let yp = vecOfSeq (range 5 10 1) in
  mapi
    (lam i. map (lam o. offsetGetYYPLambdas arg y yp (i, o)))
    [[0, 1, 2], [0, 1, 2], [0]]
with [[0, 1, 6], [2, 3, 8], [9]]

utest
  let arg = {
    ds = testSystems.linsysOtter.ds,
    lambdas = testSystems.linsysOtter.lambdas
  } in
  let y = vecOfSeq (range 0 16 1) in
  let yp = vecOfSeq (range 15 31 1) in
  mapi
    (lam i. map (lam o. offsetGetYYPLambdas arg y yp (i, o)))
    [
      [0, 1, 2],
      [0, 1, 2],
      [0, 1, 2],
      [0, 1],
      [0],
      [0, 1, 2, 3],
      [0, 1, 2, 3],
      [0]
    ]
with [
  [0, 1, 16],
  [2, 3, 18],
  [4, 5, 20],
  [6, 21],
  [22],
  [8, 9, 10, 25],
  [11, 12, 13, 28],
  [14]
]

let offsetSetYYPLambdas
  : {
    ds : Vector Int,
    lambdas : Vector Int
  }
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a
  -> () =
lam arg.
  let aliases = mapFromSeq subi (aliases arg.ds) in
  let idxOffsets = idxOffsetsFirstOrder arg.ds in
  lam y. lam yp. lam v. lam val.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let l = vecGet arg.lambdas i in
    let o = addi o l in
    let ofs = vecGet idxOffsets i in
    let dmax = vecGet arg.ds i in
    if or (lti o dmax) (eqi o 0) then
      let i = addi ofs o in
      vecSet y i val;
      let j = mapLookup i aliases in
      match j with Some j then
        vecSet yp j val
      else match j with None _ then ()
      else never
    else if eqi (subi o l) dmax then
      vecSet yp (addi ofs (pred o)) val
    else
      error "Unknown variable: daecore.offsetSetYYPLambdas"

utest
  let arg = {
    ds = testSystems.pendulum.ds,
    lambdas = testSystems.pendulum.lambdas
  } in
  let y = vecCreate 5 (lam. (negi 1)) in
  let yp = vecCreate 5 (lam. (negi 1)) in
  let offsetSetYYPLambdas = offsetSetYYPLambdas arg y yp in
  iteri
    (lam i. map (lam dv : (Int, Int). offsetSetYYPLambdas (i, dv.0) dv.1))
    [[(0, 0), (1, 1), (2, 2)], [(0, 3), (1, 4), (2, 5)], [(0, 6)]];
  [vecToSeq y, vecToSeq yp]
with [[0, 1, 3, 4, negi 1], [1, 2, 4, 5, 6]]


let offsetGetYYP
  : Vector Int
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam ds. offsetGetYYPLambdas {
  ds = ds,
  lambdas = vecCreate (vecLength ds) (lam. 0)
}

let offsetSetYYP
  : Vector Int
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam ds. offsetSetYYPLambdas {
  ds = ds,
  lambdas = vecCreate (vecLength ds) (lam. 0)
}


--------------------------
-- RESIDUAL FORMULATION --
--------------------------

type FirstOrderResidual = {
    resf
      : DualNum
      -> Vector DualNum
      -> Vector DualNum
      -> Vector (Vector DualNum)
      -> Vector DualNum
      -> Vector DualNum
      -> (),

    structureY : [IdOrd],
    structureYP : [IdOrd],
    structureU : [IdOrd],
    isdiff : [Bool]
}

-- Vector indicating which dependent variables in the first-order system are
-- differential.
let isdiffLambdas : Vector Int -> Vector Int -> [Bool] =
 lam lambdas. lam ds.
  let f = lam i. lam d.
    if eqi d 0 then
      if eqi (vecGet lambdas i) 0 then [false] else [true]
    else create d (lam. true)
  in
  join (vecFoldi (lam acc. lam i. lam d. snoc acc (f i d)) [] ds)

let isdiff : Vector Int -> [Bool] =
  lam ds. isdiffLambdas (vecCreate (vecLength ds) (lam. 0)) ds

utest
  let ds = vecOfSeq [2, 2, 0] in
  let lambdas = vecOfSeq [0, 0, 1] in
  isdiffLambdas lambdas ds
with [true, true, true, true, true]

utest
  let ds = vecOfSeq [2, 2, 2, 1, 0, 3, 3, 0] in
  let lambdas = vecOfSeq [0, 0, 0, 0, 1, 0, 0, 0] in
  isdiffLambdas lambdas ds
with snoc (create 14 (lam. true)) false using eqSeq eqBool

utest
  let ds = vecOfSeq [2, 2, 0] in
  let lambdas = vecOfSeq [0, 0, 1] in
  isdiff ds
with [true, true, true, true, false]

-- Define v_i(t)
let v = lam get.
  recursive let recur = lam d. lam i.
    lam t. dualnumLift1 (lam. get (i, d)) (recur (succ d) i) t
  in recur 0

-- Formulate residual function for naive index-reduced, non-stabilized DAE.
let residual
  : {
    cs : Vector Int,
    ds : Vector Int,
    es : Vector Int
  }
  -> ResidualFun
  -> FirstOrderResidual
  = lam arg. lam fs.
  let aliases = aliases arg.ds in
  let nx = vecLength arg.ds in
  let nu = vecLength arg.es in
  let stateGet = offsetGetYYP arg.ds in
  let inputGet = offsetGet (idxOffsets arg.es) in
  let resf = lam th. lam u.
    let fs = fs th in
    let inputGet = inputGet u in
    -- Define u_i(t)
    let u = v inputGet in
    -- Create u_i(t) for i = 0..nu-1
    let us = vecCreate nu u in
    let fs = fs us in
    lam t. lam y. lam yp. lam r.
      let stateGet = stateGet y yp in
      -- Define x_i(t)
      let x = v stateGet in
      -- Create x_i(t) for i = 0..nx-1
      let xs = vecCreate nx x in
      let fs = fs xs in
      -- Compute index-reduced residual
      iteri (lam i. lam f. vecSet r i (nder (vecGet arg.cs i) f t)) fs;
      -- Compute alias equations
      iteri
        (lam i. lam a : (Int, Int).
          match a with (j, k) then
            vecSet r (addi i nx) (subn (vecGet y j) (vecGet yp k))
          else never)
        aliases;
      ()
  in
  let structureY =
    join
      (map (lam vs. if eqi (length vs) 1 then vs else init vs) (structure arg.ds))
  in
  let structureYP = map idOrdDer structureY in
  let structureU = join (structure arg.es) in
  let isdiff = isdiff arg.ds in
  {
    resf = resf,
    structureY = structureY,
    structureYP = structureYP,
    structureU = structureU,
    isdiff = isdiff
  }

let x0 = 1.
let dx0 = 2.
let ddx0 = 3.
let x1 = 4.
let dx1 = 5.
let ddx1 = 6.
let x2 = 7.

utest
  let arg = {
    cs = testSystems.pendulum.cs,
    ds = testSystems.pendulum.ds,
    es = testSystems.pendulum.es
  }
  in
  let fs = testSystems.pendulum.dae.residual in
  let res : FirstOrderResidual = residual arg fs in
  let t = num 0. in
  let y = vecOfSeq (map num [x0, dx0, x1, dx1, x2]) in
  let yp = vecOfSeq (map num [dx0, ddx0, dx1, ddx1, negf 10000.]) in
  let u = vecCreate 2 (lam. num 0.) in
  let r = vecCreate 5 (lam. num 0.) in
  let th = vecCreate 3 (lam. num 1.) in
  res.resf th u t y yp r;
  map dualnumUnpackNum (vecToSeq r)
with [
  subf ddx0 (mulf x0 x2),
  addf (subf ddx1 (mulf x1 x2)) 1.,
  mulf 2. (addf
            (addf (mulf ddx0 x0) (mulf ddx1 x1))
            (addf (mulf dx0 dx0) (mulf dx1 dx1))),
  0.,
  0.
]

utest
  let arg = {
    cs = testSystems.pendulum.cs,
    ds = testSystems.pendulum.ds,
    es = testSystems.pendulum.es
  }
  in
  let fs = testSystems.pendulum.dae.residual in
  let res : FirstOrderResidual = residual arg fs in
  (res.structureY, res.structureYP, res.structureU, res.isdiff)
with (
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0)],
  [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1)],
  [(0, 0), (1, 0)],
  [true, true, true, true, false]
)

-- Formulate residual function for index-reduced, stabilized DAE.
let residualStabilized
  : {
    sigma : Matrix Int,
    cs : Vector Int,
    ds : Vector Int,
    incidenceJ : Vector Int,
    blocks : [[Int]],
    lambdas : Vector Int,
    us : [[Int]]
  }
  -> [
    Vector (DualNum -> DualNum) ->
    Vector (DualNum -> DualNum) ->
    Vector DualNum ->
    DualNum ->
    DualNum
  ]
  -> FirstOrderResidual
  = lam arg. lam fs.
  -- Compute input offsets
  let es =
    inputOffsets
      (vecMapCopy (lam c. mini 0 (subi c 1)) arg.cs)
      arg.us
  in
  -- Getters
  let stateGetY = offsetGet (idxOffsetsFirstOrder arg.ds) in
  let inputGet = offsetGet (idxOffsets es) in
  let stateGetYYP = offsetGetYYPLambdas {
    ds = arg.ds,
    lambdas = arg.lambdas
  } in
  -- Sort equations
  let se = sortEquations {
    sigma = arg.sigma,
    cs = arg.cs,
    ds = arg.ds,
    incidenceJ = arg.incidenceJ,
    blocks = arg.blocks,
    lambdas = arg.lambdas
  } in
  -- Compute problem sizes
  let nf0d = length se.eqs0d in
  let nf0a = length se.eqs0a in
  let nf0c = length se.eqs0c in
  let nfNc = length se.eqsNc in
  let nf = foldl addi 0 [nf0d, nf0a, nf0c, nfNc] in
  let nx = vecLength arg.ds in
  let nu = vecLength es in
  -- number of variables in first-order system
  let nvars = nVariables arg.ds in
  -- Alias residual
  let aliases = aliases arg.ds in
  let naliases = length aliases in
  -- number of dummy variables
  let nmu = nfNc in
  -- Pre-allocate intermediate data-structures
  let g_i = vecCreate nfNc (lam. num 0.) in
  let resf = lam th. lam u.
    let fs = fs th in
    -- Define u_i(t)
    let u = v (inputGet u) in
    -- Create u_i(t) for i = 0..nu-1
    let us = vecCreate nu u in
    let fs = fs us in
    lam t. lam y. lam yp. lam r.
      -- Differentiated constraint residual
      let resNc = lam y. lam r.
        let stateGet = stateGetY y in
        -- Define x_i(t)
        let x = v stateGet in
        -- Create x_i(t) for i = 0..nx-1
        let xs = vecCreate nx x in
        -- Differentiated constraint residual, except at the highest
        -- differentiation order
        let fs = fs xs in
        let fNc =
          map (lam e : IdOrd. (get fs (idOrdId e), idOrdOrd e)) se.eqsNc
        in
        iteri
          (lam i. lam fo : (DualNum -> DualNum, Int).
            match fo with (f, n) then vecSet r i (nder n f t)
            else never)
          fNc
      in
      -- Define x_i(t)
      let x = v (stateGetYYP y yp) in
      -- Create x_i(t) for i = 0..nx-1
      let xs = vecCreate nx x in
      let fs = fs xs in
      -- Non-differentiated differential residual
      let f0d = map (lam i. get fs i) se.eqs0d in
      -- Algebraic residual
      let f0a = map (lam i. get fs i) se.eqs0a in
      -- Non-differentiated constraint residual
      let f0c = map (lam i. get fs i) se.eqs0c in
      -- Compute non-differentiated differential residual
      iteri (lam i. lam f. vecSet r i (f t)) f0d;
      -- Compute algebraic residual
      let ofs = nf0d in
      iteri (lam i. lam f. vecSet r (addi i ofs) (f t)) f0a;
      -- Compute non-differentiated constraint residual
      let ofs = addi ofs nf0a in
      iteri (lam i. lam f. vecSet r (addi i ofs) (f t)) f0c;
      -- Compute differentiated constraint residual
      let ofs = addi ofs nf0c in
      resNc y (vecSub r ofs nfNc);
      -- Compute stabilized alias residual
      iteri
        (lam i. lam a : (Int, Int).
          match a with (j, k) then
            jaci (lam y. resNc y) j y g_i;
            vecMapiInplace (lam i. muln (vecGet yp (addi nvars i))) g_i;
            let alias = subn (vecGet y j) (vecGet yp k) in
            let corr = vecFold addn (num 0.) g_i in
            vecSet r (addi nf i) (addn alias corr)
          else never)
        aliases;

      ()
  in
  let structureY =
    join
      (mapi
        (lam i. lam vs.
          if eqi (length vs) 1 then
            let n = vecGet arg.lambdas i in
            map (idOrdIntN n) vs
          else init vs)
        (structure arg.ds))
  in
  let structureMu = map (lam i. (i, negi 1)) (range nx (addi nx nmu) 1) in
  let structureY = concat structureY structureMu in
  let structureYP = map idOrdDer structureY in
  let structureU = join (structure es) in
  -- Update variable offset vector
  let nds = vecLength arg.ds in
  let ds = vecCreate (addi nds nmu) (lam. 1) in
  vecIteri
    (lam i. lam d. vecSet ds i (addi d (vecGet arg.lambdas i)))
    arg.ds;
  let isdiff = isdiffLambdas arg.lambdas ds in
  {
    resf = resf,
    structureY = structureY,
    structureYP = structureYP,
    structureU = structureU,
    isdiff = isdiff
  }


let x0 = 1.
let dx0 = 2.
let ddx0 = 3.
let x1 = 4.
let dx1 = 5.
let ddx1 = 6.
let x2 = 7.
let mu0 = 8.

utest
  let arg = {
    sigma = testSystems.pendulum.sigma,
    cs = testSystems.pendulum.cs,
    ds = testSystems.pendulum.ds,
    incidenceJ = testSystems.pendulum.incidenceJ,
    lambdas = testSystems.pendulum.lambdas,
    blocks = testSystems.pendulum.blocks,
    us = testSystems.pendulum.dae.inputs
  } in
  let fs = testSystems.pendulum.dae.residual in
  let res : FirstOrderResidual = residualStabilized arg fs in
  let t = num 0. in
  let y = vecOfSeq (map num [x0, dx0, x1, dx1, negf 10000., 0.]) in
  let yp = vecOfSeq (map num [dx0, ddx0, dx1, ddx1, x2, mu0]) in
  let u = vecCreate 2 (lam. num 0.) in
  let r = vecCreate 6 (lam. num 0.) in
  let th = vecCreate 3 (lam. num 1.) in
  res.resf th u t y yp r;
  map dualnumUnpackNum (vecToSeq r)
with [
  subf ddx0 (mulf x0 x2),
  addf (subf ddx1 (mulf x1 x2)) 1.,
  subf (addf (mulf x0 x0) (mulf x1 x1)) 1.,
  mulf 2. (addf
            (mulf dx0 x0)
            (mulf dx1 x1)),
  mulf mu0 (mulf 2. x0),
  mulf mu0 (mulf 2. x1)
]

utest
  let arg = {
    sigma = testSystems.pendulum.sigma,
    cs = testSystems.pendulum.cs,
    ds = testSystems.pendulum.ds,
    incidenceJ = testSystems.pendulum.incidenceJ,
    lambdas = testSystems.pendulum.lambdas,
    blocks = testSystems.pendulum.blocks,
    us = testSystems.pendulum.dae.inputs
  } in
  let fs = testSystems.pendulum.dae.residual in
  let res : FirstOrderResidual = residualStabilized arg fs in
  (res.structureY, res.structureYP, res.structureU, res.isdiff)
with (
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, negi 1), (3, negi 1)],
  [(0, 1), (0, 2), (1, 1), (1, 2), (2, 0), (3, 0)],
  [(0, 0), (1, 0)],
  [true, true, true, true, true, true]
)

---------------------------
-- OBJECTIVE FORMULATION --
---------------------------

let augmentedResidualIdOrds = lam cs.
  vecFoldi
    (lam acc. lam i. lam c.
      let os =
        unfoldr (lam o. if gti o c then None () else Some ((i, o), succ o)) 0
      in
      concat acc os)
    []
    cs

utest
  let cs = testSystems.pendulum.cs in
  augmentedResidualIdOrds cs
with [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2)]


let objective =
lam arg : { res : [ResidualFun], cs : Vector Int, ds : Vector Int }.
  let nx = vecLength arg.ds in
  let idords = augmentedResidualIdOrds arg.cs in
  let res =
    map (lam io : Idords. nder (idOrdDer io) (get arg.res (idOrdDer io))) idords
  in
  let stateGet = offsetGet (idxOffsets arg.ds) in
  lam th. lam u. lam t. lam x.
    -- define x_i(t)
    let x = v stateGet in
    -- create x_i(t) for i = 0..nx-1
    let xs = vecCreate nx x in
    -- compute objective
    foldl1
      (lam obj. lam f.
        let f = f xs u th t in
        addn obj (muln f f))
      res

let constraints =
lam arg : { gs : [ConstraintFun], ds : Vector Int }.
  let nx = vecLength arg.ds in
  let stateGet = offsetGet (idxOffsets arg.ds) in
  lam th. lam u. lam t. lam x. lam g.
    -- define x_i(t)
    let x = v stateGet in
    -- create x_i(t) for i = 0..nx-1
    let xs = vecCreate nx x in
    -- compute constraints
    iteri (lam i. lam g. vecSet g i (g xs u th t)) arg.gs;
    ()

----------------------
-- MAIN ENTRY POINT --
----------------------

type DaecoreResidual = {
  -- Residual function f(t, y, yp, u, r), where r stores the result of the
  -- residual.
  resf
  : DualNum                     -- free variable t
  -> Vector DualNum             -- parameter vector theta
  -> Vector DualNum             -- input vector u
  -> Vector DualNum             -- state vector y
  -> Vector DualNum             -- vector of first derivatives of y w.r.t. t
  -> Vector DualNum             -- vector to store the value of the residual
  -> (),

  -- Structure of y, associates variables of the ofiginal problem to y.
  structureY : [IdOrd],

  -- Structure of y', associates variables of the ofiginal problem to y'.
  structureYP : [IdOrd],

  -- Struture of u, inputs may appear differentiated in the index-reduced
  -- problem.
  structureU : [IdOrd],

  -- Variables in y appearing differentiated in the residual.
  isdiff : [Bool]
}

-- Non-stabilized low-index residual
let daecoreResidual : DAE -> DaecoreResidual = lam dae.
  let fs = dae.residual in
  let vs = dae.variables in
  let us = dae.inputs in
  let sigma = sigmaMatrix vs in
  match sigmaIndexReduce sigma with
    { cs = cs, ds = ds, incidenceJ = incidenceJ }
  then
    let es = inputOffsets cs us in
    let res : FirstOrderResidual =
      residual { cs = cs, ds = ds, es = es } fs
    in
    {
      resf = res.resf,
      structureY = res.structureY,
      structureYP = res.structureYP,
      structureU = res.structureU,
      isdiff = res.isdiff
    }
  else never

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  let y = vecOfSeq (map num [1., 0., 0., 0., 0.]) in
  let yp = vecOfSeq (map num [0., 0., 0., negf 1., 0.]) in
  let th = vecCreate 3 (lam. num 1.) in
  let u = vecCreate 2 (lam. num 0.) in
  let r = vecCreate 5 (lam. num 0.) in
  let t = num 0. in
  res.resf th u t y yp r;
  vecToSeq r
with create 5 (lam. num 0.) using eqSeq (dualnumEq eqf)

-- Stabilized low-index residual
let daecoreResidualStabilized : DAE -> DaecoreResidual = lam dae.
  let fs = dae.residual in
  let vs = dae.variables in
  let us = dae.inputs in
  let sigma = sigmaMatrix vs in
  match sigmaIndexReduce sigma with
    { cs = cs, ds = ds, incidenceJ = incidenceJ }
  then
    let es = inputOffsets cs us in
    let blocks = bltSort sigma incidenceJ in
    let lambdas = sortFindLambda {
      sigma = sigma,
      ds = ds,
      blocks = blocks,
      incidenceJ = incidenceJ
    } in
    let res : FirstOrderResidual = residualStabilized {
      sigma = sigma,
      cs = cs,
      ds = ds,
      incidenceJ = incidenceJ,
      lambdas = lambdas,
      blocks = blocks,
      us = us
    } fs in
    {
      resf = res.resf,
      structureY = res.structureY,
      structureYP = res.structureYP,
      structureU = res.structureU,
      isdiff = res.isdiff
    }
  else never

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  let y = vecOfSeq (map num [1., 0., 0., 0., 0., 0.]) in
  let yp = vecOfSeq (map num [0., 0., 0., negf 1., 0., 0.]) in
  let th = vecCreate 3 (lam. num 1.) in
  let u = vecCreate 2 (lam. num 0.) in
  let r = vecCreate 6 (lam. num 0.) in
  let t = num 0. in
  res.resf th u t y yp r;
  vecToSeq r
with create 6 (lam. num 0.) using eqSeq (dualnumEq eqf)
