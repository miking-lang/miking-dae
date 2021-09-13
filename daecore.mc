include "math.mc"
include "ad/dualnum.mc"
include "tensor.mc"
include "maxmatch-tensor.mc"
include "digraph.mc"
include "set.mc"

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
let tget = tensorGetExn
let tset = tensorSetExn
let tcreate = tensorCreateDense

-- Constants
let _neginf = negi (1000000)

-- A sufficiently large negative number representing a non-existant edge in the
-- graph corresponding to the sigma matrix
let sigmaNoEdge = _neginf

-- Short circuit and/or
let or = lam x. lam y. if x then true else y
let and = lam x. lam y. if not x then false else y

-- For documentation purposes, we indicate the rank of tensors
type Vector a = Tensor[a]
type Matrix a = Tensor[a]

------------------------------------------------
-- DIFFERENTIAL ALGEBRAIC SYSTEM OF EQUATIONS --
------------------------------------------------

-- A tuple representing an identifier and differentiation order.
type IdOrd = (Int, Int)
let idOrdId = lam x : IdOrd. x.0
let idOrdOrd = lam x : IdOrd. x.1
let cmpIdOrd = lam x : IdOrd. lam y : IdOrd.
  if eqi (idOrdId x) (idOrdId y) then subi (idOrdOrd x) (idOrdOrd y)
  else subi (idOrdId x) (idOrdId y)
let idOrdDer = lam x : IdOrd. (x.0, succ x.1)
let idOrdInt = lam x : IdOrd. (x.0, pred x.1)

-- A single scalar residual function in a high-index DAE
type Residual =
  Vector (DualNum -> DualNum) ->
  Vector (DualNum -> DualNum) ->
  Vector DualNum ->
  DualNum ->
  DualNum

-- A high index DAE consists of a list of tuples, where the first element in the
-- tuple is a residual function and the second element is a list of dependent
-- variables present in this particular residual function.
type DAE = [(Residual, [IdOrd], [Int])]

let daeResiduals : DAE -> [Residual] =
  map (lam x : (Residual, [IdOrd], [Int]). x.0)

let daeVars : DAE -> [[IdOrd]] =
  map (lam x : (Residual, [IdOrd], [Int]). x.1)

let daeInputs : DAE -> [[Int]] =
  map (lam x : (Residual, [IdOrd], [Int]). x.2)

let daeConsistent : DAE -> Bool =
lam dae.
  let ids = setToSeq (setOfSeq subi (map idOrdId (join (daeVars dae)))) in
  let n = length dae in
  and (eqi (length ids) n) (lti (maxOrElse (lam. 0) subi ids) n)

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
    dae =
      let f1 = lam xs. lam us. lam ths. lam t.
        let m = tget ths [0] in
        let u1 = tget us [0] in
        let x1 = tget xs [0] in
        let x3 = tget xs [2] in
        subn (muln m (nder 2 x1 t)) (addn (muln (x1 t) (x3 t)) (u1 t))
      in
      let xs1 = [(0, 0), (0, 2), (2, 0)] in
      let us1 = [0] in
      let f2 = lam xs. lam us. lam ths. lam t.
        let m = tget ths [0] in
        let g = tget ths [1] in
        let u2 = tget us [1] in
        let x2 = tget xs [1] in
        let x3 = tget xs [2] in
        addn
          (subn (muln m (nder 2 x2 t)) (addn (muln (x2 t) (x3 t)) (u2 t)))
          (muln m g)
      in
      let xs2 = [(1, 0), (1, 2), (2, 0)] in
      let us2 = [1] in
      let f3 = lam xs. lam us. lam ths. lam t.
        let l = tget ths [2] in
        let x1 = tget xs [0] in
        let x2 = tget xs [1] in
        subn (addn (muln (x1 t) (x1 t)) (muln (x2 t) (x2 t))) (muln l l)
      in
      let xs3 = [(0, 0), (1, 0)] in
      let us3 = [] in
      [(f1, xs1, us1), (f2, xs2, us2), (f3, xs3, us3)],

    sigma =
      tensorOfSeqExn tcreate [3, 3]
        [2, n, 0
        ,n, 2, 0
        ,0, 0, n],

    cs = tensorOfSeqExn tcreate [3] [0, 0, 2],
    ds = tensorOfSeqExn tcreate [3] [2, 2, 0],
    es = tensorOfSeqExn tcreate [2] [0, 0],
    incidenceI = tensorOfSeqExn tcreate [3] [0, 2, 1],
    incidenceJ = tensorOfSeqExn tcreate [3] [0, 2, 1],
    blocks = [[0, 1, 2]],
    assignedVars = [[0, 2, 1]],
    assignedBlocks = [0, 0, 0],
    varsInBlock = [[0, 1, 2]],
    lambdas = tensorOfSeqExn tcreate [3] [0, 0, 1],
    varIdxOffsets = tensorOfSeqExn tcreate [3] [0, 2, 4],
    inputIdxOffsets = tensorOfSeqExn tcreate [2] [0, 1],
    aliases = [(1, 0), (3, 2)]
  },

  linsysOtter = {
    dae =
      let f1 = lam xs. lam us. lam ths. lam t.
        let u1 = tget us [0] in
        let x1 = tget xs [0] in
        let x2 = tget xs [1] in
        addn (u1 t) (addn (x1 t) (x2 t))
      in
      let xs1 = [(0, 0), (1, 0)] in
      let us1 = [0] in
      let f2 = lam xs. lam us. lam ths. lam t.
        let u2 = tget us [1] in
        let x1 = tget xs [0] in
        let x2 = tget xs [1] in
        let x3 = tget xs [2] in
        let x6 = tget xs [5] in
        addn (u2 t) (addn (x1 t) (subn (x2 t) (subn (x3 t) (der x6 t))))
      in
      let xs2 = [(0, 0), (1, 0), (2, 0), (5, 1)] in
      let us2 = [1] in
      let f3 = lam xs. lam us. lam ths. lam t.
        let u3 = tget us [2] in
        let x1 = tget xs [0] in
        let x3 = tget xs [2] in
        let x4 = tget xs [3] in
        addn (u3 t) (addn (x1 t) (subn (der x3 t) (x4 t)))
      in
      let xs3 = [(0, 0), (2, 1), (3, 0)] in
      let us3 = [2] in
      let f4 = lam xs. lam us. lam ths. lam t.
        let u4 = tget us [3] in
        let x1 = tget xs [0] in
        let x2 = tget xs [1] in
        let x3 = tget xs [2] in
        let x4 = tget xs [3] in
        let x6 = tget xs [5] in
        addn (u4 t)
             (addn (muln (num 2.) (nder 2 x1 t))
                   (addn (nder 2 x2 t)
                         (addn (nder 2 x3 t)
                               (addn (der x4 t)
                                     (nder 3 x6 t)))))
      in
      let xs4 = [(0, 2), (1, 2), (2, 2), (3, 1), (5, 3)] in
      let us4 = [3] in
      let f5 = lam xs. lam us. lam ths. lam t.
        let u5 = tget us [4] in
        let x1 = tget xs [0] in
        let x2 = tget xs [1] in
        let x5 = tget xs [4] in
        let x8 = tget xs [7] in
        addn (u5 t)
             (addn (muln (num 3.) (nder 3 x1 t))
                   (addn (muln (num 2.) (nder 3 x2 t))
                         (addn (x5 t)
                               (muln (num 0.1) (x8 t)))))
      in
      let xs5 = [(0, 2), (1, 2), (4, 0), (7, 0)] in
      let us5 = [4] in
      let f6 = lam xs. lam us. lam ths. lam t.
        let u6 = tget us [5] in
        let x6 = tget xs [5] in
        let x7 = tget xs [6] in
        addn (u6 t)
             (addn (muln (num 2.) (x6 t))
                   (x7 t))
      in
      let xs6 = [(5, 0), (6, 0)] in
      let us6 = [5] in
      let f7 = lam xs. lam us. lam ths. lam t.
        let u7 = tget us [6] in
        let x6 = tget xs [5] in
        let x7 = tget xs [6] in
        addn (u7 t)
             (addn (muln (num 3.) (x6 t))
                   (muln (num 4.) (x7 t)))
      in
      let xs7 = [(5, 0), (6, 0)] in
      let us7 = [6] in
      let f8 = lam xs. lam us. lam ths. lam t.
        let u8 = tget us [7] in
        let x8 = tget xs [7] in
        addn (u8 t) (x8 t)
      in
      let xs8 = [(7, 0)] in
      let us8 = [7] in
      [(f1, xs1, us1), (f2, xs2, us2), (f3, xs3, us3), (f4, xs4, us4),
       (f5, xs5, us5), (f6, xs6, us6), (f7, xs7, us7), (f8, xs8, us8)],

    sigma = tensorOfSeqExn tcreate [8, 8]
      [0, 0, n, n, n, n, n, n  -- x1 - x2
      ,0, 0, 0, n, n, 1, n, n  -- x1 + x2 - x3 + x6'
      ,0, n, 1, 0, n, n, n, n  -- x1 + x3' - x4
      ,2, 2, 2, 1, n, 3, n, n  -- 2x1'' + x2'' + x3'' + x4' + x6'''
      ,2, 2, n, n, 0, n, n, 0  -- 3x1'' + 2x2'' + x5 + 0.1x8
      ,n, n, n, n, n, 0, 0, n  -- 2x6 + x7
      ,n, n, n, n, n, 0, 0, n  -- 3x6 + 4x7
      ,n, n, n, n, n, n, n, 0],-- x8

    cs = tensorOfSeqExn tcreate [8] [2, 2, 1, 0, 0, 3, 3, 0],
    ds = tensorOfSeqExn tcreate [8] [2, 2, 2, 1, 0, 3, 3, 0],
    es = tensorOfSeqExn tcreate [8] [2, 2, 1, 0, 0, 3, 3, 0],
    incidenceI = tensorOfSeqExn tcreate [8] [1, 0, 2, 3, 4, 6, 5, 7],
    incidenceJ = tensorOfSeqExn tcreate [8] [1, 0, 2, 3, 4, 6, 5, 7],
    blocks = [[0, 1, 2, 3], [4], [5, 6], [7]],
    assignedVars = [[0, 1, 2, 3], [4], [5, 6], [7]],
    assignedBlocks = [0, 0, 0, 0, 1, 2, 2, 3],
    varsInBlock = [[0, 1, 2, 3, 5], [0, 1, 4, 7], [5, 6], [7]],
    lambdas = tensorOfSeqExn tcreate [8] [0, 0, 0, 0, 1, 0, 0, 0],
    varIdxOffsets = tensorOfSeqExn tcreate [8] [0, 2, 4, 6, 7, 8, 11, 14],
    inputIdxOffsets = tcreate [0] (lam. 0),
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
    let t = tcreate [n, n] (lam. sigmaNoEdge) in
    iteri
      (lam i. lam xs.
        iter
          (lam x.
            let d = maxi (tget t [i, idOrdId x]) (idOrdOrd x) in
            tset t [i, idOrdId x] d)
          xs)
      xss;
    t

utest
  let xss = daeVars testSystems.pendulum.dae in
  sigmaMatrix xss
with testSystems.pendulum.sigma
using tensorEq eqi

utest
  let xss = daeVars testSystems.linsysOtter.dae in
  sigmaMatrix xss
with testSystems.linsysOtter.sigma
using tensorEq eqi


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

  let n = get (tensorShape sigma) 0 in

  let solverPrimalProblem = maxmatchFindMatch in

  let solveDualProblem = lam incidenceI. lam ds. lam cs.

    let sigmaTr = tensorTransposeExn sigma 0 1 in
    let tmpSigma = tcreate (tensorShape sigma) (lam. 0) in
    let tmpCs = tcreate [n] (lam. 0) in

    recursive let loop = lam.
      tensorMapExn (lam c. c) cs tmpCs;

      -- d[j] <- max_i(sigma[i][j] + c[i])
      tensorMapiExn (lam idx. lam s.
                      let j = get idx 1 in addi (tget cs [j]) s)
                    sigmaTr
                    tmpSigma;

      tensorIterSlice (lam j. lam row. tset ds [j] (tensorMax subi row))
                      tmpSigma;

      -- c[i] <- d[incidenceI[i]] - sigma[i][incidenceI[i]]
      tensorMapiInplace
        (lam idx. lam.
          let i = get idx 0 in
          let ii = tget incidenceI idx in
          subi (tget ds [ii]) (tget sigma [i, ii]))
          cs;

      tensorMapiExn (lam i. lam c. subi c (tget tmpCs i)) cs tmpCs;

      if tensorAll (eqi 0) tmpCs then ()
      else loop ()
    in
    loop ()
  in

  -- Start of algorithm
  if or (neqi (tensorRank sigma) 2) (not (tensorDimsEqual sigma)) then
    error "Invalid argument: daecore.sigmaIndexReduce"
  else
    match solverPrimalProblem sigma with
      { incidenceU = incidenceI, incidenceV = incidenceJ, weight = weight }
    then
      if lti weight 0 then error "Singular matrix: daecore.sigmaIndexReduce"
      else
        let ds = tcreate [n] (lam. 0) in
        let cs = tcreate [n] (lam. 0) in
        solveDualProblem incidenceI ds cs;
        { cs = cs, ds = ds, incidenceI = incidenceI, incidenceJ = incidenceJ }
    else never

utest (sigmaIndexReduce testSystems.pendulum.sigma).cs
with testSystems.pendulum.cs using tensorEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).ds
with testSystems.pendulum.ds using tensorEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).incidenceI
with testSystems.pendulum.incidenceI using tensorEq eqi

utest (sigmaIndexReduce testSystems.pendulum.sigma).incidenceJ
with testSystems.pendulum.incidenceJ using tensorEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).cs
with testSystems.linsysOtter.cs using tensorEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).ds
with testSystems.linsysOtter.ds using tensorEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).incidenceI
with testSystems.linsysOtter.incidenceI using tensorEq eqi

utest (sigmaIndexReduce testSystems.linsysOtter.sigma).incidenceJ
with testSystems.linsysOtter.incidenceJ using tensorEq eqi


-- Columns of `sigma` incident to row `i`.
let sigmaAllIncident : Matrix Int -> Int -> [Int] =
  lam sigma. lam i.
    map
      head
      (tensorFilteri
        (lam. lam x. gti x sigmaNoEdge)
        (tensorSliceExn sigma [i]))

utest
  let sigma = testSystems.pendulum.sigma in
  map (sigmaAllIncident sigma) [0, 1, 2]
with [[0, 2], [1, 2], [0, 1]]


let inputOffsets : Matrix Int -> Vector Int -> [[Int]] -> Vector Int =
lam sigma. lam cs. lam us.
  let nu =
    setSize (foldl setUnion (setEmpty subi) (map (setOfSeq subi) us))
  in
  let uos = tcreate [nu] (lam idx. 0) in
  iteri
    (lam i. lam us.
      (iter
        (lam j.
          tset uos [j] (maxi (tget cs [i]) (tget uos [j])))
        us))
    us;
  uos

utest
  let us = daeInputs testSystems.pendulum.dae in
  let sigma = testSystems.pendulum.sigma in
  let cs = testSystems.pendulum.cs in
  inputOffsets sigma cs us
with testSystems.pendulum.es
using tensorEq eqi

utest
  let us = daeInputs testSystems.linsysOtter.dae in
  let sigma = testSystems.linsysOtter.sigma in
  let cs = testSystems.linsysOtter.cs in
  inputOffsets sigma cs us
with testSystems.linsysOtter.es
using tensorEq eqi

-----------------
-- BLT SORTING --
-----------------

let mkDependencyGraph : Matrix Int -> Vector Int -> Digraph Int Int =
lam sigma. lam incidenceJ.
  let n = tensorSize incidenceJ in
  let fs = create n (lam i. i) in
  let g = digraphEmpty eqi eqi in
  let g = foldl (lam g. lam f. digraphAddVertex f g) g fs in
  tensorFoldi
    (lam g. lam fv. lam x.
      match fv with [f, v] then
        let af = tget incidenceJ [v] in
        if and (gti x sigmaNoEdge) (neqi af f) then digraphAddEdge af f x g
        else g
      else error "Invalid argument: daecore.mkDependencyGraph")
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
    map (map (lam eq. tget incidenceJ [eq])) blocks

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
  eqi (addi (tget ds [v]) (tget lambdas [v])) 0

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
  let nvs = tensorSize arg.ds in

  -- Number of blocks
  let nblocks = length arg.blocks in

  -- Enumerate variables
  let vs = create nvs (lam v. v) in

  -- Variables assigned to each BLT block
  let assignedVars = bltAssignedVars arg.incidenceJ arg.blocks in

  -- BLT block assigned to each variable
  let blockAssignedToVars =
    tensorOfSeqExn tcreate [nvs] (bltAssigned assignedVars vs)
  in

  let assignedVars =
    tensorOfSeqExn tcreate [nblocks] assignedVars
  in

  -- Variables in each BLT block
  let bltVars =
    tensorOfSeqExn tcreate [nblocks] (bltVars arg.sigma arg.blocks)
  in

  -- Vector indicating if algebraic variable should be substituted with its
  -- derivative. A 0 means no and a 1 means yes.
  let lambdas = tcreate [nvs] (lam. 0) in

  let isAlgebraic = isAlgebraic arg.ds lambdas in
  let isDifferential = isDifferential arg.ds lambdas in

  -- Substitute `v` for its derivative if `v` is algebraic
  let maybeSubstitute =
    lam v. if isAlgebraic v then tset lambdas [v] 1 else ()
  in

  -- Main Algorithm
  recursive let recur = lam us.
    match us with [] then ()
    else match us with [u] ++ us then
      if isAlgebraic u then
        let block = tget blockAssignedToVars [u] in
        let assignedVars = tget assignedVars [block] in
        let blockVars = tget bltVars [block] in
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
using tensorEq eqi

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
using tensorEq eqi


-----------------------------
-- FIRST-ORDER FORMULATION --
-----------------------------

-- The index offset of each variable in a first-order formulation
let idxOffsets : Vector Int -> Vector Int =
  lam ofs.
    let n = tensorSize ofs in
    let t = tensorMapCopy (maxi 1) ofs in
    tensorCumsumiInplace t;
    let idxOfs = tensorCreateDense [n] (lam. 0) in
    tensorMapExn
      (lam x. x)
      (tensorSubExn t 0 (subi n 1))
      (tensorSubExn idxOfs 1 (subi n 1));
    idxOfs

utest
  let ofs = idxOffsets (tcreate [0] (lam. 0)) in
  tensorToSeqExn ofs
with []

utest idxOffsets testSystems.pendulum.ds
with testSystems.pendulum.varIdxOffsets
using tensorEq eqi

utest idxOffsets testSystems.linsysOtter.ds
with testSystems.linsysOtter.varIdxOffsets
using tensorEq eqi


-- Indexes indicating alias equations of the first-order DAE
let aliases : Vector Int -> [(Int, Int)] =
lam ds.
  let idxOffsets = idxOffsets ds in
  let dxs = tensorFilteri (lam. lam d. gti d 0) ds in
  let f =
    recursive let recur = lam a. lam d. lam idx.
      if eqi (tget ds idx) d then a
      else recur (snoc a (addi (tget idxOffsets idx) d)) (succ d) idx
    in recur [] 0
  in
  let g = lam idxs. zip (tail idxs) (init idxs) in
  join (map (compose g f) dxs)

utest
  let ds = testSystems.pendulum.ds in
  aliases ds
with [(1, 0), (3, 2)]

utest
  let ds = testSystems.linsysOtter.ds in
  aliases ds
with [(1, 0), (3, 2), (5, 4), (9, 8), (10, 9), (12, 11), (13, 12)]


let nVariables : Vector Int -> Int =
  lam ofs. tensorFold (lam a. lam d. addi a (maxi 1 d)) 0 ofs

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
  let isDifferentiated = lam e. gti (tget arg.cs [e]) 0 in

  let neqs = tensorSize arg.cs in
  let eqs = create neqs (lam e. e) in
  let nblocks = length arg.blocks in

  let assignedVars =
    tensorOfSeqExn tcreate [nblocks] (bltAssignedVars arg.incidenceJ arg.blocks)
  in

  let assignedEqs =
    tensorOfSeqExn tcreate [neqs] (bltAssigned arg.blocks eqs)
  in

  let eqs0d =
    filter
      (lam e.
        let block = tget assignedEqs [e] in
        let assignedVars = tget assignedVars [block] in
        and (not (isDifferentiated e)) (all isDifferential assignedVars))
      eqs
  in

  let eqs0a =
      filter
      (lam e.
        let block = tget assignedEqs [e] in
        let assignedVars = tget assignedVars [block] in
        and (not (isDifferentiated e)) (all isAlgebraic assignedVars))
      eqs
  in

  let eqs0c = filter isDifferentiated eqs in

  let eqsNc =
  foldl
    (lam a. lam i. concat a (map (lam o. (i, o)) (range 1 (tget arg.cs [i]) 1)))
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
    (6, 1), (6, 2) ]
}


-------------------------
-- SETTERS AND GETTERS --
-------------------------

let offsetGet : Vector Int -> Vector a -> IdOrd -> a =
lam offsets.
  let idxOffsets = idxOffsets offsets in
  lam y. lam v.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let ofs = tget idxOffsets [i] in
    tget y [addi ofs o]

let offsetSet : Vector Int -> Vector a -> IdOrd -> a -> () =
lam offsets.
  let idxOffsets = idxOffsets offsets in
  lam y. lam v. lam val.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let ofs = tget idxOffsets [i] in
    tset y [addi ofs o] val

let offsetGetYYPLambdas
  : { ds : Vector Int, lambdas : Vector Int }
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam arg.
  let idxOffsets = idxOffsets arg.ds in
  lam y. lam yp. lam v.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let l = tget arg.lambdas [i] in
    let o = addi o l in
    let ofs = tget idxOffsets [i] in
    let dmax = tget arg.ds [i] in

    if or (lti o dmax) (eqi o 0) then
      tget y [addi ofs o]
    else if eqi (subi o l) dmax then
      tget yp [addi ofs (pred o)]
    else
      error "Unknown variable: daecore.offsetGetYYPLambdas"

utest
  let arg = {
    ds = testSystems.pendulum.ds,
    lambdas = testSystems.pendulum.lambdas
  } in
  let y = tensorRangei tcreate [5] 0 in
  let yp = tensorRangei tcreate [5] 5 in
  mapi
    (lam i. map (lam o. offsetGetYYPLambdas arg y yp (i, o)))
    [[0, 1, 2], [0, 1, 2], [0]]
with [[0, 1, 6], [2, 3, 8], [9]]

utest
  let arg = {
    ds = testSystems.linsysOtter.ds,
    lambdas = testSystems.linsysOtter.lambdas
  } in
  let y = tensorRangei tcreate [15] 0 in
  let yp = tensorRangei tcreate [15] 15 in
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
  let idxOffsets = idxOffsets arg.ds in
  lam y. lam yp. lam v. lam val.
    let i = idOrdId v in
    let o = idOrdOrd v in
    let l = tget arg.lambdas [i] in
    let o = addi o l in
    let ofs = tget idxOffsets [i] in
    let dmax = tget arg.ds [i] in
    if or (lti o dmax) (eqi o 0) then
      let i = addi ofs o in
      tset y [i] val;
      let j = mapLookup i aliases in
      match j with Some j then
        tset yp [j] val
      else match j with None _ then ()
      else never
    else if eqi (subi o l) dmax then
      tset yp [addi ofs (pred o)] val
    else
      error "Unknown variable: daecore.offsetSetYYPLambdas"

utest
  let arg = {
    ds = testSystems.pendulum.ds,
    lambdas = testSystems.pendulum.lambdas
  } in
  let y = tcreate [5] (lam. (negi 1)) in
  let yp = tcreate [5] (lam. (negi 1)) in
  let offsetSetYYPLambdas = offsetSetYYPLambdas arg y yp in
  iteri
    (lam i. map (lam dv : (Int, Int). offsetSetYYPLambdas (i, dv.0) dv.1))
    [[(0, 0), (1, 1), (2, 2)], [(0, 3), (1, 4), (2, 5)], [(0, 6)]];
  [tensorToSeqExn y, tensorToSeqExn yp]
with [[0, 1, 3, 4, negi 1], [1, 2, 4, 5, 6]]


let offsetGetYYP
  : Vector Int
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam ds. offsetGetYYPLambdas {
  ds = ds,
  lambdas = tcreate [tensorSize ds] (lam. 0)
}

let offsetSetYYP
  : Vector Int
  -> Vector a
  -> Vector a
  -> IdOrd
  -> a =
lam ds. offsetSetYYPLambdas {
  ds = ds,
  lambdas = tcreate [tensorSize ds] (lam. 0)
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

    ds : Vector Int,
    es : Vector Int,
    ny : Int
}

-- Vector indicating which dependent variables in the first-order system are
-- differential.
let isdiffLambdas : Vector Int -> Vector Int -> [Bool] =
 lam lambdas. lam ds.
  let f = lam idx. lam d.
    if eqi d 0 then
      if eqi (tget lambdas idx) 0 then [false] else [true]
    else create d (lam. true)
  in
  join (tensorFoldi (lam acc. lam idx. lam d. snoc acc (f idx d)) [] ds)

let isdiff : Vector Int -> [Bool] =
  lam ds. isdiffLambdas (tcreate [tensorSize ds] (lam. 0)) ds

utest
  let ds = tensorOfSeqExn tcreate [3] [2, 2, 0] in
  let lambdas = tensorOfSeqExn tcreate [3] [0, 0, 1] in
  isdiffLambdas lambdas ds
with [true, true, true, true, true]

utest
  let ds = tensorOfSeqExn tcreate [8] [2, 2, 2, 1, 0, 3, 3, 0] in
  let lambdas = tensorOfSeqExn tcreate [8] [0, 0, 0, 0, 1, 0, 0, 0] in
  isdiffLambdas lambdas ds
with snoc (create 14 (lam. true)) false using eqSeq eqBool

utest
  let ds = tensorOfSeqExn tcreate [3] [2, 2, 0] in
  let lambdas = tensorOfSeqExn tcreate [3] [0, 0, 1] in
  isdiff ds
with [true, true, true, true, false]

-- Define v_i(t)
let v = lam get.
  recursive let recur = lam d. lam i.
    lam t. dualnumLift1 (lam. get (i, d)) (recur (succ d) i) t
  in recur 0


-- Formulate residual function for index-reduced, non-stabilized DAE.
let residual
  : {
    cs : Vector Int,
    ds : Vector Int,
    es : Vector Int
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
  let aliases = aliases arg.ds in
  let nx = tensorSize arg.ds in
  let nu = tensorSize arg.es in
  let xs = tcreate [nx] (lam. lam. num 0.) in
  let us = tcreate [nu] (lam. lam. num 0.) in
  let xis = create nx (lam i. i) in
  let uis = create nu (lam i. i) in
  let stateGet = offsetGetYYP arg.ds in
  let resf = lam t. lam y. lam yp. lam u. lam th. lam r.
    let stateGet = stateGet y yp in
    let inputGet = lam x : IdOrd. tget (tget u [idOrdId x]) [idOrdOrd x] in

    -- Define x_i(t)
    let x = v stateGet in

    -- Define u_i(t)
    let u = v inputGet in

    -- Populate xs with x_i(t) for i = 0..nx-1
    iter (lam i. tset xs [i] (x i)) xis;

    -- Populate us with u_i(t) for i = 0..nu-1
    iter (lam i. tset us [i] (u i)) uis;

    -- Compute index-reduced residual
    iteri (lam i. lam f. tset r [i] (nder (tget arg.cs [i]) (f xs us th) t)) fs;

    -- Compute alias equations
    iteri
      (lam i. lam a : (Int, Int).
        tset r [addi i nx] (subn (tget y [a.0]) (tget yp [a.1])))
      aliases

  in

  let ds = tensorCopy arg.ds in
  let es = tensorCopy arg.es in
  let ny = nVariables arg.ds in

  { resf = resf, ds = ds, es = es, ny = ny }

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
  let fs = daeResiduals testSystems.pendulum.dae in
  let res : FirstOrderResidual = residual arg fs in
  let t = num 0. in
  let y = tensorOfSeqExn tcreate [5] (map num [x0, dx0, x1, dx1, x2]) in
  let yp =
    tensorOfSeqExn tcreate [5] (map num [dx0, ddx0, dx1, ddx1, negf 10000.])
  in
  let u = tcreate [2] (lam. tcreate [1] (lam. num 0.)) in
  let r = tcreate [5] (lam. num 0.) in
  let th = tcreate [3] (lam. num 1.) in
  res.resf t y yp u th r;
  map dualnumUnpackNum (tensorToSeqExn r)
with [
  subf ddx0 (mulf x0 x2),
  addf (subf ddx1 (mulf x1 x2)) 1.,
  mulf 2. (addf
            (addf (mulf ddx0 x0) (mulf ddx1 x1))
            (addf (mulf dx0 dx0) (mulf dx1 dx1))),
  0.,
  0.
]

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
      arg.sigma
      (tensorMapCopy (lam c. mini 0 (subi c 1)) arg.cs)
      arg.us
  in

  -- Getters
  let stateGetY = offsetGet arg.ds in
  let inputGet = lam u. lam x : IdOrd. tget (tget u [idOrdId x]) [idOrdOrd x] in
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

  -- Sort residual functions

  -- Non-differentiated differential residual
  let f0d = map (lam i. get fs i) se.eqs0d in

  -- Algebraic residual
  let f0a = map (lam i. get fs i) se.eqs0a in

  -- Non-differentiated constraint residual
  let f0c = map (lam i. get fs i) se.eqs0c in

  -- Differentiated constraint residual, except at the highest differentiation
  -- order
  let fNc =
    map (lam e : IdOrd. (get fs (idOrdId e), idOrdOrd e)) se.eqsNc
  in

  -- Compute problem sizes
  let nf0d = length f0d in
  let nf0a = length f0a in
  let nf0c = length f0c in
  let nfNc = length fNc in
  let nf = foldl addi 0 [nf0d, nf0a, nf0c, nfNc] in
  let nx = tensorSize arg.ds in
  let nu = tensorSize es in

  -- number of variables in first-order system
  let nvars = nVariables arg.ds in

  -- Alias residual
  let aliases = aliases arg.ds in
  let naliases = length aliases in

  -- number of dummy variables
  let nmu = nfNc in

  -- Pre-allocate intermediate data-structures
  let xis = create nx (lam i. i) in
  let uis = create nu (lam i. i) in
  let xs = tcreate [nx] (lam. lam. num 0.) in
  let us = tcreate [nu] (lam. lam. num 0.) in
  let g_i = tcreate [nfNc] (lam. num 0.) in

  -- Differentiated constraint residual
  let resNc = lam t. lam y. lam u. lam th. lam r.
    let stateGet = stateGetY y in
    let inputGet = inputGet u in

    -- Define x_i(t)
    let x = v stateGet in

    -- Define u_i(t)
    let u = v inputGet in

    -- Populate xs with x_i(t) for i = 0..nx-1
    iter (lam i. tset xs [i] (x i)) xis;

    -- Populate us with u_i(t) for i = 0..nu-1
    iter (lam i. tset us [i] (u i)) uis;

    iteri
      (lam i. lam fo : (Residual, Int). tset r [i] (nder fo.1 (fo.0 xs us th) t))
      fNc
  in

  let resf = lam t. lam y. lam yp. lam u. lam th. lam r.
    let stateGet = stateGetYYP y yp in
    let inputGet = inputGet u in

    -- Define x_i(t)
    let x = v stateGet in

    -- Define u_i(t)
    let u = v inputGet in

    -- Populate xs with x_i(t) for i = 0..nx-1
    iter (lam i. tset xs [i] (x i)) xis;

    -- Populate us with u_i(t) for i = 0..nu-1
    iter (lam i. tset us [i] (u i)) uis;

    -- Compute non-differentiated differential residual
    iteri (lam i. lam f. tset r [i] (f xs us th t)) f0d;

    -- Compute algebraic residual
    let ofs = nf0d in
    iteri (lam i. lam f. tset r [addi i ofs] (f xs us th t)) f0a;

    -- Compute non-differentiated constraint residual
    let ofs = addi ofs nf0a in
    iteri (lam i. lam f. tset r [addi i ofs] (f xs us th t)) f0c;

    -- Compute differentiated constraint residual
    let ofs = addi ofs nf0c in
    resNc t y u th (tensorSubExn r ofs nfNc);

    -- Compute stabilized alias residual
    iteri
      (lam i. lam a : (Int, Int).
        jaci (lam y. resNc t y u th) a.0 y g_i;
        tensorMapiInplace
          (lam idx. muln (tget yp [addi nvars (head idx)]))
          g_i;
        let alias = subn (tget y [a.0]) (tget yp [a.1]) in
        let corr = tensorFold addn (num 0.) g_i in
        tset r [addi nf i] (addn alias corr))
      aliases;

    ()
  in

  -- Update variable offset vector
  let nds = tensorSize arg.ds in
  let ds = tcreate [addi nds nmu] (lam. 1) in
  tensorIteri
    (lam idx. lam d. tset ds idx (addi d (tget arg.lambdas idx)))
    arg.ds;

  { resf = resf, ds = ds, es = es, ny = addi nvars nmu }


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
    us = daeInputs testSystems.pendulum.dae
  } in
  let fs = daeResiduals testSystems.pendulum.dae in
  let res : FirstOrderResidual = residualStabilized arg fs in
  let t = num 0. in
  let y =
    tensorOfSeqExn tcreate [6] (map num [x0, dx0, x1, dx1, negf 10000., 0.])
  in
  let yp =
    tensorOfSeqExn tcreate [6] (map num [dx0, ddx0, dx1, ddx1, x2, mu0])
  in
  let u = tcreate [2] (lam. tcreate [1] (lam. num 0.)) in
  let r = tcreate [6] (lam. num 0.) in
  let th = tcreate [3] (lam. num 1.) in
  res.resf t y yp u th r;
  map dualnumUnpackNum (tensorToSeqExn r)
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

----------------------
-- MAIN ENTRY POINT --
----------------------

type DaecoreResidual = {
  -- Residual function f(t, y, yp, u, r), where r stores the result of the
  -- residual.
  resf
  : DualNum
  -> Vector DualNum
  -> Vector DualNum
  -> Vector (Vector DualNum)
  -> Vector DualNum
  -> Vector DualNum
  -> (),

  -- Getter for the state y, yp.
  stateGet : Vector a -> Vector a -> IdOrd -> a,

  -- Setter for the state y, yp.
  stateSet : Vector a -> Vector a -> IdOrd -> a -> (),

  -- Variable offset
  ds : Vector Int,

  -- Input offset
  es : Vector Int,

  -- Size of residual
  ny : Int
}

-- Non-stabilized low-index residual
let daecoreResidual : DAE -> DaecoreResidual = lam dae.
  if not (daeConsistent dae) then
    error "Inconsistent DAE: daecore.daecoreResidual"
  else
    let fs = daeResiduals dae in
    let vs = daeVars dae in
    let us = daeInputs dae in

    let sigma = sigmaMatrix vs in
    match sigmaIndexReduce sigma with
      { cs = cs, ds = ds, incidenceJ = incidenceJ }
    then
      let es = inputOffsets sigma cs us in
      let stateGet = offsetGetYYP ds in
      let stateSet = offsetSetYYP ds in

      let res : FirstOrderResidual =
        residual { cs = cs, ds = ds, es = es } fs
      in

      {
        resf = res.resf,
        stateGet = stateGet,
        stateSet = stateSet,
        ds = res.ds,
        es = res.es,
        ny = res.ny
      }
    else never

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  let y = tensorOfSeqExn tcreate [5] (map num [1., 0., 0., 0., 0.]) in
  let yp = tensorOfSeqExn tcreate [5] (map num [0., 0., 0., negf 1., 0.]) in
  let u = tcreate [2] (lam. tcreate [1] (lam. num 0.)) in
  let r = tcreate [5] (lam. num 0.) in
  let t = num 0. in
  res.resf t y yp u r;
  tensorToSeqExn r
with create 5 (lam. num 0.) using eqSeq (dualnumEq eqf)

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  let y = tcreate [5] (lam. 0) in
  let yp = tcreate [5] (lam. 0) in
  res.stateSet y yp (0, 0) 1;
  res.stateSet y yp (0, 1) 2;
  res.stateSet y yp (0, 2) 3;
  res.stateSet y yp (1, 0) 4;
  res.stateSet y yp (1, 1) 5;
  res.stateSet y yp (1, 2) 6;
  res.stateSet y yp (2, 0) 7;
  (tensorToSeqExn y, tensorToSeqExn yp)
with ([1, 2, 4, 5, 7], [2, 3, 5, 6, 0])

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  let y = tcreate [5] (lam idx. addi 1 (head idx)) in
  let yp = tcreate [5] (lam idx. addi 6 (head idx)) in
  [
    res.stateGet y yp (0, 0),
    res.stateGet y yp (0, 1),
    res.stateGet y yp (0, 2),
    res.stateGet y yp (1, 0),
    res.stateGet y yp (1, 1),
    res.stateGet y yp (1, 2),
    res.stateGet y yp (2, 0)
  ]
with [1, 2, 7, 3, 4, 9, 5]

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  tensorToSeqExn res.ds
with [2, 2, 0]

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  tensorToSeqExn res.es
with [0, 0]

utest
  let res = daecoreResidual testSystems.pendulum.dae in
  res.ny
with 5

-- Stabilized low-index residual
let daecoreResidualStabilized : DAE -> DaecoreResidual = lam dae.
  if not (daeConsistent dae) then
    error "Inconsistent DAE: daecore.daecoreResidual"
  else
    let fs = daeResiduals dae in
    let vs = daeVars dae in
    let us = daeInputs dae in

    let sigma = sigmaMatrix vs in
    match sigmaIndexReduce sigma with
      { cs = cs, ds = ds, incidenceJ = incidenceJ }
    then
      let es = inputOffsets sigma cs us in
      let blocks = bltSort sigma incidenceJ in
      let lambdas = sortFindLambda {
        sigma = sigma,
        ds = ds,
        blocks = blocks,
        incidenceJ = incidenceJ
      } in

      let stateGet = offsetGetYYPLambdas { ds = ds, lambdas = lambdas } in
      let stateSet = offsetSetYYPLambdas { ds = ds, lambdas = lambdas } in

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
        stateGet = stateGet,
        stateSet = stateSet,
        ds = res.ds,
        es = res.es,
        ny = res.ny
      }
    else never

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  let y = tensorOfSeqExn tcreate [6] (map num [1., 0., 0., 0., 0., 0.]) in
  let yp = tensorOfSeqExn tcreate [6] (map num [0., 0., 0., negf 1., 0., 0.]) in
  let u = tcreate [2] (lam. tcreate [1] (lam. num 0.)) in
  let r = tcreate [6] (lam. num 0.) in
  let t = num 0. in
  res.resf t y yp u r;
  tensorToSeqExn r
with create 6 (lam. num 0.) using eqSeq (dualnumEq eqf)

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  let y = tcreate [6] (lam. 0) in
  let yp = tcreate [6] (lam. 0) in
  res.stateSet y yp (0, 0) 1;
  res.stateSet y yp (0, 1) 2;
  res.stateSet y yp (0, 2) 3;
  res.stateSet y yp (1, 0) 4;
  res.stateSet y yp (1, 1) 5;
  res.stateSet y yp (1, 2) 6;
  res.stateSet y yp (2, 0) 7;
  (tensorToSeqExn y, tensorToSeqExn yp)
with ([1, 2, 4, 5, 0, 0], [2, 3, 5, 6, 7, 0])

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  let y = tcreate [6] (lam idx. addi 1 (head idx)) in
  let yp = tcreate [6] (lam idx. addi 7 (head idx)) in
  [
    res.stateGet y yp (0, 0),
    res.stateGet y yp (0, 1),
    res.stateGet y yp (0, 2),
    res.stateGet y yp (1, 0),
    res.stateGet y yp (1, 1),
    res.stateGet y yp (1, 2),
    res.stateGet y yp (2, 0)
  ]
with [1, 2, 8, 3, 4, 10, 11]

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  tensorToSeqExn res.ds
with [2, 2, 1, 1]

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  tensorToSeqExn res.es
with [0, 0]

utest
  let res = daecoreResidualStabilized testSystems.pendulum.dae in
  res.ny
with 6
