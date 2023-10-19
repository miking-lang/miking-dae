include "result.mc"
include "error.mc"
include "set.mc"
include "maxmatch-tensor.mc"
include "digraph.mc"
include "daecore-types.mc"

include "./lib/mat.mc"
include "./lib/vec.mc"

----------------------
-- HELPER FUNCTIONS --
----------------------

type Res a = Result ErrorSection ErrorSection a

type SigmaStructuralAnalysis = {
  c : Vector Int,
  d : Vector Int,
  incidenceI : Vector Int,
  incidenceJ : Vector Int
}

let _sigmaStructuralAnalysis
  : Matrix Int -> Res SigmaStructuralAnalysis =
  lam sigma.
    let n = (matDim sigma).0 in
    let solverPrimalProblem = maxmatchFindMatch in
    let solveDualProblem = lam incidenceI. lam d. lam c.
      let sigmaTr = matTranspose sigma in
      let tmpSigma = matCreate (matDim sigma) (lam. lam. 0) in
      let tmpCs = vecCreate n (lam. 0) in
      recursive let recur = lam.
        vecBlit c tmpCs;
        -- d[j] <- max_i(sigma[i][j] + c[i])
        matMapi
          (lam. lam j. lam s. lam. addi (vecGet c j) s)
          sigmaTr
          tmpSigma;
        matIterRow
          (lam j. lam row. vecSet d j (vecMax subi row))
          tmpSigma;
        -- c[i] <- d[incidenceI[i]] - sigma[i][incidenceI[i]]
        vecMapiInplace
          (lam i. lam.
            let j = vecGet incidenceI i in
            subi (vecGet d j) (matGet sigma i j))
          c;
        vecMap subi c tmpCs;
        if vecAll (eqi 0) tmpCs then ()
        else recur ()
      in
      recur ()
    in
    -- Start of algorithm
    if not (matIsSquareMatrix sigma) then
      result.err {
        errorDefault with
        msg = "Non-square matrix: daecore.sigmaIndexReduce"
      }
    else
      match solverPrimalProblem sigma with
        { incidenceU = incidenceI, incidenceV = incidenceJ, weight = weight }
      in
      if lti weight 0 then
        result.err {
          errorDefault with
          msg = "Singular matrix: daecore.sigmaIndexReduce"
        }
      else
        let d = vecCreate n (lam. 0) in
        let c = vecCreate n (lam. 0) in
        solveDualProblem incidenceI d c;
        result.ok {
          c = c,
          d = d,
          incidenceI = incidenceI,
          incidenceJ = incidenceJ
        }


-- Columns of `sigma` incident to row `i`.
let _sigmaAllIncident : Matrix Int -> Int -> [Int] =
  lam sigma. lam i.
    vecFilteri (lam. lam x. gti x daecoreSigmaNoEdge) (matRow sigma i)

let _inputOffsets : Vector Int -> [[Int]] -> Vector Int = lam c. lam us.
  let nu =
    setSize (foldl setUnion (setEmpty subi) (map (setOfSeq subi) us))
  in
  let uos = vecCreate nu (lam idx. 0) in
  iteri
    (lam i. lam us.
      (iter
         (lam j.
           vecSet uos j (maxi (vecGet c i) (vecGet uos j)))
         us))
    us;
  uos

let _mkDependencyGraph : Matrix Int -> Vector Int -> Digraph Int Int =
  lam sigma. lam incidenceJ.
    let n = vecLength incidenceJ in
    let fs = create n (lam i. i) in
    let g = digraphEmpty subi eqi in
    let g = foldl (lam g. lam f. digraphAddVertex f g) g fs in
    matFoldi
      (lam g. lam f. lam v. lam x.
        let af = vecGet incidenceJ v in
        if
          and
            (gti x daecoreSigmaNoEdge)
            (neqi af f) then digraphAddEdge af f x g
        else g)
      g
      sigma

-- Sorts system given by `sigma` and `varToEq` into BLT blocks.
let _bltSort : Matrix Int -> Vector Int -> [[Int]] = lam sigma. lam varToEq.
  let g = _mkDependencyGraph sigma varToEq in
  digraphStrongConnects g

-- Assigned variables in each BLT block (`varToEq`, `block`).
let _bltAssignedVars : Vector Int -> [[Int]] -> [[Int]] =
  lam varToEq. lam blocks.
    map (map (lam eqn. vecGet varToEq eqn)) blocks

-- BLT block of `blocks` assigned to each variable `xs`
let _bltAssigned : [[Int]] -> [Int] -> Res [Int] =
  lam blocks. lam xs.
    let isAssigned = lam x. lam blocks. any (eqi x) blocks in
    optionMapOr
      (result.err {
        errorDefault with
        msg = "Unassigned variable: daecore._bltAssigned"
      })
      result.ok
      (optionMapM (lam x. index (isAssigned x) blocks) xs)

-- Variables in each BLT block
let _bltVars : Matrix Int -> [[Int]] -> [[Int]] =
  lam sigma. lam blocks.
    let vars = map (map (_sigmaAllIncident sigma)) blocks in
    map (lam vars. setToSeq (foldl1 setUnion (map (setOfSeq subi) vars))) vars

-- Variable `v` is algebraic
let _isAlgebraic = lam ds. lam lambdas. lam v.
  eqi (addi (vecGet ds v) (vecGet lambdas v)) 0

-- Variable `v` is differential
let _isDifferential = lam ds. lam lambdas. lam v.
  not (_isAlgebraic ds lambdas v)


type SortFindLambdaArg = {
  sigma : Matrix Int,
  d : Vector Int,
  blocks : [[Int]],
  varToEq : Vector Int
}

-- The lambda vector, indicating algebraic varaibles to be substituted for their
-- derivative.
let _sortFindLambda : SortFindLambdaArg -> Res (Vector Int) =
  lam arg.
    -- Number of variables
    let nvs = vecLength arg.d in
    -- Number of blocks
    let nblocks = length arg.blocks in
    -- Enumerate variables
    let vs = create nvs (lam v. v) in
    -- Variables assigned to each BLT block
    let assignedVars = _bltAssignedVars arg.varToEq arg.blocks in
    -- BLT block assigned to each variable
    result.bind (_bltAssigned assignedVars vs)
      (lam seq.
        let blockAssignedToVars = vecOfSeq seq in
        let assignedVars = vecOfSeq assignedVars in
        -- Variables in each BLT block
        let bltVars = vecOfSeq (_bltVars arg.sigma arg.blocks) in
        -- Vector indicating if algebraic variable should be substituted with
        -- its derivative. A 0 means no and a 1 means yes.
        let lambda = vecCreate nvs (lam. 0) in
        let isAlgebraic = _isAlgebraic arg.d lambda in
        let isDifferential = _isDifferential arg.d lambda in
        -- Substitute `v` for its derivative if `v` is algebraic
        let maybeSubstitute =
          lam v. if isAlgebraic v then vecSet lambda v 1 else ()
        in
        -- Main Algorithm
        recursive let recur = lam us.
          switch us
          case [] then ()
          case [u] ++ us then
            if isAlgebraic u then
              let block = vecGet blockAssignedToVars u in
              let assignedVars = vecGet assignedVars block in
              let blockVars = vecGet bltVars block in
              if or
                   (any isDifferential assignedVars)
                   (any isDifferential blockVars)
              then
                -- Since this algebraic variable is assigned to a BLT block
                -- where either some assigned variable is differential, and/or
                -- not all variables in this block are algebraic, we need to
                -- substitute all assigned algebraic variables in this BLT block
                -- with their derivatives.
                iter maybeSubstitute assignedVars;
                -- Then we repeat the algorithm from the first variable since
                -- the substitution might affect other BLT blocks.
                recur vs
              else recur us
            else recur us
          end
        in
        recur vs;
        result.ok lambda)

let _sortEqns : {
  c : Vector Int,
  lambda : Vector Int,
  eqns : [EqnStructure]
} -> {eqns0d : [Int], eqns0a : [Int], eqns0c : [Int], eqnsNc : [IdOrd]} =
  lam arg.
    match arg with { c = c, lambda = lambda, eqns = eqns } in
    let eqns = map (lam x : EqnStructure. x.variables) eqns in
    -- Substitute algebraic variables for their derivatives according to lambda.
    let eqns =
      map
        (lam e : [IdOrd].
          let f = lam v : IdOrd.
            match v with (id, ord) in (id, addi ord (vecGet lambda id))
          in
          map f e)
        eqns
    in
    -- Sort in differentiated and non-differentiated equations.
    let eqnsd = map (lam id. (id, get eqns id)) (vecFilteri (lam. eqi 0) c) in
    let eqns0c = vecFilteri (lam. lti 0) c in
    let getId = lam x : (Int, [IdOrd]). x.0 in
    -- Sort dynamic equations in into algebraic and differential equations.
    let hasDiffVar = lam e : (Int, [IdOrd]).
      match e with (_, vars) in
      any (lam v : IdOrd. match v with (_, ord) in gti ord 0) vars
    in
    let eqns0d = map getId (filter hasDiffVar eqnsd) in
    let eqns0a = map getId (filter (lam e. not (hasDiffVar e)) eqnsd) in
    -- Sort constraint equations into algebraic and differentiated constraints.
    let eqnsNc =
      foldl
        (lam a. lam i.
          concat a (map (lam o. (i, o)) (range 1 (vecGet arg.c i) 1)))
        []
        eqns0c
    in
    { eqns0d = eqns0d, eqns0a = eqns0a, eqns0c = eqns0c, eqnsNc = eqnsNc }

--------------------
-- IMPLEMENTATION --
--------------------

-- Constructs the sigma matrix from a sequence of equation structures.
let createSigmaMatrix : [EqnStructure] -> Matrix Int = lam eqns.
  let n = length eqns in
  let t = matCreate (n, n) (lam. lam. daecoreSigmaNoEdge) in
  iteri
    (lam i. lam xs.
      iter
        (lam x : IdOrd.
          match x with (id, ord) in
          let ord = maxi (matGet t i id) ord in
          matSet t i id ord)
        xs)
    (map (lam e : EqnStructure. e.variables) eqns);
  t


---------------
-- INTERFACE --
---------------

-- Analyses structure of DAE
let structuralAnalysis : [EqnStructure] -> Res DAEStructureLowIndex =
  lam eqns.
    let sigma = createSigmaMatrix eqns in
    result.bind (_sigmaStructuralAnalysis sigma)
      (lam analysis.
        match analysis with { c = c, d = d, incidenceJ = varToEq } in
        let e = _inputOffsets c (map (lam e. e.inputs) eqns) in
        result.ok { sigma = sigma, c = c, d = d, e = e, varToEq = varToEq })

-- Analyses structure of DAE and returns structure of index-reduced, stabilized
-- DAE.
let structuralAnalysisStable
  : [EqnStructure] -> Res DAEStructureLowIndexStable =
  lam eqns.
    result.bind (structuralAnalysis eqns)
      (lam analysis.
        match analysis with
          { sigma = sigma, c = c, d = d, e = e, varToEq = varToEq }
        in
        let blocks = _bltSort sigma varToEq in
        result.bind (_sortFindLambda {
          sigma   = sigma,
          d       = d,
          blocks  = blocks,
          varToEq = varToEq
        })
          (lam lambda.
            vecMap addi lambda d;
            vecMapInplace (lam e. if gti e 0 then pred e else e) e;
            match _sortEqns { c = c, lambda = lambda, eqns = eqns } with {
              eqns0d = eqns0d,
              eqns0a = eqns0a,
              eqns0c = eqns0c,
              eqnsNc = eqnsNc
            } in
            let nmu = length eqnsNc in
            result.ok {
              d      = d,
              e      = e,
              lambda = lambda,
              nmu    = nmu,
              eqns0d  = eqns0d,
              eqns0a  = eqns0a,
              eqns0c  = eqns0c,
              eqnsNc  = eqnsNc
            }))

mexpr

let teq = tensorEq in
let teqi = teq eqi in

-- We test this library on the following DAE equations:

--------------
-- PENDULUM --
--------------

-- A planar pendulum expressed in Cartesian Coordinates (index 3):

-- (1) m x1'' = x3 x1
-- (2) m x2'' = x3 x2 - mg
-- (3) x1^2 + x2^2 = l^2

-- where x1, x2 are the position of the pendulum endpoint in the plane and x3
-- the tension per unit length in the pendulum arm. physical constants m, l, g
-- are the mass, length, and the acceleration of gravity, respectively.

-- Model structure
let eqns = [
  { variables = [(0, 0), (0, 2), (2, 0)], inputs = [] },
  { variables = [(1, 0), (1, 2), (2, 0)], inputs = [] },
  { variables = [(0, 0), (1, 0)], inputs = [] }
] in

-- Test fixtures
let none = daecoreSigmaNoEdge in
let sigma =
  let n = none in
  matOfSeq (3, 3) [
    2 , n , 0 ,
    n , 2 , 0 ,
    0 , 0 , n
  ] in

let c = vecOfSeq [0, 0, 2] in
let d = vecOfSeq [2, 2, 0] in
let e = vecOfSeq [] in
let varToEq = vecOfSeq [0, 2, 1] in
let lambda = vecOfSeq [0, 0, 1] in

-- Test helper functions (for debugging purposes)
let testHelpers =
  let blocks = [[0, 1, 2]] in
  let assignedVars = [[0, 2, 1]] in
  let assignedBlocks = [0, 0, 0] in
  let varsInBlock = [[0, 1, 2]] in

  utest map (_sigmaAllIncident sigma) [0, 1, 2] with [[0, 2], [1, 2], [0, 1]] in
  utest _bltSort sigma varToEq with blocks using eqsetEqual (eqsetEqual eqi) in

  utest _bltAssignedVars varToEq blocks
    with assignedVars using eqsetEqual (eqsetEqual eqi) in

  utest
    let vs = create 3 (lam v. v) in
    match result.consume (_bltAssigned blocks vs) with (_, Right res) in res
    with assignedBlocks in

  utest _bltVars sigma blocks with varsInBlock in

  utest
    match result.consume (_sortFindLambda {
      sigma   = sigma,
      d       = d,
      blocks  = blocks,
      varToEq = varToEq
    }) with (_, Right res) in res
    with lambda using vecEq eqi in
  ()
in

-- Test functions over structure
utest createSigmaMatrix eqns with sigma using teqi in

let s =
  match result.consume (structuralAnalysis eqns) with (_, Right res) in res
in
utest s.c with c using teqi in
utest s.d with d using teqi in
utest s.e with e using teqi in
utest s.varToEq with varToEq using teqi in

let d = vecOfSeq [2, 2, 1] in
let e = vecOfSeq [] in
let nmu = 1 in
let eqns0d = [0, 1] in
let eqns0a : [Int] = [] in
let eqns0c = [2] in
let eqnsNc = [(2, 1)] in

let s =
  match result.consume (structuralAnalysisStable eqns)
    with (_, Right res)
  in res
in
utest s.d with d using teqi in
utest s.e with e using teqi in
utest s.lambda with lambda using teqi in
utest s.nmu with nmu in
utest s.eqns0d with eqns0d in
utest s.eqns0a with eqns0a in
utest s.eqns0c with eqns0c in
utest s.eqnsNc with eqnsNc in

-------------------
-- LINEAR SYSTEM --
-------------------

-- A Linear system with inputs

-- (1) u1 + x1 - x2 = 0
-- (2) u2 + x1 + x2 - x3 + x6' = 0
-- (3) u3 + x1 + x3' - x4 = 0
-- (4) u4 + 2x1'' + x2'' + x3'' + x4' + x6''' = 0
-- (5) u5 + 3x1'' + 2x2'' + x5 + 0.1x8 = 0
-- (6) u6 + 2x6 + x7 = 0
-- (7) u7 + 3x6 + 4x7 = 0
-- (8) u8 + x8 = 0

-- where u are inputs and x are states.

-- Model structure
let eqns = [
  { variables = [(0, 0), (1, 0)], inputs = [0] },
  { variables = [(0, 0), (1, 0), (2, 0), (5, 1)], inputs = [1] },
  { variables = [(0, 0), (2, 1), (3, 0)], inputs = [2] },
  { variables = [(0, 2), (1, 2), (2, 2), (3, 1), (5, 3)], inputs = [3] },
  { variables = [(0, 2), (1, 2), (4, 0), (7, 0)], inputs = [4] },
  { variables = [(5, 0), (6, 0)], inputs = [5] },
  { variables = [(5, 0), (6, 0)], inputs = [6] },
  { variables = [(7, 0)], inputs = [7] }
] in

let sigma =
  let n = none in
  matOfSeq (8, 8) [
    0 , 0 , n , n , n , n , n , n ,
    0 , 0 , 0 , n , n , 1 , n , n ,
    0 , n , 1 , 0 , n , n , n , n ,
    2 , 2 , 2 , 1 , n , 3 , n , n ,
    2 , 2 , n , n , 0 , n , n , 0 ,
    n , n , n , n , n , 0 , 0 , n ,
    n , n , n , n , n , 0 , 0 , n ,
    n , n , n , n , n , n , n , 0
  ] in

let c = vecOfSeq [2, 2, 1, 0, 0, 3, 3, 0] in
let d = vecOfSeq [2, 2, 2, 1, 0, 3, 3, 0] in
let e = vecOfSeq [2, 2, 1, 0, 0, 3, 3, 0] in
let varToEq = vecOfSeq [1, 0, 2, 3, 4, 6, 5, 7] in
let lambda = vecOfSeq [0, 0, 0, 0, 1, 0, 0, 0] in

-- Test helper functions (for debugging purposes)
let testHelpers =
  let blocks = [[0, 1, 2, 3], [4], [5, 6], [7]] in
  let assignedVars = [[0, 1, 2, 3], [4], [5, 6], [7]] in
  let assignedBlocks = [0, 0, 0, 0, 1, 2, 2, 3] in
  let varsInBlock = [[0, 1, 2, 3, 5], [0, 1, 4, 7], [5, 6], [7]] in

  utest _bltAssignedVars varToEq blocks
    with assignedVars using eqsetEqual (eqsetEqual eqi) in

  utest
    let vs = create 8 (lam v. v) in
    match result.consume (_bltAssigned blocks vs) with (_, Right res) in res
    with assignedBlocks in

  utest _bltVars sigma blocks with varsInBlock in

  utest
    match result.consume (_sortFindLambda {
      sigma   = sigma,
      d       = d,
      blocks  = blocks,
      varToEq = varToEq
    })
      with (_, Right res) in res with
    lambda using vecEq eqi in
  ()
in

-- Test functions over structure
utest createSigmaMatrix eqns with sigma using teqi in

let s =
  match result.consume (structuralAnalysis eqns) with (_, Right res) in res
in
utest s.c with c using teqi in
utest s.d with d using teqi in
utest s.e with e using teqi in
utest s.varToEq with varToEq using teqi in

let d = vecOfSeq [2, 2, 2, 1, 1, 3, 3, 0] in
let e = vecOfSeq [1, 1, 0, 0, 0, 2, 2, 0] in
let nmu = 6 in
let eqns0d = [3, 4] in
let eqns0a = [7] in
let eqns0c = [0, 1, 2, 5, 6] in
let eqnsNc = [(0, 1), (1, 1), (5, 1), (5, 2), (6, 1), (6, 2)] in

let s =
  match result.consume (structuralAnalysisStable eqns)
    with (_, Right res)
  in res
in
utest s.d with d using teqi in
utest s.e with e using teqi in
utest s.lambda with lambda using teqi in
utest s.nmu with nmu in
utest s.eqns0d with eqns0d in
utest s.eqns0a with eqns0a in
utest s.eqns0c with eqns0c in
utest s.eqnsNc with eqnsNc in

-- DD example
let sigma =
  let n = none in
  matOfSeq (4, 4) [
    0 , 0 , n , n ,
    0 , 0 , 0 , n ,
    0 , n , 1 , 0 ,
    2 , 2 , 2 , 1
  ] in

-- utest _sigmaStructuralAnalysis sigma with {} in

---------------------
-- PENDULUM ROBERT --
---------------------

-- A planar pendulum expressed in Cartesian Coordinates (index 3):

-- (0) m x1'' - x3 x1 + k |x1'| x1 - u - w^2
-- (1) m x2'' = x3 x2 + k |x2'| x2 + mg
-- (2) x1^2 + x2^2 - L^2
-- (3) l4' + x3 l1 - 2 x1 l3
-- (4) l5' + x3 l2 - 2 x2 l3
-- (5) x1 l1 + x2 l2
-- m l1' - 2 k |x1'| l1 + l4
-- m l2' - 2 k |x2'| l2 + l5

-- y:
-- (0) x1
-- (1) x2
-- (2) x3
-- (3) l1
-- (4) l2
-- (5) l3
-- (6) l4
-- (7) l5

-- Model structure
let eqns = [
  { variables = [(0, 0), (0, 1), (0, 2), (2, 0)], inputs = [0, 1] },
  { variables = [(1, 0), (1, 1), (1, 2), (2, 0)], inputs = [] },
  { variables = [(0, 0), (1, 0)], inputs = [] },
  { variables = [(0, 0), (2, 0), (3, 0), (5, 0), (6, 1)], inputs = [] },
  { variables = [(1, 0), (2, 0), (4, 0), (5, 0), (7, 1)], inputs = [] },
  { variables = [(0, 0), (1, 0), (3, 0), (4, 0)], inputs = [] },
  { variables = [(0, 1), (3, 0), (3, 1), (6, 0)], inputs = [] },
  { variables = [(1, 1), (4, 0), (4, 1), (7, 0)], inputs = [] }
] in

let s =
  match result.consume (structuralAnalysisStable eqns)
    with (_, Right res)
  in res
in

let d = vecOfSeq [2, 2, 1, 2, 2, 1, 1, 1] in
let e = vecOfSeq [0, 0] in
let nmu = 2 in
let lambda = vecOfSeq [0, 0, 1, 0, 0, 1, 0, 0] in
let eqns0d = [0, 1, 3, 4] in
let eqns0a = [] in
let eqns0c = [2, 5, 6, 7] in
let eqnsNc = [(2, 1), (5, 1)] in

utest s.d with d using teqi in
utest s.e with e using teqi in
utest s.lambda with lambda using teqi in
utest s.nmu with nmu in
utest s.eqns0d with eqns0d in
utest s.eqns0a with eqns0a in
utest s.eqns0c with eqns0c in
utest s.eqnsNc with eqnsNc in

()
