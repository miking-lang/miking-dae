include "set.mc"

------------------------------------------------
-- DIFFERENTIAL ALGEBRAIC SYSTEM OF EQUATIONS --
------------------------------------------------

-- The DAE is given on the form:
--
-- F(x, dxdt, d2xdt, ..., u, th, t) = 0,
--
-- where the vectors x, dxdt, and d2xdt holds the dependent variables and their
-- derivatives, u the inputs, th the parameters, and the scalar t is the free
-- variable.

-- A tuple `(id, ord)` representing a dependent variable `id` at the
-- differentiation order `ord` w.r.t. the free variable. `id` is assumed to be
-- in the range [0, n-1], where n is the size of the DAE problem.
type IdOrd = (Int, Int)

-- A scalar residual function
type Residual =
  (Int -> DualNum) ->              -- parameters theta
  (Int -> (DualNum -> DualNum)) -> -- inputs u(t)
  (Int -> (DualNum -> DualNum)) -> -- states x(t)
  [DualNum -> DualNum]             -- residuals f(t)

-- A single residual function in a high-index DAE. consists of a list of tuples,
-- where `variables` is a list of dependent variables present in this particular
-- residual function and `inputs` are inputs present in this particular
-- residual.
type DAE = { residual : Residual, variables : [[IdOrd]], inputs : [[Int]] }

type ConstraintFun =
  (Int -> DualNum) ->              -- parameters theta
  (Int -> (DualNum -> DualNum)) -> -- inputs u(t)
  DualNum ->                       -- free variable t
  (Int -> (DualNum -> DualNum)) -> -- states x(t)
  Vector DualNum ->                -- value of constraint function g
  ()

-------------
-- HELPERS --
-------------

let idOrdId = lam x : IdOrd. x.0
let idOrdOrd = lam x : IdOrd. x.1
let cmpIdOrd = lam x : IdOrd. lam y : IdOrd.
  if eqi (idOrdId x) (idOrdId y) then subi (idOrdOrd x) (idOrdOrd y)
  else subi (idOrdId x) (idOrdId y)
let idOrdDer = lam x : IdOrd. (x.0, succ x.1)
let idOrdDerN = lam n. lam x : IdOrd. (x.0, addi x.1 n)
let idOrdInt = lam x : IdOrd. (x.0, pred x.1)
let idOrdIntN = lam n. lam x : IdOrd. (x.0, subi x.1 n)
let idOrdToString =
  lam x : IdOrd.
    join ["d", int2string (idOrdOrd x), "x", int2string (idOrdId x)]
