import ExpectedStatements
import Statements
import StatementCheck

/-!
# Comparing `Statements.lean` (M175184) with the pinned propositions

`Statements` imports only `Mathlib` and defines four of the five types used in `Main`. The fifth,
`RiemannHypothesis`, comes from Mathlib and is compared here as well.
-/

-- Kernel check: each project definition is, by definition, the pinned proposition.
theorem CompareStatements.zeta : RiemannZetaZerosOnLine = RHExpected.RHLit := rfl
theorem CompareStatements.nonvanishing :
    DirichletLNonvanishingRightOfHalf = RHExpected.DirichletNonvanishingLit := rfl
theorem CompareStatements.zeros : DirichletLZerosOnLine = RHExpected.DirichletZerosLit := rfl
theorem CompareStatements.primitive :
    PrimitiveDirichletLZerosOnLine = RHExpected.PrimitiveDirichletZerosLit := rfl

run_cmd StatementCheck.checkPairs #[
  (`RiemannHypothesis, `RHExpected.RHLit),
  (`RiemannZetaZerosOnLine, `RHExpected.RHLit),
  (`DirichletLNonvanishingRightOfHalf, `RHExpected.DirichletNonvanishingLit),
  (`DirichletLZerosOnLine, `RHExpected.DirichletZerosLit),
  (`PrimitiveDirichletLZerosOnLine, `RHExpected.PrimitiveDirichletZerosLit)]

run_cmd StatementCheck.checkAxioms #[``CompareStatements.zeta, ``CompareStatements.nonvanishing,
  ``CompareStatements.zeros, ``CompareStatements.primitive]

-- Full terms (pp.all), to expose every implicit argument and instance.
set_option pp.all true in
#print RiemannHypothesis
set_option pp.all true in
#print RiemannZetaZerosOnLine
set_option pp.all true in
#print DirichletLNonvanishingRightOfHalf
set_option pp.all true in
#print DirichletLZerosOnLine
set_option pp.all true in
#print PrimitiveDirichletLZerosOnLine
