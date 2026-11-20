import ExpectedStatements
import Main
import StatementCheck

/-!
# Comparing the five theorems of `Main` (M170889) with the pinned propositions

Requires the genuine `Main.olean`, built from sources matching the index SHA-256 digests. No
statement is elaborated here: only names from `RHExpected` are used, and those propositions were
elaborated with Mathlib alone in `ExpectedStatements.lean`.
-/

-- The kernel checks that each theorem of `Main` proves the pinned proposition (literal form).
theorem CompareMain.rh : RHExpected.RHLit := riemannHypothesis
theorem CompareMain.zeta : RHExpected.RHLit := riemannZeta_eq_zero_re
theorem CompareMain.nonvanishing : RHExpected.DirichletNonvanishingLit :=
  LFunction_ne_zero_of_half_lt_re
theorem CompareMain.zeros : RHExpected.DirichletZerosLit := LFunction_eq_zero_re
theorem CompareMain.primitive : RHExpected.PrimitiveDirichletZerosLit :=
  LFunction_eq_zero_re_of_isPrimitive

-- Independent forms, through the equivalences proved with Mathlib alone.
theorem CompareMain.rh' : RHExpected.RH := RHExpected.rh_iff_lit.mpr CompareMain.rh
theorem CompareMain.nonvanishing' : RHExpected.DirichletNonvanishing :=
  RHExpected.dirichletNonvanishing_iff_lit.mpr CompareMain.nonvanishing
theorem CompareMain.zeros' : RHExpected.DirichletZeros :=
  RHExpected.dirichletZeros_iff_lit.mpr CompareMain.zeros
theorem CompareMain.primitive' : RHExpected.PrimitiveDirichletZeros :=
  RHExpected.primitiveDirichletZeros_iff_lit.mpr CompareMain.primitive

-- Term-by-term comparison of the types after unfolding only project definitions.
run_cmd StatementCheck.checkPairs #[
  (`riemannHypothesis, `RHExpected.RHMathlib),
  (`riemannZeta_eq_zero_re, `RHExpected.RHLit),
  (`LFunction_ne_zero_of_half_lt_re, `RHExpected.DirichletNonvanishingLit),
  (`LFunction_eq_zero_re, `RHExpected.DirichletZerosLit),
  (`LFunction_eq_zero_re_of_isPrimitive, `RHExpected.PrimitiveDirichletZerosLit)]

run_cmd StatementCheck.checkAxioms #[``riemannHypothesis, ``riemannZeta_eq_zero_re,
  ``LFunction_ne_zero_of_half_lt_re, ``LFunction_eq_zero_re,
  ``LFunction_eq_zero_re_of_isPrimitive, ``CompareMain.rh, ``CompareMain.zeta,
  ``CompareMain.nonvanishing, ``CompareMain.zeros, ``CompareMain.primitive, ``CompareMain.rh',
  ``CompareMain.nonvanishing', ``CompareMain.zeros', ``CompareMain.primitive']

-- Full types (pp.all) of the five theorems.
set_option pp.all true in
#check @riemannHypothesis
set_option pp.all true in
#check @riemannZeta_eq_zero_re
set_option pp.all true in
#check @LFunction_ne_zero_of_half_lt_re
set_option pp.all true in
#check @LFunction_eq_zero_re
set_option pp.all true in
#check @LFunction_eq_zero_re_of_isPrimitive
