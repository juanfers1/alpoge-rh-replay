import Mathlib

/-!
# Expected statements of `Main`, elaborated with Mathlib alone

This file imports only `Mathlib` (revision 0df444a360eaa60ab8c11dca51a86af692955474, Lean 4.33.1).
The propositions below are therefore elaborated without any instance, notation or definition from
the project: their terms mention only Mathlib constants, and no module imported later can redefine
those constants.

Two layers:

* **Literal forms** (`…Lit`): the exact wording expected for the five theorems of `Main`, to be
  compared term by term with the project's types.
* **Independent forms**: the same mathematics written differently (set of trivial zeros, critical
  strip as `Set.Ioo`, pole exclusion as `¬ (χ = 1 ∧ s = 1)`), each with a Mathlib-only proof that
  it is equivalent to its literal form.

At the end there are sanity checks: excluding the trivial zeros is necessary, excluding `s = 1`
does not weaken anything because `ζ(1) ≠ 0` in Mathlib, and the Dirichlet statement contains RH in
the strip (trivial character mod 1).
-/

namespace RHExpected

open Complex

/-! ## Literal forms -/

/-- RH: every zero of `ζ` other than `-2(n+1)` and different from `1` has real part `1/2`.
Same wording as Mathlib's `RiemannHypothesis`. -/
def RHLit : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- GRH for Dirichlet L-functions, non-vanishing form: for every character `χ` mod `N ≥ 1` and
every `s` with `Re s > 1/2`, except the pole (`χ` trivial and `s = 1`), `L(χ, s) ≠ 0`. -/
def DirichletNonvanishingLit : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- GRH for every Dirichlet character (primitive or not): zeros of `L(χ, s)` in the open strip
`0 < Re s < 1` have real part `1/2`. -/
def DirichletZerosLit : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- GRH restricted to primitive characters. -/
def PrimitiveDirichletZerosLit : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Mathlib's `RiemannHypothesis`, not unfolded: the literal type of `Main.riemannHypothesis`. -/
def RHMathlib : Prop := RiemannHypothesis

/-- The literal form is definitionally Mathlib's `RiemannHypothesis`. -/
theorem rhLit_eq_mathlib : RHLit = RiemannHypothesis := rfl

/-! ## Independent forms -/

/-- Trivial zeros of `ζ`: `-2, -4, -6, …`, written as `-(2k)` with `k ≥ 1`. -/
def trivialZeros : Set ℂ := {s | ∃ k : ℕ, 1 ≤ k ∧ s = -(2 * (k : ℂ))}

/-- Open critical strip. -/
def criticalStrip : Set ℂ := {s | s.re ∈ Set.Ioo (0 : ℝ) 1}

/-- Critical line. -/
def criticalLine : Set ℂ := {s | s.re = 1 / 2}

/-- RH: the non-trivial zeros of `ζ` lie on the critical line. `s = 1` is not excluded: in Mathlib
`ζ(1) ≠ 0`, so `1` is not a zero (see `zeta_one_ne_zero`). -/
def RH : Prop := riemannZeta ⁻¹' {0} \ trivialZeros ⊆ criticalLine

def DirichletNonvanishing : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    s.re > 1 / 2 → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletZeros : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    {s | DirichletCharacter.LFunction χ s = 0} ∩ criticalStrip ⊆ criticalLine

def PrimitiveDirichletZeros : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    {s | DirichletCharacter.LFunction χ s = 0} ∩ criticalStrip ⊆ criticalLine

/-! ## Sanity checks (Mathlib only) -/

theorem zeta_one_ne_zero : riemannZeta 1 ≠ 0 := riemannZeta_one_ne_zero

theorem zeta_neg_two : riemannZeta (-2) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

/-- Without excluding the trivial zeros the statement would be false. -/
theorem trivial_exclusion_needed : ¬ ∀ s : ℂ, riemannZeta s = 0 → s.re = 1 / 2 := by
  intro h
  have := h (-2) zeta_neg_two
  norm_num at this

/-- Excluding `s = 1` changes nothing: the form without that hypothesis is equivalent. -/
theorem rhLit_iff_without_pole :
    RHLit ↔ ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2 := by
  constructor
  · intro h s hz hnt
    exact h s hz hnt (by rintro rfl; exact zeta_one_ne_zero hz)
  · intro h s hz hnt _
    exact h s hz hnt

/-- The trivial zeros of the independent form are exactly those of the literal form. -/
theorem mem_trivialZeros_iff (s : ℂ) : s ∈ trivialZeros ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact ⟨n, by push_cast; ring⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, by omega, by push_cast; ring⟩

/-! ## Equivalences between the two layers (Mathlib only) -/

theorem rh_iff_lit : RH ↔ RHLit := by
  constructor
  · intro h s hz hnt _
    exact h ⟨hz, fun ht => hnt ((mem_trivialZeros_iff s).mp ht)⟩
  · rintro h s ⟨hz, hnt⟩
    exact h s hz (fun ht => hnt ((mem_trivialZeros_iff s).mpr ht))
      (by rintro rfl; exact zeta_one_ne_zero hz)

theorem dirichletNonvanishing_iff_lit : DirichletNonvanishing ↔ DirichletNonvanishingLit := by
  constructor
  · intro h N _ χ s hs hχ
    exact h N χ s hs (by rintro ⟨rfl, rfl⟩; exact hχ.elim (· rfl) (· rfl))
  · intro h N _ χ s hs hχ
    exact h N χ s hs (not_and_or.mp hχ)

theorem dirichletZeros_iff_lit : DirichletZeros ↔ DirichletZerosLit := by
  constructor
  · intro h N _ χ s h0 h1 hz
    exact h N χ ⟨hz, h0, h1⟩
  · rintro h N _ χ s ⟨hz, h0, h1⟩
    exact h N χ s h0 h1 hz

theorem primitiveDirichletZeros_iff_lit :
    PrimitiveDirichletZeros ↔ PrimitiveDirichletZerosLit := by
  constructor
  · intro h N _ χ hχ s h0 h1 hz
    exact h N χ hχ ⟨hz, h0, h1⟩
  · rintro h N _ χ hχ s ⟨hz, h0, h1⟩
    exact h N χ hχ s h0 h1 hz

/-! ## Relations between the statements (Mathlib only) -/

/-- The `Re s ≥ 1` part of the non-vanishing statement is already a Mathlib theorem, so the new
content lies in the band `1/2 < Re s < 1`. -/
theorem dirichletNonvanishing_of_one_le_re (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 ≤ s.re) (hχ : χ ≠ 1 ∨ s ≠ 1) : DirichletCharacter.LFunction χ s ≠ 0 :=
  χ.LFunction_ne_zero_of_one_le_re hχ hs

/-- The statement for all characters implies the one for primitive characters. -/
theorem primitive_of_all : DirichletZerosLit → PrimitiveDirichletZerosLit :=
  fun h N _ χ _ s h0 h1 hz => h N χ s h0 h1 hz

/-- The Dirichlet statement contains RH in the strip: with `N = 1`, `L(χ, s) = ζ(s)`. -/
theorem zeta_strip_of_dirichletZeros (h : DirichletZerosLit) (s : ℂ) (h0 : 0 < s.re)
    (h1 : s.re < 1) (hz : riemannZeta s = 0) : s.re = 1 / 2 := by
  have := h 1 (1 : DirichletCharacter ℂ 1) s h0 h1
  rw [DirichletCharacter.LFunction_modOne_eq] at this
  exact this hz

end RHExpected

#print axioms RHExpected.rhLit_eq_mathlib
#print axioms RHExpected.rh_iff_lit
#print axioms RHExpected.dirichletNonvanishing_iff_lit
#print axioms RHExpected.dirichletZeros_iff_lit
#print axioms RHExpected.primitiveDirichletZeros_iff_lit
#print axioms RHExpected.trivial_exclusion_needed
#print axioms RHExpected.rhLit_iff_without_pole
#print axioms RHExpected.zeta_strip_of_dirichletZeros
