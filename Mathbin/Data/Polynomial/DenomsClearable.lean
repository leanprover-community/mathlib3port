/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.polynomial.denoms_clearable
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.EraseLead
import Mathbin.Data.Polynomial.Eval

/-!
# Denominators of evaluation of polynomials at ratios

Let `i : R → K` be a homomorphism of semirings.  Assume that `K` is commutative.  If `a` and
`b` are elements of `R` such that `i b ∈ K` is invertible, then for any polynomial
`f ∈ R[X]` the "mathematical" expression `b ^ f.nat_degree * f (a / b) ∈ K` is in
the image of the homomorphism `i`.
-/


open Polynomial Finset

open Polynomial

section DenomsClearable

variable {R K : Type _} [Semiring R] [CommSemiring K] {i : R →+* K}

variable {a b : R} {bi : K}

-- TODO: use hypothesis (ub : is_unit (i b)) to work with localizations.
/-- `denoms_clearable` formalizes the property that `b ^ N * f (a / b)`
does not have denominators, if the inequality `f.nat_degree ≤ N` holds.

The definition asserts the existence of an element `D` of `R` and an
element `bi = 1 / i b` of `K` such that clearing the denominators of
the fraction equals `i D`.
-/
def DenomsClearable (a b : R) (N : ℕ) (f : R[X]) (i : R →+* K) : Prop :=
  ∃ (D : R)(bi : K), bi * i b = 1 ∧ i D = i b ^ N * eval (i a * bi) (f.map i)
#align denoms_clearable DenomsClearable

theorem denoms_clearable_zero (N : ℕ) (a : R) (bu : bi * i b = 1) : DenomsClearable a b N 0 i :=
  ⟨0, bi, bu, by simp only [eval_zero, RingHom.map_zero, mul_zero, Polynomial.map_zero]⟩
#align denoms_clearable_zero denoms_clearable_zero

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([2]) } -/
theorem denoms_clearable_C_mul_X_pow {N : ℕ} (a : R) (bu : bi * i b = 1) {n : ℕ} (r : R)
    (nN : n ≤ N) : DenomsClearable a b N (c r * X ^ n) i :=
  by
  refine' ⟨r * a ^ n * b ^ (N - n), bi, bu, _⟩
  rw [C_mul_X_pow_eq_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, eval_mul, eval_pow, eval_C]
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, eval_X, mul_comm]
  rw [← tsub_add_cancel_of_le nN]
  rw [pow_add, mul_assoc, mul_comm (i b ^ n), mul_pow, mul_assoc, mul_assoc (i a ^ n), ← mul_pow]
  rw [bu, one_pow, mul_one]
#align denoms_clearable_C_mul_X_pow denoms_clearable_C_mul_X_pow

theorem DenomsClearable.add {N : ℕ} {f g : R[X]} :
    DenomsClearable a b N f i → DenomsClearable a b N g i → DenomsClearable a b N (f + g) i :=
  fun ⟨Df, bf, bfu, Hf⟩ ⟨Dg, bg, bgu, Hg⟩ =>
  ⟨Df + Dg, bf, bfu,
    by
    rw [RingHom.map_add, Polynomial.map_add, eval_add, mul_add, Hf, Hg]
    congr
    refine' @inv_unique K _ (i b) bg bf _ _ <;> rwa [mul_comm]⟩
#align denoms_clearable.add DenomsClearable.add

theorem denoms_clearable_of_nat_degree_le (N : ℕ) (a : R) (bu : bi * i b = 1) :
    ∀ f : R[X], f.natDegree ≤ N → DenomsClearable a b N f i :=
  induction_with_nat_degree_le _ N (denoms_clearable_zero N a bu)
    (fun N_1 r r0 => denoms_clearable_C_mul_X_pow a bu r) fun f g fg gN df dg => df.add dg
#align denoms_clearable_of_nat_degree_le denoms_clearable_of_nat_degree_le

/-- If `i : R → K` is a ring homomorphism, `f` is a polynomial with coefficients in `R`,
`a, b` are elements of `R`, with `i b` invertible, then there is a `D ∈ R` such that
`b ^ f.nat_degree * f (a / b)` equals `i D`. -/
theorem denoms_clearable_nat_degree (i : R →+* K) (f : R[X]) (a : R) (bu : bi * i b = 1) :
    DenomsClearable a b f.natDegree f i :=
  denoms_clearable_of_nat_degree_le f.natDegree a bu f le_rfl
#align denoms_clearable_nat_degree denoms_clearable_nat_degree

end DenomsClearable

open RingHom

/-- Evaluating a polynomial with integer coefficients at a rational number and clearing
denominators, yields a number greater than or equal to one.  The target can be any
`linear_ordered_field K`.
The assumption on `K` could be weakened to `linear_ordered_comm_ring` assuming that the
image of the denominator is invertible in `K`. -/
theorem one_le_pow_mul_abs_eval_div {K : Type _} [LinearOrderedField K] {f : ℤ[X]} {a b : ℤ}
    (b0 : 0 < b) (fab : eval ((a : K) / b) (f.map (algebraMap ℤ K)) ≠ 0) :
    (1 : K) ≤ b ^ f.natDegree * |eval ((a : K) / b) (f.map (algebraMap ℤ K))| :=
  by
  obtain ⟨ev, bi, bu, hF⟩ :=
    @denoms_clearable_nat_degree _ _ _ _ b _ (algebraMap ℤ K) f a
      (by
        rw [eq_intCast, one_div_mul_cancel]
        rw [Int.cast_ne_zero]
        exact b0.ne.symm)
  obtain Fa := congr_arg abs hF
  rw [eq_one_div_of_mul_eq_one_left bu, eq_intCast, eq_intCast, abs_mul] at Fa
  rw [abs_of_pos (pow_pos (int.cast_pos.mpr b0) _ : 0 < (b : K) ^ _), one_div, eq_intCast] at Fa
  rw [div_eq_mul_inv, ← Fa, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  refine' Int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr fun F0 => fab _))
  rw [eq_one_div_of_mul_eq_one_left bu, F0, one_div, eq_intCast, Int.cast_zero, zero_eq_mul] at hF
  cases' hF with hF hF
  · exact (not_le.mpr b0 (le_of_eq (int.cast_eq_zero.mp (pow_eq_zero hF)))).elim
  · rwa [div_eq_mul_inv]
#align one_le_pow_mul_abs_eval_div one_le_pow_mul_abs_eval_div

