/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Data.ENNReal.Basic

#align_import data.real.conjugate_exponents from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Real conjugate exponents

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`p.is_conjugate_exponent q` registers the fact that the real numbers `p` and `q` are `> 1` and
satisfy `1/p + 1/q = 1`. This property shows up often in analysis, especially when dealing with
`L^p` spaces.

We make several basic facts available through dot notation in this situation.

We also introduce `p.conjugate_exponent` for `p / (p-1)`. When `p > 1`, it is conjugate to `p`.
-/


noncomputable section

namespace Real

#print Real.IsConjExponent /-
/-- Two real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
structure IsConjExponent (p q : ℝ) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : 1 / p + 1 / q = 1
#align real.is_conjugate_exponent Real.IsConjExponent
-/

#print Real.conjExponent /-
/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
def conjExponent (p : ℝ) : ℝ :=
  p / (p - 1)
#align real.conjugate_exponent Real.conjExponent
-/

namespace IsConjugateExponent

variable {p q : ℝ} (h : p.IsConjExponent q)

#print Real.IsConjExponent.pos /-
/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
theorem pos : 0 < p :=
  lt_trans zero_lt_one h.one_lt
#align real.is_conjugate_exponent.pos Real.IsConjExponent.pos
-/

#print Real.IsConjExponent.nonneg /-
theorem nonneg : 0 ≤ p :=
  le_of_lt h.Pos
#align real.is_conjugate_exponent.nonneg Real.IsConjExponent.nonneg
-/

#print Real.IsConjExponent.ne_zero /-
theorem ne_zero : p ≠ 0 :=
  ne_of_gt h.Pos
#align real.is_conjugate_exponent.ne_zero Real.IsConjExponent.ne_zero
-/

#print Real.IsConjExponent.sub_one_pos /-
theorem sub_one_pos : 0 < p - 1 :=
  sub_pos.2 h.one_lt
#align real.is_conjugate_exponent.sub_one_pos Real.IsConjExponent.sub_one_pos
-/

#print Real.IsConjExponent.sub_one_ne_zero /-
theorem sub_one_ne_zero : p - 1 ≠ 0 :=
  ne_of_gt h.sub_one_pos
#align real.is_conjugate_exponent.sub_one_ne_zero Real.IsConjExponent.sub_one_ne_zero
-/

#print Real.IsConjExponent.one_div_pos /-
theorem one_div_pos : 0 < 1 / p :=
  one_div_pos.2 h.Pos
#align real.is_conjugate_exponent.one_div_pos Real.IsConjExponent.one_div_pos
-/

#print Real.IsConjExponent.one_div_nonneg /-
theorem one_div_nonneg : 0 ≤ 1 / p :=
  le_of_lt h.one_div_pos
#align real.is_conjugate_exponent.one_div_nonneg Real.IsConjExponent.one_div_nonneg
-/

#print Real.IsConjExponent.one_div_ne_zero /-
theorem one_div_ne_zero : 1 / p ≠ 0 :=
  ne_of_gt h.one_div_pos
#align real.is_conjugate_exponent.one_div_ne_zero Real.IsConjExponent.one_div_ne_zero
-/

#print Real.IsConjExponent.conj_eq /-
theorem conj_eq : q = p / (p - 1) :=
  by
  have := h.inv_add_inv_conj
  rw [← eq_sub_iff_add_eq', one_div, inv_eq_iff_eq_inv] at this
  field_simp [this, h.ne_zero]
#align real.is_conjugate_exponent.conj_eq Real.IsConjExponent.conj_eq
-/

#print Real.IsConjExponent.conjExponent_eq /-
theorem conjExponent_eq : conjExponent p = q :=
  h.conj_eq.symm
#align real.is_conjugate_exponent.conjugate_eq Real.IsConjExponent.conjExponent_eq
-/

#print Real.IsConjExponent.sub_one_mul_conj /-
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq
#align real.is_conjugate_exponent.sub_one_mul_conj Real.IsConjExponent.sub_one_mul_conj
-/

#print Real.IsConjExponent.mul_eq_add /-
theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj
#align real.is_conjugate_exponent.mul_eq_add Real.IsConjExponent.mul_eq_add
-/

#print Real.IsConjExponent.symm /-
@[symm]
protected theorem symm : q.IsConjExponent p :=
  { one_lt := by rw [h.conj_eq]; exact (one_lt_div h.sub_one_pos).mpr (sub_one_lt p)
    inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj }
#align real.is_conjugate_exponent.symm Real.IsConjExponent.symm
-/

#print Real.IsConjExponent.div_conj_eq_sub_one /-
theorem div_conj_eq_sub_one : p / q = p - 1 :=
  by
  field_simp [h.symm.ne_zero]
  rw [h.sub_one_mul_conj]
#align real.is_conjugate_exponent.div_conj_eq_sub_one Real.IsConjExponent.div_conj_eq_sub_one
-/

#print NNReal.IsConjExponent.one_lt /-
theorem one_lt : 1 < Real.toNNReal p :=
  by
  rw [← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff h.pos]
  exact h.one_lt
#align real.is_conjugate_exponent.one_lt_nnreal NNReal.IsConjExponent.one_lt
-/

#print NNReal.IsConjExponent.inv_add_inv_conj /-
theorem inv_add_inv_conj : 1 / Real.toNNReal p + 1 / Real.toNNReal q = 1 := by
  rw [← Real.toNNReal_one, ← Real.toNNReal_div' h.nonneg, ← Real.toNNReal_div' h.symm.nonneg, ←
    Real.toNNReal_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]
#align real.is_conjugate_exponent.inv_add_inv_conj_nnreal NNReal.IsConjExponent.inv_add_inv_conj
-/

#print Real.IsConjExponent.inv_add_inv_conj_ennreal /-
theorem inv_add_inv_conj_ennreal : 1 / ENNReal.ofReal p + 1 / ENNReal.ofReal q = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos h.pos, ←
    ENNReal.ofReal_div_of_pos h.symm.pos, ←
    ENNReal.ofReal_add h.one_div_nonneg h.symm.one_div_nonneg, h.inv_add_inv_conj]
#align real.is_conjugate_exponent.inv_add_inv_conj_ennreal Real.IsConjExponent.inv_add_inv_conj_ennreal
-/

end IsConjugateExponent

#print Real.isConjExponent_iff /-
theorem isConjExponent_iff {p q : ℝ} (h : 1 < p) : p.IsConjExponent q ↔ q = p / (p - 1) :=
  ⟨fun H => H.conj_eq, fun H => ⟨h, by field_simp [H, ne_of_gt (lt_trans zero_lt_one h)]⟩⟩
#align real.is_conjugate_exponent_iff Real.isConjExponent_iff
-/

#print Real.IsConjExponent.conjExponent /-
theorem Real.IsConjExponent.conjExponent {p : ℝ} (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff h).2 rfl
#align real.is_conjugate_exponent_conjugate_exponent Real.IsConjExponent.conjExponent
-/

#print Real.isConjExponent_one_div /-
theorem isConjExponent_one_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).IsConjExponent (1 / b) :=
  ⟨by rw [lt_div_iff ha, one_mul]; linarith, by simp_rw [one_div_one_div]; exact hab⟩
#align real.is_conjugate_exponent_one_div Real.isConjExponent_one_div
-/

end Real

