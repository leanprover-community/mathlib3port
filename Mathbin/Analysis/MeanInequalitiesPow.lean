/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne

! This file was ported from Lean 3 source module analysis.mean_inequalities_pow
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.SpecificFunctions
import Mathbin.Tactic.Positivity

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/


universe u v

open Finset

open Classical BigOperators Nnreal Ennreal

noncomputable section

variable {ι : Type u} (s : Finset ι)

namespace Real

theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : (∑ i in s, w i) = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
    (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n :=
  (convex_on_pow n).map_sum_le hw hw' hz
#align real.pow_arith_mean_le_arith_mean_pow Real.pow_arith_mean_le_arith_mean_pow

theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : (∑ i in s, w i) = 1) {n : ℕ} (hn : Even n) :
    (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n :=
  hn.convex_on_pow.map_sum_le hw hw' fun _ _ => trivial
#align real.pow_arith_mean_le_arith_mean_pow_of_even Real.pow_arith_mean_le_arith_mean_pow_of_even

theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : (∑ i in s, w i) = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
    (∑ i in s, w i * z i) ^ m ≤ ∑ i in s, w i * z i ^ m :=
  (convex_on_zpow m).map_sum_le hw hw' hz
#align real.zpow_arith_mean_le_arith_mean_zpow Real.zpow_arith_mean_le_arith_mean_zpow

theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : (∑ i in s, w i) = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, w i * z i ^ p :=
  (convex_on_rpow hp).map_sum_le hw hw' hz
#align real.rpow_arith_mean_le_arith_mean_rpow Real.rpow_arith_mean_le_arith_mean_rpow

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr sum_nonneg, ",", expr rpow_nonneg_of_nonneg, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr mul_nonneg, ",", expr rpow_nonneg_of_nonneg, ",", expr hw i hi, ",", expr hz i hi, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : (∑ i in s, w i) = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, w i * z i) ≤ (∑ i in s, w i * z i ^ p) ^ (1 / p) :=
  by
  have : 0 < p := by positivity
  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one]
  exact rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp
  all_goals
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr sum_nonneg, \",\", expr rpow_nonneg_of_nonneg, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
    intro i hi
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr mul_nonneg, \",\", expr rpow_nonneg_of_nonneg, \",\", expr hw i hi, \",\", expr hz i hi, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
#align real.arith_mean_le_rpow_mean Real.arith_mean_le_rpow_mean

end Real

namespace Nnreal

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ≥0) (hw' : (∑ i in s, w i) = 1) (n : ℕ) :
    (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n := by
  exact_mod_cast
    Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
      (by exact_mod_cast hw') (fun i _ => (z i).coe_nonneg) n
#align nnreal.pow_arith_mean_le_arith_mean_pow Nnreal.pow_arith_mean_le_arith_mean_pow

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0) (hw' : (∑ i in s, w i) = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, w i * z i ^ p := by
  exact_mod_cast
    Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
      (by exact_mod_cast hw') (fun i _ => (z i).coe_nonneg) hp
#align nnreal.rpow_arith_mean_le_arith_mean_rpow Nnreal.rpow_arith_mean_le_arith_mean_rpow

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
  by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] _ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]
#align nnreal.rpow_arith_mean_le_arith_mean2_rpow Nnreal.rpow_arith_mean_le_arith_mean2_rpow

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean (w z : ι → ℝ≥0) (hw' : (∑ i in s, w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, w i * z i) ≤ (∑ i in s, w i * z i ^ p) ^ (1 / p) := by
  exact_mod_cast
    Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg) (by exact_mod_cast hw')
      (fun i _ => (z i).coe_nonneg) hp
#align nnreal.arith_mean_le_rpow_mean Nnreal.arith_mean_le_rpow_mean

end Nnreal

namespace Nnreal

private theorem add_rpow_le_one_of_add_le_one {p : ℝ} (a b : ℝ≥0) (hab : a + b ≤ 1) (hp1 : 1 ≤ p) :
    a ^ p + b ^ p ≤ 1 :=
  by
  have h_le_one : ∀ x : ℝ≥0, x ≤ 1 → x ^ p ≤ x := fun x hx => rpow_le_self_of_le_one hx hp1
  have ha : a ≤ 1 := (self_le_add_right a b).trans hab
  have hb : b ≤ 1 := (self_le_add_left b a).trans hab
  exact (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab
#align nnreal.add_rpow_le_one_of_add_le_one nnreal.add_rpow_le_one_of_add_le_one

theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p :=
  by
  have hp_pos : 0 < p := by positivity
  by_cases h_zero : a + b = 0
  · simp [add_eq_zero_iff.mp h_zero, hp_pos.ne']
  have h_nonzero : ¬(a = 0 ∧ b = 0) := by rwa [add_eq_zero_iff] at h_zero
  have h_add : a / (a + b) + b / (a + b) = 1 := by rw [div_add_div_same, div_self h_zero]
  have h := add_rpow_le_one_of_add_le_one (a / (a + b)) (b / (a + b)) h_add.le hp1
  rw [div_rpow a (a + b), div_rpow b (a + b)] at h
  have hab_0 : (a + b) ^ p ≠ 0 := by simp [hp_pos, h_nonzero]
  have hab_0' : 0 < (a + b) ^ p := zero_lt_iff.mpr hab_0
  have h_mul : (a + b) ^ p * (a ^ p / (a + b) ^ p + b ^ p / (a + b) ^ p) ≤ (a + b) ^ p :=
    by
    nth_rw 4 [← mul_one ((a + b) ^ p)]
    exact (mul_le_mul_left hab_0').mpr h
  rwa [div_eq_mul_inv, div_eq_mul_inv, mul_add, mul_comm (a ^ p), mul_comm (b ^ p), ← mul_assoc, ←
    mul_assoc, mul_inv_cancel hab_0, one_mul, one_mul] at h_mul
#align nnreal.add_rpow_le_rpow_add Nnreal.add_rpow_le_rpow_add

theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b :=
  by
  rw [← @Nnreal.le_rpow_one_div_iff _ _ (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [one_div_one_div]
  exact add_rpow_le_rpow_add _ _ hp1
#align nnreal.rpow_add_rpow_le_add Nnreal.rpow_add_rpow_le_add

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) :=
  by
  have h_rpow : ∀ a : ℝ≥0, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← Nnreal.rpow_mul, div_eq_inv_mul, ← mul_assoc, _root_.mul_inv_cancel hp_pos.ne.symm,
      one_mul]
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p :=
    by
    refine' rpow_add_rpow_le_add (a ^ p) (b ^ p) _
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, Nnreal.le_rpow_one_div_iff hp_pos, ← Nnreal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add
#align nnreal.rpow_add_rpow_le Nnreal.rpow_add_rpow_le

theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p :=
  by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · simp
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one] at h
  repeat' rw [Nnreal.rpow_one] at h
  exact (Nnreal.le_rpow_one_div_iff hp_pos).mp h
#align nnreal.rpow_add_le_add_rpow Nnreal.rpow_add_le_add_rpow

end Nnreal

namespace Ennreal

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0∞`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ≥0∞) (hw' : (∑ i in s, w i) = 1) {p : ℝ}
    (hp : 1 ≤ p) : (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, w i * z i ^ p :=
  by
  have hp_pos : 0 < p
  positivity
  have hp_nonneg : 0 ≤ p
  positivity
  have hp_not_nonpos : ¬p ≤ 0 := by simp [hp_pos]
  have hp_not_neg : ¬p < 0 := by simp [hp_nonneg]
  have h_top_iff_rpow_top : ∀ (i : ι) (hi : i ∈ s), w i * z i = ⊤ ↔ w i * z i ^ p = ⊤ := by
    simp [hp_pos, hp_nonneg, hp_not_nonpos, hp_not_neg]
  refine' le_of_top_imp_top_of_to_nnreal_le _ _
  · -- first, prove `(∑ i in s, w i * z i) ^ p = ⊤ → ∑ i in s, (w i * z i ^ p) = ⊤`
    rw [rpow_eq_top_iff, sum_eq_top_iff, sum_eq_top_iff]
    intro h
    simp only [and_false_iff, hp_not_neg, false_or_iff] at h
    rcases h.left with ⟨a, H, ha⟩
    use a, H
    rwa [← h_top_iff_rpow_top a H]
  · -- second, suppose both `(∑ i in s, w i * z i) ^ p ≠ ⊤` and `∑ i in s, (w i * z i ^ p) ≠ ⊤`,
    -- and prove `((∑ i in s, w i * z i) ^ p).to_nnreal ≤ (∑ i in s, (w i * z i ^ p)).to_nnreal`,
    -- by using `nnreal.rpow_arith_mean_le_arith_mean_rpow`.
    intro h_top_rpow_sum _
    -- show hypotheses needed to put the `.to_nnreal` inside the sums.
    have h_top : ∀ a : ι, a ∈ s → w a * z a ≠ ⊤ :=
      haveI h_top_sum : (∑ i : ι in s, w i * z i) ≠ ⊤ :=
        by
        intro h
        rw [h, top_rpow_of_pos hp_pos] at h_top_rpow_sum
        exact h_top_rpow_sum rfl
      fun a ha => (lt_top_of_sum_ne_top h_top_sum ha).Ne
    have h_top_rpow : ∀ a : ι, a ∈ s → w a * z a ^ p ≠ ⊤ :=
      by
      intro i hi
      specialize h_top i hi
      rwa [Ne.def, ← h_top_iff_rpow_top i hi]
    -- put the `.to_nnreal` inside the sums.
    simp_rw [to_nnreal_sum h_top_rpow, ← to_nnreal_rpow, to_nnreal_sum h_top, to_nnreal_mul, ←
      to_nnreal_rpow]
    -- use corresponding nnreal result
    refine'
      Nnreal.rpow_arith_mean_le_arith_mean_rpow s (fun i => (w i).toNnreal)
        (fun i => (z i).toNnreal) _ hp
    -- verify the hypothesis `∑ i in s, (w i).to_nnreal = 1`, using `∑ i in s, w i = 1` .
    have h_sum_nnreal : (∑ i in s, w i) = ↑(∑ i in s, (w i).toNnreal) :=
      by
      rw [coe_finset_sum]
      refine' sum_congr rfl fun i hi => (coe_to_nnreal _).symm
      refine' (lt_top_of_sum_ne_top _ hi).Ne
      exact hw'.symm ▸ Ennreal.one_ne_top
    rwa [← coe_eq_coe, ← h_sum_nnreal]
#align ennreal.rpow_arith_mean_le_arith_mean_rpow Ennreal.rpow_arith_mean_le_arith_mean_rpow

/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and real
exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow (w₁ w₂ z₁ z₂ : ℝ≥0∞) (hw' : w₁ + w₂ = 1) {p : ℝ}
    (hp : 1 ≤ p) : (w₁ * z₁ + w₂ * z₂) ^ p ≤ w₁ * z₁ ^ p + w₂ * z₂ ^ p :=
  by
  have h := rpow_arith_mean_le_arith_mean_rpow univ ![w₁, w₂] ![z₁, z₂] _ hp
  · simpa [Fin.sum_univ_succ] using h
  · simp [hw', Fin.sum_univ_succ]
#align ennreal.rpow_arith_mean_le_arith_mean2_rpow Ennreal.rpow_arith_mean_le_arith_mean2_rpow

end Ennreal

namespace Ennreal

theorem add_rpow_le_rpow_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) : a ^ p + b ^ p ≤ (a + b) ^ p :=
  by
  have hp_pos : 0 < p := by positivity
  by_cases h_top : a + b = ⊤
  · rw [← @Ennreal.rpow_eq_top_iff_of_pos (a + b) p hp_pos] at h_top
    rw [h_top]
    exact le_top
  obtain ⟨ha_top, hb_top⟩ := add_ne_top.mp h_top
  lift a to ℝ≥0 using ha_top
  lift b to ℝ≥0 using hb_top
  simpa [← Ennreal.coe_rpow_of_nonneg _ hp_pos.le] using
    Ennreal.coe_le_coe.2 (Nnreal.add_rpow_le_rpow_add a b hp1)
#align ennreal.add_rpow_le_rpow_add Ennreal.add_rpow_le_rpow_add

theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) :
    (a ^ p + b ^ p) ^ (1 / p) ≤ a + b :=
  by
  rw [← @Ennreal.le_rpow_one_div_iff _ _ (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
  rw [one_div_one_div]
  exact add_rpow_le_rpow_add _ _ hp1
#align ennreal.rpow_add_rpow_le_add Ennreal.rpow_add_rpow_le_add

theorem rpow_add_rpow_le {p q : ℝ} (a b : ℝ≥0∞) (hp_pos : 0 < p) (hpq : p ≤ q) :
    (a ^ q + b ^ q) ^ (1 / q) ≤ (a ^ p + b ^ p) ^ (1 / p) :=
  by
  have h_rpow : ∀ a : ℝ≥0∞, a ^ q = (a ^ p) ^ (q / p) := fun a => by
    rw [← Ennreal.rpow_mul, _root_.mul_div_cancel' _ hp_pos.ne']
  have h_rpow_add_rpow_le_add :
    ((a ^ p) ^ (q / p) + (b ^ p) ^ (q / p)) ^ (1 / (q / p)) ≤ a ^ p + b ^ p :=
    by
    refine' rpow_add_rpow_le_add (a ^ p) (b ^ p) _
    rwa [one_le_div hp_pos]
  rw [h_rpow a, h_rpow b, Ennreal.le_rpow_one_div_iff hp_pos, ← Ennreal.rpow_mul, mul_comm,
    mul_one_div]
  rwa [one_div_div] at h_rpow_add_rpow_le_add
#align ennreal.rpow_add_rpow_le Ennreal.rpow_add_rpow_le

theorem rpow_add_le_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a + b) ^ p ≤ a ^ p + b ^ p :=
  by
  rcases hp.eq_or_lt with (rfl | hp_pos)
  · suffices (1 : ℝ≥0∞) ≤ 1 + 1 by simpa using this
    norm_cast
    norm_num
  have h := rpow_add_rpow_le a b hp_pos hp1
  rw [one_div_one] at h
  repeat' rw [Ennreal.rpow_one] at h
  exact (Ennreal.le_rpow_one_div_iff hp_pos).mp h
#align ennreal.rpow_add_le_add_rpow Ennreal.rpow_add_le_add_rpow

end Ennreal

