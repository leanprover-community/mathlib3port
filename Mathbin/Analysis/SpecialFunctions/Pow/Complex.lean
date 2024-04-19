/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Analysis.SpecialFunctions.Complex.Log

#align_import analysis.special_functions.pow.complex from "leanprover-community/mathlib"@"33c67ae661dd8988516ff7f247b0be3018cdd952"

/-! # Power function on `ℂ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/


open scoped Classical Real Topology Filter ComplexConjugate

open Filter Finset Set

namespace Complex

#print Complex.cpow /-
/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
#align complex.cpow Complex.cpow
-/

noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

#print Complex.cpow_eq_pow /-
@[simp]
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl
#align complex.cpow_eq_pow Complex.cpow_eq_pow
-/

#print Complex.cpow_def /-
theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl
#align complex.cpow_def Complex.cpow_def
-/

#print Complex.cpow_def_of_ne_zero /-
theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  if_neg hx
#align complex.cpow_def_of_ne_zero Complex.cpow_def_of_ne_zero
-/

#print Complex.cpow_zero /-
@[simp]
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]
#align complex.cpow_zero Complex.cpow_zero
-/

#print Complex.cpow_eq_zero_iff /-
@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by simp only [cpow_def];
  split_ifs <;> simp [*, exp_ne_zero]
#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iff
-/

#print Complex.zero_cpow /-
@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
#align complex.zero_cpow Complex.zero_cpow
-/

#print Complex.zero_cpow_eq_iff /-
theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 :=
  by
  constructor
  · intro hyp
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp
    by_cases x = 0
    · subst h; simp only [if_true, eq_self_iff_true] at hyp; right; exact ⟨rfl, hyp.symm⟩
    · rw [if_neg h] at hyp; left; exact ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _
#align complex.zero_cpow_eq_iff Complex.zero_cpow_eq_iff
-/

#print Complex.eq_zero_cpow_iff /-
theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]
#align complex.eq_zero_cpow_iff Complex.eq_zero_cpow_iff
-/

#print Complex.cpow_one /-
@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]
#align complex.cpow_one Complex.cpow_one
-/

#print Complex.one_cpow /-
@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def] <;> split_ifs <;> simp_all [one_ne_zero]
#align complex.one_cpow Complex.one_cpow
-/

#print Complex.cpow_add /-
theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole] <;>
    simp_all [NormedSpace.exp_add, mul_add]
#align complex.cpow_add Complex.cpow_add
-/

#print Complex.cpow_mul /-
theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
#align complex.cpow_mul Complex.cpow_mul
-/

#print Complex.cpow_neg /-
theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg] <;> split_ifs <;> simp [NormedSpace.exp_neg]
#align complex.cpow_neg Complex.cpow_neg
-/

#print Complex.cpow_sub /-
theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
#align complex.cpow_sub Complex.cpow_sub
-/

#print Complex.cpow_neg_one /-
theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1
#align complex.cpow_neg_one Complex.cpow_neg_one
-/

#print Complex.cpow_natCast /-
@[simp, norm_cast]
theorem cpow_natCast (x : ℂ) : ∀ n : ℕ, x ^ (n : ℂ) = x ^ n
  | 0 => by simp
  | n + 1 =>
    if hx : x = 0 then by
      simp only [hx, pow_succ', Complex.zero_cpow (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)),
        MulZeroClass.zero_mul]
    else by simp [cpow_add, hx, pow_add, cpow_nat_cast n]
#align complex.cpow_nat_cast Complex.cpow_natCast
-/

#print Complex.cpow_two /-
@[simp]
theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ 2 := by rw [← cpow_nat_cast];
  simp only [Nat.cast_bit0, Nat.cast_one]
#align complex.cpow_two Complex.cpow_two
-/

#print Complex.cpow_intCast /-
@[simp, norm_cast]
theorem cpow_intCast (x : ℂ) : ∀ n : ℤ, x ^ (n : ℂ) = x ^ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    rw [zpow_negSucc] <;>
      simp only [Int.negSucc_coe, Int.cast_neg, Complex.cpow_neg, inv_eq_one_div, Int.cast_natCast,
        cpow_nat_cast]
#align complex.cpow_int_cast Complex.cpow_intCast
-/

#print Complex.cpow_nat_inv_pow /-
theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
  by
  suffices im (log x * n⁻¹) ∈ Ioc (-π) π
    by
    rw [← cpow_nat_cast, ← cpow_mul _ this.1 this.2, inv_mul_cancel, cpow_one]
    exact_mod_cast hn
  rw [mul_comm, ← of_real_nat_cast, ← of_real_inv, of_real_mul_im, ← div_eq_inv_mul]
  rw [← pos_iff_ne_zero] at hn
  have hn' : 0 < (n : ℝ) := by assumption_mod_cast
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.2 hn
  constructor
  · rw [lt_div_iff hn']
    calc
      -π * n ≤ -π * 1 := mul_le_mul_of_nonpos_left hn1 (neg_nonpos.2 real.pi_pos.le)
      _ = -π := (mul_one _)
      _ < im (log x) := neg_pi_lt_log_im _
  · rw [div_le_iff hn']
    calc
      im (log x) ≤ π := log_im_le_pi _
      _ = π * 1 := (mul_one π).symm
      _ ≤ π * n := mul_le_mul_of_nonneg_left hn1 real.pi_pos.le
#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_pow
-/

#print Complex.mul_cpow_ofReal_nonneg /-
theorem mul_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r :=
  by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [of_real_zero, MulZeroClass.zero_mul, zero_cpow hr, MulZeroClass.zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [of_real_zero, MulZeroClass.mul_zero, zero_cpow hr, MulZeroClass.mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := of_real_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := of_real_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_of_real_mul ha' hb'', of_real_log ha,
    add_mul, NormedSpace.exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_ofReal_nonneg
-/

#print Complex.inv_cpow_eq_ite /-
theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ :=
  by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    RCLike.conj_inv, apply_ite conj, apply_ite NormedSpace.exp, apply_ite Inv.inv, map_zero,
    map_one, NormedSpace.exp_neg, inv_one, inv_zero, ← NormedSpace.exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
#align complex.inv_cpow_eq_ite Complex.inv_cpow_eq_ite
-/

#print Complex.inv_cpow /-
theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
#align complex.inv_cpow Complex.inv_cpow
-/

#print Complex.inv_cpow_eq_ite' /-
/-- `complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n :=
  by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  split_ifs
  · rfl
  · rw [inv_cpow _ _ h]
#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'
-/

#print Complex.conj_cpow_eq_ite /-
theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) :=
  by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← NormedSpace.exp_conj,
    map_mul, conj_conj, log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
#align complex.conj_cpow_eq_ite Complex.conj_cpow_eq_ite
-/

#print Complex.conj_cpow /-
theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
#align complex.conj_cpow Complex.conj_cpow
-/

#print Complex.cpow_conj /-
theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
#align complex.cpow_conj Complex.cpow_conj
-/

end Complex

section Tactics

/-!
## Tactic extensions for complex powers
-/


namespace NormNum

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, hb, Complex.cpow_natCast]
#align norm_num.cpow_pos NormNum.cpow_pos

theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
    a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_natCast]
#align norm_num.cpow_neg NormNum.cpow_neg

open Tactic

/-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let icα ← mk_instance_cache α
  let icβ ← mk_instance_cache β
  match match_sign b with
    | Sum.inl b => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      let cr ← c
      let (icα, c', hc) ← prove_inv icα c cr
      pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
    | Sum.inr ff => pure (one, expr.const zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow' norm_num.prove_rpow'

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))
#align norm_num.prove_cpow norm_num.prove_cpow

/-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_cpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
  | _ => tactic.failed
#align norm_num.eval_cpow norm_num.eval_cpow

end NormNum

end Tactics

