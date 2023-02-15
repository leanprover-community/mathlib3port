/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Log

/-!
# Power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` and `y` are complex numbers,
* or `x` and `y` are real numbers,
* or `x` is a nonnegative real number and `y` is a real number;
* or `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/


noncomputable section

open Classical Real Topology Nnreal Ennreal Filter BigOperators ComplexConjugate

open Filter Finset Set

namespace Complex

/-- The complex power function `x^y`, given by `x^y = exp(y log x)` (where `log` is the principal
determination of the logarithm), unless `x = 0` where one sets `0^0 = 1` and `0^y = 0` for
`y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
#align complex.cpow Complex.cpow

noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

@[simp]
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl
#align complex.cpow_eq_pow Complex.cpow_eq_pow

theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl
#align complex.cpow_def Complex.cpow_def

theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  if_neg hx
#align complex.cpow_def_of_ne_zero Complex.cpow_def_of_ne_zero

@[simp]
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]
#align complex.cpow_zero Complex.cpow_zero

@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]
#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iff

@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
#align complex.zero_cpow Complex.zero_cpow

theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 :=
  by
  constructor
  · intro hyp
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp
    by_cases x = 0
    · subst h
      simp only [if_true, eq_self_iff_true] at hyp
      right
      exact ⟨rfl, hyp.symm⟩
    · rw [if_neg h] at hyp
      left
      exact ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _
#align complex.zero_cpow_eq_iff Complex.zero_cpow_eq_iff

theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]
#align complex.eq_zero_cpow_iff Complex.eq_zero_cpow_iff

@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]
#align complex.cpow_one Complex.cpow_one

@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def] <;> split_ifs <;> simp_all [one_ne_zero]
#align complex.one_cpow Complex.one_cpow

theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole] <;> simp_all [exp_add, mul_add]
#align complex.cpow_add Complex.cpow_add

theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
#align complex.cpow_mul Complex.cpow_mul

theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg] <;> split_ifs <;> simp [exp_neg]
#align complex.cpow_neg Complex.cpow_neg

theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
#align complex.cpow_sub Complex.cpow_sub

theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1
#align complex.cpow_neg_one Complex.cpow_neg_one

@[simp, norm_cast]
theorem cpow_nat_cast (x : ℂ) : ∀ n : ℕ, x ^ (n : ℂ) = x ^ n
  | 0 => by simp
  | n + 1 =>
    if hx : x = 0 then by
      simp only [hx, pow_succ, Complex.zero_cpow (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)),
        zero_mul]
    else by simp [cpow_add, hx, pow_add, cpow_nat_cast n]
#align complex.cpow_nat_cast Complex.cpow_nat_cast

@[simp]
theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ 2 :=
  by
  rw [← cpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align complex.cpow_two Complex.cpow_two

@[simp, norm_cast]
theorem cpow_int_cast (x : ℂ) : ∀ n : ℤ, x ^ (n : ℂ) = x ^ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    rw [zpow_negSucc] <;>
      simp only [Int.negSucc_coe, Int.cast_neg, Complex.cpow_neg, inv_eq_one_div, Int.cast_ofNat,
        cpow_nat_cast]
#align complex.cpow_int_cast Complex.cpow_int_cast

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
      _ = -π := mul_one _
      _ < im (log x) := neg_pi_lt_log_im _
      
  · rw [div_le_iff hn']
    calc
      im (log x) ≤ π := log_im_le_pi _
      _ = π * 1 := (mul_one π).symm
      _ ≤ π * n := mul_le_mul_of_nonneg_left hn1 real.pi_pos.le
      
#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_pow

theorem mul_cpow_of_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r :=
  by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [of_real_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [of_real_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := of_real_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := of_real_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_of_real_mul ha' hb'', of_real_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_of_real_nonneg

end Complex

section limUnder

open Complex

variable {α : Type _}

theorem zero_cpow_eq_nhds {b : ℂ} (hb : b ≠ 0) : (fun x : ℂ => (0 : ℂ) ^ x) =ᶠ[𝓝 b] 0 :=
  by
  suffices : ∀ᶠ x : ℂ in 𝓝 b, x ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [zero_cpow hx, Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb
#align zero_cpow_eq_nhds zero_cpow_eq_nhds

theorem cpow_eq_nhds {a b : ℂ} (ha : a ≠ 0) : (fun x => x ^ b) =ᶠ[𝓝 a] fun x => exp (log x * b) :=
  by
  suffices : ∀ᶠ x : ℂ in 𝓝 a, x ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha
#align cpow_eq_nhds cpow_eq_nhds

theorem cpow_eq_nhds' {p : ℂ × ℂ} (hp_fst : p.fst ≠ 0) :
    (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
  by
  suffices : ∀ᶠ x : ℂ × ℂ in 𝓝 p, x.1 ≠ 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  refine' IsOpen.eventually_mem _ hp_fst
  change IsOpen ({ x : ℂ × ℂ | x.1 = 0 }ᶜ)
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const
#align cpow_eq_nhds' cpow_eq_nhds'

-- Continuity of `λ x, a ^ x`: union of these two lemmas is optimal.
theorem continuousAt_const_cpow {a b : ℂ} (ha : a ≠ 0) : ContinuousAt (fun x => a ^ x) b :=
  by
  have cpow_eq : (fun x : ℂ => a ^ x) = fun x => exp (log a * x) :=
    by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuous_at.comp (ContinuousAt.mul continuousAt_const continuousAt_id)
#align continuous_at_const_cpow continuousAt_const_cpow

theorem continuousAt_const_cpow' {a b : ℂ} (h : b ≠ 0) : ContinuousAt (fun x => a ^ x) b :=
  by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha
#align continuous_at_const_cpow' continuousAt_const_cpow'

/-- The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong to the interval
`(-∞, 0]` on the real line. See also `complex.continuous_at_cpow_zero_of_re_pos` for a version that
works for `z = 0` but assumes `0 < re w`. -/
theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : 0 < p.fst.re ∨ p.fst.im ≠ 0) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p :=
  by
  have hp_fst_ne_zero : p.fst ≠ 0 := by
    intro h
    cases hp_fst <;>
      · rw [h] at hp_fst
        simpa using hp_fst
  rw [continuousAt_congr (cpow_eq_nhds' hp_fst_ne_zero)]
  refine' continuous_exp.continuous_at.comp _
  refine'
    ContinuousAt.mul (ContinuousAt.comp _ continuous_fst.continuous_at) continuous_snd.continuous_at
  exact continuousAt_clog hp_fst
#align continuous_at_cpow continuousAt_cpow

theorem continuousAt_cpow_const {a b : ℂ} (ha : 0 < a.re ∨ a.im ≠ 0) :
    ContinuousAt (fun x => cpow x b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.Prod continuousAt_const)
#align continuous_at_cpow_const continuousAt_cpow_const

theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : 0 < a.re ∨ a.im ≠ 0) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).Tendsto.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.cpow Filter.Tendsto.cpow

theorem Filter.Tendsto.const_cpow {l : Filter α} {f : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 b))
    (h : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => a ^ f x) l (𝓝 (a ^ b)) :=
  by
  cases h
  · exact (continuousAt_const_cpow h).Tendsto.comp hf
  · exact (continuousAt_const_cpow' h).Tendsto.comp hf
#align filter.tendsto.const_cpow Filter.Tendsto.const_cpow

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a)
    (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0
#align continuous_within_at.cpow ContinuousWithinAt.cpow

theorem ContinuousWithinAt.const_cpow {b : ℂ} (hf : ContinuousWithinAt f s a)
    (h : b ≠ 0 ∨ f a ≠ 0) : ContinuousWithinAt (fun x => b ^ f x) s a :=
  hf.const_cpow h
#align continuous_within_at.const_cpow ContinuousWithinAt.const_cpow

theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0
#align continuous_at.cpow ContinuousAt.cpow

theorem ContinuousAt.const_cpow {b : ℂ} (hf : ContinuousAt f a) (h : b ≠ 0 ∨ f a ≠ 0) :
    ContinuousAt (fun x => b ^ f x) a :=
  hf.const_cpow h
#align continuous_at.const_cpow ContinuousAt.const_cpow

theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)
#align continuous_on.cpow ContinuousOn.cpow

theorem ContinuousOn.const_cpow {b : ℂ} (hf : ContinuousOn f s) (h : b ≠ 0 ∨ ∀ a ∈ s, f a ≠ 0) :
    ContinuousOn (fun x => b ^ f x) s := fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)
#align continuous_on.const_cpow ContinuousOn.const_cpow

theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, 0 < (f a).re ∨ (f a).im ≠ 0) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.ContinuousAt.cpow hg.ContinuousAt (h0 a)
#align continuous.cpow Continuous.cpow

theorem Continuous.const_cpow {b : ℂ} (hf : Continuous f) (h : b ≠ 0 ∨ ∀ a, f a ≠ 0) :
    Continuous fun x => b ^ f x :=
  continuous_iff_continuousAt.2 fun a => hf.ContinuousAt.const_cpow <| h.imp id fun h => h a
#align continuous.const_cpow Continuous.const_cpow

theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → 0 < (f a).re ∨ (f a).im ≠ 0) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h
#align continuous_on.cpow_const ContinuousOn.cpow_const

end limUnder

namespace Real

/-- The real power function `x^y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp(y log x)`. For `x = 0`, one sets `0^0=1` and `0^y=0` for `y ≠ 0`.
For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (πy)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
#align real.rpow Real.rpow

noncomputable instance : Pow ℝ ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y :=
  rfl
#align real.rpow_eq_pow Real.rpow_eq_pow

theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re :=
  rfl
#align real.rpow_def Real.rpow_def

theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def] <;> split_ifs <;>
    simp_all [(Complex.of_real_log hx).symm, -Complex.of_real_mul, -IsROrC.of_real_mul,
      (Complex.of_real_mul _ _).symm, Complex.exp_of_real_re]
#align real.rpow_def_of_nonneg Real.rpow_def_of_nonneg

theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]
#align real.rpow_def_of_pos Real.rpow_def_of_pos

theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]
#align real.exp_mul Real.exp_mul

@[simp]
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]
#align real.exp_one_rpow Real.exp_one_rpow

theorem rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]
#align real.rpow_eq_zero_iff_of_nonneg Real.rpow_eq_zero_iff_of_nonneg

open Real

theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) :=
  by
  rw [rpow_def, Complex.cpow_def, if_neg]
  have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.i :=
    by
    simp only [Complex.log, abs_of_neg hx, Complex.arg_of_real_of_neg hx, Complex.abs_of_real,
      Complex.of_real_mul]
    ring
  · rw [this, Complex.exp_add_mul_i, ← Complex.of_real_exp, ← Complex.of_real_cos, ←
      Complex.of_real_sin, mul_add, ← Complex.of_real_mul, ← mul_assoc, ← Complex.of_real_mul,
      Complex.add_re, Complex.of_real_re, Complex.mul_re, Complex.i_re, Complex.of_real_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.of_real_eq_zero]
    exact ne_of_lt hx
#align real.rpow_def_of_neg Real.rpow_def_of_neg

theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs <;> simp [rpow_def, *] <;> exact rpow_def_of_neg (lt_of_le_of_ne hx h) _
#align real.rpow_def_of_nonpos Real.rpow_def_of_nonpos

theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx] <;> apply exp_pos
#align real.rpow_pos_of_pos Real.rpow_pos_of_pos

@[simp]
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]
#align real.rpow_zero Real.rpow_zero

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
#align real.zero_rpow Real.zero_rpow

theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 :=
  by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.of_real_zero] at hyp
    by_cases x = 0
    · subst h
      simp only [Complex.one_re, Complex.of_real_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (complex.of_real_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _
#align real.zero_rpow_eq_iff Real.zero_rpow_eq_iff

theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]
#align real.eq_zero_rpow_iff Real.eq_zero_rpow_iff

@[simp]
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
#align real.rpow_one Real.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]
#align real.one_rpow Real.one_rpow

theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_le_one Real.zero_rpow_le_one

theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_nonneg Real.zero_rpow_nonneg

theorem rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx] <;> split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]
#align real.rpow_nonneg_of_nonneg Real.rpow_nonneg_of_nonneg

theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y :=
  by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg_of_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]
#align real.abs_rpow_of_nonneg Real.abs_rpow_of_nonneg

theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y :=
  by
  cases' le_or_lt 0 x with hx hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
#align real.abs_rpow_le_abs_rpow Real.abs_rpow_le_abs_rpow

theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) :=
  by
  refine' (abs_rpow_le_abs_rpow x y).trans _
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]
#align real.abs_rpow_le_exp_log_mul Real.abs_rpow_le_exp_log_mul

theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y :=
  by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg
#align real.norm_rpow_of_nonneg Real.norm_rpow_of_nonneg

end Real

namespace Complex

theorem of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, of_real_eq_zero] <;> split_ifs <;>
    simp [Complex.of_real_log hx]
#align complex.of_real_cpow Complex.of_real_cpow

theorem of_real_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * i * y) :=
  by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := of_real_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, abs.map_neg, arg_of_real_of_neg hlt, ← of_real_neg,
    arg_of_real_of_nonneg (neg_nonneg.2 hx), of_real_zero, zero_mul, add_zero]
#align complex.of_real_cpow_of_nonpos Complex.of_real_cpow_of_nonpos

theorem abs_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, abs_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (abs.pos hz)]
#align complex.abs_cpow_of_ne_zero Complex.abs_cpow_of_ne_zero

theorem abs_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) :=
  by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact abs_cpow_of_ne_zero hz w, rw [map_zero]]
  cases' eq_or_ne w.re 0 with hw hw
  · simp [hw, h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, map_zero]
    exact ne_of_apply_ne re hw
#align complex.abs_cpow_of_imp Complex.abs_cpow_of_imp

theorem abs_cpow_le (z w : ℂ) : abs (z ^ w) ≤ abs z ^ w.re / Real.exp (arg z * im w) :=
  by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact (abs_cpow_of_ne_zero hz w).le, rw [map_zero]]
  rcases eq_or_ne w 0 with (rfl | hw); · simp
  rw [zero_cpow hw, map_zero]
  exact div_nonneg (Real.rpow_nonneg_of_nonneg le_rfl _) (Real.exp_pos _).le
#align complex.abs_cpow_le Complex.abs_cpow_le

section

variable {α : Type _} {l : Filter α} {f g : α → ℂ}

open Asymptotics

theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun x => (1 : ℝ) :=
  by
  rcases hl with ⟨b, hb⟩
  refine' Real.isTheta_exp_comp_one.2 ⟨π * b, _⟩
  rw [eventually_map] at hb⊢
  refine' hb.mono fun x hx => _
  erw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) real.pi_pos.le
#align complex.is_Theta_exp_arg_mul_im Complex.isTheta_exp_arg_mul_im

theorem isO_cpow_rpow (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => abs (f x) ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l] fun x => abs (f x) ^ (g x).re / Real.exp (arg (f x) * im (g x)) :=
      isO_of_le _ fun x => (abs_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] fun x => abs (f x) ^ (g x).re / (1 : ℝ) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl)
    _ =ᶠ[l] fun x => abs (f x) ^ (g x).re := by simp only [of_real_one, div_one]
    
#align complex.is_O_cpow_rpow Complex.isO_cpow_rpow

theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|)
    (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => abs (f x) ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l] fun x => abs (f x) ^ (g x).re / Real.exp (arg (f x) * im (g x)) :=
      isTheta_of_norm_eventually_eq' <| hl.mono fun x => abs_cpow_of_imp
    _ =Θ[l] fun x => abs (f x) ^ (g x).re / (1 : ℝ) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] fun x => abs (f x) ^ (g x).re := by simp only [of_real_one, div_one]
    
#align complex.is_Theta_cpow_rpow Complex.isTheta_cpow_rpow

theorem isTheta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
    (fun x => f x ^ b) =Θ[l] fun x => abs (f x) ^ b.re :=
  isTheta_cpow_rpow isBoundedUnder_const <| by
    simpa only [eventually_imp_distrib_right, Ne.def, ← not_frequently, not_imp_not, Imp.swap] using
      hl
#align complex.is_Theta_cpow_const_rpow Complex.isTheta_cpow_const_rpow

end

@[simp]
theorem abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = x.abs ^ y := by
  rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy), skip] <;>
    simp [*, abs_cpow_of_ne_zero]
#align complex.abs_cpow_real Complex.abs_cpow_real

@[simp]
theorem abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = x.abs ^ (n⁻¹ : ℝ) := by
  rw [← abs_cpow_real] <;> simp [-abs_cpow_real]
#align complex.abs_cpow_inv_nat Complex.abs_cpow_inv_nat

theorem abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : abs (x ^ y) = x ^ y.re := by
  rw [abs_cpow_of_ne_zero (of_real_ne_zero.mpr hx.ne'), arg_of_real_of_nonneg hx.le, zero_mul,
    Real.exp_zero, div_one, abs_of_nonneg hx.le]
#align complex.abs_cpow_eq_rpow_re_of_pos Complex.abs_cpow_eq_rpow_re_of_pos

theorem abs_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    abs (x ^ y) = x ^ re y := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rw [of_real_zero, zero_cpow, map_zero, Real.zero_rpow hy]
    exact ne_of_apply_ne re hy
  · exact abs_cpow_eq_rpow_re_of_pos hlt y
#align complex.abs_cpow_eq_rpow_re_of_nonneg Complex.abs_cpow_eq_rpow_re_of_nonneg

theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ :=
  by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    IsROrC.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
#align complex.inv_cpow_eq_ite Complex.inv_cpow_eq_ite

theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
#align complex.inv_cpow Complex.inv_cpow

/-- `complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n :=
  by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  split_ifs
  · rfl
  · rw [inv_cpow _ _ h]
#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'

theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) :=
  by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
#align complex.conj_cpow_eq_ite Complex.conj_cpow_eq_ite

theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
#align complex.conj_cpow Complex.conj_cpow

theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
#align complex.cpow_conj Complex.cpow_conj

end Complex

namespace Real

variable {x y z : ℝ}

theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]
#align real.rpow_add Real.rpow_add

theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add Pos _ _
#align real.rpow_add' Real.rpow_add'

theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)
#align real.rpow_add_of_nonneg Real.rpow_add_of_nonneg

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right hand side is `1` while the left hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) :=
  by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 :=
          mul_le_mul (zero_rpow_le_one y) (zero_rpow_le_one z) (zero_rpow_nonneg z) zero_le_one
        _ = 1 := by simp
        
    · simp [rpow_add', ← H, h]
  · simp [rpow_add Pos]
#align real.le_rpow_add Real.le_rpow_add

theorem rpow_sum_of_pos {ι : Type _} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  @AddMonoidHom.map_sum ℝ ι (Additive ℝ) _ _ ⟨fun x : ℝ => (a ^ x : ℝ), rpow_zero a, rpow_add ha⟩ f
    s
#align real.rpow_sum_of_pos Real.rpow_sum_of_pos

theorem rpow_sum_of_nonneg {ι : Type _} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  by
  induction' s using Finset.cons_induction with i s hi ihs
  · rw [sum_empty, Finset.prod_empty, rpow_zero]
  · rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]
#align real.rpow_sum_of_nonneg Real.rpow_sum_of_nonneg

theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.of_real_inj, Complex.of_real_cpow (rpow_nonneg_of_nonneg hx _),
      Complex.of_real_cpow hx, Complex.of_real_mul, Complex.cpow_mul, Complex.of_real_cpow hx] <;>
    simp only [(Complex.of_real_mul _ _).symm, (Complex.of_real_log hx).symm, Complex.of_real_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]
#align real.rpow_mul Real.rpow_mul

theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx] <;> split_ifs <;> simp_all [exp_neg]
#align real.rpow_neg Real.rpow_neg

theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]
#align real.rpow_sub Real.rpow_sub

theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  by
  simp only [sub_eq_add_neg] at h⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]
#align real.rpow_sub' Real.rpow_sub'

theorem rpow_add_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  rw [rpow_def, Complex.of_real_add, Complex.cpow_add _ _ (complex.of_real_ne_zero.mpr hx),
    Complex.of_real_int_cast, Complex.cpow_int_cast, ← Complex.of_real_zpow, mul_comm,
    Complex.of_real_mul_re, ← rpow_def, mul_comm]
#align real.rpow_add_int Real.rpow_add_int

theorem rpow_add_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  simpa using rpow_add_int hx y n
#align real.rpow_add_nat Real.rpow_add_nat

theorem rpow_sub_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_add_int hx y (-n)
#align real.rpow_sub_int Real.rpow_sub_int

theorem rpow_sub_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  simpa using rpow_sub_int hx y n
#align real.rpow_sub_nat Real.rpow_sub_nat

theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_nat hx y 1
#align real.rpow_add_one Real.rpow_add_one

theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_nat hx y 1
#align real.rpow_sub_one Real.rpow_sub_one

@[simp, norm_cast]
theorem rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.of_real_zpow, Complex.cpow_int_cast, Complex.of_real_int_cast,
    Complex.of_real_re]
#align real.rpow_int_cast Real.rpow_int_cast

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by simpa using rpow_int_cast x n
#align real.rpow_nat_cast Real.rpow_nat_cast

@[simp]
theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align real.rpow_two Real.rpow_two

theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ :=
  by
  suffices H : x ^ ((-1 : ℤ) : ℝ) = x⁻¹; · rwa [Int.cast_neg, Int.cast_one] at H
  simp only [rpow_int_cast, zpow_one, zpow_neg]
#align real.rpow_neg_one Real.rpow_neg_one

theorem mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z :=
  by
  iterate 3 rw [Real.rpow_def_of_nonneg]; split_ifs <;> simp_all
  · have hx : 0 < x := by
      cases' lt_or_eq_of_le h with h₂ h₂
      · exact h₂
      exfalso
      apply h_2
      exact Eq.symm h₂
    have hy : 0 < y := by
      cases' lt_or_eq_of_le h₁ with h₂ h₂
      · exact h₂
      exfalso
      apply h_3
      exact Eq.symm h₂
    rw [log_mul (ne_of_gt hx) (ne_of_gt hy), add_mul, exp_add]
  · exact h₁
  · exact h
  · exact mul_nonneg h h₁
#align real.mul_rpow Real.mul_rpow

theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  simp only [← rpow_neg_one, ← rpow_mul hx, mul_comm]
#align real.inv_rpow Real.inv_rpow

theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]
#align real.div_rpow Real.div_rpow

theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x :=
  by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
#align real.log_rpow Real.log_rpow

theorem rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z :=
  by
  rw [le_iff_eq_or_lt] at hx; cases hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
  exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
#align real.rpow_lt_rpow Real.rpow_lt_rpow

theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')
#align real.rpow_le_rpow Real.rpow_le_rpow

theorem rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow hy h (le_of_lt hz), fun h => rpow_lt_rpow hx h hz⟩
#align real.rpow_lt_rpow_iff Real.rpow_lt_rpow_iff

theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff hy hx hz
#align real.rpow_le_rpow_iff Real.rpow_le_rpow_iff

theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_le_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [le_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.le_rpow_inv_iff_of_neg Real.le_rpow_inv_iff_of_neg

theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_lt_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [lt_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.lt_rpow_inv_iff_of_neg Real.lt_rpow_inv_iff_of_neg

theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  by
  convert lt_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _) hz <;>
    simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_lt_iff_of_neg Real.rpow_inv_lt_iff_of_neg

theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  by
  convert le_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _) hz <;>
    simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_le_iff_of_neg Real.rpow_inv_le_iff_of_neg

theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z :=
  by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)
#align real.rpow_lt_rpow_of_exponent_lt Real.rpow_lt_rpow_of_exponent_lt

theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z :=
  by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx)
#align real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_le

@[simp]
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z :=
  by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_right (log_pos hx)]
#align real.rpow_le_rpow_left_iff Real.rpow_le_rpow_left_iff

@[simp]
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_le, rpow_le_rpow_left_iff hx, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff Real.rpow_lt_rpow_left_iff

theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z :=
  by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)
#align real.rpow_lt_rpow_of_exponent_gt Real.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z :=
  by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)
#align real.rpow_le_rpow_of_exponent_ge Real.rpow_le_rpow_of_exponent_ge

@[simp]
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y ≤ x ^ z ↔ z ≤ y :=
  by
  rw [← log_le_log (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]
#align real.rpow_le_rpow_left_iff_of_base_lt_one Real.rpow_le_rpow_left_iff_of_base_lt_one

@[simp]
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y < x ^ z ↔ z < y :=
  by rw [lt_iff_not_le, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff_of_base_lt_one Real.rpow_lt_rpow_left_iff_of_base_lt_one

theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz
#align real.rpow_lt_one Real.rpow_lt_one

theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  by
  rw [← one_rpow z]
  exact rpow_le_rpow hx1 hx2 hz
#align real.rpow_le_one Real.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  by
  convert rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm
#align real.rpow_lt_one_of_one_lt_of_neg Real.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  by
  convert rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm
#align real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_one_of_one_le_of_nonpos

theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz
#align real.one_lt_rpow Real.one_lt_rpow

theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z :=
  by
  rw [← one_rpow z]
  exact rpow_le_rpow zero_le_one hx hz
#align real.one_le_rpow Real.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z :=
  by
  convert rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_lt_rpow_of_pos_of_lt_one_of_neg Real.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_le_rpow_of_pos_of_le_one_of_nonpos Real.one_le_rpow_of_pos_of_le_one_of_nonpos

theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx, log_neg_iff hx]
#align real.rpow_lt_one_iff_of_pos Real.rpow_lt_one_iff_of_pos

theorem rpow_lt_one_iff (hx : 0 ≤ x) : x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]
#align real.rpow_lt_one_iff Real.rpow_lt_one_iff

theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx, log_neg_iff hx]
#align real.one_lt_rpow_iff_of_pos Real.one_lt_rpow_iff_of_pos

theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, (zero_lt_one' ℝ).not_lt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]
#align real.one_lt_rpow_iff Real.one_lt_rpow_iff

theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_lt_of_le hz with (rfl | hz')
    · exact (rpow_zero 0).symm ▸ rpow_le_one hx0 hx1 hyz
    rw [zero_rpow, zero_rpow] <;> linarith
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz
#align real.rpow_le_rpow_of_exponent_ge' Real.rpow_le_rpow_of_exponent_ge'

theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } :=
  by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul hy, rpow_mul hz, hyz]
#align real.rpow_left_inj_on Real.rpow_left_injOn

theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ Real.log x ≤ z * Real.log y := by
  rw [← Real.log_le_log hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.le_rpow_iff_log_le Real.le_rpow_iff_log_le

theorem le_rpow_of_log_le (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x ≤ z * Real.log y) : x ≤ y ^ z :=
  by
  obtain hx | rfl := hx.lt_or_eq
  · exact (le_rpow_iff_log_le hx hy).2 h
  exact (Real.rpow_pos_of_pos hy z).le
#align real.le_rpow_of_log_le Real.le_rpow_of_log_le

theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ Real.log x < z * Real.log y := by
  rw [← Real.log_lt_log_iff hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.lt_rpow_iff_log_lt Real.lt_rpow_iff_log_lt

theorem lt_rpow_of_log_lt (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x < z * Real.log y) : x < y ^ z :=
  by
  obtain hx | rfl := hx.lt_or_eq
  · exact (lt_rpow_iff_log_lt hx hy).2 h
  exact Real.rpow_pos_of_pos hy z
#align real.lt_rpow_of_log_lt Real.lt_rpow_of_log_lt

theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx]
#align real.rpow_le_one_iff_of_pos Real.rpow_le_one_iff_of_pos

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this
#align real.abs_log_mul_self_rpow_lt Real.abs_log_mul_self_rpow_lt

theorem pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x :=
  by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]
#align real.pow_nat_rpow_nat_inv Real.pow_nat_rpow_nat_inv

theorem rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x :=
  by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]
#align real.rpow_nat_inv_pow_nat Real.rpow_nat_inv_pow_nat

theorem continuousAt_const_rpow {a b : ℝ} (h : a ≠ 0) : ContinuousAt (rpow a) b :=
  by
  have : rpow a = fun x : ℝ => ((a : ℂ) ^ (x : ℂ)).re :=
    by
    ext1 x
    rw [rpow_eq_pow, rpow_def]
  rw [this]
  refine' complex.continuous_re.continuous_at.comp _
  refine' (continuousAt_const_cpow _).comp complex.continuous_of_real.continuous_at
  norm_cast
  exact h
#align real.continuous_at_const_rpow Real.continuousAt_const_rpow

theorem continuousAt_const_rpow' {a b : ℝ} (h : b ≠ 0) : ContinuousAt (rpow a) b :=
  by
  have : rpow a = fun x : ℝ => ((a : ℂ) ^ (x : ℂ)).re :=
    by
    ext1 x
    rw [rpow_eq_pow, rpow_def]
  rw [this]
  refine' complex.continuous_re.continuous_at.comp _
  refine' (continuousAt_const_cpow' _).comp complex.continuous_of_real.continuous_at
  norm_cast
  exact h
#align real.continuous_at_const_rpow' Real.continuousAt_const_rpow'

theorem rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
  by
  suffices : ∀ᶠ x : ℝ × ℝ in 𝓝 p, x.1 < 0
  exact
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst
#align real.rpow_eq_nhds_of_neg Real.rpow_eq_nhds_of_neg

theorem rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
  by
  suffices : ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1
  exact
    this.mono fun x hx => by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst
#align real.rpow_eq_nhds_of_pos Real.rpow_eq_nhds_of_pos

theorem continuousAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  by
  rw [ne_iff_lt_or_gt] at hp
  cases hp
  · rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine' ContinuousAt.mul _ (continuous_cos.continuous_at.comp _)
    · refine' continuous_exp.continuous_at.comp (ContinuousAt.mul _ continuous_snd.continuous_at)
      refine' (continuous_at_log _).comp continuous_fst.continuous_at
      exact hp.ne
    · exact continuous_snd.continuous_at.mul continuousAt_const
  · rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine' continuous_exp.continuous_at.comp (ContinuousAt.mul _ continuous_snd.continuous_at)
    refine' (continuous_at_log _).comp continuous_fst.continuous_at
    exact hp.lt.ne.symm
#align real.continuous_at_rpow_of_ne Real.continuousAt_rpow_of_ne

theorem continuousAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  by
  cases' p with x y
  obtain hx | rfl := ne_or_eq x 0
  · exact continuous_at_rpow_of_ne (x, y) hx
  have A : tendsto (fun p : ℝ × ℝ => exp (log p.1 * p.2)) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    tendsto_exp_at_bot.comp
      ((tendsto_log_nhds_within_zero.comp tendsto_fst).atBot_mul hp tendsto_snd)
  have B : tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[≠] 0 ×ᶠ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[{0}] 0 ×ᶠ 𝓝 y) (pure 0) :=
    by
    rw [nhdsWithin_singleton, tendsto_pure, pure_prod, eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))
#align real.continuous_at_rpow_of_pos Real.continuousAt_rpow_of_pos

theorem continuousAt_rpow (p : ℝ × ℝ) (h : p.1 ≠ 0 ∨ 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h
#align real.continuous_at_rpow Real.continuousAt_rpow

theorem continuousAt_rpow_const (x : ℝ) (q : ℝ) (h : x ≠ 0 ∨ 0 < q) :
    ContinuousAt (fun x : ℝ => x ^ q) x :=
  by
  change ContinuousAt ((fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun y : ℝ => (y, q)) x
  apply ContinuousAt.comp
  · exact continuous_at_rpow (x, q) h
  · exact (continuous_id'.prod_mk continuous_const).ContinuousAt
#align real.continuous_at_rpow_const Real.continuousAt_rpow_const

end Real

section

variable {α : Type _}

theorem Filter.Tendsto.rpow {l : Filter α} {f g : α → ℝ} {x y : ℝ} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) : Tendsto (fun t => f t ^ g t) l (𝓝 (x ^ y)) :=
  (Real.continuousAt_rpow (x, y) h).Tendsto.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.rpow Filter.Tendsto.rpow

theorem Filter.Tendsto.rpow_const {l : Filter α} {f : α → ℝ} {x p : ℝ} (hf : Tendsto f l (𝓝 x))
    (h : x ≠ 0 ∨ 0 ≤ p) : Tendsto (fun a => f a ^ p) l (𝓝 (x ^ p)) :=
  if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)
#align filter.tendsto.rpow_const Filter.Tendsto.rpow_const

variable [TopologicalSpace α] {f g : α → ℝ} {s : Set α} {x : α} {p : ℝ}

theorem ContinuousAt.rpow (hf : ContinuousAt f x) (hg : ContinuousAt g x) (h : f x ≠ 0 ∨ 0 < g x) :
    ContinuousAt (fun t => f t ^ g t) x :=
  hf.rpow hg h
#align continuous_at.rpow ContinuousAt.rpow

theorem ContinuousWithinAt.rpow (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : f x ≠ 0 ∨ 0 < g x) : ContinuousWithinAt (fun t => f t ^ g t) s x :=
  hf.rpow hg h
#align continuous_within_at.rpow ContinuousWithinAt.rpow

theorem ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s := fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)
#align continuous_on.rpow ContinuousOn.rpow

theorem Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ 0 ∨ 0 < g x) :
    Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.rpow hg.ContinuousAt (h x)
#align continuous.rpow Continuous.rpow

theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h
#align continuous_within_at.rpow_const ContinuousWithinAt.rpow_const

theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h
#align continuous_at.rpow_const ContinuousAt.rpow_const

theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousOn (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)
#align continuous_on.rpow_const ContinuousOn.rpow_const

theorem Continuous.rpow_const (hf : Continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
    Continuous fun x => f x ^ p :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.rpow_const (h x)
#align continuous.rpow_const Continuous.rpow_const

end

namespace Real

variable {z x y : ℝ}

section Sqrt

theorem sqrt_eq_rpow (x : ℝ) : sqrt x = x ^ (1 / (2 : ℝ)) :=
  by
  obtain h | h := le_or_lt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg_of_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_nat_cast, ← rpow_mul h]
    norm_num
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ)
    ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]
#align real.sqrt_eq_rpow Real.sqrt_eq_rpow

theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = sqrt x ^ r :=
  by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring
#align real.rpow_div_two_eq_sqrt Real.rpow_div_two_eq_sqrt

end Sqrt

end Real

section Limits

open Real Filter

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ y) atTop atTop :=
  by
  rw [tendsto_at_top_at_top]
  intro b
  use max b 0 ^ (1 / y)
  intro x hx
  exact
    le_of_max_le_left
      (by
        convert rpow_le_rpow (rpow_nonneg_of_nonneg (le_max_right b 0) (1 / y)) hx (le_of_lt hy)
        rw [← rpow_mul (le_max_right b 0), (eq_div_iff (ne_of_gt hy)).mp rfl, rpow_one])
#align tendsto_rpow_at_top tendsto_rpow_atTop

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ (-y)) atTop (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun x hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop
#align tendsto_rpow_neg_at_top tendsto_rpow_neg_atTop

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
theorem tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1) :=
  by
  refine'
    tendsto.congr' _
      ((tendsto_exp_nhds_0_nhds_1.comp
            (by
              simpa only [mul_zero, pow_one] using
                (@tendsto_const_nhds _ _ _ a _).mul
                  (tendsto_div_pow_mul_exp_add_at_top b c 1 hb))).comp
        tendsto_log_at_top)
  apply eventually_eq_of_mem (Ioi_mem_at_top (0 : ℝ))
  intro x hx
  simp only [Set.mem_Ioi, Function.comp_apply] at hx⊢
  rw [exp_log hx, ← exp_log (rpow_pos_of_pos hx (a / (b * x + c))), log_rpow hx (a / (b * x + c))]
  field_simp
#align tendsto_rpow_div_mul_add tendsto_rpow_div_mul_add

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : ℝ) / x)) atTop (𝓝 1) :=
  by
  convert tendsto_rpow_div_mul_add (1 : ℝ) _ (0 : ℝ) zero_ne_one
  funext
  congr 2
  ring
#align tendsto_rpow_div tendsto_rpow_div

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : ℝ) / x)) atTop (𝓝 1) :=
  by
  convert tendsto_rpow_div_mul_add (-(1 : ℝ)) _ (0 : ℝ) zero_ne_one
  funext
  congr 2
  ring
#align tendsto_rpow_neg_div tendsto_rpow_neg_div

/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`. -/
theorem tendsto_exp_div_rpow_atTop (s : ℝ) : Tendsto (fun x : ℝ => exp x / x ^ s) atTop atTop :=
  by
  cases' archimedean_iff_nat_lt.1 Real.archimedean s with n hn
  refine' tendsto_at_top_mono' _ _ (tendsto_exp_div_pow_at_top n)
  filter_upwards [eventually_gt_at_top (0 : ℝ), eventually_ge_at_top (1 : ℝ)]with x hx₀ hx₁
  rw [div_le_div_left (exp_pos _) (pow_pos hx₀ _) (rpow_pos_of_pos hx₀ _), ← rpow_nat_cast]
  exact rpow_le_rpow_of_exponent_le hx₁ hn.le
#align tendsto_exp_div_rpow_at_top tendsto_exp_div_rpow_atTop

/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_exp_mul_div_rpow_atTop (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => exp (b * x) / x ^ s) atTop atTop :=
  by
  refine' ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' _
  filter_upwards [eventually_ge_at_top (0 : ℝ)]with x hx₀
  simp [div_rpow, (exp_pos x).le, rpow_nonneg_of_nonneg, ← rpow_mul, ← exp_mul, mul_comm x, hb.ne',
    *]
#align tendsto_exp_mul_div_rpow_at_top tendsto_exp_mul_div_rpow_atTop

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in filter_upwards #[[], ["with", ident x],
  ["using", expr by simp [] [] [] ["[", expr exp_neg, ",", expr inv_div, ",", expr div_eq_mul_inv _
    (exp _), "]"] [] []]]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args -/
/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * exp (-b * x)) atTop (𝓝 0) :=
  by
  refine' (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' _
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in filter_upwards #[[], [\"with\", ident x],\n  [\"using\", expr by simp [] [] [] [\"[\", expr exp_neg, \",\", expr inv_div, \",\", expr div_eq_mul_inv _\n    (exp _), \"]\"] [] []]]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error @ arg 0: next failed, no more args"
#align tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0

namespace Asymptotics

variable {α : Type _} {r c : ℝ} {l : Filter α} {f g : α → ℝ}

theorem IsOWith.rpow (h : IsOWith c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
    IsOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r :=
  by
  apply is_O_with.of_bound
  filter_upwards [hg, h.bound]with x hgx hx
  calc
    |f x ^ r| ≤ |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ ≤ (c * |g x|) ^ r := rpow_le_rpow (abs_nonneg _) hx hr
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]
    
#align asymptotics.is_O_with.rpow Asymptotics.IsOWith.rpow

theorem IsO.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨c, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).IsO
#align asymptotics.is_O.rpow Asymptotics.IsO.rpow

theorem IsOCat.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r :=
  IsOCat.of_isOWith fun c hc =>
    ((h.forall_isOWith (rpow_pos_of_pos hc r⁻¹)).rpow (rpow_nonneg_of_nonneg hc.le _) hr.le
          hg).congr_const
      (by rw [← rpow_mul hc.le, inv_mul_cancel hr.ne', rpow_one])
#align asymptotics.is_o.rpow Asymptotics.IsOCat.rpow

end Asymptotics

open Asymptotics

/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
theorem isOCat_rpow_exp_pos_mul_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ s) =o[atTop] fun x => exp (b * x) :=
  Iff.mpr (isOCat_iff_tendsto fun x h => absurd h (exp_pos _).ne') <| by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_0 s b hb
#align is_o_rpow_exp_pos_mul_at_top isOCat_rpow_exp_pos_mul_atTop

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
theorem isOCat_zpow_exp_pos_mul_atTop (k : ℤ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [rpow_int_cast] using isOCat_rpow_exp_pos_mul_atTop k hb
#align is_o_zpow_exp_pos_mul_at_top isOCat_zpow_exp_pos_mul_atTop

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
theorem isOCat_pow_exp_pos_mul_atTop (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa using isOCat_zpow_exp_pos_mul_atTop k hb
#align is_o_pow_exp_pos_mul_at_top isOCat_pow_exp_pos_mul_atTop

/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
theorem isOCat_rpow_exp_atTop (s : ℝ) : (fun x : ℝ => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isOCat_rpow_exp_pos_mul_atTop s one_pos
#align is_o_rpow_exp_at_top isOCat_rpow_exp_atTop

theorem isOCat_log_rpow_atTop {r : ℝ} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isO_self_const_mul _ hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      (eventually_gt_atTop 0).mono fun x hx => (log_rpow hx _).symm
    _ =o[atTop] fun x => x ^ r := isOCat_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)
    
#align is_o_log_rpow_at_top isOCat_log_rpow_atTop

theorem isOCat_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
  have hr : 0 < r' := lt_max_iff.2 <| Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
      IsO.of_bound 1 <|
        (tendsto_log_atTop.eventually_ge_atTop 1).mono fun x hx =>
          by
          have hx₀ : 0 ≤ log x := zero_le_one.trans hx
          simp [norm_eq_abs, abs_rpow_of_nonneg, abs_rpow_of_nonneg hx₀,
            rpow_le_rpow_of_exponent_le (hx.trans (le_abs_self _))]
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      (isOCat_log_rpow_atTop H).rpow hr <|
        (tendsto_rpow_atTop H).Eventually <| eventually_ge_atTop 0
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx => by simp only [← rpow_mul hx, div_mul_cancel _ hr.ne']
    
#align is_o_log_rpow_rpow_at_top isOCat_log_rpow_rpow_atTop

theorem isOCat_abs_log_rpow_rpow_nhds_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s :=
  ((isOCat_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_zero_atTop).congr'
    (mem_of_superset (Icc_mem_nhdsWithin_Ioi <| Set.left_mem_Ico.2 one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply, inv_rpow hx.out.le, rpow_neg hx.out.le, inv_inv])
#align is_o_abs_log_rpow_rpow_nhds_zero isOCat_abs_log_rpow_rpow_nhds_zero

theorem isOCat_log_rpow_nhds_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isOCat_abs_log_rpow_rpow_nhds_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsWithin_Ioi <| Set.left_mem_Ico.2 one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    EventuallyEq.rfl
#align is_o_log_rpow_nhds_zero isOCat_log_rpow_nhds_zero

theorem tendsto_log_div_rpow_nhds_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (isOCat_log_rpow_nhds_zero hr).tendsto_div_nhds_zero
#align tendsto_log_div_rpow_nhds_zero tendsto_log_div_rpow_nhds_zero

theorem tendsto_log_mul_rpow_nhds_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_log_div_rpow_nhds_zero <| neg_lt_zero.2 hr).congr' <|
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]
#align tendsto_log_mul_rpow_nhds_zero tendsto_log_mul_rpow_nhds_zero

end Limits

namespace Complex

/-- See also `continuous_at_cpow` and `complex.continuous_at_cpow_of_re_pos`. -/
theorem continuousAt_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, z) :=
  by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero]
  refine' squeeze_zero (fun _ => norm_nonneg _) (fun _ => abs_cpow_le _ _) _
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine' tendsto.zero_mul_is_bounded_under_le _ _
  ·
    convert
        (continuous_fst.norm.tendsto _).rpow ((continuous_re.comp continuous_snd).Tendsto _) _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [(· ∘ ·), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt (|im z|) with ⟨C, hC⟩
    refine' ⟨Real.exp (π * C), eventually_map.2 _⟩
    refine'
      (((continuous_im.comp continuous_snd).abs.Tendsto (_, z)).Eventually (gt_mem_nhds hC)).mono
        fun z hz => Real.exp_le_exp.2 <| (neg_le_abs_self _).trans _
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        real.pi_pos.le
#align complex.continuous_at_cpow_zero_of_re_pos Complex.continuousAt_cpow_zero_of_re_pos

/-- See also `continuous_at_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
theorem continuousAt_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p :=
  by
  cases' p with z w
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_or, Ne.def, Classical.not_not,
    not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts[continuousAt_cpow h₁, continuous_at_cpow_zero_of_re_pos h₂]
#align complex.continuous_at_cpow_of_re_pos Complex.continuousAt_cpow_of_re_pos

/-- See also `continuous_at_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
theorem continuousAt_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
    ContinuousAt (fun x => x ^ w) z :=
  Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw) (continuousAt_id.Prod continuousAt_const)
#align complex.continuous_at_cpow_const_of_re_pos Complex.continuousAt_cpow_const_of_re_pos

/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
theorem continuousAt_of_real_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun p => ↑p.1 ^ p.2 : ℝ × ℂ → ℂ) (x, y) :=
  by
  rcases lt_trichotomy 0 x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) :=
      continuous_of_real.continuous_at.prod_map continuousAt_id
    refine' (continuousAt_cpow (Or.inl _)).comp this
    rwa [of_real_re]
  · -- x = 0 : reduce to continuous_at_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0 : ℝ), y⟩ :=
      by
      rw [of_real_zero]
      apply continuous_at_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩ :=
      continuous_of_real.continuous_at.prod_map continuousAt_id
    exact @ContinuousAt.comp (ℝ × ℂ) (ℂ × ℂ) ℂ _ _ _ _ (fun p => ⟨↑p.1, p.2⟩) ⟨0, y⟩ A B
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-↑p.1) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y)
      by
      refine' this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) _)
      exact fun p hp => (of_real_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) :=
      ContinuousAt.prod_map continuous_of_real.continuous_at.neg continuousAt_id
    apply ContinuousAt.mul
    · refine' (continuousAt_cpow (Or.inl _)).comp A
      rwa [neg_re, of_real_re, neg_pos]
    · exact (continuous_exp.comp (continuous_const.mul continuous_snd)).ContinuousAt
#align complex.continuous_at_of_real_cpow Complex.continuousAt_of_real_cpow

theorem continuousAt_of_real_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun a => a ^ y : ℝ → ℂ) x :=
  @ContinuousAt.comp _ _ _ _ _ _ _ _ x (continuousAt_of_real_cpow x y h)
    (continuous_id.prod_mk continuous_const).ContinuousAt
#align complex.continuous_at_of_real_cpow_const Complex.continuousAt_of_real_cpow_const

theorem continuous_of_real_cpow_const {y : ℂ} (hs : 0 < y.re) :
    Continuous (fun x => x ^ y : ℝ → ℂ) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_of_real_cpow_const x y (Or.inl hs)
#align complex.continuous_of_real_cpow_const Complex.continuous_of_real_cpow_const

end Complex

namespace Nnreal

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg_of_nonneg x.2 y⟩
#align nnreal.rpow Nnreal.rpow

noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align nnreal.rpow_eq_pow Nnreal.rpow_eq_pow

@[simp, norm_cast]
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl
#align nnreal.coe_rpow Nnreal.coe_rpow

@[simp]
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  Nnreal.eq <| Real.rpow_zero _
#align nnreal.rpow_zero Nnreal.rpow_zero

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  rw [← Nnreal.coe_eq, coe_rpow, ← Nnreal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2
#align nnreal.rpow_eq_zero_iff Nnreal.rpow_eq_zero_iff

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
  Nnreal.eq <| Real.zero_rpow h
#align nnreal.zero_rpow Nnreal.zero_rpow

@[simp]
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  Nnreal.eq <| Real.rpow_one _
#align nnreal.rpow_one Nnreal.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  Nnreal.eq <| Real.one_rpow _
#align nnreal.one_rpow Nnreal.one_rpow

theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  Nnreal.eq <| Real.rpow_add (pos_iff_ne_zero.2 hx) _ _
#align nnreal.rpow_add Nnreal.rpow_add

theorem rpow_add' (x : ℝ≥0) {y z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  Nnreal.eq <| Real.rpow_add' x.2 h
#align nnreal.rpow_add' Nnreal.rpow_add'

theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  Nnreal.eq <| Real.rpow_mul x.2 y z
#align nnreal.rpow_mul Nnreal.rpow_mul

theorem rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  Nnreal.eq <| Real.rpow_neg x.2 _
#align nnreal.rpow_neg Nnreal.rpow_neg

theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align nnreal.rpow_neg_one Nnreal.rpow_neg_one

theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  Nnreal.eq <| Real.rpow_sub (pos_iff_ne_zero.2 hx) y z
#align nnreal.rpow_sub Nnreal.rpow_sub

theorem rpow_sub' (x : ℝ≥0) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  Nnreal.eq <| Real.rpow_sub' x.2 h
#align nnreal.rpow_sub' Nnreal.rpow_sub'

theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_inv_rpow_self Nnreal.rpow_inv_rpow_self

theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x := by
  field_simp [← rpow_mul]
#align nnreal.rpow_self_rpow_inv Nnreal.rpow_self_rpow_inv

theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  Nnreal.eq <| Real.inv_rpow x.2 y
#align nnreal.inv_rpow Nnreal.inv_rpow

theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  Nnreal.eq <| Real.div_rpow x.2 y.2 z
#align nnreal.div_rpow Nnreal.div_rpow

theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) :=
  by
  refine' Nnreal.eq _
  push_cast
  exact Real.sqrt_eq_rpow x.1
#align nnreal.sqrt_eq_rpow Nnreal.sqrt_eq_rpow

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  Nnreal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_nat_cast x n
#align nnreal.rpow_nat_cast Nnreal.rpow_nat_cast

@[simp]
theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align nnreal.rpow_two Nnreal.rpow_two

theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  Nnreal.eq <| Real.mul_rpow x.2 y.2
#align nnreal.mul_rpow Nnreal.mul_rpow

theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂
#align nnreal.rpow_le_rpow Nnreal.rpow_le_rpow

theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂
#align nnreal.rpow_lt_rpow Nnreal.rpow_lt_rpow

theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz
#align nnreal.rpow_lt_rpow_iff Nnreal.rpow_lt_rpow_iff

theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz
#align nnreal.rpow_le_rpow_iff Nnreal.rpow_le_rpow_iff

theorem le_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.le_rpow_one_div_iff Nnreal.le_rpow_one_div_iff

theorem rpow_one_div_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']
#align nnreal.rpow_one_div_le_iff Nnreal.rpow_one_div_le_iff

theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz
#align nnreal.rpow_lt_rpow_of_exponent_lt Nnreal.rpow_lt_rpow_of_exponent_lt

theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz
#align nnreal.rpow_le_rpow_of_exponent_le Nnreal.rpow_le_rpow_of_exponent_le

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz
#align nnreal.rpow_lt_rpow_of_exponent_gt Nnreal.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz
#align nnreal.rpow_le_rpow_of_exponent_ge Nnreal.rpow_le_rpow_of_exponent_ge

theorem rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x ^ p :=
  by
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x ^ p :=
    by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy 0 p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)
#align nnreal.rpow_pos Nnreal.rpow_pos

theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz
#align nnreal.rpow_lt_one Nnreal.rpow_lt_one

theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz
#align nnreal.rpow_le_one Nnreal.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz
#align nnreal.rpow_lt_one_of_one_lt_of_neg Nnreal.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz
#align nnreal.rpow_le_one_of_one_le_of_nonpos Nnreal.rpow_le_one_of_one_le_of_nonpos

theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz
#align nnreal.one_lt_rpow Nnreal.one_lt_rpow

theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁
#align nnreal.one_le_rpow Nnreal.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz
#align nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg Nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz
#align nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos Nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos

theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
  by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← Nnreal.rpow_one x]
  exact Nnreal.rpow_le_rpow_of_exponent_ge h hx h_one_le
#align nnreal.rpow_le_self_of_le_one Nnreal.rpow_le_self_of_le_one

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz
#align nnreal.rpow_left_injective Nnreal.rpow_left_injective

theorem rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff
#align nnreal.rpow_eq_rpow_iff Nnreal.rpow_eq_rpow_iff

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align nnreal.rpow_left_surjective Nnreal.rpow_left_surjective

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align nnreal.rpow_left_bijective Nnreal.rpow_left_bijective

theorem eq_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x = y ^ (1 / z) ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.eq_rpow_one_div_iff Nnreal.eq_rpow_one_div_iff

theorem rpow_one_div_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ (1 / z) = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz, rpow_self_rpow_inv hz]
#align nnreal.rpow_one_div_eq_iff Nnreal.rpow_one_div_eq_iff

theorem pow_nat_rpow_nat_inv (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x :=
  by
  rw [← Nnreal.coe_eq, coe_rpow, Nnreal.coe_pow]
  exact Real.pow_nat_rpow_nat_inv x.2 hn
#align nnreal.pow_nat_rpow_nat_inv Nnreal.pow_nat_rpow_nat_inv

theorem rpow_nat_inv_pow_nat (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x :=
  by
  rw [← Nnreal.coe_eq, Nnreal.coe_pow, coe_rpow]
  exact Real.rpow_nat_inv_pow_nat x.2 hn
#align nnreal.rpow_nat_inv_pow_nat Nnreal.rpow_nat_inv_pow_nat

theorem continuousAt_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
    ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (x, y) :=
  by
  have :
    (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) =
      Real.toNnreal ∘ (fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun p : ℝ≥0 × ℝ => (p.1.1, p.2) :=
    by
    ext p
    rw [coe_rpow, Real.coe_toNnreal _ (Real.rpow_nonneg_of_nonneg p.1.2 _)]
    rfl
  rw [this]
  refine' continuous_real_to_nnreal.continuous_at.comp (ContinuousAt.comp _ _)
  · apply Real.continuousAt_rpow
    simp only [Ne.def] at h
    rw [← Nnreal.coe_eq_zero x] at h
    exact h
  · exact ((continuous_subtype_val.comp continuous_fst).prod_mk continuous_snd).ContinuousAt
#align nnreal.continuous_at_rpow Nnreal.continuousAt_rpow

theorem Real.toNnreal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNnreal (x ^ y) = Real.toNnreal x ^ y :=
  by
  nth_rw 1 [← Real.coe_toNnreal x hx]
  rw [← Nnreal.coe_rpow, Real.toNnreal_coe]
#align real.to_nnreal_rpow_of_nonneg Real.toNnreal_rpow_of_nonneg

theorem eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y :=
  by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine' eventually_at_top.2 ⟨m + 1, fun n hn => _⟩
  simpa only [Nnreal.rpow_one_div_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    Nnreal.rpow_nat_cast] using hm.le.trans (pow_le_pow hy.le (m.le_succ.trans hn))
#align nnreal.eventually_pow_one_div_le Nnreal.eventually_pow_one_div_le

end Nnreal

namespace Real

variable {n : ℕ}

theorem exists_rat_pow_btwn_rat_aux (hn : n ≠ 0) (x y : ℝ) (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ ↑q ^ n < y :=
  by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn.bot_lt
  obtain ⟨q, hxq, hqy⟩ :=
    exists_rat_btwn (rpow_lt_rpow (le_max_left 0 x) (max_lt hy h) <| inv_pos.mpr hn')
  have := rpow_nonneg_of_nonneg (le_max_left 0 x) n⁻¹
  have hq := this.trans_lt hxq
  replace hxq := rpow_lt_rpow this hxq hn'
  replace hqy := rpow_lt_rpow hq.le hqy hn'
  rw [rpow_nat_cast, rpow_nat_cast, rpow_nat_inv_pow_nat _ hn] at hxq hqy
  exact ⟨q, by exact_mod_cast hq, (le_max_right _ _).trans_lt hxq, hqy⟩
  · exact le_max_left _ _
  · exact hy.le
#align real.exists_rat_pow_btwn_rat_aux Real.exists_rat_pow_btwn_rat_aux

theorem exists_rat_pow_btwn_rat (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  apply_mod_cast exists_rat_pow_btwn_rat_aux hn x y <;> assumption
#align real.exists_rat_pow_btwn_rat Real.exists_rat_pow_btwn_rat

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
theorem exists_rat_pow_btwn {α : Type _} [LinearOrderedField α] [Archimedean α] (hn : n ≠ 0)
    {x y : α} (h : x < y) (hy : 0 < y) : ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ (q ^ n : α) < y :=
  by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast  at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this
  refine' ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans _, hy₂.trans' _⟩ <;> assumption_mod_cast
#align real.exists_rat_pow_btwn Real.exists_rat_pow_btwn

end Real

open Filter

theorem Filter.Tendsto.nnrpow {α : Type _} {f : Filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0}
    {y : ℝ} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
    Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y)) :=
  Tendsto.comp (Nnreal.continuousAt_rpow h) (hx.prod_mk_nhds hy)
#align filter.tendsto.nnrpow Filter.Tendsto.nnrpow

namespace Nnreal

theorem continuousAt_rpow_const {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) :
    ContinuousAt (fun z => z ^ y) x :=
  h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)
#align nnreal.continuous_at_rpow_const Nnreal.continuousAt_rpow_const

theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
  continuous_iff_continuousAt.2 fun x => continuousAt_rpow_const (Or.inr h)
#align nnreal.continuous_rpow_const Nnreal.continuous_rpow_const

theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ≥0 => x ^ y) atTop atTop :=
  by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_at_top_at_top.mp (tendsto_rpow_atTop hy) b
  use c.to_nnreal
  intro a ha
  exact_mod_cast hc a (real.to_nnreal_le_iff_le_coe.mp ha)
#align nnreal.tendsto_rpow_at_top Nnreal.tendsto_rpow_atTop

end Nnreal

namespace Ennreal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0
#align ennreal.rpow Ennreal.rpow

noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl
#align ennreal.rpow_eq_pow Ennreal.rpow_eq_pow

@[simp]
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), rpow]
      simp [lt_irrefl]
#align ennreal.rpow_zero Ennreal.rpow_zero

theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl
#align ennreal.top_rpow_def Ennreal.top_rpow_def

@[simp]
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]
#align ennreal.top_rpow_of_pos Ennreal.top_rpow_of_pos

@[simp]
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]
#align ennreal.top_rpow_of_neg Ennreal.top_rpow_of_neg

@[simp]
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 :=
  by
  rw [← Ennreal.coe_zero, ← Ennreal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h, asymm h, ne_of_gt h]
#align ennreal.zero_rpow_of_pos Ennreal.zero_rpow_of_pos

@[simp]
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ :=
  by
  rw [← Ennreal.coe_zero, ← Ennreal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h, ne_of_gt h]
#align ennreal.zero_rpow_of_neg Ennreal.zero_rpow_of_neg

theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ :=
  by
  rcases lt_trichotomy 0 y with (H | rfl | H)
  · simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl]
  · simp [lt_irrefl]
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]
#align ennreal.zero_rpow_def Ennreal.zero_rpow_def

@[simp]
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * 0 ^ y = 0 ^ y :=
  by
  rw [zero_rpow_def]
  split_ifs
  exacts[zero_mul _, one_mul _, top_mul_top]
#align ennreal.zero_rpow_mul_self Ennreal.zero_rpow_mul_self

@[norm_cast]
theorem coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
  by
  rw [← Ennreal.some_eq_coe]
  dsimp only [(· ^ ·), rpow]
  simp [h]
#align ennreal.coe_rpow_of_ne_zero Ennreal.coe_rpow_of_ne_zero

@[norm_cast]
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : (x : ℝ≥0∞) ^ y = (x ^ y : ℝ≥0) :=
  by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, Nnreal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _
#align ennreal.coe_rpow_of_nonneg Ennreal.coe_rpow_of_nonneg

theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0) :=
  rfl
#align ennreal.coe_rpow_def Ennreal.coe_rpow_def

@[simp]
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x :=
  by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [Nnreal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_lt
#align ennreal.rpow_one Ennreal.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 :=
  by
  rw [← coe_one, coe_rpow_of_ne_zero one_ne_zero]
  simp
#align ennreal.one_rpow Ennreal.one_rpow

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_zero_iff Ennreal.rpow_eq_zero_iff

@[simp]
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [coe_rpow_of_ne_zero h, h]
#align ennreal.rpow_eq_top_iff Ennreal.rpow_eq_top_iff

theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]
#align ennreal.rpow_eq_top_iff_of_pos Ennreal.rpow_eq_top_iff_of_pos

theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ :=
  by
  rw [Ennreal.rpow_eq_top_iff]
  intro h
  cases h
  · exfalso
    rw [lt_iff_not_ge] at h
    exact h.right hy0
  · exact h.left
#align ennreal.rpow_eq_top_of_nonneg Ennreal.rpow_eq_top_of_nonneg

theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (Ennreal.rpow_eq_top_of_nonneg x hy0) h
#align ennreal.rpow_ne_top_of_nonneg Ennreal.rpow_ne_top_of_nonneg

theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (Ennreal.rpow_ne_top_of_nonneg hy0 h)
#align ennreal.rpow_lt_top_of_nonneg Ennreal.rpow_lt_top_of_nonneg

theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z :=
  by
  cases x; · exact (h'x rfl).elim
  have : x ≠ 0 := fun h => by simpa [h] using hx
  simp [coe_rpow_of_ne_zero this, Nnreal.rpow_add this]
#align ennreal.rpow_add Ennreal.rpow_add

theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, ← coe_inv A, Nnreal.rpow_neg]
#align ennreal.rpow_neg Ennreal.rpow_neg

theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]
#align ennreal.rpow_sub Ennreal.rpow_sub

theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
#align ennreal.rpow_neg_one Ennreal.rpow_neg_one

theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  by
  cases x
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  · by_cases h : x = 0
    ·
      rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [coe_rpow_of_ne_zero h, coe_rpow_of_ne_zero this, Nnreal.rpow_mul]
#align ennreal.rpow_mul Ennreal.rpow_mul

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_pos _)]
  · simp [coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]
#align ennreal.rpow_nat_cast Ennreal.rpow_nat_cast

@[simp]
theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 :=
  by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align ennreal.rpow_two Ennreal.rpow_two

theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z :=
  by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_lt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_le hxy) using 2 <;> simp only [mul_comm, and_comm', or_comm']
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y using WithTop.recTopCoe <;> cases' hz with hz hz <;> simp [*, hz.not_lt]
  rcases eq_or_ne y 0 with (rfl | hy0); · exact (hx0 (bot_unique hxy)).elim
  induction x using WithTop.recTopCoe; · cases' hz with hz hz <;> simp [hz, top_unique hxy]
  induction y using WithTop.recTopCoe; · cases' hz with hz hz <;> simp [*]
  simp only [*, false_and_iff, and_false_iff, false_or_iff, if_false]
  norm_cast  at *
  rw [coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), Nnreal.mul_rpow]
#align ennreal.mul_rpow_eq_ite Ennreal.mul_rpow_eq_ite

theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_top Ennreal.mul_rpow_of_ne_top

@[norm_cast]
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = x ^ z * y ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z
#align ennreal.coe_mul_rpow Ennreal.coe_mul_rpow

theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_ne_zero Ennreal.mul_rpow_of_ne_zero

theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_lt, mul_rpow_eq_ite]
#align ennreal.mul_rpow_of_nonneg Ennreal.mul_rpow_of_nonneg

theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_lt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply Ennreal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (Ennreal.inv_ne_zero.2 h_top) h0, Ennreal.inv_mul_cancel h0 h_top,
    one_rpow]
#align ennreal.inv_rpow Ennreal.inv_rpow

theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]
#align ennreal.div_rpow_of_nonneg Ennreal.div_rpow_of_nonneg

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z :=
  by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [coe_rpow_of_nonneg _ h.le, Nnreal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]
#align ennreal.strict_mono_rpow_of_pos Ennreal.strictMono_rpow_of_pos

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).Monotone
#align ennreal.monotone_rpow_of_nonneg Ennreal.monotone_rpow_of_nonneg

/-- Bundles `λ x : ℝ≥0∞, x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `λ x : ℝ≥0∞, x ^ (1 / y)`. -/
@[simps apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]
#align ennreal.order_iso_rpow Ennreal.orderIsoRpow

theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) :=
  by
  simp only [order_iso_rpow, one_div_one_div]
  rfl
#align ennreal.order_iso_rpow_symm_apply Ennreal.orderIsoRpow_symm_apply

theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁
#align ennreal.rpow_le_rpow Ennreal.rpow_le_rpow

theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁
#align ennreal.rpow_lt_rpow Ennreal.rpow_lt_rpow

theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le
#align ennreal.rpow_le_rpow_iff Ennreal.rpow_le_rpow_iff

theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt
#align ennreal.rpow_lt_rpow_iff Ennreal.rpow_lt_rpow_iff

theorem le_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y :=
  by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z hz.ne']
  rw [rpow_mul, ← one_div, @rpow_le_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.le_rpow_one_div_iff Ennreal.le_rpow_one_div_iff

theorem lt_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y :=
  by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @_root_.mul_inv_cancel _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, ← one_div, @rpow_lt_rpow_iff _ _ (1 / z) (by simp [hz])]
#align ennreal.lt_rpow_one_div_iff Ennreal.lt_rpow_one_div_iff

theorem rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z :=
  by
  nth_rw 1 [← Ennreal.rpow_one y]
  nth_rw 2 [← @_root_.mul_inv_cancel _ _ z hz.ne.symm]
  rw [Ennreal.rpow_mul, ← one_div, Ennreal.rpow_le_rpow_iff (one_div_pos.2 hz)]
#align ennreal.rpow_one_div_le_iff Ennreal.rpow_one_div_le_iff

theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
    Nnreal.rpow_lt_rpow_of_exponent_lt hx hyz]
#align ennreal.rpow_lt_rpow_of_exponent_lt Ennreal.rpow_lt_rpow_of_exponent_lt

theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl] <;>
      linarith
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      Nnreal.rpow_le_rpow_of_exponent_le hx hyz]
#align ennreal.rpow_le_rpow_of_exponent_le Ennreal.rpow_le_rpow_of_exponent_le

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [coe_rpow_of_ne_zero (ne_of_gt hx0), Nnreal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
#align ennreal.rpow_lt_rpow_of_exponent_gt Ennreal.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  ·
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl] <;>
      linarith
  · rw [coe_le_one_iff] at hx1
    simp [coe_rpow_of_ne_zero h,
      Nnreal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]
#align ennreal.rpow_le_rpow_of_exponent_ge Ennreal.rpow_le_rpow_of_exponent_ge

theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
  by
  nth_rw 2 [← Ennreal.rpow_one x]
  exact Ennreal.rpow_le_rpow_of_exponent_ge hx h_one_le
#align ennreal.rpow_le_self_of_le_one Ennreal.rpow_le_self_of_le_one

theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z :=
  by
  nth_rw 1 [← Ennreal.rpow_one x]
  exact Ennreal.rpow_le_rpow_of_exponent_le hx h_one_le
#align ennreal.le_rpow_self_of_one_le Ennreal.le_rpow_self_of_one_le

theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p :=
  by
  by_cases hp_zero : p = 0
  · simp [hp_zero, Ennreal.zero_lt_one]
  · rw [← Ne.def] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos
#align ennreal.rpow_pos_of_nonneg Ennreal.rpow_pos_of_nonneg

theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p :=
  by
  cases' lt_or_le 0 p with hp_pos hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, Ennreal.inv_pos]
    exact rpow_ne_top_of_nonneg (right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top
#align ennreal.rpow_pos Ennreal.rpow_pos

theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [coe_rpow_of_nonneg _ (le_of_lt hz), Nnreal.rpow_lt_one hx hz]
#align ennreal.rpow_lt_one Ennreal.rpow_lt_one

theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [coe_rpow_of_nonneg _ hz, Nnreal.rpow_le_one hx hz]
#align ennreal.rpow_le_one Ennreal.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  by
  cases x
  · simp [top_rpow_of_neg hz, Ennreal.zero_lt_one]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      Nnreal.rpow_lt_one_of_one_lt_of_neg hx hz]
#align ennreal.rpow_lt_one_of_one_lt_of_neg Ennreal.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 :=
  by
  cases x
  · simp [top_rpow_of_neg hz, Ennreal.zero_lt_one]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      Nnreal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]
#align ennreal.rpow_le_one_of_one_le_of_neg Ennreal.rpow_le_one_of_one_le_of_neg

theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), Nnreal.one_lt_rpow hx hz]
#align ennreal.one_lt_rpow Ennreal.one_lt_rpow

theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z :=
  by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [coe_rpow_of_nonneg _ (le_of_lt hz), Nnreal.one_le_rpow hx (le_of_lt hz)]
#align ennreal.one_le_rpow Ennreal.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1), Nnreal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]
#align ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg Ennreal.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z :=
  by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2⊢
  simp [coe_rpow_of_ne_zero (ne_of_gt hx1),
    Nnreal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]
#align ennreal.one_le_rpow_of_pos_of_le_one_of_neg Ennreal.one_le_rpow_of_pos_of_le_one_of_neg

theorem toNnreal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toNnreal ^ z = (x ^ z).toNnreal :=
  by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x
    · simp [H, ne_of_lt]
    by_cases hx : x = 0
    · simp [hx, H, ne_of_lt]
    · simp [coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [coe_rpow_of_nonneg _ (le_of_lt H)]
#align ennreal.to_nnreal_rpow Ennreal.toNnreal_rpow

theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [Ennreal.toReal, Ennreal.toReal, ← Nnreal.coe_rpow, Ennreal.toNnreal_rpow]
#align ennreal.to_real_rpow Ennreal.toReal_rpow

theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    Ennreal.ofReal x ^ p = Ennreal.ofReal (x ^ p) :=
  by
  simp_rw [Ennreal.ofReal]
  rw [coe_rpow_of_ne_zero, coe_eq_coe, Real.toNnreal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]
#align ennreal.of_real_rpow_of_pos Ennreal.ofReal_rpow_of_pos

theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    Ennreal.ofReal x ^ p = Ennreal.ofReal (x ^ p) :=
  by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne.def] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne.def] at hx0
  exact of_real_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)
#align ennreal.of_real_rpow_of_nonneg Ennreal.ofReal_rpow_of_nonneg

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0∞ => y ^ x :=
  by
  intro y z hyz
  dsimp only at hyz
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul, rpow_mul, hyz]
#align ennreal.rpow_left_injective Ennreal.rpow_left_injective

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, _root_.inv_mul_cancel hx, rpow_one]⟩
#align ennreal.rpow_left_surjective Ennreal.rpow_left_surjective

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
#align ennreal.rpow_left_bijective Ennreal.rpow_left_bijective

theorem tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ≥0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) :=
  by
  rw [tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (at_top_basis_Ioi.tendsto_iff at_top_basis_Ioi).mp (Nnreal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds coe_lt_top
  refine' eventually_of_mem hc' _
  intro a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to ℝ≥0 using ha'
  change ↑c < ↑a at ha
  rw [coe_rpow_of_nonneg _ hy.le]
  exact_mod_cast hc a (by exact_mod_cast ha)
#align ennreal.tendsto_rpow_at_top Ennreal.tendsto_rpow_at_top

theorem eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y :=
  by
  lift x to ℝ≥0 using hx
  by_cases y = ∞
  · exact eventually_of_forall fun n => h.symm ▸ le_top
  · lift y to ℝ≥0 using h
    have := Nnreal.eventually_pow_one_div_le x (by exact_mod_cast hy : 1 < y)
    refine' this.congr (eventually_of_forall fun n => _)
    rw [coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe]
#align ennreal.eventually_pow_one_div_le Ennreal.eventually_pow_one_div_le

private theorem continuous_at_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
    ContinuousAt (fun a : ℝ≥0∞ => a ^ y) x :=
  by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert tendsto_rpow_atTop h
    simp [h]
  lift x to ℝ≥0 using hx
  rw [continuous_at_coe_iff]
  convert continuous_coe.continuous_at.comp (Nnreal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [coe_rpow_of_nonneg _ h.le]
#align ennreal.continuous_at_rpow_const_of_pos ennreal.continuous_at_rpow_const_of_pos

@[continuity]
theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y :=
  by
  apply continuous_iff_continuousAt.2 fun x => _
  rcases lt_trichotomy 0 y with (hy | rfl | hy)
  · exact continuous_at_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuous_at.comp (continuous_at_rpow_const_of_pos z_pos)
#align ennreal.continuous_rpow_const Ennreal.continuous_rpow_const

theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => c * x ^ y) (𝓝 0) (𝓝 0) :=
  by
  convert Ennreal.Tendsto.const_mul (ennreal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc
#align ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos Ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos

end Ennreal

theorem Filter.Tendsto.ennrpow_const {α : Type _} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (Ennreal.continuous_rpow_const.Tendsto a).comp hm
#align filter.tendsto.ennrpow_const Filter.Tendsto.ennrpow_const

namespace NormNum

open Tactic

theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b' : ℝ) = b) (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, ← hb, Real.rpow_nat_cast]
#align norm_num.rpow_pos NormNum.rpow_pos

theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ) (a0 : 0 ≤ a) (hb : (b' : ℝ) = b) (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, ← hb, Real.rpow_neg a0, Real.rpow_nat_cast]
#align norm_num.rpow_neg NormNum.rpow_neg

/-- Evaluate `real.rpow a b` where `a` is a rational numeral and `b` is an integer.
(This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a side condition;
we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because it comes
out to some garbage.) -/
unsafe def prove_rpow (a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let ic ← mk_instance_cache q(ℝ)
  match match_sign b with
    | Sum.inl b => do
      let (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      let cr ← c
      let (ic, c', hc) ← prove_inv ic c cr
      pure (c', (expr.const `` rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
    | Sum.inr ff => pure (q((1 : ℝ)), expr.const `` Real.rpow_zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      pure (c, (expr.const `` rpow_pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow norm_num.prove_rpow

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

open Nnreal Ennreal

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, hb, Complex.cpow_nat_cast]
#align norm_num.cpow_pos NormNum.cpow_pos

theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
    a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_nat_cast]
#align norm_num.cpow_neg NormNum.cpow_neg

theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, Nnreal.rpow_nat_cast]
#align norm_num.nnrpow_pos NormNum.nnrpow_pos

theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, hb, Nnreal.rpow_neg, Nnreal.rpow_nat_cast]
#align norm_num.nnrpow_neg NormNum.nnrpow_neg

theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, Ennreal.rpow_nat_cast]
#align norm_num.ennrpow_pos NormNum.ennrpow_pos

theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by
  rw [← hc, ← h, hb, Ennreal.rpow_neg, Ennreal.rpow_nat_cast]
#align norm_num.ennrpow_neg NormNum.ennrpow_neg

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))
#align norm_num.prove_cpow norm_num.prove_cpow

/-- Evaluate `nnreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` nnrpow_pos `` nnrpow_neg `` Nnreal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))
#align norm_num.prove_nnrpow norm_num.prove_nnrpow

/-- Evaluate `ennreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` ennrpow_pos `` ennrpow_neg `` Ennreal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))
#align norm_num.prove_ennrpow norm_num.prove_ennrpow

/-- Evaluates expressions of the form `rpow a b`, `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_rpow_cpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => b.to_int >> prove_rpow a b
  | q(Real.rpow $(a) $(b)) => b.to_int >> prove_rpow a b
  | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(@Pow.pow _ _ Nnreal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(Nnreal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(@Pow.pow _ _ Ennreal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | q(Ennreal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | _ => tactic.failed
#align norm_num.eval_rpow_cpow norm_num.eval_rpow_cpow

end NormNum

namespace Tactic

namespace Positivity

/-- Auxiliary definition for the `positivity` tactic to handle real powers of reals. -/
unsafe def prove_rpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | nonnegative p => nonnegative <$> mk_app `` Real.rpow_nonneg_of_nonneg [p, b]
    | positive p => positive <$> mk_app `` Real.rpow_pos_of_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_rpow tactic.positivity.prove_rpow

private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
  Nnreal.rpow_pos ha
#align tactic.positivity.nnrpow_pos tactic.positivity.nnrpow_pos

/-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals. -/
unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_nnrpow tactic.positivity.prove_nnrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0`
private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
  Ennreal.rpow_pos_of_nonneg ha hb.le
#align tactic.positivity.ennrpow_pos tactic.positivity.ennrpow_pos

/-- Auxiliary definition for the `positivity` tactic to handle real powers of extended nonnegative
reals. -/
unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  let strictness_b ← core b
  match strictness_a, strictness_b with
    | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
    | positive pa, nonnegative pb => positive <$> mk_app `` Ennreal.rpow_pos_of_nonneg [pa, pb]
    | _, _ => failed
#align tactic.positivity.prove_ennrpow tactic.positivity.prove_ennrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0∞`
end Positivity

open Positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
unsafe def positivity_rpow : expr → tactic strictness
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => prove_rpow a b
  | q(Real.rpow $(a) $(b)) => prove_rpow a b
  | q(@Pow.pow _ _ Nnreal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
  | q(Nnreal.rpow $(a) $(b)) => prove_nnrpow a b
  | q(@Pow.pow _ _ Ennreal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
  | q(Ennreal.rpow $(a) $(b)) => prove_ennrpow a b
  | _ => failed
#align tactic.positivity_rpow tactic.positivity_rpow

end Tactic

