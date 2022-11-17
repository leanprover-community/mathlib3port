/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.NumberTheory.Zsqrtd.Basic
import Mathbin.Data.Complex.Basic
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `to_complex` into the complex numbers is also defined in this file.

## Main statements

`prime_iff_mod_four_eq_three_of_nat_prime`
A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notations

This file uses the local notation `ℤ[i]` for `gaussian_int`

## Implementation notes

Gaussian integers are implemented using the more general definition `zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `zsqrtd` can easily be used.
-/


open Zsqrtd Complex

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
@[reducible]
def GaussianInt : Type :=
  Zsqrtd (-1)
#align gaussian_int GaussianInt

-- mathport name: «exprℤ[i]»
local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

instance : Repr ℤ[i] :=
  ⟨fun x => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩

instance : CommRing ℤ[i] :=
  Zsqrtd.commRing

section

attribute [-instance] Complex.field

-- Avoid making things noncomputable unnecessarily.
/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift ⟨i, by simp⟩
#align gaussian_int.to_complex GaussianInt.toComplex

end

instance : Coe ℤ[i] ℂ :=
  ⟨toComplex⟩

theorem to_complex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I :=
  rfl
#align gaussian_int.to_complex_def GaussianInt.to_complex_def

theorem to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [to_complex_def]
#align gaussian_int.to_complex_def' GaussianInt.to_complex_def'

theorem to_complex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by apply Complex.ext <;> simp [to_complex_def]
#align gaussian_int.to_complex_def₂ GaussianInt.to_complex_def₂

@[simp]
theorem to_real_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
#align gaussian_int.to_real_re GaussianInt.to_real_re

@[simp]
theorem to_real_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [to_complex_def]
#align gaussian_int.to_real_im GaussianInt.to_real_im

@[simp]
theorem to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [to_complex_def]
#align gaussian_int.to_complex_re GaussianInt.to_complex_re

@[simp]
theorem to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [to_complex_def]
#align gaussian_int.to_complex_im GaussianInt.to_complex_im

@[simp]
theorem to_complex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y :=
  toComplex.map_add _ _
#align gaussian_int.to_complex_add GaussianInt.to_complex_add

@[simp]
theorem to_complex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y :=
  toComplex.map_mul _ _
#align gaussian_int.to_complex_mul GaussianInt.to_complex_mul

@[simp]
theorem to_complex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  toComplex.map_one
#align gaussian_int.to_complex_one GaussianInt.to_complex_one

@[simp]
theorem to_complex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  toComplex.map_zero
#align gaussian_int.to_complex_zero GaussianInt.to_complex_zero

@[simp]
theorem to_complex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  toComplex.map_neg _
#align gaussian_int.to_complex_neg GaussianInt.to_complex_neg

@[simp]
theorem to_complex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  toComplex.map_sub _ _
#align gaussian_int.to_complex_sub GaussianInt.to_complex_sub

@[simp]
theorem to_complex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y := by cases x <;> cases y <;> simp [to_complex_def₂]
#align gaussian_int.to_complex_inj GaussianInt.to_complex_inj

@[simp]
theorem to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 := by rw [← to_complex_zero, to_complex_inj]
#align gaussian_int.to_complex_eq_zero GaussianInt.to_complex_eq_zero

@[simp]
theorem nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).normSq := by rw [Zsqrtd.norm, norm_sq] <;> simp
#align gaussian_int.nat_cast_real_norm GaussianInt.nat_cast_real_norm

@[simp]
theorem nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).normSq := by
  cases x <;> rw [Zsqrtd.norm, norm_sq] <;> simp
#align gaussian_int.nat_cast_complex_norm GaussianInt.nat_cast_complex_norm

theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  norm_nonneg (by norm_num) _
#align gaussian_int.norm_nonneg GaussianInt.norm_nonneg

@[simp]
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 := by rw [← @Int.cast_inj ℝ _ _ _] <;> simp
#align gaussian_int.norm_eq_zero GaussianInt.norm_eq_zero

theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne.def, eq_comm, norm_eq_zero] <;> simp [norm_nonneg]
#align gaussian_int.norm_pos GaussianInt.norm_pos

theorem coe_nat_abs_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)
#align gaussian_int.coe_nat_abs_norm GaussianInt.coe_nat_abs_norm

@[simp]
theorem nat_cast_nat_abs_norm {α : Type _} [Ring α] (x : ℤ[i]) : (x.norm.natAbs : α) = x.norm := by
  rw [← Int.cast_ofNat, coe_nat_abs_norm]
#align gaussian_int.nat_cast_nat_abs_norm GaussianInt.nat_cast_nat_abs_norm

theorem nat_abs_norm_eq (x : ℤ[i]) : x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs :=
  Int.ofNat.inj $ by
    simp
    simp [Zsqrtd.norm]
#align gaussian_int.nat_abs_norm_eq GaussianInt.nat_abs_norm_eq

instance : Div ℤ[i] :=
  ⟨fun x y =>
    let n := (norm y : ℚ)⁻¹
    let c := y.conj
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

theorem div_def (x y : ℤ[i]) : x / y = ⟨round ((x * conj y).re / norm y : ℚ), round ((x * conj y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]
#align gaussian_int.div_def GaussianInt.div_def

theorem to_complex_div_re (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re := by
  rw [div_def, ← @Rat.round_cast ℝ _ _] <;> simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]
#align gaussian_int.to_complex_div_re GaussianInt.to_complex_div_re

theorem to_complex_div_im (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im := by
  rw [div_def, ← @Rat.round_cast ℝ _ _, ← @Rat.round_cast ℝ _ _] <;>
    simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, mul_add, add_mul]
#align gaussian_int.to_complex_div_im GaussianInt.to_complex_div_im

theorem norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|) (him : |x.im| ≤ |y.im|) :
    x.normSq ≤ y.normSq := by
  rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul, ← _root_.abs_mul_self y.re,
      _root_.abs_mul y.re, ← _root_.abs_mul_self x.im, _root_.abs_mul x.im, ← _root_.abs_mul_self y.im,
      _root_.abs_mul y.im] <;>
    exact add_le_add (mul_self_le_mul_self (abs_nonneg _) hre) (mul_self_le_mul_self (abs_nonneg _) him)
#align gaussian_int.norm_sq_le_norm_sq_of_re_le_of_im_le GaussianInt.norm_sq_le_norm_sq_of_re_le_of_im_le

theorem norm_sq_div_sub_div_lt_one (x y : ℤ[i]) : ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq < 1 :=
  calc
    ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)).normSq =
        ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re + ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) * I : ℂ).normSq :=
      congr_arg _ $ by apply Complex.ext <;> simp
    _ ≤ (1 / 2 + 1 / 2 * I).normSq :=
      have : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_nonneg (by norm_num)
      norm_sq_le_norm_sq_of_re_le_of_im_le
        (by rw [to_complex_div_re] <;> simp [norm_sq, this] <;> simpa using abs_sub_round (x / y : ℂ).re)
        (by rw [to_complex_div_im] <;> simp [norm_sq, this] <;> simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 := by simp [norm_sq] <;> norm_num
    
#align gaussian_int.norm_sq_div_sub_div_lt_one GaussianInt.norm_sq_div_sub_div_lt_one

instance : Mod ℤ[i] :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) :=
  rfl
#align gaussian_int.mod_def GaussianInt.mod_def

theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have : (y : ℂ) ≠ 0 := by rwa [Ne.def, ← to_complex_zero, to_complex_inj]
  (@Int.cast_lt ℝ _ _ _ _).1 $
    calc
      ↑(Zsqrtd.norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).normSq := by simp [mod_def]
      _ = (y : ℂ).normSq * (x / y - (x / y : ℤ[i]) : ℂ).normSq := by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
      _ < (y : ℂ).normSq * 1 := mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _) (norm_sq_pos.2 this)
      _ = Zsqrtd.norm y := by simp
      
#align gaussian_int.norm_mod_lt GaussianInt.norm_mod_lt

theorem nat_abs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm.natAbs < y.norm.natAbs :=
  Int.coe_nat_lt.1 (by simp [-Int.coe_nat_lt, norm_mod_lt x hy])
#align gaussian_int.nat_abs_norm_mod_lt GaussianInt.nat_abs_norm_mod_lt

theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul] <;>
    exact
      le_mul_of_one_le_right (Nat.zero_le _)
        (Int.coe_nat_le.1 (by rw [coe_nat_abs_norm] <;> exact Int.add_one_le_of_lt (norm_pos.2 hy)))
#align gaussian_int.norm_le_norm_mul_left GaussianInt.norm_le_norm_mul_left

instance : Nontrivial ℤ[i] :=
  ⟨⟨0, 1, dec_trivial⟩⟩

instance : EuclideanDomain ℤ[i] :=
  { GaussianInt.commRing, GaussianInt.nontrivial with Quotient := (· / ·), remainder := (· % ·),
    quotient_zero := by
      simp [div_def]
      rfl,
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def], R := _,
    r_well_founded := measure_wf (Int.natAbs ∘ norm), remainderLt := nat_abs_norm_mod_lt,
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge $ norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

theorem mod_four_eq_three_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime] (hpi : Prime (p : ℤ[i])) : p % 4 = 3 :=
  hp.1.eq_two_or_odd.elim
    (fun hp2 =>
      absurd hpi
        (mt irreducible_iff_prime.2 $ fun ⟨hu, h⟩ => by
          have := h ⟨1, 1⟩ ⟨1, -1⟩ (hp2.symm ▸ rfl)
          rw [← norm_eq_one_iff, ← norm_eq_one_iff] at this
          exact absurd this dec_trivial))
    fun hp1 =>
    by_contradiction $ fun hp3 : p % 4 ≠ 3 => by
      have hp41 : p % 4 = 1 := by
        rw [← Nat.mod_mul_left_mod p 2 2, show 2 * 2 = 4 from rfl] at hp1
        have := Nat.mod_lt p (show 0 < 4 from dec_trivial)
        revert this hp3 hp1
        generalize p % 4 = m
        decide!
      let ⟨k, hk⟩ := Zmod.exists_sq_eq_neg_one_iff.2 $ by rw [hp41] <;> exact dec_trivial
      obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (h : k' < p), (k' : Zmod p) = k := by
        refine' ⟨k.val, k.val_lt, Zmod.nat_cast_zmod_val k⟩
      have hpk : p ∣ k ^ 2 + 1 := by
        rw [pow_two, ← CharP.cast_eq_zero_iff (Zmod p) p, Nat.cast_add, Nat.cast_mul, Nat.cast_one, ← hk, add_left_neg]
      have hkmul : (k ^ 2 + 1 : ℤ[i]) = ⟨k, 1⟩ * ⟨k, -1⟩ := by simp [sq, Zsqrtd.ext]
      have hpne1 : p ≠ 1 := ne_of_gt hp.1.one_lt
      have hkltp : 1 + k * k < p * p :=
        calc
          1 + k * k ≤ k + k * k :=
            add_le_add_right (Nat.pos_of_ne_zero fun hk0 => by clear_aux_decl <;> simp_all [pow_succ']) _
          _ = k * (k + 1) := by simp [add_comm, mul_add]
          _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_pos _) (Nat.zero_le _)
          
      have hpk₁ : ¬(p : ℤ[i]) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs $
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, -1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                (show (-1 : ℤ) ≠ 0 from dec_trivial) $ by simpa [hx0] using congr_arg Zsqrtd.im hx
            
      have hpk₂ : ¬(p : ℤ[i]) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
        lt_irrefl (p * x : ℤ[i]).norm.natAbs $
          calc
            (norm (p * x : ℤ[i])).natAbs = (Zsqrtd.norm ⟨k, 1⟩).natAbs := by rw [hx]
            _ < (norm (p : ℤ[i])).natAbs := by simpa [add_comm, Zsqrtd.norm] using hkltp
            _ ≤ (norm (p * x : ℤ[i])).natAbs :=
              norm_le_norm_mul_left _ fun hx0 =>
                (show (1 : ℤ) ≠ 0 from dec_trivial) $ by simpa [hx0] using congr_arg Zsqrtd.im hx
            
      have hpu : ¬IsUnit (p : ℤ[i]) :=
        mt norm_eq_one_iff.2
          (by rw [norm_nat_cast, Int.natAbs_mul, Nat.mul_eq_one_iff] <;> exact fun h => (ne_of_lt hp.1.one_lt).symm h.1)
      obtain ⟨y, hy⟩ := hpk
      have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← Nat.cast_mul p, ← hy] <;> simp⟩
      clear_aux_decl
      tauto
#align gaussian_int.mod_four_eq_three_of_nat_prime_of_prime GaussianInt.mod_four_eq_three_of_nat_prime_of_prime

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime] (hpi : ¬Irreducible (p : ℤ[i])) :
    ∃ (a) (b), a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2 $ by
      rw [norm_nat_cast, Int.natAbs_mul, Nat.mul_eq_one_iff] <;> exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : ∃ (a) (b), (p : ℤ[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 $ by
        rw [← Int.coe_nat_inj', Int.coe_nat_pow, sq, ← @norm_nat_cast (-1), hpab] <;> simp).1
  ⟨a.re.natAbs, a.im.natAbs, by simpa [nat_abs_norm_eq, sq] using hnap⟩
#align gaussian_int.sq_add_sq_of_nat_prime_of_not_irreducible GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible

theorem primeOfNatPrimeOfModFourEqThree (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) : Prime (p : ℤ[i]) :=
  irreducible_iff_prime.1 $
    Classical.by_contradiction $ fun hpi =>
      let ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
      have : ∀ a b : Zmod 4, a ^ 2 + b ^ 2 ≠ p := by erw [← Zmod.nat_cast_mod p 4, hp3] <;> exact dec_trivial
      this a b (hab ▸ by simp)
#align gaussian_int.prime_of_nat_prime_of_mod_four_eq_three GaussianInt.primeOfNatPrimeOfModFourEqThree

/-- A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4` -/
theorem prime_iff_mod_four_eq_three_of_nat_prime (p : ℕ) [hp : Fact p.Prime] : Prime (p : ℤ[i]) ↔ p % 4 = 3 :=
  ⟨mod_four_eq_three_of_nat_prime_of_prime p, primeOfNatPrimeOfModFourEqThree p⟩
#align gaussian_int.prime_iff_mod_four_eq_three_of_nat_prime GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime

end GaussianInt

