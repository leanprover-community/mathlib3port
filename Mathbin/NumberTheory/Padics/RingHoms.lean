/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Data.Zmod.Basic
import NumberTheory.Padics.PadicIntegers

#align_import number_theory.padics.ring_homs from "leanprover-community/mathlib"@"f60c6087a7275b72d5db3c5a1d0e19e35a429c0a"

/-!

# Relating `ℤ_[p]` to `zmod (p ^ n)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we establish connections between the `p`-adic integers $\mathbb{Z}_p$
and the integers modulo powers of `p`, $\mathbb{Z}/p^n\mathbb{Z}$.

## Main declarations

We show that $\mathbb{Z}_p$ has a ring hom to $\mathbb{Z}/p^n\mathbb{Z}$ for each `n`.
The case for `n = 1` is handled separately, since it is used in the general construction
and we may want to use it without the `^1` getting in the way.
* `padic_int.to_zmod`: ring hom to `zmod p`
* `padic_int.to_zmod_pow`: ring hom to `zmod (p^n)`
* `padic_int.ker_to_zmod` / `padic_int.ker_to_zmod_pow`: the kernels of these maps are the ideals
  generated by `p^n`

We also establish the universal property of $\mathbb{Z}_p$ as a projective limit.
Given a family of compatible ring homs $f_k : R \to \mathbb{Z}/p^n\mathbb{Z}$,
there is a unique limit $R \to \mathbb{Z}_p$.
* `padic_int.lift`: the limit function
* `padic_int.lift_spec` / `padic_int.lift_unique`: the universal property

## Implementation notes

The ring hom constructions go through an auxiliary constructor `padic_int.to_zmod_hom`,
which removes some boilerplate code.

-/


noncomputable section

open scoped Classical

open Nat LocalRing Padic

namespace PadicInt

variable {p : ℕ} [hp_prime : Fact p.Prime]

section RingHoms

/-! ### Ring homomorphisms to `zmod p` and `zmod (p ^ n)` -/


variable (p) (r : ℚ)

#print PadicInt.modPart /-
/-- `mod_part p r` is an integer that satisfies
`‖(r - mod_part p r : ℚ_[p])‖ < 1` when `‖(r : ℚ_[p])‖ ≤ 1`,
see `padic_int.norm_sub_mod_part`.
It is the unique non-negative integer that is `< p` with this property.

(Note that this definition assumes `r : ℚ`.
See `padic_int.zmod_repr` for a version that takes values in `ℕ`
and works for arbitrary `x : ℤ_[p]`.) -/
def modPart : ℤ :=
  r.num * gcdA r.den p % p
#align padic_int.mod_part PadicInt.modPart
-/

variable {p}

#print PadicInt.modPart_lt_p /-
theorem modPart_lt_p : modPart p r < p :=
  by
  convert Int.emod_lt _ _
  · simp
  · exact_mod_cast hp_prime.1.NeZero
#align padic_int.mod_part_lt_p PadicInt.modPart_lt_p
-/

#print PadicInt.modPart_nonneg /-
theorem modPart_nonneg : 0 ≤ modPart p r :=
  Int.emod_nonneg _ <| by exact_mod_cast hp_prime.1.NeZero
#align padic_int.mod_part_nonneg PadicInt.modPart_nonneg
-/

#print PadicInt.isUnit_den /-
theorem isUnit_den (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) : IsUnit (r.den : ℤ_[p]) :=
  by
  rw [is_unit_iff]
  apply le_antisymm (r.denom : ℤ_[p]).2
  rw [← not_lt, val_eq_coe, coe_nat_cast]
  intro norm_denom_lt
  have hr : ‖(r * r.denom : ℚ_[p])‖ = ‖(r.num : ℚ_[p])‖ := by rw_mod_cast [@Rat.mul_den_eq_num r];
    rfl
  rw [padicNormE.mul] at hr
  have key : ‖(r.num : ℚ_[p])‖ < 1 := by
    calc
      _ = _ := hr.symm
      _ < 1 * 1 := (mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one)
      _ = 1 := mul_one 1
  have : ↑p ∣ r.num ∧ (p : ℤ) ∣ r.denom :=
    by
    simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_e_of_padic_int]
    norm_cast; exact ⟨key, norm_denom_lt⟩
  apply hp_prime.1.not_dvd_one
  rwa [← r.cop.gcd_eq_one, Nat.dvd_gcd_iff, ← Int.coe_nat_dvd_left, ← Int.coe_nat_dvd]
#align padic_int.is_unit_denom PadicInt.isUnit_den
-/

#print PadicInt.norm_sub_modPart_aux /-
theorem norm_sub_modPart_aux (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) :
    ↑p ∣ r.num - r.num * r.den.gcdA p % p * ↑r.den :=
  by
  rw [← ZMod.int_cast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_ofNat, ZMod.nat_cast_mod, Int.cast_mul, Int.cast_sub]
  have := congr_arg (coe : ℤ → ZMod p) (gcd_eq_gcd_ab r.denom p)
  simp only [Int.cast_ofNat, add_zero, Int.cast_add, ZMod.nat_cast_self, Int.cast_mul,
    MulZeroClass.zero_mul] at this
  push_cast
  rw [mul_right_comm, mul_assoc, ← this]
  suffices rdcp : r.denom.coprime p
  · rw [rdcp.gcd_eq_one]; simp only [mul_one, cast_one, sub_self]
  apply coprime.symm
  apply (coprime_or_dvd_of_prime hp_prime.1 _).resolve_right
  rw [← Int.coe_nat_dvd, ← norm_int_lt_one_iff_dvd, not_lt]
  apply ge_of_eq
  rw [← is_unit_iff]
  exact is_unit_denom r h
#align padic_int.norm_sub_mod_part_aux PadicInt.norm_sub_modPart_aux
-/

#print PadicInt.norm_sub_modPart /-
theorem norm_sub_modPart (h : ‖(r : ℚ_[p])‖ ≤ 1) : ‖(⟨r, h⟩ - modPart p r : ℤ_[p])‖ < 1 :=
  by
  let n := mod_part p r
  rw [norm_lt_one_iff_dvd, ← (is_unit_denom r h).dvd_mul_right]
  suffices ↑p ∣ r.num - n * r.denom
    by
    convert (Int.castRingHom ℤ_[p]).map_dvd this
    simp only [sub_mul, Int.cast_ofNat, eq_intCast, Int.cast_mul, sub_left_inj, Int.cast_sub]
    apply Subtype.coe_injective
    simp only [coe_mul, Subtype.coe_mk, coe_nat_cast]
    rw_mod_cast [@Rat.mul_den_eq_num r]; rfl
  exact norm_sub_mod_part_aux r h
#align padic_int.norm_sub_mod_part PadicInt.norm_sub_modPart
-/

#print PadicInt.exists_mem_range_of_norm_rat_le_one /-
theorem exists_mem_range_of_norm_rat_le_one (h : ‖(r : ℚ_[p])‖ ≤ 1) :
    ∃ n : ℤ, 0 ≤ n ∧ n < p ∧ ‖(⟨r, h⟩ - n : ℤ_[p])‖ < 1 :=
  ⟨modPart p r, modPart_nonneg _, modPart_lt_p _, norm_sub_modPart _ h⟩
#align padic_int.exists_mem_range_of_norm_rat_le_one PadicInt.exists_mem_range_of_norm_rat_le_one
-/

#print PadicInt.zmod_congr_of_sub_mem_span_aux /-
theorem zmod_congr_of_sub_mem_span_aux (n : ℕ) (x : ℤ_[p]) (a b : ℤ)
    (ha : x - a ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]))
    (hb : x - b ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p])) : (a : ZMod (p ^ n)) = b :=
  by
  rw [Ideal.mem_span_singleton] at ha hb
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.int_cast_zmod_eq_zero_iff_dvd, Int.coe_nat_pow]
  rw [← dvd_neg, neg_sub] at ha
  have := dvd_add ha hb
  rwa [sub_eq_add_neg, sub_eq_add_neg, add_assoc, neg_add_cancel_left, ← sub_eq_add_neg, ←
    Int.cast_sub, pow_p_dvd_int_iff] at this
#align padic_int.zmod_congr_of_sub_mem_span_aux PadicInt.zmod_congr_of_sub_mem_span_aux
-/

#print PadicInt.zmod_congr_of_sub_mem_span /-
theorem zmod_congr_of_sub_mem_span (n : ℕ) (x : ℤ_[p]) (a b : ℕ)
    (ha : x - a ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]))
    (hb : x - b ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p])) : (a : ZMod (p ^ n)) = b := by
  simpa using zmod_congr_of_sub_mem_span_aux n x a b ha hb
#align padic_int.zmod_congr_of_sub_mem_span PadicInt.zmod_congr_of_sub_mem_span
-/

#print PadicInt.zmod_congr_of_sub_mem_max_ideal /-
theorem zmod_congr_of_sub_mem_max_ideal (x : ℤ_[p]) (m n : ℕ) (hm : x - m ∈ maximalIdeal ℤ_[p])
    (hn : x - n ∈ maximalIdeal ℤ_[p]) : (m : ZMod p) = n :=
  by
  rw [maximal_ideal_eq_span_p] at hm hn
  have := zmod_congr_of_sub_mem_span_aux 1 x m n
  simp only [pow_one] at this
  specialize this hm hn
  apply_fun ZMod.castHom (show p ∣ p ^ 1 by rw [pow_one]) (ZMod p) at this
  simp only [map_intCast] at this
  simpa only [Int.cast_ofNat] using this
#align padic_int.zmod_congr_of_sub_mem_max_ideal PadicInt.zmod_congr_of_sub_mem_max_ideal
-/

variable (x : ℤ_[p])

#print PadicInt.exists_mem_range /-
theorem exists_mem_range : ∃ n : ℕ, n < p ∧ x - n ∈ maximalIdeal ℤ_[p] :=
  by
  simp only [maximal_ideal_eq_span_p, Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  obtain ⟨r, hr⟩ := rat_dense p (x : ℚ_[p]) zero_lt_one
  have H : ‖(r : ℚ_[p])‖ ≤ 1 := by
    rw [norm_sub_rev] at hr
    calc
      _ = ‖(r : ℚ_[p]) - x + x‖ := by ring_nf
      _ ≤ _ := (padicNormE.nonarchimedean _ _)
      _ ≤ _ := max_le (le_of_lt hr) x.2
  obtain ⟨n, hzn, hnp, hn⟩ := exists_mem_range_of_norm_rat_le_one r H
  lift n to ℕ using hzn
  use n
  constructor; · exact_mod_cast hnp
  simp only [norm_def, coe_sub, Subtype.coe_mk, coe_nat_cast] at hn ⊢
  rw [show (x - n : ℚ_[p]) = x - r + (r - n) by ring]
  apply lt_of_le_of_lt (padicNormE.nonarchimedean _ _)
  apply max_lt hr
  simpa using hn
#align padic_int.exists_mem_range PadicInt.exists_mem_range
-/

#print PadicInt.zmodRepr /-
/-- `zmod_repr x` is the unique natural number smaller than `p`
satisfying `‖(x - zmod_repr x : ℤ_[p])‖ < 1`.
-/
def zmodRepr : ℕ :=
  Classical.choose (exists_mem_range x)
#align padic_int.zmod_repr PadicInt.zmodRepr
-/

#print PadicInt.zmodRepr_spec /-
theorem zmodRepr_spec : zmodRepr x < p ∧ x - zmodRepr x ∈ maximalIdeal ℤ_[p] :=
  Classical.choose_spec (exists_mem_range x)
#align padic_int.zmod_repr_spec PadicInt.zmodRepr_spec
-/

#print PadicInt.zmodRepr_lt_p /-
theorem zmodRepr_lt_p : zmodRepr x < p :=
  (zmodRepr_spec _).1
#align padic_int.zmod_repr_lt_p PadicInt.zmodRepr_lt_p
-/

#print PadicInt.sub_zmodRepr_mem /-
theorem sub_zmodRepr_mem : x - zmodRepr x ∈ maximalIdeal ℤ_[p] :=
  (zmodRepr_spec _).2
#align padic_int.sub_zmod_repr_mem PadicInt.sub_zmodRepr_mem
-/

#print PadicInt.toZModHom /-
/-- `to_zmod_hom` is an auxiliary constructor for creating ring homs from `ℤ_[p]` to `zmod v`.
-/
def toZModHom (v : ℕ) (f : ℤ_[p] → ℕ) (f_spec : ∀ x, x - f x ∈ (Ideal.span {v} : Ideal ℤ_[p]))
    (f_congr :
      ∀ (x : ℤ_[p]) (a b : ℕ),
        x - a ∈ (Ideal.span {v} : Ideal ℤ_[p]) →
          x - b ∈ (Ideal.span {v} : Ideal ℤ_[p]) → (a : ZMod v) = b) :
    ℤ_[p] →+* ZMod v where
  toFun x := f x
  map_zero' := by
    rw [f_congr (0 : ℤ_[p]) _ 0, cast_zero]
    · exact f_spec _
    · simp only [sub_zero, cast_zero, Submodule.zero_mem]
  map_one' := by
    rw [f_congr (1 : ℤ_[p]) _ 1, cast_one]
    · exact f_spec _
    · simp only [sub_self, cast_one, Submodule.zero_mem]
  map_add' := by
    intro x y
    rw [f_congr (x + y) _ (f x + f y), cast_add]
    · exact f_spec _
    · convert Ideal.add_mem _ (f_spec x) (f_spec y)
      rw [cast_add]
      ring
  map_mul' := by
    intro x y
    rw [f_congr (x * y) _ (f x * f y), cast_mul]
    · exact f_spec _
    · let I : Ideal ℤ_[p] := Ideal.span {v}
      convert I.add_mem (I.mul_mem_left x (f_spec y)) (I.mul_mem_right (f y) (f_spec x))
      rw [cast_mul]
      ring
#align padic_int.to_zmod_hom PadicInt.toZModHom
-/

#print PadicInt.toZMod /-
/-- `to_zmod` is a ring hom from `ℤ_[p]` to `zmod p`,
with the equality `to_zmod x = (zmod_repr x : zmod p)`.
-/
def toZMod : ℤ_[p] →+* ZMod p :=
  toZModHom p zmodRepr (by rw [← maximal_ideal_eq_span_p]; exact sub_zmod_repr_mem)
    (by rw [← maximal_ideal_eq_span_p]; exact zmod_congr_of_sub_mem_max_ideal)
#align padic_int.to_zmod PadicInt.toZMod
-/

#print PadicInt.toZMod_spec /-
/-- `z - (to_zmod z : ℤ_[p])` is contained in the maximal ideal of `ℤ_[p]`, for every `z : ℤ_[p]`.

The coercion from `zmod p` to `ℤ_[p]` is `zmod.has_coe_t`,
which coerces `zmod p` into artibrary rings.
This is unfortunate, but a consequence of the fact that we allow `zmod p`
to coerce to rings of arbitrary characteristic, instead of only rings of characteristic `p`.
This coercion is only a ring homomorphism if it coerces into a ring whose characteristic divides
`p`. While this is not the case here we can still make use of the coercion.
-/
theorem toZMod_spec (z : ℤ_[p]) : z - (toZMod z : ℤ_[p]) ∈ maximalIdeal ℤ_[p] :=
  by
  convert sub_zmod_repr_mem z using 2
  dsimp [to_zmod, to_zmod_hom]
  rcases exists_eq_add_of_lt hp_prime.1.Pos with ⟨p', rfl⟩
  change ↑(ZMod.val _) = _
  simp only [ZMod.val_nat_cast, add_zero, add_def, Nat.cast_inj, zero_add]
  apply mod_eq_of_lt
  simpa only [zero_add] using zmod_repr_lt_p z
#align padic_int.to_zmod_spec PadicInt.toZMod_spec
-/

#print PadicInt.ker_toZMod /-
theorem ker_toZMod : (toZMod : ℤ_[p] →+* ZMod p).ker = maximalIdeal ℤ_[p] :=
  by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro h
    simpa only [h, ZMod.cast_zero, sub_zero] using to_zmod_spec x
  · intro h
    rw [← sub_zero x] at h
    dsimp [to_zmod, to_zmod_hom]
    convert zmod_congr_of_sub_mem_max_ideal x _ 0 _ h
    norm_cast; apply sub_zmod_repr_mem
#align padic_int.ker_to_zmod PadicInt.ker_toZMod
-/

#print PadicInt.appr /-
/-- `appr n x` gives a value `v : ℕ` such that `x` and `↑v : ℤ_p` are congruent mod `p^n`.
See `appr_spec`. -/
noncomputable irreducible_def appr : ℤ_[p] → ℕ → ℕ
  | x, 0 => 0
  | x, n + 1 =>
    let y := x - appr x n
    if hy : y = 0 then appr x n
    else
      let u := unitCoeff hy
      appr x n + p ^ n * (toZMod ((u : ℤ_[p]) * p ^ (y.Valuation - n).natAbs)).val
#align padic_int.appr PadicInt.appr
-/

#print PadicInt.appr_lt /-
theorem appr_lt (x : ℤ_[p]) (n : ℕ) : x.appr n < p ^ n :=
  by
  induction' n with n ih generalizing x
  · simp only [appr, succ_pos', pow_zero]
  simp only [appr, map_natCast, ZMod.nat_cast_self, RingHom.map_pow, Int.natAbs, RingHom.map_mul]
  have hp : p ^ n < p ^ (n + 1) := by apply pow_lt_pow hp_prime.1.one_lt (lt_add_one n)
  split_ifs with h
  · apply lt_trans (ih _) hp
  · calc
      _ < p ^ n + p ^ n * (p - 1) := _
      _ = p ^ (n + 1) := _
    · apply add_lt_add_of_lt_of_le (ih _)
      apply Nat.mul_le_mul_left
      apply le_pred_of_lt
      apply ZMod.val_lt
    · rw [mul_tsub, mul_one, ← pow_succ']
      apply add_tsub_cancel_of_le (le_of_lt hp)
#align padic_int.appr_lt PadicInt.appr_lt
-/

#print PadicInt.appr_mono /-
theorem appr_mono (x : ℤ_[p]) : Monotone x.appr :=
  by
  apply monotone_nat_of_le_succ
  intro n
  dsimp [appr]
  split_ifs; · rfl
  apply Nat.le_add_right
#align padic_int.appr_mono PadicInt.appr_mono
-/

#print PadicInt.dvd_appr_sub_appr /-
theorem dvd_appr_sub_appr (x : ℤ_[p]) (m n : ℕ) (h : m ≤ n) : p ^ m ∣ x.appr n - x.appr m :=
  by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  induction' k with k ih
  · simp only [add_zero, tsub_self, dvd_zero]
  rw [Nat.succ_eq_add_one, ← add_assoc]
  dsimp [appr]
  split_ifs with h
  · exact ih
  rw [add_comm, add_tsub_assoc_of_le (appr_mono _ (Nat.le_add_right m k))]
  apply dvd_add _ ih
  apply dvd_mul_of_dvd_left
  apply pow_dvd_pow _ (Nat.le_add_right m k)
#align padic_int.dvd_appr_sub_appr PadicInt.dvd_appr_sub_appr
-/

#print PadicInt.appr_spec /-
theorem appr_spec (n : ℕ) : ∀ x : ℤ_[p], x - appr x n ∈ (Ideal.span {p ^ n} : Ideal ℤ_[p]) :=
  by
  simp only [Ideal.mem_span_singleton]
  induction' n with n ih
  · simp only [isUnit_one, IsUnit.dvd, pow_zero, forall_true_iff]
  intro x
  dsimp only [appr]
  split_ifs with h
  · rw [h]; apply dvd_zero
  push_cast; rw [sub_add_eq_sub_sub]
  obtain ⟨c, hc⟩ := ih x
  simp only [map_natCast, ZMod.nat_cast_self, RingHom.map_pow, RingHom.map_mul, ZMod.nat_cast_val]
  have hc' : c ≠ 0 := by rintro rfl; simp only [MulZeroClass.mul_zero] at hc; contradiction
  conv_rhs =>
    congr
    simp only [hc]
  rw [show (x - ↑(appr x n)).Valuation = (↑p ^ n * c).Valuation by rw [hc]]
  rw [valuation_p_pow_mul _ _ hc', add_sub_cancel', pow_succ', ← mul_sub]
  apply mul_dvd_mul_left
  obtain hc0 | hc0 := c.valuation.nat_abs.eq_zero_or_pos
  · simp only [hc0, mul_one, pow_zero]
    rw [mul_comm, unit_coeff_spec h] at hc
    suffices c = unit_coeff h
      by
      rw [← this, ← Ideal.mem_span_singleton, ← maximal_ideal_eq_span_p]
      apply to_zmod_spec
    obtain ⟨c, rfl⟩ : IsUnit c :=
      by
      -- TODO: write a can_lift instance for units
      rw [Int.natAbs_eq_zero] at hc0
      rw [is_unit_iff, norm_eq_pow_val hc', hc0, neg_zero, zpow_zero]
    rw [DiscreteValuationRing.unit_mul_pow_congr_unit _ _ _ _ _ hc]
    exact irreducible_p
  · rw [zero_pow hc0]
    simp only [sub_zero, ZMod.cast_zero, MulZeroClass.mul_zero]
    rw [unit_coeff_spec hc']
    exact (dvd_pow_self (p : ℤ_[p]) hc0.ne').hMul_left _
#align padic_int.appr_spec PadicInt.appr_spec
-/

#print PadicInt.toZModPow /-
/-- A ring hom from `ℤ_[p]` to `zmod (p^n)`, with underlying function `padic_int.appr n`. -/
def toZModPow (n : ℕ) : ℤ_[p] →+* ZMod (p ^ n) :=
  toZModHom (p ^ n) (fun x => appr x n) (by intros; convert appr_spec n _ using 1; simp)
    (by
      intro x a b ha hb
      apply zmod_congr_of_sub_mem_span n x a b
      · simpa using ha
      · simpa using hb)
#align padic_int.to_zmod_pow PadicInt.toZModPow
-/

#print PadicInt.ker_toZModPow /-
theorem ker_toZModPow (n : ℕ) : (toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).ker = Ideal.span {p ^ n} :=
  by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro h
    suffices x.appr n = 0 by convert appr_spec n x; simp only [this, sub_zero, cast_zero]
    dsimp [to_zmod_pow, to_zmod_hom] at h
    rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd] at h
    apply eq_zero_of_dvd_of_lt h (appr_lt _ _)
  · intro h
    rw [← sub_zero x] at h
    dsimp [to_zmod_pow, to_zmod_hom]
    rw [zmod_congr_of_sub_mem_span n x _ 0 _ h, cast_zero]
    apply appr_spec
#align padic_int.ker_to_zmod_pow PadicInt.ker_toZModPow
-/

#print PadicInt.zmod_cast_comp_toZModPow /-
@[simp]
theorem zmod_cast_comp_toZModPow (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (toZModPow n) = toZModPow m :=
  by
  apply ZMod.ringHom_eq_of_ker_eq
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  simp only [Function.comp_apply, ZMod.castHom_apply, RingHom.coe_comp]
  simp only [to_zmod_pow, to_zmod_hom, RingHom.coe_mk]
  rw [ZMod.cast_nat_cast (pow_dvd_pow p h),
    zmod_congr_of_sub_mem_span m (x.appr n) (x.appr n) (x.appr m)]
  · rw [sub_self]; apply Ideal.zero_mem _
  · rw [Ideal.mem_span_singleton]
    rcases dvd_appr_sub_appr x m n h with ⟨c, hc⟩
    use c
    rw [← Nat.cast_sub (appr_mono _ h), hc, Nat.cast_mul, Nat.cast_pow]
  · infer_instance
#align padic_int.zmod_cast_comp_to_zmod_pow PadicInt.zmod_cast_comp_toZModPow
-/

#print PadicInt.cast_toZModPow /-
@[simp]
theorem cast_toZModPow (m n : ℕ) (h : m ≤ n) (x : ℤ_[p]) : ↑(toZModPow n x) = toZModPow m x := by
  rw [← zmod_cast_comp_to_zmod_pow _ _ h]; rfl
#align padic_int.cast_to_zmod_pow PadicInt.cast_toZModPow
-/

#print PadicInt.denseRange_nat_cast /-
theorem denseRange_nat_cast : DenseRange (Nat.cast : ℕ → ℤ_[p]) :=
  by
  intro x
  rw [Metric.mem_closure_range_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_neg_lt p hε
  use x.appr n
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ hn
  rw [norm_le_pow_iff_mem_span_pow]
  apply appr_spec
#align padic_int.dense_range_nat_cast PadicInt.denseRange_nat_cast
-/

#print PadicInt.denseRange_int_cast /-
theorem denseRange_int_cast : DenseRange (Int.cast : ℤ → ℤ_[p]) :=
  by
  intro x
  apply dense_range_nat_cast.induction_on x
  · exact isClosed_closure
  · intro a
    change (a.cast : ℤ_[p]) with (a : ℤ).cast
    apply subset_closure
    exact Set.mem_range_self _
#align padic_int.dense_range_int_cast PadicInt.denseRange_int_cast
-/

end RingHoms

section lift

/-! ### Universal property as projective limit -/


open CauSeq PadicSeq

variable {R : Type _} [NonAssocSemiring R] (f : ∀ k : ℕ, R →+* ZMod (p ^ k))
  (f_compat : ∀ (k1 k2) (hk : k1 ≤ k2), (ZMod.castHom (pow_dvd_pow p hk) _).comp (f k2) = f k1)

#print PadicInt.nthHom /-
/-- Given a family of ring homs `f : Π n : ℕ, R →+* zmod (p ^ n)`,
`nth_hom f r` is an integer-valued sequence
whose `n`th value is the unique integer `k` such that `0 ≤ k < p ^ n`
and `f n r = (k : zmod (p ^ n))`.
-/
def nthHom (r : R) : ℕ → ℤ := fun n => (f n r : ZMod (p ^ n)).val
#align padic_int.nth_hom PadicInt.nthHom
-/

#print PadicInt.nthHom_zero /-
@[simp]
theorem nthHom_zero : nthHom f 0 = 0 := by simp [nth_hom] <;> rfl
#align padic_int.nth_hom_zero PadicInt.nthHom_zero
-/

variable {f}

#print PadicInt.pow_dvd_nthHom_sub /-
theorem pow_dvd_nthHom_sub (r : R) (i j : ℕ) (h : i ≤ j) : ↑p ^ i ∣ nthHom f r j - nthHom f r i :=
  by
  specialize f_compat i j h
  rw [← Int.coe_nat_pow, ← ZMod.int_cast_zmod_eq_zero_iff_dvd, Int.cast_sub]
  dsimp [nth_hom]
  rw [← f_compat, RingHom.comp_apply]
  simp only [ZMod.cast_id, ZMod.castHom_apply, sub_self, ZMod.nat_cast_val, ZMod.int_cast_cast]
#align padic_int.pow_dvd_nth_hom_sub PadicInt.pow_dvd_nthHom_sub
-/

#print PadicInt.isCauSeq_nthHom /-
theorem isCauSeq_nthHom (r : R) : IsCauSeq (padicNorm p) fun n => nthHom f r n :=
  by
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (p ^ (-(↑(k : ℕ) : ℤ)) : ℚ) < ε := exists_pow_neg_lt_rat p hε
  use k
  intro j hj
  refine' lt_of_le_of_lt _ hk
  norm_cast
  rw [← padicNorm.dvd_iff_norm_le]
  exact_mod_cast pow_dvd_nth_hom_sub f_compat r k j hj
#align padic_int.is_cau_seq_nth_hom PadicInt.isCauSeq_nthHom
-/

#print PadicInt.nthHomSeq /-
/-- `nth_hom_seq f_compat r` bundles `padic_int.nth_hom f r`
as a Cauchy sequence of rationals with respect to the `p`-adic norm.
The `n`th value of the sequence is `((f n r).val : ℚ)`.
-/
def nthHomSeq (r : R) : PadicSeq p :=
  ⟨fun n => nthHom f r n, isCauSeq_nthHom f_compat r⟩
#align padic_int.nth_hom_seq PadicInt.nthHomSeq
-/

#print PadicInt.nthHomSeq_one /-
-- this lemma ran into issues after changing to `ne_zero` and I'm not sure why.
theorem nthHomSeq_one : nthHomSeq f_compat 1 ≈ 1 :=
  by
  intro ε hε
  change _ < _ at hε
  use 1
  intro j hj
  haveI : Fact (1 < p ^ j) := ⟨Nat.one_lt_pow _ _ (by linarith) hp_prime.1.one_lt⟩
  suffices ((1 : ZMod (p ^ j)) : ℚ) = 1 by simp [nth_hom_seq, nth_hom, this, hε]
  rw [ZMod.cast_eq_val, ZMod.val_one, Nat.cast_one]
#align padic_int.nth_hom_seq_one PadicInt.nthHomSeq_one
-/

#print PadicInt.nthHomSeq_add /-
theorem nthHomSeq_add (r s : R) :
    nthHomSeq f_compat (r + s) ≈ nthHomSeq f_compat r + nthHomSeq f_compat s :=
  by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_neg_lt_rat p hε
  use n
  intro j hj
  dsimp [nth_hom_seq]
  apply lt_of_le_of_lt _ hn
  rw [← Int.cast_add, ← Int.cast_sub, ← padicNorm.dvd_iff_norm_le, ←
    ZMod.int_cast_zmod_eq_zero_iff_dvd]
  dsimp [nth_hom]
  simp only [ZMod.nat_cast_val, RingHom.map_add, Int.cast_sub, ZMod.int_cast_cast, Int.cast_add]
  rw [ZMod.cast_add (show p ^ n ∣ p ^ j from pow_dvd_pow _ hj), sub_self]
  · infer_instance
#align padic_int.nth_hom_seq_add PadicInt.nthHomSeq_add
-/

#print PadicInt.nthHomSeq_mul /-
theorem nthHomSeq_mul (r s : R) :
    nthHomSeq f_compat (r * s) ≈ nthHomSeq f_compat r * nthHomSeq f_compat s :=
  by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_neg_lt_rat p hε
  use n
  intro j hj
  dsimp [nth_hom_seq]
  apply lt_of_le_of_lt _ hn
  rw [← Int.cast_mul, ← Int.cast_sub, ← padicNorm.dvd_iff_norm_le, ←
    ZMod.int_cast_zmod_eq_zero_iff_dvd]
  dsimp [nth_hom]
  simp only [ZMod.nat_cast_val, RingHom.map_mul, Int.cast_sub, ZMod.int_cast_cast, Int.cast_mul]
  rw [ZMod.cast_mul (show p ^ n ∣ p ^ j from pow_dvd_pow _ hj), sub_self]
  · infer_instance
#align padic_int.nth_hom_seq_mul PadicInt.nthHomSeq_mul
-/

#print PadicInt.limNthHom /-
/--
`lim_nth_hom f_compat r` is the limit of a sequence `f` of compatible ring homs `R →+* zmod (p^k)`.
This is itself a ring hom: see `padic_int.lift`.
-/
def limNthHom (r : R) : ℤ_[p] :=
  ofIntSeq (nthHom f r) (isCauSeq_nthHom f_compat r)
#align padic_int.lim_nth_hom PadicInt.limNthHom
-/

#print PadicInt.limNthHom_spec /-
theorem limNthHom_spec (r : R) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖limNthHom f_compat r - nthHom f r n‖ < ε :=
  by
  intro ε hε
  obtain ⟨ε', hε'0, hε'⟩ : ∃ v : ℚ, (0 : ℝ) < v ∧ ↑v < ε := exists_rat_btwn hε
  norm_cast at hε'0
  obtain ⟨N, hN⟩ := padicNormE.defn (nth_hom_seq f_compat r) hε'0
  use N
  intro n hn
  apply lt_trans _ hε'
  change ↑(padicNormE _) < _
  norm_cast
  exact hN _ hn
#align padic_int.lim_nth_hom_spec PadicInt.limNthHom_spec
-/

#print PadicInt.limNthHom_zero /-
theorem limNthHom_zero : limNthHom f_compat 0 = 0 := by simp [lim_nth_hom] <;> rfl
#align padic_int.lim_nth_hom_zero PadicInt.limNthHom_zero
-/

#print PadicInt.limNthHom_one /-
theorem limNthHom_one : limNthHom f_compat 1 = 1 :=
  Subtype.ext <| Quot.sound <| nthHomSeq_one _
#align padic_int.lim_nth_hom_one PadicInt.limNthHom_one
-/

#print PadicInt.limNthHom_add /-
theorem limNthHom_add (r s : R) :
    limNthHom f_compat (r + s) = limNthHom f_compat r + limNthHom f_compat s :=
  Subtype.ext <| Quot.sound <| nthHomSeq_add _ _ _
#align padic_int.lim_nth_hom_add PadicInt.limNthHom_add
-/

#print PadicInt.limNthHom_mul /-
theorem limNthHom_mul (r s : R) :
    limNthHom f_compat (r * s) = limNthHom f_compat r * limNthHom f_compat s :=
  Subtype.ext <| Quot.sound <| nthHomSeq_mul _ _ _
#align padic_int.lim_nth_hom_mul PadicInt.limNthHom_mul
-/

#print PadicInt.lift /-
-- TODO: generalize this to arbitrary complete discrete valuation rings
/-- `lift f_compat` is the limit of a sequence `f` of compatible ring homs `R →+* zmod (p^k)`,
with the equality `lift f_compat r = padic_int.lim_nth_hom f_compat r`.
-/
def lift : R →+* ℤ_[p] where
  toFun := limNthHom f_compat
  map_one' := limNthHom_one f_compat
  map_mul' := limNthHom_mul f_compat
  map_zero' := limNthHom_zero f_compat
  map_add' := limNthHom_add f_compat
#align padic_int.lift PadicInt.lift
-/

#print PadicInt.lift_sub_val_mem_span /-
theorem lift_sub_val_mem_span (r : R) (n : ℕ) :
    lift f_compat r - (f n r).val ∈ (Ideal.span {↑p ^ n} : Ideal ℤ_[p]) :=
  by
  obtain ⟨k, hk⟩ :=
    lim_nth_hom_spec f_compat r _
      (show (0 : ℝ) < p ^ (-n : ℤ) from Nat.zpow_pos_of_pos hp_prime.1.Pos _)
  have := le_of_lt (hk (max n k) (le_max_right _ _))
  rw [norm_le_pow_iff_mem_span_pow] at this
  dsimp [lift]
  rw [sub_eq_sub_add_sub (lim_nth_hom f_compat r) _ ↑(nth_hom f r (max n k))]
  apply Ideal.add_mem _ _ this
  rw [Ideal.mem_span_singleton]
  simpa only [eq_intCast, RingHom.map_pow, Int.cast_sub] using
    (Int.castRingHom ℤ_[p]).map_dvd (pow_dvd_nth_hom_sub f_compat r n (max n k) (le_max_left _ _))
#align padic_int.lift_sub_val_mem_span PadicInt.lift_sub_val_mem_span
-/

#print PadicInt.lift_spec /-
/-- One part of the universal property of `ℤ_[p]` as a projective limit.
See also `padic_int.lift_unique`.
-/
theorem lift_spec (n : ℕ) : (toZModPow n).comp (lift f_compat) = f n :=
  by
  ext r
  rw [RingHom.comp_apply, ← ZMod.nat_cast_zmod_val (f n r), ← map_natCast <| to_zmod_pow n, ←
    sub_eq_zero, ← RingHom.map_sub, ← RingHom.mem_ker, ker_to_zmod_pow]
  apply lift_sub_val_mem_span
#align padic_int.lift_spec PadicInt.lift_spec
-/

#print PadicInt.lift_unique /-
/-- One part of the universal property of `ℤ_[p]` as a projective limit.
See also `padic_int.lift_spec`.
-/
theorem lift_unique (g : R →+* ℤ_[p]) (hg : ∀ n, (toZModPow n).comp g = f n) : lift f_compat = g :=
  by
  ext1 r
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_neg_lt p hε
  apply le_trans _ (le_of_lt hn)
  rw [dist_eq_norm, norm_le_pow_iff_mem_span_pow, ← ker_to_zmod_pow, RingHom.mem_ker,
    RingHom.map_sub, ← RingHom.comp_apply, ← RingHom.comp_apply, lift_spec, hg, sub_self]
#align padic_int.lift_unique PadicInt.lift_unique
-/

#print PadicInt.lift_self /-
@[simp]
theorem lift_self (z : ℤ_[p]) : @lift p _ ℤ_[p] _ toZModPow zmod_cast_comp_toZModPow z = z :=
  by
  show _ = RingHom.id _ z
  rw [@lift_unique p _ ℤ_[p] _ _ zmod_cast_comp_to_zmod_pow (RingHom.id ℤ_[p])]
  intro; rw [RingHom.comp_id]
#align padic_int.lift_self PadicInt.lift_self
-/

end lift

#print PadicInt.ext_of_toZModPow /-
theorem ext_of_toZModPow {x y : ℤ_[p]} : (∀ n, toZModPow n x = toZModPow n y) ↔ x = y :=
  by
  constructor
  · intro h
    rw [← lift_self x, ← lift_self y]
    simp [lift, lim_nth_hom, nth_hom, h]
  · rintro rfl _; rfl
#align padic_int.ext_of_to_zmod_pow PadicInt.ext_of_toZModPow
-/

#print PadicInt.toZModPow_eq_iff_ext /-
theorem toZModPow_eq_iff_ext {R : Type _} [NonAssocSemiring R] {g g' : R →+* ℤ_[p]} :
    (∀ n, (toZModPow n).comp g = (toZModPow n).comp g') ↔ g = g' :=
  by
  constructor
  · intro hg
    ext x : 1
    apply ext_of_to_zmod_pow.mp
    intro n
    show (to_zmod_pow n).comp g x = (to_zmod_pow n).comp g' x
    rw [hg n]
  · rintro rfl _; rfl
#align padic_int.to_zmod_pow_eq_iff_ext PadicInt.toZModPow_eq_iff_ext
-/

end PadicInt

