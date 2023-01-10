/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module ring_theory.nilpotent
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Algebra.Algebra.Bilinear
import Mathbin.RingTheory.Ideal.Operations

/-!
# Nilpotent elements

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

-/


universe u v

variable {R S : Type u} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
#align is_nilpotent IsNilpotent

theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩
#align is_nilpotent.mk IsNilpotent.mk

theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩
#align is_nilpotent.zero IsNilpotent.zero

theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, mul_zero]
#align is_nilpotent.neg IsNilpotent.neg

@[simp]
theorem is_nilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩
#align is_nilpotent_neg_iff is_nilpotent_neg_iff

theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type _}
    [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) : IsNilpotent (f r) :=
  by
  use hr.some
  rw [← map_pow, hr.some_spec, map_zero]
#align is_nilpotent.map IsNilpotent.map

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type _) [Zero R] [Pow R ℕ] : Prop where
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced

instance (priority := 900) is_reduced_of_no_zero_divisors [MonoidWithZero R] [NoZeroDivisors R] :
    IsReduced R :=
  ⟨fun _ ⟨_, hn⟩ => pow_eq_zero hn⟩
#align is_reduced_of_no_zero_divisors is_reduced_of_no_zero_divisors

instance (priority := 900) is_reduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩
#align is_reduced_of_subsingleton is_reduced_of_subsingleton

theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h
#align is_nilpotent.eq_zero IsNilpotent.eq_zero

@[simp]
theorem is_nilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩
#align is_nilpotent_iff_eq_zero is_nilpotent_iff_eq_zero

theorem is_reduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type _}
    [MonoidWithZeroHomClass F R S] (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
#align is_reduced_of_injective is_reduced_of_injective

theorem RingHom.ker_is_radical_iff_reduced_of_surjective {S F} [CommSemiring R] [CommRing S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [is_reduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker] <;> rfl
#align
  ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_is_radical_iff_reduced_of_surjective

theorem Ideal.is_radical_iff_quotient_reduced [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) :=
  by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_is_radical_iff_reduced_of_surjective (@Ideal.Quotient.mk_surjective R _ I)
#align ideal.is_radical_iff_quotient_reduced Ideal.is_radical_iff_quotient_reduced

/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical

theorem zero_is_radical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R :=
  by
  simp_rw [is_reduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_swap
#align zero_is_radical_iff zero_is_radical_iff

theorem is_radical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical :=
  by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp_distrib.symm)
#align is_radical_iff_span_singleton is_radical_iff_span_singleton

theorem is_radical_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨fun h x => h k x, fun h =>
    k.cauchy_induction_mul (fun n h x hd => h x <| (pow_succ' x n).symm ▸ hd.mul_right x) 0 hk
      (fun x hd => pow_one x ▸ hd) fun n _ hn x hd => h x <| hn _ <| (pow_mul x k n).subst hd⟩
#align is_radical_iff_pow_one_lt is_radical_iff_pow_one_lt

theorem is_reduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_is_radical_iff, is_radical_iff_pow_one_lt k hk, zero_dvd_iff]
#align is_reduced_iff_pow_one_lt is_reduced_iff_pow_one_lt

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

include h_comm

theorem is_nilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) :=
  by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m - 1
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj
  · rw [pow_eq_zero_of_le hi hn, zero_mul]
  · rw [pow_eq_zero_of_le hj hm, mul_zero]
#align commute.is_nilpotent_add Commute.is_nilpotent_add

theorem is_nilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, zero_mul]
#align commute.is_nilpotent_mul_left Commute.is_nilpotent_mul_left

theorem is_nilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) :=
  by
  rw [h_comm.eq]
  exact h_comm.symm.is_nilpotent_mul_left h
#align commute.is_nilpotent_mul_right Commute.is_nilpotent_mul_right

end Semiring

section Ring

variable [Ring R] (h_comm : Commute x y)

include h_comm

theorem is_nilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) :=
  by
  rw [← neg_right_iff] at h_comm
  rw [← is_nilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.is_nilpotent_add hx hy
#align commute.is_nilpotent_sub Commute.is_nilpotent_sub

end Ring

end Commute

section CommSemiring

variable [CommSemiring R]

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type _) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical

theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
#align mem_nilradical mem_nilradical

theorem nilradical_eq_Inf (R : Type _) [CommSemiring R] :
    nilradical R = infₛ { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_Inf ⊥).trans <| by simp_rw [and_iff_right bot_le]
#align nilradical_eq_Inf nilradical_eq_Inf

theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J :=
  by
  rw [← mem_nilradical, nilradical_eq_Inf, Submodule.mem_Inf]
  rfl
#align nilpotent_iff_mem_prime nilpotent_iff_mem_prime

theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_Inf R).symm ▸ infₛ_le H
#align nilradical_le_prime nilradical_le_prime

@[simp]
theorem nilradical_eq_zero (R : Type _) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => is_nilpotent_iff_eq_zero
#align nilradical_eq_zero nilradical_eq_zero

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem is_nilpotent_mul_left_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_left_eq_zero_iff, pow_mul_left] at hn⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_left_iff LinearMap.is_nilpotent_mul_left_iff

@[simp]
theorem is_nilpotent_mul_right_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_right_eq_zero_iff, pow_mul_right] at hn⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_right_iff LinearMap.is_nilpotent_mul_right_iff

end LinearMap

namespace Module.EndCat

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

variable {f : Module.EndCat R M} {p : Submodule R M} (hp : p ≤ p.comap f)

theorem IsNilpotent.mapq (hnp : IsNilpotent f) : IsNilpotent (p.mapq p f hp) :=
  by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapq_pow, hk]
#align module.End.is_nilpotent.mapq Module.EndCat.IsNilpotent.mapq

end Module.EndCat

section Ideal

variable [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)

/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, Prop}
    (h₁ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, I ^ 2 = ⊥ → P I)
    (h₂ :
      ∀ ⦃S : Type _⦄ [CommRing S],
        ∀ I J : Ideal S, I ≤ J → P I → P (J.map (Ideal.Quotient.mk I)) → P J) :
    P I := by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  revert S
  apply Nat.strong_induction_on n
  clear n
  intro n H S _ I hI
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot, zero_pow]
    exact zero_lt_two
  cases n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    haveI := subsingleton_of_bot_eq_top hI.symm
    exact (hI' (Subsingleton.elim _ _)).elim
  cases n
  · rw [pow_one] at hI
    exact (hI' hI).elim
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  · apply H n.succ _ (I ^ 2)
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      exact Ideal.pow_le_pow (by linarith)
    · exact le_refl n.succ.succ
  · apply h₁
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
#align ideal.is_nilpotent.induction_on Ideal.IsNilpotent.induction_on

theorem IsNilpotent.is_unit_quotient_mk_iff {R : Type _} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x :=
  by
  refine' ⟨_, fun h => h.map I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    skip
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one, _root_.map_mul, hy, IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    have : (x * y - 1) ^ 2 = 0 := by
      rw [← Ideal.mem_bot, ← e]
      exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 :=
      by
      rw [eq_comm, ← sub_eq_zero, ← this]
      ring
    exact isUnit_of_mul_eq_one _ _ this
#align is_nilpotent.is_unit_quotient_mk_iff IsNilpotent.is_unit_quotient_mk_iff

end Ideal

