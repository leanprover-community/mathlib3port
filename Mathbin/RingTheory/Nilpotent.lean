/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Algebra.Algebra.Bilinear
import Mathbin.RingTheory.Ideal.Operations

#align_import ring_theory.nilpotent from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# Nilpotent elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print IsNilpotent /-
/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
#align is_nilpotent IsNilpotent
-/

#print IsNilpotent.mk /-
theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩
#align is_nilpotent.mk IsNilpotent.mk
-/

#print IsNilpotent.zero /-
theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩
#align is_nilpotent.zero IsNilpotent.zero
-/

#print IsNilpotent.neg /-
theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, MulZeroClass.mul_zero]
#align is_nilpotent.neg IsNilpotent.neg
-/

#print isNilpotent_neg_iff /-
@[simp]
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩
#align is_nilpotent_neg_iff isNilpotent_neg_iff
-/

#print IsNilpotent.map /-
theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type _}
    [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) : IsNilpotent (f r) := by
  use hr.some; rw [← map_pow, hr.some_spec, map_zero]
#align is_nilpotent.map IsNilpotent.map
-/

#print IsReduced /-
/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type _) [Zero R] [Pow R ℕ] : Prop where
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced
-/

#print isReduced_of_noZeroDivisors /-
instance (priority := 900) isReduced_of_noZeroDivisors [MonoidWithZero R] [NoZeroDivisors R] :
    IsReduced R :=
  ⟨fun _ ⟨_, hn⟩ => pow_eq_zero hn⟩
#align is_reduced_of_no_zero_divisors isReduced_of_noZeroDivisors
-/

#print isReduced_of_subsingleton /-
instance (priority := 900) isReduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩
#align is_reduced_of_subsingleton isReduced_of_subsingleton
-/

#print IsNilpotent.eq_zero /-
theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h
#align is_nilpotent.eq_zero IsNilpotent.eq_zero
-/

#print isNilpotent_iff_eq_zero /-
@[simp]
theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩
#align is_nilpotent_iff_eq_zero isNilpotent_iff_eq_zero
-/

#print isReduced_of_injective /-
theorem isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type _}
    [MonoidWithZeroHomClass F R S] (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
#align is_reduced_of_injective isReduced_of_injective
-/

#print RingHom.ker_isRadical_iff_reduced_of_surjective /-
theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [CommRing S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker] <;> rfl
#align ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_isRadical_iff_reduced_of_surjective
-/

#print IsRadical /-
/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical
-/

#print zero_isRadical_iff /-
theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R := by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]; exact forall_swap
#align zero_is_radical_iff zero_isRadical_iff
-/

#print isRadical_iff_span_singleton /-
theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical :=
  by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp_distrib.symm)
#align is_radical_iff_span_singleton isRadical_iff_span_singleton
-/

#print isRadical_iff_pow_one_lt /-
theorem isRadical_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨fun h x => h k x, fun h =>
    k.cauchy_induction_mul (fun n h x hd => h x <| (pow_succ' x n).symm ▸ hd.hMul_right x) 0 hk
      (fun x hd => pow_one x ▸ hd) fun n _ hn x hd => h x <| hn _ <| (pow_mul x k n).subst hd⟩
#align is_radical_iff_pow_one_lt isRadical_iff_pow_one_lt
-/

#print isReduced_iff_pow_one_lt /-
theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]
#align is_reduced_iff_pow_one_lt isReduced_iff_pow_one_lt
-/

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

#print Commute.isNilpotent_add /-
theorem isNilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) :=
  by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m - 1
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, MulZeroClass.mul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj
  · rw [pow_eq_zero_of_le hi hn, MulZeroClass.zero_mul]
  · rw [pow_eq_zero_of_le hj hm, MulZeroClass.mul_zero]
#align commute.is_nilpotent_add Commute.isNilpotent_add
-/

#print Commute.isNilpotent_mul_left /-
theorem isNilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, MulZeroClass.zero_mul]
#align commute.is_nilpotent_mul_left Commute.isNilpotent_mul_left
-/

#print Commute.isNilpotent_mul_right /-
theorem isNilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) := by rw [h_comm.eq];
  exact h_comm.symm.is_nilpotent_mul_left h
#align commute.is_nilpotent_mul_right Commute.isNilpotent_mul_right
-/

end Semiring

section Ring

variable [Ring R] (h_comm : Commute x y)

#print Commute.isNilpotent_sub /-
theorem isNilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) :=
  by
  rw [← neg_right_iff] at h_comm 
  rw [← isNilpotent_neg_iff] at hy 
  rw [sub_eq_add_neg]
  exact h_comm.is_nilpotent_add hx hy
#align commute.is_nilpotent_sub Commute.isNilpotent_sub
-/

end Ring

end Commute

section CommSemiring

variable [CommSemiring R]

#print nilradical /-
/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type _) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical
-/

#print mem_nilradical /-
theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
#align mem_nilradical mem_nilradical
-/

#print nilradical_eq_sInf /-
theorem nilradical_eq_sInf (R : Type _) [CommSemiring R] :
    nilradical R = sInf {J : Ideal R | J.IsPrime} :=
  (Ideal.radical_eq_sInf ⊥).trans <| by simp_rw [and_iff_right bot_le]
#align nilradical_eq_Inf nilradical_eq_sInf
-/

#print nilpotent_iff_mem_prime /-
theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]; rfl
#align nilpotent_iff_mem_prime nilpotent_iff_mem_prime
-/

#print nilradical_le_prime /-
theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H
#align nilradical_le_prime nilradical_le_prime
-/

#print nilradical_eq_zero /-
@[simp]
theorem nilradical_eq_zero (R : Type _) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero
#align nilradical_eq_zero nilradical_eq_zero
-/

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

#print LinearMap.isNilpotent_mulLeft_iff /-
@[simp]
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_left_eq_zero_iff, pow_mul_left] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_left_iff LinearMap.isNilpotent_mulLeft_iff
-/

#print LinearMap.isNilpotent_mulRight_iff /-
@[simp]
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_right_eq_zero_iff, pow_mul_right] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_right_iff LinearMap.isNilpotent_mulRight_iff
-/

end LinearMap

namespace Module.End

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

#print Module.End.IsNilpotent.mapQ /-
theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) :=
  by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapq_pow, hk]
#align module.End.is_nilpotent.mapq Module.End.IsNilpotent.mapQ
-/

end Module.End

