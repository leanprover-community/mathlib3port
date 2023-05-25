/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module group_theory.exponent
! leanprover-community/mathlib commit 52fa514ec337dd970d71d8de8d0fd68b455a1e54
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Quotient
import Mathbin.GroupTheory.NoncommPiCoprod
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.Algebra.GcdMonoid.Finset
import Mathbin.Data.Nat.Factorization.Basic
import Mathbin.Tactic.ByContra

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `monoid.exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `add_monoid.exponent_exists` the additive version of `monoid.exponent_exists`.
* `add_monoid.exponent` the additive version of `monoid.exponent`.

## Main results

* `monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `finset.lcm` of the order of its elements.
* `monoid.exponent_eq_supr_order_of(')`: For a commutative cancel monoid, the exponent is
  equal to `⨆ g : G, order_of g` (or zero if it has any order-zero elements).

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/


universe u

variable {G : Type u}

open Classical

namespace Monoid

section Monoid

variable (G) [Monoid G]

#print Monoid.ExponentExists /-
/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive
      "A predicate on an additive monoid saying that there is a positive integer `n` such\n  that `n • g = 0` for all `g`."]
def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1
#align monoid.exponent_exists Monoid.ExponentExists
#align add_monoid.exponent_exists AddMonoid.ExponentExists
-/

#print Monoid.exponent /-
/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[to_additive
      "The exponent of an additive group is the smallest positive integer `n` such that\n  `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
  if h : ExponentExists G then Nat.find h else 0
#align monoid.exponent Monoid.exponent
#align add_monoid.exponent AddMonoid.exponent
-/

variable {G}

#print Monoid.exponentExists_iff_ne_zero /-
@[to_additive]
theorem exponentExists_iff_ne_zero : ExponentExists G ↔ exponent G ≠ 0 :=
  by
  rw [exponent]
  split_ifs
  · simp [h, @not_lt_zero' ℕ]
  --if this isn't done this way, `to_additive` freaks
  · tauto
#align monoid.exponent_exists_iff_ne_zero Monoid.exponentExists_iff_ne_zero
#align add_monoid.exponent_exists_iff_ne_zero AddMonoid.exponentExists_iff_ne_zero
-/

#print Monoid.exponent_eq_zero_iff /-
@[to_additive]
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G := by
  simp only [exponent_exists_iff_ne_zero, Classical.not_not]
#align monoid.exponent_eq_zero_iff Monoid.exponent_eq_zero_iff
#align add_monoid.exponent_eq_zero_iff AddMonoid.exponent_eq_zero_iff
-/

#print Monoid.exponent_eq_zero_of_order_zero /-
@[to_additive]
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun ⟨n, hn, hgn⟩ => orderOf_eq_zero_iff'.mp hg n hn <| hgn g
#align monoid.exponent_eq_zero_of_order_zero Monoid.exponent_eq_zero_of_order_zero
#align add_monoid.exponent_eq_zero_of_order_zero AddMonoid.exponent_eq_zero_addOrder_zero
-/

/- warning: monoid.pow_exponent_eq_one -> Monoid.pow_exponent_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g (Monoid.exponent.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g (Monoid.exponent.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align monoid.pow_exponent_eq_one Monoid.pow_exponent_eq_oneₓ'. -/
@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 :=
  by
  by_cases exponent_exists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_spec h).2 g
  · simp_rw [exponent, dif_neg h, pow_zero]
#align monoid.pow_exponent_eq_one Monoid.pow_exponent_eq_one
#align add_monoid.exponent_nsmul_eq_zero AddMonoid.exponent_nsmul_eq_zero

#print Monoid.pow_eq_mod_exponent /-
@[to_additive]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by rw [Nat.mod_add_div]
    _ = g ^ (n % exponent G) := by simp [pow_add, pow_mul, pow_exponent_eq_one]
    
#align monoid.pow_eq_mod_exponent Monoid.pow_eq_mod_exponent
#align add_monoid.nsmul_eq_mod_exponent AddMonoid.nsmul_eq_mod_exponent
-/

/- warning: monoid.exponent_pos_of_exists -> Monoid.exponent_pos_of_exists is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (n : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_1)))))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Monoid.exponent.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (n : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_1)))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Monoid.exponent.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align monoid.exponent_pos_of_exists Monoid.exponent_pos_of_existsₓ'. -/
@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : 0 < exponent G :=
  by
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1 := ⟨n, hpos, hG⟩
  rw [exponent, dif_pos]
  exact (Nat.find_spec h).1
#align monoid.exponent_pos_of_exists Monoid.exponent_pos_of_exists
#align add_monoid.exponent_pos_of_exists AddMonoid.exponent_pos_of_exists

/- warning: monoid.exponent_min' -> Monoid.exponent_min' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (n : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_1)))))) -> (LE.le.{0} Nat Nat.hasLe (Monoid.exponent.{u1} G _inst_1) n)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (n : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_1)))) -> (LE.le.{0} Nat instLENat (Monoid.exponent.{u1} G _inst_1) n)
Case conversion may be inaccurate. Consider using '#align monoid.exponent_min' Monoid.exponent_min'ₓ'. -/
@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n :=
  by
  rw [exponent, dif_pos]
  · apply Nat.find_min'
    exact ⟨hpos, hG⟩
  · exact ⟨n, hpos, hG⟩
#align monoid.exponent_min' Monoid.exponent_min'
#align add_monoid.exponent_min' AddMonoid.exponent_min'

/- warning: monoid.exponent_min -> Monoid.exponent_min is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (m : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LT.lt.{0} Nat Nat.hasLt m (Monoid.exponent.{u1} G _inst_1)) -> (Exists.{succ u1} G (fun (g : G) => Ne.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g m) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] (m : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LT.lt.{0} Nat instLTNat m (Monoid.exponent.{u1} G _inst_1)) -> (Exists.{succ u1} G (fun (g : G) => Ne.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_1)) g m) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align monoid.exponent_min Monoid.exponent_minₓ'. -/
@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 :=
  by
  by_contra' h
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  linarith
#align monoid.exponent_min Monoid.exponent_min
#align add_monoid.exponent_min AddMonoid.exponent_min

#print Monoid.exp_eq_one_of_subsingleton /-
@[simp, to_additive]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 :=
  by
  apply le_antisymm
  · apply exponent_min' _ Nat.one_pos
    simp
  · apply Nat.succ_le_of_lt
    apply exponent_pos_of_exists 1 Nat.one_pos
    simp
#align monoid.exp_eq_one_of_subsingleton Monoid.exp_eq_one_of_subsingleton
#align add_monoid.exp_eq_zero_of_subsingleton AddMonoid.exp_eq_zero_of_subsingleton
-/

#print Monoid.order_dvd_exponent /-
@[to_additive add_order_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  orderOf_dvd_of_pow_eq_one <| pow_exponent_eq_one g
#align monoid.order_dvd_exponent Monoid.order_dvd_exponent
#align add_monoid.add_order_dvd_exponent AddMonoid.addOrder_dvd_exponent
-/

variable (G)

/- warning: monoid.exponent_dvd_of_forall_pow_eq_one -> Monoid.exponent_dvd_of_forall_pow_eq_one is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : Monoid.{u1} G] (n : Nat), (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_2)) g n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_2)))))) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Monoid.exponent.{u1} G _inst_2) n)
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : Monoid.{u1} G] (n : Nat), (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_2)) g n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_2)))) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Monoid.exponent.{u1} G _inst_2) n)
Case conversion may be inaccurate. Consider using '#align monoid.exponent_dvd_of_forall_pow_eq_one Monoid.exponent_dvd_of_forall_pow_eq_oneₓ'. -/
@[to_additive]
theorem exponent_dvd_of_forall_pow_eq_one (G) [Monoid G] (n : ℕ) (hG : ∀ g : G, g ^ n = 1) :
    exponent G ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · exact dvd_zero _
  apply Nat.dvd_of_mod_eq_zero
  by_contra h
  have h₁ := Nat.pos_of_ne_zero h
  have h₂ : n % exponent G < exponent G := Nat.mod_lt _ (exponent_pos_of_exists n hpos hG)
  have h₃ : exponent G ≤ n % exponent G :=
    by
    apply exponent_min' _ h₁
    simp_rw [← pow_eq_mod_exponent]
    exact hG
  linarith
#align monoid.exponent_dvd_of_forall_pow_eq_one Monoid.exponent_dvd_of_forall_pow_eq_one
#align add_monoid.exponent_dvd_of_forall_nsmul_eq_zero AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero

/- warning: monoid.lcm_order_of_dvd_exponent -> Monoid.lcm_orderOf_dvd_exponent is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Monoid.{u1} G] [_inst_2 : Fintype.{u1} G], Dvd.Dvd.{0} Nat Nat.hasDvd (Finset.lcm.{0, u1} Nat G Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid (Finset.univ.{u1} G _inst_2) (orderOf.{u1} G _inst_1)) (Monoid.exponent.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Monoid.{u1} G] [_inst_2 : Fintype.{u1} G], Dvd.dvd.{0} Nat Nat.instDvdNat (Finset.lcm.{0, u1} Nat G Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero (Finset.univ.{u1} G _inst_2) (orderOf.{u1} G _inst_1)) (Monoid.exponent.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid.lcm_order_of_dvd_exponent Monoid.lcm_orderOf_dvd_exponentₓ'. -/
@[to_additive lcm_add_order_of_dvd_exponent]
theorem lcm_orderOf_dvd_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf ∣ exponent G :=
  by
  apply Finset.lcm_dvd
  intro g hg
  exact order_dvd_exponent g
#align monoid.lcm_order_of_dvd_exponent Monoid.lcm_orderOf_dvd_exponent
#align add_monoid.lcm_add_order_of_dvd_exponent AddMonoid.lcm_addOrderOf_dvd_exponent

#print Nat.Prime.exists_orderOf_eq_pow_factorization_exponent /-
@[to_additive exists_order_of_eq_pow_padic_val_nat_add_exponent]
theorem Nat.Prime.exists_orderOf_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p :=
  by
  haveI := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine' ⟨1, by rw [h, pow_zero, orderOf_one]⟩
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 :=
    by
    suffices key : ¬exponent G ∣ exponent G / p
    · simpa using mt (exponent_dvd_of_forall_pow_eq_one G (exponent G / p)) key
    exact fun hd =>
      hp.one_lt.not_le
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvd he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_factorization h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.ord_proj_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (finsupp.mem_support_iff.mp h)
  refine' ⟨g ^ k, _⟩
  rw [ht]
  apply orderOf_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ', ← mul_assoc, Nat.mul_div_cancel _ hp.pos, pow_mul] at hg
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mul, mul_comm, ← hk]
    exact pow_exponent_eq_one g
#align nat.prime.exists_order_of_eq_pow_factorization_exponent Nat.Prime.exists_orderOf_eq_pow_factorization_exponent
#align nat.prime.exists_order_of_eq_pow_padic_val_nat_add_exponent Nat.Prime.exists_addOrderOf_eq_pow_padic_val_nat_add_exponent
-/

variable {G}

#print Monoid.exponent_ne_zero_iff_range_orderOf_finite /-
@[to_additive]
theorem exponent_ne_zero_iff_range_orderOf_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.range (orderOf : G → ℕ)).Finite :=
  by
  refine' ⟨fun he => _, fun he => _⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_gt h (exponent G)
    exact pow_ne_one_of_lt_orderOf' he het (pow_exponent_eq_one t)
  · lift Set.range orderOf to Finset ℕ using he with t ht
    have htpos : 0 < t.prod id :=
      by
      refine' Finset.prod_pos fun a ha => _
      rw [← Finset.mem_coe, ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h, zero_dvd_iff] at this
      exact htpos.ne' this
    refine' exponent_dvd_of_forall_pow_eq_one _ _ fun g => _
    rw [pow_eq_mod_orderOf, Nat.mod_eq_zero_of_dvd, pow_zero g]
    apply Finset.dvd_prod_of_mem
    rw [← Finset.mem_coe, ht]
    exact Set.mem_range_self g
#align monoid.exponent_ne_zero_iff_range_order_of_finite Monoid.exponent_ne_zero_iff_range_orderOf_finite
#align add_monoid.exponent_ne_zero_iff_range_order_of_finite AddMonoid.exponent_ne_zero_iff_range_addOrderOf_finite
-/

#print Monoid.exponent_eq_zero_iff_range_orderOf_infinite /-
@[to_additive]
theorem exponent_eq_zero_iff_range_orderOf_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.range (orderOf : G → ℕ)).Infinite :=
  by
  have := exponent_ne_zero_iff_range_orderOf_finite h
  rwa [Ne.def, not_iff_comm, Iff.comm] at this
#align monoid.exponent_eq_zero_iff_range_order_of_infinite Monoid.exponent_eq_zero_iff_range_orderOf_infinite
#align add_monoid.exponent_eq_zero_iff_range_order_of_infinite AddMonoid.exponent_eq_zero_iff_range_addOrderOf_infinite
-/

/- warning: monoid.lcm_order_eq_exponent -> Monoid.lcm_order_eq_exponent is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Finset.lcm.{0, u1} Nat G Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid (Finset.univ.{u1} G _inst_2) (orderOf.{u1} G _inst_1)) (Monoid.exponent.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Monoid.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Finset.lcm.{0, u1} Nat G Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero (Finset.univ.{u1} G _inst_2) (orderOf.{u1} G _inst_1)) (Monoid.exponent.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid.lcm_order_eq_exponent Monoid.lcm_order_eq_exponentₓ'. -/
@[to_additive lcm_add_order_eq_exponent]
theorem lcm_order_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G :=
  by
  apply Nat.dvd_antisymm (lcm_order_of_dvd_exponent G)
  refine' exponent_dvd_of_forall_pow_eq_one G _ fun g => _
  obtain ⟨m, hm⟩ : orderOf g ∣ finset.univ.lcm orderOf := Finset.dvd_lcm (Finset.mem_univ g)
  rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
#align monoid.lcm_order_eq_exponent Monoid.lcm_order_eq_exponent
#align add_monoid.lcm_add_order_eq_exponent AddMonoid.lcm_addOrder_eq_exponent

end Monoid

section LeftCancelMonoid

variable [LeftCancelMonoid G]

#print Monoid.exponent_ne_zero_of_finite /-
@[to_additive]
theorem exponent_ne_zero_of_finite [Finite G] : exponent G ≠ 0 :=
  by
  cases nonempty_fintype G
  simpa [← lcm_order_eq_exponent, Finset.lcm_eq_zero_iff] using fun x => (orderOf_pos x).ne'
#align monoid.exponent_ne_zero_of_finite Monoid.exponent_ne_zero_of_finite
#align add_monoid.exponent_ne_zero_of_finite AddMonoid.exponent_ne_zero_of_finite
-/

end LeftCancelMonoid

section CommMonoid

variable [CommMonoid G]

#print Monoid.exponent_eq_iSup_orderOf /-
@[to_additive]
theorem exponent_eq_iSup_orderOf (h : ∀ g : G, 0 < orderOf g) : exponent G = ⨆ g : G, orderOf g :=
  by
  rw [iSup]
  rcases eq_or_ne (exponent G) 0 with (he | he)
  · rw [he, Set.Infinite.Nat.sSup_eq_zero <| (exponent_eq_zero_iff_range_order_of_infinite h).1 he]
  have hne : (Set.range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, orderOf_one⟩
  have hfin : (Set.range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_order_of_finite h]
  obtain ⟨t, ht⟩ := hne.cSup_mem hfin
  apply Nat.dvd_antisymm _
  · rw [← ht]
    apply order_dvd_exponent
  refine' Nat.dvd_of_factors_subperm he _
  rw [List.subperm_ext_iff]
  by_contra' h
  obtain ⟨p, hp, hpe⟩ := h
  replace hp := Nat.prime_of_mem_factors hp
  simp only [Nat.factors_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_order_of_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g)
    by
    rw [ht] at this
    exact this.not_le (le_csSup hfin.bdd_above <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.ord_proj_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [orderOf_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_right hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).coprime (orderOf g) :=
    by
    rw [hg, Nat.coprime_pow_right_iff (pos_of_gt hpe), Nat.coprime_comm]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 1 [← pow_one p]
    convert Nat.pow_succ_factorization_not_dvd (h <| t ^ p ^ k).ne' hp
    rw [hpk', Nat.factorization_div hpk]
    simp [hp]
  rw [(Commute.all _ g).orderOf_mul_eq_mul_orderOf_of_coprime hcoprime, hpk', hg, ha, ← ht, ← hk,
    pow_add, pow_add, pow_one, ← mul_assoc, ← mul_assoc, Nat.div_mul_cancel, mul_assoc,
    lt_mul_iff_one_lt_right <| h t, ← pow_succ']
  exact one_lt_pow hp.one_lt a.succ_ne_zero
  exact hpk
#align monoid.exponent_eq_supr_order_of Monoid.exponent_eq_iSup_orderOf
#align add_monoid.exponent_eq_supr_order_of AddMonoid.exponent_eq_iSup_addOrderOf
-/

#print Monoid.exponent_eq_iSup_orderOf' /-
@[to_additive]
theorem exponent_eq_iSup_orderOf' :
    exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g :=
  by
  split_ifs
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
  · have := not_exists.mp h
    exact exponent_eq_supr_order_of fun g => Ne.bot_lt <| this g
#align monoid.exponent_eq_supr_order_of' Monoid.exponent_eq_iSup_orderOf'
#align add_monoid.exponent_eq_supr_order_of' AddMonoid.exponent_eq_iSup_addOrderOf'
-/

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid G]

/- warning: monoid.exponent_eq_max'_order_of -> Monoid.exponent_eq_max'_orderOf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Monoid.exponent.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.max'.{0} Nat Nat.linearOrder (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2)) (Exists.intro.{1} Nat (fun (x : Nat) => Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) x (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Eq.mpr.{0} (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) True) (Eq.trans.{1} Prop (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Exists.{succ u1} G (fun (a : G) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))))) True (Eq.trans.{1} Prop (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Exists.{succ u1} G (fun (a : G) => Exists.{0} (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Exists.{succ u1} G (fun (a : G) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))))) (propext (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Exists.{succ u1} G (fun (a : G) => Exists.{0} (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.mem_image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) ((fun (p : G -> Prop) (p_1 : G -> Prop) (e_1 : Eq.{succ u1} (G -> Prop) p p_1) => congr_arg.{succ u1, 1} (G -> Prop) Prop p p_1 (Exists.{succ u1} G) e_1) (fun (a : G) => Exists.{0} (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : G) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) (funext.{succ u1, 1} G (fun (x : G) => Prop) (fun (x : G) => Exists.{0} (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) x (Finset.univ.{u1} G _inst_2)) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) x (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (x : G) => (fun (x_1 : True) => Eq.{succ u1} G x (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) True.intro) (fun (a : G) => Eq.trans.{1} Prop (Exists.{0} (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Exists.{0} True (fun (h : True) => (fun (h : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) (Iff.mpr (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) True ((fun {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (x : α) => iff_true_intro (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.univ.{u1} α _inst_1)) (Finset.mem_univ.{u1} α _inst_1 x)) G _inst_2 a) h))) ((fun (x : True) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) True.intro) (exists_prop_congr' (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) True (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (fun (h : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) (fun (h : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) a (Finset.univ.{u1} G _inst_2)) => orderOf_eq_one_iff.{u1} G a (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) ((fun {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (x : α) => iff_true_intro (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.univ.{u1} α _inst_1)) (Finset.mem_univ.{u1} α _inst_1 x)) G _inst_2 a)) (propext (Exists.{0} True (fun (x : True) => (fun (x : True) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) x)) ((fun (x : True) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))) True.intro) (exists_true_left (fun (x : True) => Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))))))))) (propext (Exists.{succ u1} G (fun (a : G) => Eq.{succ u1} G ((fun (a : G) => a) a) ((fun (a : G) => a) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))))))) True ((fun {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (a' : α) => iff_true_intro (Exists.{succ u1} α (fun (a : α) => Eq.{succ u1} β (f a) (f a'))) (exists_apply_eq_apply.{succ u1, succ u1} α β f a')) G G (fun (a : G) => a) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))))))) trivial)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CancelCommMonoid.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Monoid.exponent.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.max'.{0} Nat Nat.linearOrder (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2)) (Exists.intro.{1} Nat (fun (x : Nat) => Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) x (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (of_eq_true (Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Eq.trans.{1} Prop (Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Exists.{succ u1} G (fun (x : G) => Eq.{succ u1} G x (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))) True (Eq.trans.{1} Prop (Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Finset.image.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2))) (Exists.{succ u1} G (fun (a : G) => And (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) a (Finset.univ.{u1} G _inst_2)) (Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Exists.{succ u1} G (fun (x : G) => Eq.{succ u1} G x (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))) (Mathlib.Data.Finset.Image._auxLemma.23.{u1, 0} G Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))) (Finset.univ.{u1} G _inst_2) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (congrArg.{succ u1, 1} (G -> Prop) Prop (fun (x : G) => And (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) x (Finset.univ.{u1} G _inst_2)) (Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x : G) => Eq.{succ u1} G x (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))) (Exists.{succ u1} G) (funext.{succ u1, 1} G (fun (x : G) => Prop) (fun (x : G) => And (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) x (Finset.univ.{u1} G _inst_2)) (Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x : G) => Eq.{succ u1} G x (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))) (fun (a : G) => Eq.trans.{1} Prop (And (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) a (Finset.univ.{u1} G _inst_2)) (Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (And True (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))) (congr.{1, 1} Prop Prop (And (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) a (Finset.univ.{u1} G _inst_2))) (And True) (Eq.{1} Nat (orderOf.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))) a) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))))) (congrArg.{1, 1} Prop (Prop -> Prop) (Membership.mem.{u1, u1} G (Finset.{u1} G) (Finset.instMembershipFinset.{u1} G) a (Finset.univ.{u1} G _inst_2)) True And (Mathlib.Data.Fintype.Basic._auxLemma.1.{u1} G _inst_2 a)) (Mathlib.GroupTheory.OrderOfElement._auxLemma.8.{u1} G a (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1))))) (true_and (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))))))) (Std.Logic._auxLemma.35.{succ u1} G (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (RightCancelMonoid.toMonoid.{u1} G (CancelMonoid.toRightCancelMonoid.{u1} G (CancelCommMonoid.toCancelMonoid.{u1} G _inst_1)))))))))))
Case conversion may be inaccurate. Consider using '#align monoid.exponent_eq_max'_order_of Monoid.exponent_eq_max'_orderOfₓ'. -/
@[to_additive]
theorem exponent_eq_max'_orderOf [Fintype G] :
    exponent G = ((@Finset.univ G _).image orderOf).max' ⟨1, by simp⟩ :=
  by
  rw [← Finset.Nonempty.cSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← iSup]
  exact exponent_eq_supr_order_of orderOf_pos
#align monoid.exponent_eq_max'_order_of Monoid.exponent_eq_max'_orderOf
#align add_monoid.exponent_eq_max'_order_of AddMonoid.exponent_eq_max'_addOrderOf

end CancelCommMonoid

end Monoid

section CommGroup

open Subgroup

open BigOperators

variable (G) [CommGroup G] [Group.FG G]

#print card_dvd_exponent_pow_rank /-
@[to_additive]
theorem card_dvd_exponent_pow_rank : Nat.card G ∣ Monoid.exponent G ^ Group.rank G :=
  by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Finset.card_univ, ← Finset.prod_const]
  let f : (∀ g : S, zpowers (g : G)) →* G := noncomm_pi_coprod fun s t h x y hx hy => mul_comm x y
  have hf : Function.Surjective f :=
    by
    rw [← MonoidHom.range_top_iff_surjective, eq_top_iff, ← hS2, closure_le]
    exact fun g hg => ⟨Pi.mulSingle ⟨g, hg⟩ ⟨g, mem_zpowers g⟩, noncomm_pi_coprod_mul_single _ _⟩
  replace hf := nat_card_dvd_of_surjective f hf
  rw [Nat.card_pi] at hf
  refine' hf.trans (Finset.prod_dvd_prod_of_dvd _ _ fun g hg => _)
  rw [← order_eq_card_zpowers']
  exact Monoid.order_dvd_exponent (g : G)
#align card_dvd_exponent_pow_rank card_dvd_exponent_pow_rank
#align card_dvd_exponent_nsmul_rank card_dvd_exponent_nsmul_rank
-/

/- warning: card_dvd_exponent_pow_rank' -> card_dvd_exponent_pow_rank' is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : CommGroup.{u1} G] [_inst_2 : Group.FG.{u1} G (CommGroup.toGroup.{u1} G _inst_1)] {n : Nat}, (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) g n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))))) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Nat.card.{u1} G) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) n (Group.rank.{u1} G (CommGroup.toGroup.{u1} G _inst_1) _inst_2)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : CommGroup.{u1} G] [_inst_2 : Group.FG.{u1} G (CommGroup.toGroup.{u1} G _inst_1)] {n : Nat}, (forall (g : G), Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))) g n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1)))))))) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Nat.card.{u1} G) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) n (Group.rank.{u1} G (CommGroup.toGroup.{u1} G _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align card_dvd_exponent_pow_rank' card_dvd_exponent_pow_rank'ₓ'. -/
@[to_additive]
theorem card_dvd_exponent_pow_rank' {n : ℕ} (hG : ∀ g : G, g ^ n = 1) :
    Nat.card G ∣ n ^ Group.rank G :=
  (card_dvd_exponent_pow_rank G).trans
    (pow_dvd_pow_of_dvd (Monoid.exponent_dvd_of_forall_pow_eq_one G n hG) (Group.rank G))
#align card_dvd_exponent_pow_rank' card_dvd_exponent_pow_rank'
#align card_dvd_exponent_nsmul_rank' card_dvd_exponent_nsmul_rank'

end CommGroup

