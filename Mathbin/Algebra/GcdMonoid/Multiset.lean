/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module algebra.gcd_monoid.multiset
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Data.Multiset.Fold

/-!
# GCD and LCM operations on multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `multiset.gcd` - the greatest common denominator of a `multiset` of elements of a `gcd_monoid`
- `multiset.lcm` - the least common multiple of a `multiset` of elements of a `gcd_monoid`

## Implementation notes

TODO: simplify with a tactic and `data.multiset.lattice`

## Tags

multiset, gcd
-/


namespace Multiset

variable {α : Type _} [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/


section Lcm

#print Multiset.lcm /-
/-- Least common multiple of a multiset -/
def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1
#align multiset.lcm Multiset.lcm
-/

/- warning: multiset.lcm_zero -> Multiset.lcm_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1], Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1], Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align multiset.lcm_zero Multiset.lcm_zeroₓ'. -/
@[simp]
theorem lcm_zero : (0 : Multiset α).lcm = 1 :=
  fold_zero _ _
#align multiset.lcm_zero Multiset.lcm_zero

#print Multiset.lcm_cons /-
@[simp]
theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm :=
  fold_cons_left _ _ _ _
#align multiset.lcm_cons Multiset.lcm_cons
-/

/- warning: multiset.lcm_singleton -> Multiset.lcm_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {a : α}, Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {a : α}, Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a)
Case conversion may be inaccurate. Consider using '#align multiset.lcm_singleton Multiset.lcm_singletonₓ'. -/
@[simp]
theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a :=
  (fold_singleton _ _ _).trans <| lcm_one_right _
#align multiset.lcm_singleton Multiset.lcm_singleton

#print Multiset.lcm_add /-
@[simp]
theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)
#align multiset.lcm_add Multiset.lcm_add
-/

#print Multiset.lcm_dvd /-
theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ ∀ b ∈ s, b ∣ a :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and, lcm_dvd_iff])
#align multiset.lcm_dvd Multiset.lcm_dvd
-/

#print Multiset.dvd_lcm /-
theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h
#align multiset.dvd_lcm Multiset.dvd_lcm
-/

#print Multiset.lcm_mono /-
theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
  lcm_dvd.2 fun b hb => dvd_lcm (h hb)
#align multiset.lcm_mono Multiset.lcm_mono
-/

/- warning: multiset.normalize_lcm -> Multiset.normalize_lcm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Multiset.lcm.{u1} α _inst_1 _inst_2 s)) (Multiset.lcm.{u1} α _inst_1 _inst_2 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) (Multiset.lcm.{u1} α _inst_1 _inst_2 s)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Multiset.lcm.{u1} α _inst_1 _inst_2 s)) (Multiset.lcm.{u1} α _inst_1 _inst_2 s)
Case conversion may be inaccurate. Consider using '#align multiset.normalize_lcm Multiset.normalize_lcmₓ'. -/
@[simp]
theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH => by simp
#align multiset.normalize_lcm Multiset.normalize_lcm

/- warning: multiset.lcm_eq_zero_iff -> Multiset.lcm_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] [_inst_3 : Nontrivial.{u1} α] (s : Multiset.{u1} α), Iff (Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] [_inst_3 : Nontrivial.{u1} α] (s : Multiset.{u1} α), Iff (Eq.{succ u1} α (Multiset.lcm.{u1} α _inst_1 _inst_2 s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align multiset.lcm_eq_zero_iff Multiset.lcm_eq_zero_iffₓ'. -/
@[simp]
theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ (0 : α) ∈ s :=
  by
  induction' s using Multiset.induction_on with a s ihs
  · simp only [lcm_zero, one_ne_zero, not_mem_zero]
  · simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a]
#align multiset.lcm_eq_zero_iff Multiset.lcm_eq_zero_iff

variable [DecidableEq α]

#print Multiset.lcm_dedup /-
@[simp]
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH =>
    by
    by_cases a ∈ s <;> simp [IH, h]
    unfold lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)
#align multiset.lcm_dedup Multiset.lcm_dedup
-/

#print Multiset.lcm_ndunion /-
@[simp]
theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp
#align multiset.lcm_ndunion Multiset.lcm_ndunion
-/

#print Multiset.lcm_union /-
@[simp]
theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp
#align multiset.lcm_union Multiset.lcm_union
-/

#print Multiset.lcm_ndinsert /-
@[simp]
theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm :=
  by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_cons]
  simp
#align multiset.lcm_ndinsert Multiset.lcm_ndinsert
-/

end Lcm

/-! ### gcd -/


section Gcd

#print Multiset.gcd /-
/-- Greatest common divisor of a multiset -/
def gcd (s : Multiset α) : α :=
  s.fold GCDMonoid.gcd 0
#align multiset.gcd Multiset.gcd
-/

/- warning: multiset.gcd_zero -> Multiset.gcd_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1], Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1], Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiset.gcd_zero Multiset.gcd_zeroₓ'. -/
@[simp]
theorem gcd_zero : (0 : Multiset α).gcd = 0 :=
  fold_zero _ _
#align multiset.gcd_zero Multiset.gcd_zero

#print Multiset.gcd_cons /-
@[simp]
theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd :=
  fold_cons_left _ _ _ _
#align multiset.gcd_cons Multiset.gcd_cons
-/

/- warning: multiset.gcd_singleton -> Multiset.gcd_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {a : α}, Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a)) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {a : α}, Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a)
Case conversion may be inaccurate. Consider using '#align multiset.gcd_singleton Multiset.gcd_singletonₓ'. -/
@[simp]
theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a :=
  (fold_singleton _ _ _).trans <| gcd_zero_right _
#align multiset.gcd_singleton Multiset.gcd_singleton

#print Multiset.gcd_add /-
@[simp]
theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)
#align multiset.gcd_add Multiset.gcd_add
-/

#print Multiset.dvd_gcd /-
theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and, dvd_gcd_iff])
#align multiset.dvd_gcd Multiset.dvd_gcd
-/

#print Multiset.gcd_dvd /-
theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h
#align multiset.gcd_dvd Multiset.gcd_dvd
-/

#print Multiset.gcd_mono /-
theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun b hb => gcd_dvd (h hb)
#align multiset.gcd_mono Multiset.gcd_mono
-/

/- warning: multiset.normalize_gcd -> Multiset.normalize_gcd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)
Case conversion may be inaccurate. Consider using '#align multiset.normalize_gcd Multiset.normalize_gcdₓ'. -/
@[simp]
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s IH => by simp
#align multiset.normalize_gcd Multiset.normalize_gcd

/- warning: multiset.gcd_eq_zero_iff -> Multiset.gcd_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Iff (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), Iff (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align multiset.gcd_eq_zero_iff Multiset.gcd_eq_zero_iffₓ'. -/
theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x : α, x ∈ s → x = 0 :=
  by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · apply s.induction_on
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx => h x (mem_cons_of_mem hx)]
#align multiset.gcd_eq_zero_iff Multiset.gcd_eq_zero_iff

/- warning: multiset.gcd_map_mul -> Multiset.gcd_map_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (Multiset.map.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a) s)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a) (Multiset.gcd.{u1} α _inst_1 _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1179 : α) (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1181 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1179 x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1181) a) s)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MulZeroClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MulZeroOneClass.toMulZeroClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MonoidWithZero.toMulZeroOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (CommMonoidWithZero.toMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) _inst_1)))))) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u1, u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a) (Multiset.gcd.{u1} α _inst_1 _inst_2 s))
Case conversion may be inaccurate. Consider using '#align multiset.gcd_map_mul Multiset.gcd_map_mulₓ'. -/
theorem gcd_map_mul (a : α) (s : Multiset α) : (s.map ((· * ·) a)).gcd = normalize a * s.gcd :=
  by
  refine' s.induction_on _ fun b s ih => _
  · simp_rw [map_zero, gcd_zero, mul_zero]
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right
#align multiset.gcd_map_mul Multiset.gcd_map_mul

section

variable [DecidableEq α]

#print Multiset.gcd_dedup /-
@[simp]
theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s IH =>
    by
    by_cases a ∈ s <;> simp [IH, h]
    unfold gcd
    rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same]
    apply (associated_normalize _).gcd_eq_left
#align multiset.gcd_dedup Multiset.gcd_dedup
-/

#print Multiset.gcd_ndunion /-
@[simp]
theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp
#align multiset.gcd_ndunion Multiset.gcd_ndunion
-/

#print Multiset.gcd_union /-
@[simp]
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp
#align multiset.gcd_union Multiset.gcd_union
-/

#print Multiset.gcd_ndinsert /-
@[simp]
theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd :=
  by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_cons]
  simp
#align multiset.gcd_ndinsert Multiset.gcd_ndinsert
-/

end

/- warning: multiset.extract_gcd' -> Multiset.extract_gcd' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α) (t : Multiset.{u1} α), (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) (Ne.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))))) -> (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.map.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) t)) -> (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 t) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α) (t : Multiset.{u1} α), (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) (Ne.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) -> (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1635 : α) (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1637 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1635 x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1637) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) t)) -> (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 t) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align multiset.extract_gcd' Multiset.extract_gcd'ₓ'. -/
theorem extract_gcd' (s t : Multiset α) (hs : ∃ x, x ∈ s ∧ x ≠ (0 : α))
    (ht : s = t.map ((· * ·) s.gcd)) : t.gcd = 1 :=
  ((@mul_right_eq_self₀ _ _ s.gcd _).1 <| by
        conv_lhs => rw [← normalize_gcd, ← gcd_map_mul, ← ht]).resolve_right <|
    by
    contrapose! hs
    exact s.gcd_eq_zero_iff.1 hs
#align multiset.extract_gcd' Multiset.extract_gcd'

/- warning: multiset.extract_gcd -> Multiset.extract_gcd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), (Ne.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (Exists.{succ u1} (Multiset.{u1} α) (fun (t : Multiset.{u1} α) => And (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.map.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) t)) (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 t) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] (s : Multiset.{u1} α), (Ne.{succ u1} (Multiset.{u1} α) s (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (Exists.{succ u1} (Multiset.{u1} α) (fun (t : Multiset.{u1} α) => And (Eq.{succ u1} (Multiset.{u1} α) s (Multiset.map.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1756 : α) (x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1758 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1756 x._@.Mathlib.Algebra.GCDMonoid.Multiset._hyg.1758) (Multiset.gcd.{u1} α _inst_1 _inst_2 s)) t)) (Eq.{succ u1} α (Multiset.gcd.{u1} α _inst_1 _inst_2 t) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align multiset.extract_gcd Multiset.extract_gcdₓ'. -/
theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map ((· * ·) s.gcd) ∧ t.gcd = 1 := by
  classical
    by_cases h : ∀ x ∈ s, x = (0 : α)
    · use replicate s.card 1
      rw [map_replicate, eq_replicate, mul_one, s.gcd_eq_zero_iff.2 h, ← nsmul_singleton, ←
        gcd_dedup]
      rw [dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @gcd_dvd _ _ _ s
      have := _
      push_neg  at h
      refine' ⟨s.pmap @f fun _ => id, this, extract_gcd' s _ h this⟩
      rw [map_pmap]
      conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ => id]
      congr with (x hx)
      rw [id, ← hf hx]
#align multiset.extract_gcd Multiset.extract_gcd

end Gcd

end Multiset

