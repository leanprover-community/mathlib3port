/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module algebra.gcd_monoid.finset
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Fold
import Mathbin.Algebra.GcdMonoid.Multiset

/-!
# GCD and LCM operations on finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `finset.gcd` - the greatest common denominator of a `finset` of elements of a `gcd_monoid`
- `finset.lcm` - the least common multiple of a `finset` of elements of a `gcd_monoid`

## Implementation notes

Many of the proofs use the lemmas `gcd.def` and `lcm.def`, which relate `finset.gcd`
and `finset.lcm` to `multiset.gcd` and `multiset.lcm`.

TODO: simplify with a tactic and `data.finset.lattice`

## Tags

finset, gcd
-/


variable {α β γ : Type _}

namespace Finset

open Multiset

variable [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/


section Lcm

#print Finset.lcm /-
/-- Least common multiple of a finite set -/
def lcm (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.lcm 1 f
#align finset.lcm Finset.lcm
-/

variable {s s₁ s₂ : Finset β} {f : β → α}

/- warning: finset.lcm_def -> Finset.lcm_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f) (Multiset.lcm.{u1} α _inst_1 _inst_2 (Multiset.map.{u2, u1} β α f (Finset.val.{u2} β s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} α (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f) (Multiset.lcm.{u2} α _inst_1 _inst_2 (Multiset.map.{u1, u2} β α f (Finset.val.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align finset.lcm_def Finset.lcm_defₓ'. -/
theorem lcm_def : s.lcm f = (s.1.map f).lcm :=
  rfl
#align finset.lcm_def Finset.lcm_def

/- warning: finset.lcm_empty -> Finset.lcm_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α}, Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β)) f) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {f : β -> α}, Eq.{succ u2} α (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β)) f) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (MonoidWithZero.toMonoid.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.lcm_empty Finset.lcm_emptyₓ'. -/
@[simp]
theorem lcm_empty : (∅ : Finset β).lcm f = 1 :=
  fold_empty
#align finset.lcm_empty Finset.lcm_empty

/- warning: finset.lcm_dvd_iff -> Finset.lcm_dvd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} {a : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f) a) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (f b) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} {a : α}, Iff (Dvd.dvd.{u2} α (semigroupDvd.{u2} α (SemigroupWithZero.toSemigroup.{u2} α (MonoidWithZero.toSemigroupWithZero.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f) a) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (Dvd.dvd.{u2} α (semigroupDvd.{u2} α (SemigroupWithZero.toSemigroup.{u2} α (MonoidWithZero.toSemigroupWithZero.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (f b) a))
Case conversion may be inaccurate. Consider using '#align finset.lcm_dvd_iff Finset.lcm_dvd_iffₓ'. -/
@[simp]
theorem lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a :=
  by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩
#align finset.lcm_dvd_iff Finset.lcm_dvd_iff

#print Finset.lcm_dvd /-
theorem lcm_dvd {a : α} : (∀ b ∈ s, f b ∣ a) → s.lcm f ∣ a :=
  lcm_dvd_iff.2
#align finset.lcm_dvd Finset.lcm_dvd
-/

#print Finset.dvd_lcm /-
theorem dvd_lcm {b : β} (hb : b ∈ s) : f b ∣ s.lcm f :=
  lcm_dvd_iff.1 dvd_rfl _ hb
#align finset.dvd_lcm Finset.dvd_lcm
-/

#print Finset.lcm_insert /-
@[simp]
theorem lcm_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f) :=
  by
  by_cases h : b ∈ s
  ·
    rw [insert_eq_of_mem h,
      (lcm_eq_right_iff (f b) (s.lcm f) (Multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)]
  apply fold_insert h
#align finset.lcm_insert Finset.lcm_insert
-/

/- warning: finset.lcm_singleton -> Finset.lcm_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} {b : β}, Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b) f) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {f : β -> α} {b : β}, Eq.{succ u2} α (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b) f) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) (f b))
Case conversion may be inaccurate. Consider using '#align finset.lcm_singleton Finset.lcm_singletonₓ'. -/
@[simp]
theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) :=
  Multiset.lcm_singleton
#align finset.lcm_singleton Finset.lcm_singleton

/- warning: finset.normalize_lcm -> Finset.normalize_lcm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f)) (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.normalize_lcm Finset.normalize_lcmₓ'. -/
@[simp]
theorem normalize_lcm : normalize (s.lcm f) = s.lcm f := by simp [lcm_def]
#align finset.normalize_lcm Finset.normalize_lcm

#print Finset.lcm_union /-
theorem lcm_union [DecidableEq β] : (s₁ ∪ s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f) :=
  Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s has ih => by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]
#align finset.lcm_union Finset.lcm_union
-/

#print Finset.lcm_congr /-
theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.lcm f = s₂.lcm g :=
  by
  subst hs
  exact Finset.fold_congr hfg
#align finset.lcm_congr Finset.lcm_congr
-/

#print Finset.lcm_mono_fun /-
theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g :=
  lcm_dvd fun b hb => (h b hb).trans (dvd_lcm hb)
#align finset.lcm_mono_fun Finset.lcm_mono_fun
-/

#print Finset.lcm_mono /-
theorem lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f :=
  lcm_dvd fun b hb => dvd_lcm (h hb)
#align finset.lcm_mono Finset.lcm_mono
-/

/- warning: finset.lcm_image -> Finset.lcm_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {g : γ -> β} (s : Finset.{u3} γ), Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 (Finset.image.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) g s) f) (Finset.lcm.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} [_inst_3 : DecidableEq.{succ u3} β] {g : γ -> β} (s : Finset.{u2} γ), Eq.{succ u1} α (Finset.lcm.{u1, u3} α β _inst_1 _inst_2 (Finset.image.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) g s) f) (Finset.lcm.{u1, u2} α γ _inst_1 _inst_2 s (Function.comp.{succ u2, succ u3, succ u1} γ β α f g))
Case conversion may be inaccurate. Consider using '#align finset.lcm_image Finset.lcm_imageₓ'. -/
theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) : (s.image g).lcm f = s.lcm (f ∘ g) :=
  by classical induction' s using Finset.induction with c s hc ih <;> simp [*]
#align finset.lcm_image Finset.lcm_image

/- warning: finset.lcm_eq_lcm_image -> Finset.lcm_eq_lcm_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u1} α], Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.lcm.{u1, u1} α α _inst_1 _inst_2 (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_3 a b) f s) (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} α], Eq.{succ u2} α (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f) (Finset.lcm.{u2, u2} α α _inst_1 _inst_2 (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_3 a b) f s) (id.{succ u2} α))
Case conversion may be inaccurate. Consider using '#align finset.lcm_eq_lcm_image Finset.lcm_eq_lcm_imageₓ'. -/
theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id :=
  Eq.symm <| lcm_image _
#align finset.lcm_eq_lcm_image Finset.lcm_eq_lcm_image

/- warning: finset.lcm_eq_zero_iff -> Finset.lcm_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : Nontrivial.{u1} α], Iff (Eq.{succ u1} α (Finset.lcm.{u1, u2} α β _inst_1 _inst_2 s f) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))) (Set.image.{u2, u1} β α f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} [_inst_3 : Nontrivial.{u2} α], Iff (Eq.{succ u2} α (Finset.lcm.{u2, u1} α β _inst_1 _inst_2 s f) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (Set.image.{u1, u2} β α f (Finset.toSet.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align finset.lcm_eq_zero_iff Finset.lcm_eq_zero_iffₓ'. -/
theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ 0 ∈ f '' s := by
  simp only [Multiset.mem_map, lcm_def, Multiset.lcm_eq_zero_iff, Set.mem_image, mem_coe, ←
    Finset.mem_def]
#align finset.lcm_eq_zero_iff Finset.lcm_eq_zero_iff

end Lcm

/-! ### gcd -/


section Gcd

#print Finset.gcd /-
/-- Greatest common divisor of a finite set -/
def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f
#align finset.gcd Finset.gcd
-/

variable {s s₁ s₂ : Finset β} {f : β → α}

/- warning: finset.gcd_def -> Finset.gcd_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (Multiset.gcd.{u1} α _inst_1 _inst_2 (Multiset.map.{u2, u1} β α f (Finset.val.{u2} β s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f) (Multiset.gcd.{u2} α _inst_1 _inst_2 (Multiset.map.{u1, u2} β α f (Finset.val.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align finset.gcd_def Finset.gcd_defₓ'. -/
theorem gcd_def : s.gcd f = (s.1.map f).gcd :=
  rfl
#align finset.gcd_def Finset.gcd_def

/- warning: finset.gcd_empty -> Finset.gcd_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α}, Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β)) f) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {f : β -> α}, Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β)) f) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.gcd_empty Finset.gcd_emptyₓ'. -/
@[simp]
theorem gcd_empty : (∅ : Finset β).gcd f = 0 :=
  fold_empty
#align finset.gcd_empty Finset.gcd_empty

/- warning: finset.dvd_gcd_iff -> Finset.dvd_gcd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} {a : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f)) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} {a : α}, Iff (Dvd.dvd.{u2} α (semigroupDvd.{u2} α (SemigroupWithZero.toSemigroup.{u2} α (MonoidWithZero.toSemigroupWithZero.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) a (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f)) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) -> (Dvd.dvd.{u2} α (semigroupDvd.{u2} α (SemigroupWithZero.toSemigroup.{u2} α (MonoidWithZero.toSemigroupWithZero.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) a (f b)))
Case conversion may be inaccurate. Consider using '#align finset.dvd_gcd_iff Finset.dvd_gcd_iffₓ'. -/
theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b :=
  by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩
#align finset.dvd_gcd_iff Finset.dvd_gcd_iff

#print Finset.gcd_dvd /-
theorem gcd_dvd {b : β} (hb : b ∈ s) : s.gcd f ∣ f b :=
  dvd_gcd_iff.1 dvd_rfl _ hb
#align finset.gcd_dvd Finset.gcd_dvd
-/

#print Finset.dvd_gcd /-
theorem dvd_gcd {a : α} : (∀ b ∈ s, a ∣ f b) → a ∣ s.gcd f :=
  dvd_gcd_iff.2
#align finset.dvd_gcd Finset.dvd_gcd
-/

#print Finset.gcd_insert /-
@[simp]
theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) :=
  by
  by_cases h : b ∈ s
  ·
    rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h
#align finset.gcd_insert Finset.gcd_insert
-/

/- warning: finset.gcd_singleton -> Finset.gcd_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} {b : β}, Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b) f) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {f : β -> α} {b : β}, Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b) f) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) (f b))
Case conversion may be inaccurate. Consider using '#align finset.gcd_singleton Finset.gcd_singletonₓ'. -/
@[simp]
theorem gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b) :=
  Multiset.gcd_singleton
#align finset.gcd_singleton Finset.gcd_singleton

/- warning: finset.normalize_gcd -> Finset.normalize_gcd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} α (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f)) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α}, Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f)) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f)) (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f)
Case conversion may be inaccurate. Consider using '#align finset.normalize_gcd Finset.normalize_gcdₓ'. -/
@[simp]
theorem normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [gcd_def]
#align finset.normalize_gcd Finset.normalize_gcd

#print Finset.gcd_union /-
theorem gcd_union [DecidableEq β] : (s₁ ∪ s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f) :=
  Finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd])
    fun a s has ih => by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]
#align finset.gcd_union Finset.gcd_union
-/

#print Finset.gcd_congr /-
theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) : s₁.gcd f = s₂.gcd g :=
  by
  subst hs
  exact Finset.fold_congr hfg
#align finset.gcd_congr Finset.gcd_congr
-/

#print Finset.gcd_mono_fun /-
theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g :=
  dvd_gcd fun b hb => (gcd_dvd hb).trans (h b hb)
#align finset.gcd_mono_fun Finset.gcd_mono_fun
-/

#print Finset.gcd_mono /-
theorem gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f :=
  dvd_gcd fun b hb => gcd_dvd (h hb)
#align finset.gcd_mono Finset.gcd_mono
-/

/- warning: finset.gcd_image -> Finset.gcd_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} [_inst_3 : DecidableEq.{succ u2} β] {g : γ -> β} (s : Finset.{u3} γ), Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 (Finset.image.{u3, u2} γ β (fun (a : β) (b : β) => _inst_3 a b) g s) f) (Finset.gcd.{u1, u3} α γ _inst_1 _inst_2 s (Function.comp.{succ u3, succ u2, succ u1} γ β α f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {f : β -> α} [_inst_3 : DecidableEq.{succ u3} β] {g : γ -> β} (s : Finset.{u2} γ), Eq.{succ u1} α (Finset.gcd.{u1, u3} α β _inst_1 _inst_2 (Finset.image.{u2, u3} γ β (fun (a : β) (b : β) => _inst_3 a b) g s) f) (Finset.gcd.{u1, u2} α γ _inst_1 _inst_2 s (Function.comp.{succ u2, succ u3, succ u1} γ β α f g))
Case conversion may be inaccurate. Consider using '#align finset.gcd_image Finset.gcd_imageₓ'. -/
theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) : (s.image g).gcd f = s.gcd (f ∘ g) :=
  by classical induction' s using Finset.induction with c s hc ih <;> simp [*]
#align finset.gcd_image Finset.gcd_image

/- warning: finset.gcd_eq_gcd_image -> Finset.gcd_eq_gcd_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u1} α], Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.gcd.{u1, u1} α α _inst_1 _inst_2 (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_3 a b) f s) (id.{succ u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} [_inst_3 : DecidableEq.{succ u2} α], Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f) (Finset.gcd.{u2, u2} α α _inst_1 _inst_2 (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_3 a b) f s) (id.{succ u2} α))
Case conversion may be inaccurate. Consider using '#align finset.gcd_eq_gcd_image Finset.gcd_eq_gcd_imageₓ'. -/
theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id :=
  Eq.symm <| gcd_image _
#align finset.gcd_eq_gcd_image Finset.gcd_eq_gcd_image

/- warning: finset.gcd_eq_zero_iff -> Finset.gcd_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α}, Iff (Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (forall (x : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α}, Iff (Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (forall (x : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s) -> (Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (CommMonoidWithZero.toZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.gcd_eq_zero_iff Finset.gcd_eq_zero_iffₓ'. -/
theorem gcd_eq_zero_iff : s.gcd f = 0 ↔ ∀ x : β, x ∈ s → f x = 0 :=
  by
  rw [gcd_def, Multiset.gcd_eq_zero_iff]
  constructor <;> intro h
  · intro b bs
    apply h (f b)
    simp only [Multiset.mem_map, mem_def.1 bs]
    use b
    simp [mem_def.1 bs]
  · intro a as
    rw [Multiset.mem_map] at as
    rcases as with ⟨b, ⟨bs, rfl⟩⟩
    apply h b (mem_def.1 bs)
#align finset.gcd_eq_zero_iff Finset.gcd_eq_zero_iff

/- warning: finset.gcd_eq_gcd_filter_ne_zero -> Finset.gcd_eq_gcd_filter_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidablePred.{succ u2} β (fun (x : β) => Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))], Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β (fun (x : β) => Ne.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (fun (a : β) => Not.decidable (Eq.{succ u1} α (f a) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) (_inst_3 a)) s) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} [_inst_3 : DecidablePred.{succ u2} β (fun (x : β) => Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))], Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 (Finset.filter.{u2} β (fun (x : β) => Ne.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (fun (a : β) => instDecidableNot (Eq.{succ u1} α (f a) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (_inst_3 a)) s) f)
Case conversion may be inaccurate. Consider using '#align finset.gcd_eq_gcd_filter_ne_zero Finset.gcd_eq_gcd_filter_ne_zeroₓ'. -/
theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β => f x = 0] :
    s.gcd f = (s.filterₓ fun x => f x ≠ 0).gcd f := by
  classical
    trans ((s.filter fun x => f x = 0) ∪ s.filter fun x => f x ≠ 0).gcd f
    · rw [filter_union_filter_neg_eq]
    rw [gcd_union]
    trans GCDMonoid.gcd (0 : α) _
    · refine' congr (congr rfl _) rfl
      apply s.induction_on
      · simp
      intro a s has h
      rw [filter_insert]
      split_ifs with h1 <;> simp [h, h1]
    simp [gcd_zero_left, normalize_gcd]
#align finset.gcd_eq_gcd_filter_ne_zero Finset.gcd_eq_gcd_filter_ne_zero

/- warning: finset.gcd_mul_left -> Finset.gcd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} {a : α}, Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a (f x))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} {a : α}, Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))))) a (f x))) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MulZeroClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MulZeroOneClass.toMulZeroClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (MonoidWithZero.toMulZeroOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (CommMonoidWithZero.toMonoidWithZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) _inst_1)))))) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) a) (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f))
Case conversion may be inaccurate. Consider using '#align finset.gcd_mul_left Finset.gcd_mul_leftₓ'. -/
theorem gcd_mul_left {a : α} : (s.gcd fun x => a * f x) = normalize a * s.gcd f := by
  classical
    apply s.induction_on
    · simp
    intro b t hbt h
    rw [gcd_insert, gcd_insert, h, ← gcd_mul_left]
    apply ((normalize_associated a).mulRight _).gcd_eq_right
#align finset.gcd_mul_left Finset.gcd_mul_left

/- warning: finset.gcd_mul_right -> Finset.gcd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} {f : β -> α} {a : α}, Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (f x) a)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (_x : MonoidWithZeroHom.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => α -> α) (MonoidWithZeroHom.hasCoeToFun.{u1, u1} α α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (normalize.{u1} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u1} α _inst_1 _inst_2)) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u2} α] [_inst_2 : NormalizedGCDMonoid.{u2} α _inst_1] {s : Finset.{u1} β} {f : β -> α} {a : α}, Eq.{succ u2} α (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))))) (f x) a)) (HMul.hMul.{u2, u2, u2} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) α (instHMul.{u2} α (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))))) (Finset.gcd.{u2, u1} α β _inst_1 _inst_2 s f) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u2, u2} (MonoidWithZeroHom.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1)))) α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u2} α α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} α _inst_1))))))) (normalize.{u2} α _inst_1 (NormalizedGCDMonoid.toNormalizationMonoid.{u2} α _inst_1 _inst_2)) a))
Case conversion may be inaccurate. Consider using '#align finset.gcd_mul_right Finset.gcd_mul_rightₓ'. -/
theorem gcd_mul_right {a : α} : (s.gcd fun x => f x * a) = s.gcd f * normalize a := by
  classical
    apply s.induction_on
    · simp
    intro b t hbt h
    rw [gcd_insert, gcd_insert, h, ← gcd_mul_right]
    apply ((normalize_associated a).mulLeft _).gcd_eq_right
#align finset.gcd_mul_right Finset.gcd_mul_right

/- warning: finset.extract_gcd' -> Finset.extract_gcd' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} (f : β -> α) (g : β -> α), (Exists.{succ u2} β (fun (x : β) => And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) (Ne.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Eq.{succ u1} α (f b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (g b)))) -> (Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s g) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} (f : β -> α) (g : β -> α), (Exists.{succ u2} β (fun (x : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) (Ne.{succ u1} α (f x) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) -> (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (Eq.{succ u1} α (f b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (g b)))) -> (Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s g) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finset.extract_gcd' Finset.extract_gcd'ₓ'. -/
theorem extract_gcd' (f g : β → α) (hs : ∃ x, x ∈ s ∧ f x ≠ 0) (hg : ∀ b ∈ s, f b = s.gcd f * g b) :
    s.gcd g = 1 :=
  ((@mul_right_eq_self₀ _ _ (s.gcd f) _).1 <| by
        conv_lhs => rw [← normalize_gcd, ← gcd_mul_left, ← gcd_congr rfl hg]).resolve_right <|
    by
    contrapose! hs
    exact gcd_eq_zero_iff.1 hs
#align finset.extract_gcd' Finset.extract_gcd'

/- warning: finset.extract_gcd -> Finset.extract_gcd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{max (succ u2) (succ u1)} (β -> α) (fun (g : β -> α) => And (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Eq.{succ u1} α (f b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (g b)))) (Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s g) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : NormalizedGCDMonoid.{u1} α _inst_1] {s : Finset.{u2} β} (f : β -> α), (Finset.Nonempty.{u2} β s) -> (Exists.{max (succ u1) (succ u2)} (β -> α) (fun (g : β -> α) => And (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (Eq.{succ u1} α (f b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s f) (g b)))) (Eq.{succ u1} α (Finset.gcd.{u1, u2} α β _inst_1 _inst_2 s g) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align finset.extract_gcd Finset.extract_gcdₓ'. -/
theorem extract_gcd (f : β → α) (hs : s.Nonempty) :
    ∃ g : β → α, (∀ b ∈ s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by
  classical
    by_cases h : ∀ x ∈ s, f x = (0 : α)
    · refine' ⟨fun b => 1, fun b hb => by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], _⟩
      rw [gcd_eq_gcd_image, image_const hs, gcd_singleton, id, normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      have := fun b hb => _
      push_neg  at h
      refine' ⟨fun b => if hb : b ∈ s then g' hb else 0, this, extract_gcd' f _ h this⟩
      rw [dif_pos hb, hg hb]
#align finset.extract_gcd Finset.extract_gcd

end Gcd

end Finset

namespace Finset

section IsDomain

variable [CommRing α] [IsDomain α] [NormalizedGCDMonoid α]

/- warning: finset.gcd_eq_of_dvd_sub -> Finset.gcd_eq_of_dvd_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommRing.{u1} α] [_inst_2 : IsDomain.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))] [_inst_3 : NormalizedGCDMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2)] {s : Finset.{u2} β} {f : β -> α} {g : β -> α} {a : α}, (forall (x : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α _inst_1)))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) (f x) (g x)))) -> (Eq.{succ u1} α (GCDMonoid.gcd.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) (NormalizedGCDMonoid.toGcdMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3) a (Finset.gcd.{u1, u2} α β (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3 s f)) (GCDMonoid.gcd.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) (NormalizedGCDMonoid.toGcdMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3) a (Finset.gcd.{u1, u2} α β (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3 s g)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommRing.{u1} α] [_inst_2 : IsDomain.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_1))] [_inst_3 : NormalizedGCDMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2)] {s : Finset.{u2} β} {f : β -> α} {g : β -> α} {a : α}, (forall (x : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) x s) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α _inst_1)))))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (CommRing.toRing.{u1} α _inst_1))) (f x) (g x)))) -> (Eq.{succ u1} α (GCDMonoid.gcd.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) (NormalizedGCDMonoid.toGCDMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3) a (Finset.gcd.{u1, u2} α β (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3 s f)) (GCDMonoid.gcd.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) (NormalizedGCDMonoid.toGCDMonoid.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3) a (Finset.gcd.{u1, u2} α β (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1) _inst_2) _inst_3 s g)))
Case conversion may be inaccurate. Consider using '#align finset.gcd_eq_of_dvd_sub Finset.gcd_eq_of_dvd_subₓ'. -/
theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β → α} {a : α}
    (h : ∀ x : β, x ∈ s → a ∣ f x - g x) : GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) :=
  by
  classical
    revert h
    apply s.induction_on
    · simp
    intro b s bs hi h
    rw [gcd_insert, gcd_insert, gcd_comm (f b), ← gcd_assoc,
      hi fun x hx => h _ (mem_insert_of_mem hx), gcd_comm a, gcd_assoc,
      gcd_comm a (GCDMonoid.gcd _ _), gcd_comm (g b), gcd_assoc _ _ a, gcd_comm _ a]
    exact congr_arg _ (gcd_eq_of_dvd_sub_right (h _ (mem_insert_self _ _)))
#align finset.gcd_eq_of_dvd_sub Finset.gcd_eq_of_dvd_sub

end IsDomain

end Finset

