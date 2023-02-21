/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finsupp.indicator
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Defs

/-!
# Building finitely supported functions off finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `finsupp.indicator`: Turns a map from a `finset` into a `finsupp` from the entire type.
-/


noncomputable section

open Finset Function

variable {ι α : Type _}

namespace Finsupp

variable [Zero α] {s : Finset ι} (f : ∀ i ∈ s, α) {i : ι}

#print Finsupp.indicator /-
/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : ι →₀ α
    where
  toFun i :=
    haveI := Classical.decEq ι
    if H : i ∈ s then f i H else 0
  support :=
    haveI := Classical.decEq α
    (s.attach.filter fun i : s => f i.1 i.2 ≠ 0).map (embedding.subtype _)
  mem_support_toFun i := by
    letI := Classical.decEq α
    rw [mem_map, dite_ne_right_iff]
    exact
      ⟨fun ⟨⟨j, hj⟩, hf, rfl⟩ => ⟨hj, (mem_filter.1 hf).2⟩, fun ⟨hi, hf⟩ =>
        ⟨⟨i, hi⟩, mem_filter.2 <| ⟨mem_attach _ _, hf⟩, rfl⟩⟩
#align finsupp.indicator Finsupp.indicator
-/

/- warning: finsupp.indicator_of_mem -> Finsupp.indicator_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] {s : Finset.{u1} ι} {i : ι} (hi : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α), Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_1) (fun (_x : Finsupp.{u1, u2} ι α _inst_1) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_1) (Finsupp.indicator.{u1, u2} ι α _inst_1 s f) i) (f i hi)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] {s : Finset.{u2} ι} {i : ι} (hi : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (f : forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_1) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α _inst_1) (Finsupp.indicator.{u2, u1} ι α _inst_1 s f) i) (f i hi)
Case conversion may be inaccurate. Consider using '#align finsupp.indicator_of_mem Finsupp.indicator_of_memₓ'. -/
theorem indicator_of_mem (hi : i ∈ s) (f : ∀ i ∈ s, α) : indicator s f i = f i hi :=
  @dif_pos _ (id _) hi _ _ _
#align finsupp.indicator_of_mem Finsupp.indicator_of_mem

/- warning: finsupp.indicator_of_not_mem -> Finsupp.indicator_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] {s : Finset.{u1} ι} {i : ι}, (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) -> (forall (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α), Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_1) (fun (_x : Finsupp.{u1, u2} ι α _inst_1) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_1) (Finsupp.indicator.{u1, u2} ι α _inst_1 s f) i) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α _inst_1))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] {s : Finset.{u2} ι} {i : ι}, (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) -> (forall (f : forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_1) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α _inst_1) (Finsupp.indicator.{u2, u1} ι α _inst_1 s f) i) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.indicator_of_not_mem Finsupp.indicator_of_not_memₓ'. -/
theorem indicator_of_not_mem (hi : i ∉ s) (f : ∀ i ∈ s, α) : indicator s f i = 0 :=
  @dif_neg _ (id _) hi _ _ _
#align finsupp.indicator_of_not_mem Finsupp.indicator_of_not_mem

variable (s i)

/- warning: finsupp.indicator_apply -> Finsupp.indicator_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] (s : Finset.{u1} ι) (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α) (i : ι) [_inst_2 : DecidableEq.{succ u1} ι], Eq.{succ u2} α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_1) (fun (_x : Finsupp.{u1, u2} ι α _inst_1) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_1) (Finsupp.indicator.{u1, u2} ι α _inst_1 s f) i) (dite.{succ u2} α (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (Finset.decidableMem.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) (fun (hi : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => f i hi) (fun (hi : Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) => OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α _inst_1))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] (s : Finset.{u2} ι) (f : forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α) (i : ι) [_inst_2 : DecidableEq.{succ u2} ι], Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_1) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α _inst_1) (Finsupp.indicator.{u2, u1} ι α _inst_1 s f) i) (dite.{succ u1} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (Finset.decidableMem.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) (fun (hi : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => f i hi) (fun (hi : Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) => OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.indicator_apply Finsupp.indicator_applyₓ'. -/
@[simp]
theorem indicator_apply [DecidableEq ι] : indicator s f i = if hi : i ∈ s then f i hi else 0 := by
  convert rfl
#align finsupp.indicator_apply Finsupp.indicator_apply

/- warning: finsupp.indicator_injective -> Finsupp.indicator_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] (s : Finset.{u1} ι), Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α) (Finsupp.{u1, u2} ι α _inst_1) (fun (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α) => Finsupp.indicator.{u1, u2} ι α _inst_1 s f)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] (s : Finset.{u2} ι), Function.Injective.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α) (Finsupp.{u2, u1} ι α _inst_1) (fun (f : forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α) => Finsupp.indicator.{u2, u1} ι α _inst_1 s f)
Case conversion may be inaccurate. Consider using '#align finsupp.indicator_injective Finsupp.indicator_injectiveₓ'. -/
theorem indicator_injective : Injective fun f : ∀ i ∈ s, α => indicator s f :=
  by
  intro a b h
  ext (i hi)
  rw [← indicator_of_mem hi a, ← indicator_of_mem hi b]
  exact congr_fun h i
#align finsupp.indicator_injective Finsupp.indicator_injective

/- warning: finsupp.support_indicator_subset -> Finsupp.support_indicator_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] (s : Finset.{u1} ι) (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> α), HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) (Finsupp.support.{u1, u2} ι α _inst_1 (Finsupp.indicator.{u1, u2} ι α _inst_1 s f))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] (s : Finset.{u2} ι) (f : forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> α), HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet.{u2} ι) (Finset.toSet.{u2} ι (Finsupp.support.{u2, u1} ι α _inst_1 (Finsupp.indicator.{u2, u1} ι α _inst_1 s f))) (Finset.toSet.{u2} ι s)
Case conversion may be inaccurate. Consider using '#align finsupp.support_indicator_subset Finsupp.support_indicator_subsetₓ'. -/
theorem support_indicator_subset : ((indicator s f).support : Set ι) ⊆ s :=
  by
  intro i hi
  rw [mem_coe, mem_support_iff] at hi
  by_contra
  exact hi (indicator_of_not_mem h _)
#align finsupp.support_indicator_subset Finsupp.support_indicator_subset

end Finsupp

