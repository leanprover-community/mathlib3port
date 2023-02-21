/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.set.Union_lift
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice
import Mathbin.Order.Directed

/-!
# Union lift

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines `set.Union_lift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `set.Union_lift` -  Given a Union of sets `Union S`, define a function on any subset of the Union
  by defining it on each component, and proving that it agrees on the intersections.
* `set.lift_cover` - Version of `set.Union_lift` for the special case that the sets cover the
  entire type.

## Main statements

There are proofs of the obvious properties of `Union_lift`, i.e. what it does to elements of
each of the sets in the `Union`, stated in different ways.

There are also three lemmas about `Union_lift` intended to aid with proving that `Union_lift` is a
homomorphism when defined on a Union of substructures. There is one lemma each to show that
constants, unary functions, or binary functions are preserved. These lemmas are:

*`set.Union_lift_const`
*`set.Union_lift_unary`
*`set.Union_lift_binary`

## Tags

directed union, directed supremum, glue, gluing
-/


variable {α ι β : Type _}

namespace Set

section UnionLift

#print Set.unionᵢLift /-
/- The unused argument `hf` is left in the definition so that the `simp` lemmas
`Union_lift_inclusion` will work without the user having to provide `hf` explicitly to
simplify terms involving `Union_lift`. -/
/-- Given a Union of sets `Union S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unused_arguments]
noncomputable def unionᵢLift (S : ι → Set α) (f : ∀ (i) (x : S i), β)
    (hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α)
    (hT : T ⊆ unionᵢ S) (x : T) : β :=
  let i := Classical.indefiniteDescription _ (mem_unionᵢ.1 (hT x.Prop))
  f i ⟨x, i.Prop⟩
#align set.Union_lift Set.unionᵢLift
-/

variable {S : ι → Set α} {f : ∀ (i) (x : S i), β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α}
  {hT : T ⊆ unionᵢ S} (hT' : T = unionᵢ S)

/- warning: set.Union_lift_mk -> Set.unionᵢLift_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} {hT : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)} {i : ι} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)))))) x) T), Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T hT (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x T) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)))))) x) hx)) (f i x)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u1} α ι S)} {i : ι} (x : Set.Elem.{u3} α (S i)) (hx : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x) T), Eq.{succ u2} β (Set.unionᵢLift.{u3, u1, u2} α ι β S f hf T hT (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x T) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x) hx)) (f i x)
Case conversion may be inaccurate. Consider using '#align set.Union_lift_mk Set.unionᵢLift_mkₓ'. -/
@[simp]
theorem unionᵢLift_mk {i : ι} (x : S i) (hx : (x : α) ∈ T) :
    unionᵢLift S f hf T hT ⟨x, hx⟩ = f i x :=
  by
  let j := Classical.indefiniteDescription _ (mem_unionᵢ.1 (hT hx))
  cases' x with x hx <;> exact hf j i x j.2 _
#align set.Union_lift_mk Set.unionᵢLift_mk

/- warning: set.Union_lift_inclusion -> Set.unionᵢLift_inclusion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} {hT : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)} {i : ι} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T), Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T hT (Set.inclusion.{u1} α (S i) T h x)) (f i x)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u1} α ι S)} {i : ι} (x : Set.Elem.{u3} α (S i)) (h : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S i) T), Eq.{succ u2} β (Set.unionᵢLift.{u3, u1, u2} α ι β S f hf T hT (Set.inclusion.{u3} α (S i) T h x)) (f i x)
Case conversion may be inaccurate. Consider using '#align set.Union_lift_inclusion Set.unionᵢLift_inclusionₓ'. -/
@[simp]
theorem unionᵢLift_inclusion {i : ι} (x : S i) (h : S i ⊆ T) :
    unionᵢLift S f hf T hT (Set.inclusion h x) = f i x :=
  unionᵢLift_mk x _
#align set.Union_lift_inclusion Set.unionᵢLift_inclusion

/- warning: set.Union_lift_of_mem -> Set.unionᵢLift_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} {hT : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) {i : ι} (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x T))))) x) (S i)), Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T hT x) (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x T))))) x) hx))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u1} α ι S)} (x : Set.Elem.{u3} α T) {i : ι} (hx : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x T) x) (S i)), Eq.{succ u2} β (Set.unionᵢLift.{u3, u1, u2} α ι β S f hf T hT x) (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x T) x) hx))
Case conversion may be inaccurate. Consider using '#align set.Union_lift_of_mem Set.unionᵢLift_of_memₓ'. -/
theorem unionᵢLift_of_mem (x : T) {i : ι} (hx : (x : α) ∈ S i) :
    unionᵢLift S f hf T hT x = f i ⟨x, hx⟩ := by cases' x with x hx <;> exact hf _ _ _ _ _
#align set.Union_lift_of_mem Set.unionᵢLift_of_mem

/- warning: set.Union_lift_const -> Set.unionᵢLift_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} {hT : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)} (c : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) (ci : forall (i : ι), coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), (forall (i : ι), Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)))))) (ci i)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x T))))) c)) -> (forall (cβ : β), (forall (i : ι), Eq.{succ u3} β (f i (ci i)) cβ) -> (Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T hT c) cβ))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u1} α ι S)} (c : Set.Elem.{u3} α T) (ci : forall (i : ι), Set.Elem.{u3} α (S i)), (forall (i : ι), Eq.{succ u3} α (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (ci i)) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x T) c)) -> (forall (cβ : β), (forall (i : ι), Eq.{succ u2} β (f i (ci i)) cβ) -> (Eq.{succ u2} β (Set.unionᵢLift.{u3, u1, u2} α ι β S f hf T hT c) cβ))
Case conversion may be inaccurate. Consider using '#align set.Union_lift_const Set.unionᵢLift_constₓ'. -/
/-- `Union_lift_const` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`. -/
theorem unionᵢLift_const (c : T) (ci : ∀ i, S i) (hci : ∀ i, (ci i : α) = c) (cβ : β)
    (h : ∀ i, f i (ci i) = cβ) : unionᵢLift S f hf T hT c = cβ :=
  by
  let ⟨i, hi⟩ := Set.mem_unionᵢ.1 (hT c.Prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [Union_lift_of_mem _ hi, ← this, h]
#align set.Union_lift_const Set.unionᵢLift_const

/- warning: set.Union_lift_unary -> Set.unionᵢLift_unary is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} (hT' : Eq.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)) (u : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T)) (ui : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i))), (forall (i : ι) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) (u (Set.inclusion.{u1} α (S i) T ((fun (this : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T) => this) (Eq.subst.{succ u1} (Set.{u1} α) (fun (_x : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) _x) (Set.unionᵢ.{u1, succ u2} α ι S) T (Eq.symm.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (Set.subset_unionᵢ.{u1, succ u2} α ι S i))) x)) (Set.inclusion.{u1} α (S i) T ((fun (this : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T) => this) (Eq.subst.{succ u1} (Set.{u1} α) (fun (_x : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) _x) (Set.unionᵢ.{u1, succ u2} α ι S) T (Eq.symm.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (Set.subset_unionᵢ.{u1, succ u2} α ι S i))) (ui i x))) -> (forall (uβ : β -> β), (forall (i : ι) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u3} β (f i (ui i x)) (uβ (f i x))) -> (forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T), Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T (le_of_eq.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (u x)) (uβ (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T (le_of_eq.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') x))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {β : Type.{u1}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u1} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT' : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S)} (u : Eq.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S)) (ui : (Set.Elem.{u3} α T) -> (Set.Elem.{u3} α T)) (hui : forall (i : ι), (Set.Elem.{u3} α (S i)) -> (Set.Elem.{u3} α (S i))), (forall (ᾰ : ι) (x : Set.Elem.{u3} α (S ᾰ)), Eq.{succ u3} (Set.Elem.{u3} α T) (ui (Set.inclusion.{u3} α (S ᾰ) T ([mdata let_fun:1 (fun (this : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) T) => this) (Eq.rec.{0, succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.995 : Set.{u3} α) (h._@.Mathlib.Data.Set.UnionLift._hyg.996 : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) x._@.Mathlib.Data.Set.UnionLift._hyg.995) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) x._@.Mathlib.Data.Set.UnionLift._hyg.995) (Set.subset_unionᵢ.{succ u2, u3} α ι S ᾰ) T (Eq.symm.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S) u))]) x)) (Set.inclusion.{u3} α (S ᾰ) T ([mdata let_fun:1 (fun (this : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) T) => this) (Eq.rec.{0, succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.1019 : Set.{u3} α) (h._@.Mathlib.Data.Set.UnionLift._hyg.1020 : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) x._@.Mathlib.Data.Set.UnionLift._hyg.1019) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) x._@.Mathlib.Data.Set.UnionLift._hyg.1019) (Set.subset_unionᵢ.{succ u2, u3} α ι S ᾰ) T (Eq.symm.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S) u))]) (hui ᾰ x))) -> (forall (h : β -> β), (forall (i : ι) (x : Set.Elem.{u3} α (S i)), Eq.{succ u1} β (f i (hui i x)) (h (f i x))) -> (forall (x : Set.Elem.{u3} α T), Eq.{succ u1} β (Set.unionᵢLift.{u3, u2, u1} α ι β S f hf T (le_of_eq.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) T (Set.unionᵢ.{u3, succ u2} α ι S) u) (ui x)) (h (Set.unionᵢLift.{u3, u2, u1} α ι β S f hf T (le_of_eq.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) T (Set.unionᵢ.{u3, succ u2} α ι S) u) x))))
Case conversion may be inaccurate. Consider using '#align set.Union_lift_unary Set.unionᵢLift_unaryₓ'. -/
/-- `Union_lift_unary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of linear_maps on a union of submodules preserves scalar multiplication. -/
theorem unionᵢLift_unary (u : T → T) (ui : ∀ i, S i → S i)
    (hui :
      ∀ (i) (x : S i),
        u (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) x) =
          Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) (ui i x))
    (uβ : β → β) (h : ∀ (i) (x : S i), f i (ui i x) = uβ (f i x)) (x : T) :
    unionᵢLift S f hf T (le_of_eq hT') (u x) = uβ (unionᵢLift S f hf T (le_of_eq hT') x) :=
  by
  subst hT'
  cases' Set.mem_unionᵢ.1 x.prop with i hi
  rw [Union_lift_of_mem x hi, ← h i]
  have : x = Set.inclusion (Set.subset_unionᵢ S i) ⟨x, hi⟩ :=
    by
    cases x
    rfl
  have hx' : (Set.inclusion (Set.subset_unionᵢ S i) (ui i ⟨x, hi⟩) : α) ∈ S i := (ui i ⟨x, hi⟩).Prop
  conv_lhs => rw [this, hui, Union_lift_inclusion]
#align set.Union_lift_unary Set.unionᵢLift_unary

/- warning: set.Union_lift_binary -> Set.unionᵢLift_binary is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {T : Set.{u1} α} (hT' : Eq.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S)), (Directed.{u1, succ u2} (Set.{u1} α) ι (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α)) S) -> (forall (op : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T)) (opi : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i))), (forall (i : ι) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) (Set.inclusion.{u1} α (S i) T ((fun (this : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T) => this) (Eq.subst.{succ u1} (Set.{u1} α) (fun (_x : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) _x) (Set.unionᵢ.{u1, succ u2} α ι S) T (Eq.symm.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (Set.subset_unionᵢ.{u1, succ u2} α ι S i))) (opi i x y)) (op (Set.inclusion.{u1} α (S i) T ((fun (this : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T) => this) (Eq.subst.{succ u1} (Set.{u1} α) (fun (_x : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) _x) (Set.unionᵢ.{u1, succ u2} α ι S) T (Eq.symm.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (Set.subset_unionᵢ.{u1, succ u2} α ι S i))) x) (Set.inclusion.{u1} α (S i) T ((fun (this : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) T) => this) (Eq.subst.{succ u1} (Set.{u1} α) (fun (_x : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (S i) _x) (Set.unionᵢ.{u1, succ u2} α ι S) T (Eq.symm.{succ u1} (Set.{u1} α) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (Set.subset_unionᵢ.{u1, succ u2} α ι S i))) y))) -> (forall (opβ : β -> β -> β), (forall (i : ι) (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u3} β (f i (opi i x y)) (opβ (f i x) (f i y))) -> (forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T) (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) T), Eq.{succ u3} β (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T (le_of_eq.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') (op x y)) (opβ (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T (le_of_eq.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') x) (Set.unionᵢLift.{u1, u2, u3} α ι β S f hf T (le_of_eq.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) T (Set.unionᵢ.{u1, succ u2} α ι S) hT') y)))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {β : Type.{u1}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u1} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {T : Set.{u3} α} {hT' : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S)} (dir : Eq.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S)), (Directed.{u3, succ u2} (Set.{u3} α) ι (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.1261 : Set.{u3} α) (x._@.Mathlib.Data.Set.UnionLift._hyg.1263 : Set.{u3} α) => LE.le.{u3} (Set.{u3} α) (Set.instLESet.{u3} α) x._@.Mathlib.Data.Set.UnionLift._hyg.1261 x._@.Mathlib.Data.Set.UnionLift._hyg.1263) S) -> (forall (opi : (Set.Elem.{u3} α T) -> (Set.Elem.{u3} α T) -> (Set.Elem.{u3} α T)) (hopi : forall (i : ι), (Set.Elem.{u3} α (S i)) -> (Set.Elem.{u3} α (S i)) -> (Set.Elem.{u3} α (S i))), (forall (ᾰ : ι) (ᾰ_1 : Set.Elem.{u3} α (S ᾰ)) (y : Set.Elem.{u3} α (S ᾰ)), Eq.{succ u3} (Set.Elem.{u3} α T) (Set.inclusion.{u3} α (S ᾰ) T ([mdata let_fun:1 (fun (this : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) T) => this) (Eq.rec.{0, succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.1318 : Set.{u3} α) (h._@.Mathlib.Data.Set.UnionLift._hyg.1319 : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) x._@.Mathlib.Data.Set.UnionLift._hyg.1318) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) x._@.Mathlib.Data.Set.UnionLift._hyg.1318) (Set.subset_unionᵢ.{succ u2, u3} α ι S ᾰ) T (Eq.symm.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S) dir))]) (hopi ᾰ ᾰ_1 y)) (opi (Set.inclusion.{u3} α (S ᾰ) T ([mdata let_fun:1 (fun (this : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) T) => this) (Eq.rec.{0, succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.1350 : Set.{u3} α) (h._@.Mathlib.Data.Set.UnionLift._hyg.1351 : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) x._@.Mathlib.Data.Set.UnionLift._hyg.1350) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) x._@.Mathlib.Data.Set.UnionLift._hyg.1350) (Set.subset_unionᵢ.{succ u2, u3} α ι S ᾰ) T (Eq.symm.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S) dir))]) ᾰ_1) (Set.inclusion.{u3} α (S ᾰ) T ([mdata let_fun:1 (fun (this : HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) T) => this) (Eq.rec.{0, succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) (fun (x._@.Mathlib.Data.Set.UnionLift._hyg.1376 : Set.{u3} α) (h._@.Mathlib.Data.Set.UnionLift._hyg.1377 : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι S) x._@.Mathlib.Data.Set.UnionLift._hyg.1376) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (S ᾰ) x._@.Mathlib.Data.Set.UnionLift._hyg.1376) (Set.subset_unionᵢ.{succ u2, u3} α ι S ᾰ) T (Eq.symm.{succ u3} (Set.{u3} α) T (Set.unionᵢ.{u3, succ u2} α ι S) dir))]) y))) -> (forall (h : β -> β -> β), (forall (i : ι) (x : Set.Elem.{u3} α (S i)) (y : Set.Elem.{u3} α (S i)), Eq.{succ u1} β (f i (hopi i x y)) (h (f i x) (f i y))) -> (forall (y : Set.Elem.{u3} α T) (y_1 : Set.Elem.{u3} α T), Eq.{succ u1} β (Set.unionᵢLift.{u3, u2, u1} α ι β S f hf T (le_of_eq.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) T (Set.unionᵢ.{u3, succ u2} α ι S) dir) (opi y y_1)) (h (Set.unionᵢLift.{u3, u2, u1} α ι β S f hf T (le_of_eq.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) T (Set.unionᵢ.{u3, succ u2} α ι S) dir) y) (Set.unionᵢLift.{u3, u2, u1} α ι β S f hf T (le_of_eq.{u3} (Set.{u3} α) (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))))) T (Set.unionᵢ.{u3, succ u2} α ι S) dir) y_1)))))
Case conversion may be inaccurate. Consider using '#align set.Union_lift_binary Set.unionᵢLift_binaryₓ'. -/
/-- `Union_lift_binary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`. -/
theorem unionᵢLift_binary (dir : Directed (· ≤ ·) S) (op : T → T → T) (opi : ∀ i, S i → S i → S i)
    (hopi :
      ∀ i x y,
        Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) (opi i x y) =
          op (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) x)
            (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_unionᵢ S i) y))
    (opβ : β → β → β) (h : ∀ (i) (x y : S i), f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) :
    unionᵢLift S f hf T (le_of_eq hT') (op x y) =
      opβ (unionᵢLift S f hf T (le_of_eq hT') x) (unionᵢLift S f hf T (le_of_eq hT') y) :=
  by
  subst hT'
  cases' Set.mem_unionᵢ.1 x.prop with i hi
  cases' Set.mem_unionᵢ.1 y.prop with j hj
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [Union_lift_of_mem x (hik hi), Union_lift_of_mem y (hjk hj), ← h k]
  have hx : x = Set.inclusion (Set.subset_unionᵢ S k) ⟨x, hik hi⟩ :=
    by
    cases x
    rfl
  have hy : y = Set.inclusion (Set.subset_unionᵢ S k) ⟨y, hjk hj⟩ :=
    by
    cases y
    rfl
  have hxy : (Set.inclusion (Set.subset_unionᵢ S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) ∈ S k :=
    (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).Prop
  conv_lhs => rw [hx, hy, ← hopi, Union_lift_of_mem _ hxy]
  simp only [coe_inclusion, Subtype.coe_eta]
#align set.Union_lift_binary Set.unionᵢLift_binary

end UnionLift

variable {S : ι → Set α} {f : ∀ (i) (x : S i), β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {hS : unionᵢ S = univ}

#print Set.liftCover /-
/-- Glue together functions defined on each of a collection `S` of sets that cover a type. See
  also `set.Union_lift`.   -/
noncomputable def liftCover (S : ι → Set α) (f : ∀ (i) (x : S i), β)
    (hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hS : unionᵢ S = univ) (a : α) : β :=
  unionᵢLift S f hf univ (hS ▸ Set.Subset.refl _) ⟨a, trivial⟩
#align set.lift_cover Set.liftCover
-/

/- warning: set.lift_cover_coe -> Set.liftCover_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {hS : Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι S) (Set.univ.{u1} α)} {i : ι} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)), Eq.{succ u3} β (Set.liftCover.{u1, u2, u3} α ι β S f hf hS ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)))))) x)) (f i x)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {hS : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u1} α ι S) (Set.univ.{u3} α)} {i : ι} (x : Set.Elem.{u3} α (S i)), Eq.{succ u2} β (Set.liftCover.{u3, u1, u2} α ι β S f hf hS (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x)) (f i x)
Case conversion may be inaccurate. Consider using '#align set.lift_cover_coe Set.liftCover_coeₓ'. -/
@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS x = f i x :=
  unionᵢLift_mk x _
#align set.lift_cover_coe Set.liftCover_coe

/- warning: set.lift_cover_of_mem -> Set.liftCover_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : Type.{u3}} {S : ι -> (Set.{u1} α)} {f : forall (i : ι), (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) (hxj : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)), Eq.{succ u3} β (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S j)) x hxj))} {hS : Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι S) (Set.univ.{u1} α)} {i : ι} {x : α} (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)), Eq.{succ u3} β (Set.liftCover.{u1, u2, u3} α ι β S f hf hS x) (f i (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (S i)) x hx))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : Type.{u2}} {S : ι -> (Set.{u3} α)} {f : forall (i : ι), (Set.Elem.{u3} α (S i)) -> β} {hf : forall (i : ι) (j : ι) (x : α) (hxi : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) (hxj : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)), Eq.{succ u2} β (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hxi)) (f j (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S j)) x hxj))} {hS : Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u1} α ι S) (Set.univ.{u3} α)} {i : ι} {x : α} (hx : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)), Eq.{succ u2} β (Set.liftCover.{u3, u1, u2} α ι β S f hf hS x) (f i (Subtype.mk.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (S i)) x hx))
Case conversion may be inaccurate. Consider using '#align set.lift_cover_of_mem Set.liftCover_of_memₓ'. -/
theorem liftCover_of_mem {i : ι} {x : α} (hx : (x : α) ∈ S i) :
    liftCover S f hf hS x = f i ⟨x, hx⟩ :=
  unionᵢLift_of_mem ⟨x, trivial⟩ hx
#align set.lift_cover_of_mem Set.liftCover_of_mem

end Set

