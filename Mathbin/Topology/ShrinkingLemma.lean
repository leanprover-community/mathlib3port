/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton

! This file was ported from Lean 3 source module topology.shrinking_lemma
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation

/-!
# The shrinking lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → set X` there exists a refinement `v : ι → set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_Union_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_Union_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/


open Set Function

open Classical

noncomputable section

variable {ι X : Type _} [TopologicalSpace X] [NormalSpace X]

namespace ShrinkingLemma

/- warning: shrinking_lemma.partial_refinement -> ShrinkingLemma.PartialRefinement is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1], (ι -> (Set.{u2} X)) -> (Set.{u2} X) -> Sort.{max (succ u1) (succ u2)}
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X], (ι -> (Set.{u2} X)) -> (Set.{u2} X) -> Sort.{max (succ u1) (succ u2)}
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement ShrinkingLemma.PartialRefinementₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ∉ » carrier) -/
-- the trivial refinement needs `u` to be a covering
/-- Auxiliary definition for the proof of `shrinking_lemma`. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → set X` and a set `carrier : set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the folowing partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
@[nolint has_nonempty_instance]
structure PartialRefinement (u : ι → Set X) (s : Set X) where
  toFun : ι → Set X
  carrier : Set ι
  is_open' : ∀ i, IsOpen (to_fun i)
  subset_Union' : s ⊆ ⋃ i, to_fun i
  closure_subset' : ∀ i ∈ carrier, closure (to_fun i) ⊆ u i
  apply_eq' : ∀ (i) (_ : i ∉ carrier), to_fun i = u i
#align shrinking_lemma.partial_refinement ShrinkingLemma.PartialRefinement

namespace PartialRefinement

variable {u : ι → Set X} {s : Set X}

instance : CoeFun (PartialRefinement u s) fun _ => ι → Set X :=
  ⟨toFun⟩

/- warning: shrinking_lemma.partial_refinement.subset_Union -> ShrinkingLemma.PartialRefinement.subset_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s), HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) s (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u), HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) u (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u s i))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.subset_Union ShrinkingLemma.PartialRefinement.subset_unionᵢₓ'. -/
theorem subset_unionᵢ (v : PartialRefinement u s) : s ⊆ ⋃ i, v i :=
  v.subset_Union'
#align shrinking_lemma.partial_refinement.subset_Union ShrinkingLemma.PartialRefinement.subset_unionᵢ

/- warning: shrinking_lemma.partial_refinement.closure_subset -> ShrinkingLemma.PartialRefinement.closure_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v)) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (closure.{u2} X _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i)) (u i))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) {v : ι}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) v (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s)) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) (closure.{u2} X _inst_1 (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u s v)) (_inst_2 v))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.closure_subset ShrinkingLemma.PartialRefinement.closure_subsetₓ'. -/
theorem closure_subset (v : PartialRefinement u s) {i : ι} (hi : i ∈ v.carrier) :
    closure (v i) ⊆ u i :=
  v.closure_subset' i hi
#align shrinking_lemma.partial_refinement.closure_subset ShrinkingLemma.PartialRefinement.closure_subset

/- warning: shrinking_lemma.partial_refinement.apply_eq -> ShrinkingLemma.PartialRefinement.apply_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) {i : ι}, (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v))) -> (Eq.{succ u2} (Set.{u2} X) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i) (u i))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) {v : ι}, (Not (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) v (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s))) -> (Eq.{succ u2} (Set.{u2} X) (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u s v) (_inst_2 v))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.apply_eq ShrinkingLemma.PartialRefinement.apply_eqₓ'. -/
theorem apply_eq (v : PartialRefinement u s) {i : ι} (hi : i ∉ v.carrier) : v i = u i :=
  v.apply_eq' i hi
#align shrinking_lemma.partial_refinement.apply_eq ShrinkingLemma.PartialRefinement.apply_eq

/- warning: shrinking_lemma.partial_refinement.is_open -> ShrinkingLemma.PartialRefinement.isOpen is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (i : ι), IsOpen.{u2} X _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i)
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (v : ι), IsOpen.{u2} X _inst_1 (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u s v)
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.is_open ShrinkingLemma.PartialRefinement.isOpenₓ'. -/
protected theorem isOpen (v : PartialRefinement u s) (i : ι) : IsOpen (v i) :=
  v.is_open' i
#align shrinking_lemma.partial_refinement.is_open ShrinkingLemma.PartialRefinement.isOpen

/- warning: shrinking_lemma.partial_refinement.subset -> ShrinkingLemma.PartialRefinement.subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (i : ι), HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i) (u i)
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {_inst_2 : ι -> (Set.{u1} X)} {u : Set.{u1} X} (s : ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 _inst_2 u) (v : ι), HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (ShrinkingLemma.PartialRefinement.toFun.{u2, u1} ι X _inst_1 _inst_2 u s v) (_inst_2 v)
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.subset ShrinkingLemma.PartialRefinement.subsetₓ'. -/
protected theorem subset (v : PartialRefinement u s) (i : ι) : v i ⊆ u i :=
  if h : i ∈ v.carrier then Subset.trans subset_closure (v.closure_subset h) else (v.apply_eq h).le
#align shrinking_lemma.partial_refinement.subset ShrinkingLemma.PartialRefinement.subset

attribute [ext] partial_refinement

instance : PartialOrder (PartialRefinement u s)
    where
  le v₁ v₂ := v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i
  le_refl v := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans v₁ v₂ v₃ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    ext _ _
      (funext fun x =>
        if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

/- warning: shrinking_lemma.partial_refinement.apply_eq_of_chain -> ShrinkingLemma.PartialRefinement.apply_eq_of_chain is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} {c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)}, (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s)))) c) -> (forall {v₁ : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s} {v₂ : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s}, (Membership.Mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (Set.hasMem.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) v₁ c) -> (Membership.Mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (Set.hasMem.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) v₂ c) -> (forall {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v₁)) -> (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v₂)) -> (Eq.{succ u2} (Set.{u2} X) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v₁ i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v₂ i))))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} {s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)}, (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (fun (x._@.Mathlib.Topology.ShrinkingLemma._hyg.468 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (x._@.Mathlib.Topology.ShrinkingLemma._hyg.470 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) => LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u))) x._@.Mathlib.Topology.ShrinkingLemma._hyg.468 x._@.Mathlib.Topology.ShrinkingLemma._hyg.470) s) -> (forall {hc : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u} {v₁ : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u}, (Membership.mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (Set.instMembershipSet.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) hc s) -> (Membership.mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (Set.instMembershipSet.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) v₁ s) -> (forall {h₂ : ι}, (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) h₂ (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u hc)) -> (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) h₂ (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u v₁)) -> (Eq.{succ u2} (Set.{u2} X) (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u hc h₂) (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u v₁ h₂))))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.apply_eq_of_chain ShrinkingLemma.PartialRefinement.apply_eq_of_chainₓ'. -/
/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
theorem apply_eq_of_chain {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) {v₁ v₂}
    (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) : v₁ i = v₂ i :=
  by
  wlog hle : v₁ ≤ v₂
  · cases hc.total h₁ h₂ <;> [skip, symm] <;> apply_assumption <;> assumption'
  exact hle.2 _ hi₁
#align shrinking_lemma.partial_refinement.apply_eq_of_chain ShrinkingLemma.PartialRefinement.apply_eq_of_chain

/- warning: shrinking_lemma.partial_refinement.chain_Sup_carrier -> ShrinkingLemma.PartialRefinement.chainSupCarrier is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X}, (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) -> (Set.{u1} ι)
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X}, (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) -> (Set.{u1} ι)
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.chain_Sup_carrier ShrinkingLemma.PartialRefinement.chainSupCarrierₓ'. -/
/-- The carrier of the least upper bound of a non-empty chain of partial refinements
is the union of their carriers. -/
def chainSupCarrier (c : Set (PartialRefinement u s)) : Set ι :=
  ⋃ v ∈ c, carrier v
#align shrinking_lemma.partial_refinement.chain_Sup_carrier ShrinkingLemma.PartialRefinement.chainSupCarrier

/- warning: shrinking_lemma.partial_refinement.find -> ShrinkingLemma.PartialRefinement.find is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)), (Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c) -> ι -> (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)), (Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s) -> ι -> (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.find ShrinkingLemma.PartialRefinement.findₓ'. -/
/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
def find (c : Set (PartialRefinement u s)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s :=
  if hi : ∃ v ∈ c, i ∈ carrier v then hi.some else Ne.some
#align shrinking_lemma.partial_refinement.find ShrinkingLemma.PartialRefinement.find

/- warning: shrinking_lemma.partial_refinement.find_mem -> ShrinkingLemma.PartialRefinement.find_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} {c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)} (i : ι) (ne : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c), Membership.Mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (Set.hasMem.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s c ne i) c
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} {s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)} (c : ι) (i : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s), Membership.mem.{max u2 u1, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (Set.instMembershipSet.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s i c) s
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.find_mem ShrinkingLemma.PartialRefinement.find_memₓ'. -/
theorem find_mem {c : Set (PartialRefinement u s)} (i : ι) (ne : c.Nonempty) : find c Ne i ∈ c :=
  by
  rw [find]
  split_ifs
  exacts[h.some_spec.fst, ne.some_spec]
#align shrinking_lemma.partial_refinement.find_mem ShrinkingLemma.PartialRefinement.find_mem

/- warning: shrinking_lemma.partial_refinement.mem_find_carrier_iff -> ShrinkingLemma.PartialRefinement.mem_find_carrier_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} {c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)} {i : ι} (ne : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c), Iff (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s c ne i))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.chainSupCarrier.{u1, u2} ι X _inst_1 _inst_2 u s c))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} {s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)} {c : ι} (i : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s), Iff (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) c (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s i c))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) c (ShrinkingLemma.PartialRefinement.chainSupCarrier.{u1, u2} ι X _inst_1 _inst_2 u s))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.mem_find_carrier_iff ShrinkingLemma.PartialRefinement.mem_find_carrier_iffₓ'. -/
theorem mem_find_carrier_iff {c : Set (PartialRefinement u s)} {i : ι} (ne : c.Nonempty) :
    i ∈ (find c Ne i).carrier ↔ i ∈ chainSupCarrier c :=
  by
  rw [find]
  split_ifs
  · have : i ∈ h.some.carrier ∧ i ∈ chain_Sup_carrier c := ⟨h.some_spec.snd, mem_Union₂.2 h⟩
    simp only [this]
  · have : i ∉ ne.some.carrier ∧ i ∉ chain_Sup_carrier c :=
      ⟨fun hi => h ⟨_, ne.some_spec, hi⟩, mt mem_Union₂.1 h⟩
    simp only [this]
#align shrinking_lemma.partial_refinement.mem_find_carrier_iff ShrinkingLemma.PartialRefinement.mem_find_carrier_iff

/- warning: shrinking_lemma.partial_refinement.find_apply_of_mem -> ShrinkingLemma.PartialRefinement.find_apply_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} {c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)}, (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s)))) c) -> (forall (ne : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c) {i : ι} {v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s}, (Membership.Mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (Set.hasMem.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) v c) -> (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v)) -> (Eq.{succ u2} (Set.{u2} X) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s c ne i) i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (_x : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => ι -> (Set.{u2} X)) (ShrinkingLemma.PartialRefinement.hasCoeToFun.{u1, u2} ι X _inst_1 _inst_2 u s) v i)))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} {s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)}, (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (fun (x._@.Mathlib.Topology.ShrinkingLemma._hyg.890 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (x._@.Mathlib.Topology.ShrinkingLemma._hyg.892 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) => LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u))) x._@.Mathlib.Topology.ShrinkingLemma._hyg.890 x._@.Mathlib.Topology.ShrinkingLemma._hyg.892) s) -> (forall (hc : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s) {ne : ι} {i : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u}, (Membership.mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (Set.instMembershipSet.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) i s) -> (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) ne (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u i)) -> (Eq.{succ u2} (Set.{u2} X) (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u (ShrinkingLemma.PartialRefinement.find.{u1, u2} ι X _inst_1 _inst_2 u s hc ne) ne) (ShrinkingLemma.PartialRefinement.toFun.{u1, u2} ι X _inst_1 _inst_2 u i ne)))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.find_apply_of_mem ShrinkingLemma.PartialRefinement.find_apply_of_memₓ'. -/
theorem find_apply_of_mem {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c)
    (ne : c.Nonempty) {i v} (hv : v ∈ c) (hi : i ∈ carrier v) : find c Ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_unionᵢ₂.2 ⟨v, hv, hi⟩)
    hi
#align shrinking_lemma.partial_refinement.find_apply_of_mem ShrinkingLemma.PartialRefinement.find_apply_of_mem

/- warning: shrinking_lemma.partial_refinement.chain_Sup -> ShrinkingLemma.PartialRefinement.chainSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)), (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s)))) c) -> (Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c) -> (forall (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x s) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (u i))))) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) s (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => u i))) -> (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} (s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)), (IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (fun (x._@.Mathlib.Topology.ShrinkingLemma._hyg.979 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (x._@.Mathlib.Topology.ShrinkingLemma._hyg.981 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) => LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u))) x._@.Mathlib.Topology.ShrinkingLemma._hyg.979 x._@.Mathlib.Topology.ShrinkingLemma._hyg.981) s) -> (Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s) -> (forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x u) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (_inst_2 i))))) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) u (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => _inst_2 i))) -> (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.chain_Sup ShrinkingLemma.PartialRefinement.chainSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (i «expr ∉ » chain_Sup_carrier c) -/
/-- Least upper bound of a nonempty chain of partial refinements. -/
def chainSup (c : Set (PartialRefinement u s)) (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) : PartialRefinement u s :=
  by
  refine'
    ⟨fun i => find c Ne i i, chain_Sup_carrier c, fun i => (find _ _ _).IsOpen i, fun x hxs =>
      mem_Union.2 _, fun i hi => (find c Ne i).closure_subset ((mem_find_carrier_iff _).2 hi),
      fun i hi => (find c Ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)⟩
  rcases em (∃ (i : _)(_ : i ∉ chain_Sup_carrier c), x ∈ u i) with (⟨i, hi, hxi⟩ | hx)
  · use i
    rwa [(find c Ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
  · simp_rw [not_exists, not_imp_not, chain_Sup_carrier, mem_Union₂] at hx
    haveI : Nonempty (partial_refinement u s) := ⟨ne.some⟩
    choose! v hvc hiv using hx
    rcases(hfin x hxs).exists_maximal_wrt v _ (mem_Union.1 (hU hxs)) with
      ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v i = v j⟩
    rcases mem_Union.1 ((v i).subset_unionᵢ hxs) with ⟨j, hj⟩
    use j
    have hj' : x ∈ u j := (v i).Subset _ hj
    have : v j ≤ v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (fun h => (hmax j hj' h).ge) id
    rwa [find_apply_of_mem hc Ne (hvc _ hxi) (this.1 <| hiv _ hj')]
#align shrinking_lemma.partial_refinement.chain_Sup ShrinkingLemma.PartialRefinement.chainSup

/- warning: shrinking_lemma.partial_refinement.le_chain_Sup -> ShrinkingLemma.PartialRefinement.le_chainSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} {c : Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)} (hc : IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s)))) c) (ne : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) c) (hfin : forall (x : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x s) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (u i))))) (hU : HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) s (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => u i))) {v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s}, (Membership.Mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Set.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) (Set.hasMem.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s)) v c) -> (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s))) v (ShrinkingLemma.PartialRefinement.chainSup.{u1, u2} ι X _inst_1 _inst_2 u s c hc ne hfin hU))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {_inst_2 : ι -> (Set.{u2} X)} {u : Set.{u2} X} {s : Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)} (c : IsChain.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (fun (x._@.Mathlib.Topology.ShrinkingLemma._hyg.1450 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (x._@.Mathlib.Topology.ShrinkingLemma._hyg.1452 : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) => LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u))) x._@.Mathlib.Topology.ShrinkingLemma._hyg.1450 x._@.Mathlib.Topology.ShrinkingLemma._hyg.1452) s) (hc : Set.Nonempty.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) s) (ne : forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x u) -> (Set.Finite.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x (_inst_2 i))))) (hfin : HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) u (Set.unionᵢ.{u2, succ u1} X ι (fun (i : ι) => _inst_2 i))) {hU : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u}, (Membership.mem.{max u1 u2, max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Set.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) (Set.instMembershipSet.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u)) hU s) -> (LE.le.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (Preorder.toLE.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u))) hU (ShrinkingLemma.PartialRefinement.chainSup.{u1, u2} ι X _inst_1 _inst_2 u s c hc ne hfin))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.le_chain_Sup ShrinkingLemma.PartialRefinement.le_chainSupₓ'. -/
/-- `chain_Sup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
theorem le_chainSup {c : Set (PartialRefinement u s)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) {v} (hv : v ∈ c) :
    v ≤ chainSup c hc Ne hfin hU :=
  ⟨fun i hi => mem_bunionᵢ hv hi, fun i hi => (find_apply_of_mem hc _ hv hi).symm⟩
#align shrinking_lemma.partial_refinement.le_chain_Sup ShrinkingLemma.PartialRefinement.le_chainSup

/- warning: shrinking_lemma.partial_refinement.exists_gt -> ShrinkingLemma.PartialRefinement.exists_gt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : NormalSpace.{u2} X _inst_1] {u : ι -> (Set.{u2} X)} {s : Set.{u2} X} (v : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s), (IsClosed.{u2} X _inst_1 s) -> (forall (i : ι), (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u1, u2} ι X _inst_1 _inst_2 u s v))) -> (Exists.{max (succ u1) (succ u2)} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (fun (v' : ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) => LT.lt.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (Preorder.toLT.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (PartialOrder.toPreorder.{max u1 u2} (ShrinkingLemma.PartialRefinement.{u1, u2} ι X _inst_1 _inst_2 u s) (ShrinkingLemma.PartialRefinement.partialOrder.{u1, u2} ι X _inst_1 _inst_2 u s))) v v')))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NormalSpace.{u1} X _inst_1] {u : ι -> (Set.{u1} X)} {s : Set.{u1} X} (v : ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s), (IsClosed.{u1} X _inst_1 s) -> (forall (i : ι), (Not (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (ShrinkingLemma.PartialRefinement.carrier.{u2, u1} ι X _inst_1 u s v))) -> (Exists.{max (succ u2) (succ u1)} (ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s) (fun (v' : ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s) => LT.lt.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s) (Preorder.toLT.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s) (PartialOrder.toPreorder.{max u2 u1} (ShrinkingLemma.PartialRefinement.{u2, u1} ι X _inst_1 u s) (ShrinkingLemma.PartialRefinement.instPartialOrderPartialRefinement.{u2, u1} ι X _inst_1 u s))) v v')))
Case conversion may be inaccurate. Consider using '#align shrinking_lemma.partial_refinement.exists_gt ShrinkingLemma.PartialRefinement.exists_gtₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (j «expr ≠ » i) -/
/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
theorem exists_gt (v : PartialRefinement u s) (hs : IsClosed s) (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s, v < v' :=
  by
  have I : (s ∩ ⋂ (j) (_ : j ≠ i), v jᶜ) ⊆ v i :=
    by
    simp only [subset_def, mem_inter_iff, mem_Inter, and_imp]
    intro x hxs H
    rcases mem_Union.1 (v.subset_Union hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s ∩ ⋂ (j) (_ : j ≠ i), v jᶜ) :=
    IsClosed.inter hs (isClosed_binterᵢ fun _ _ => isClosed_compl_iff.2 <| v.is_open _)
  rcases normal_exists_closure_subset C (v.is_open i) I with ⟨vi, ovi, hvi, cvi⟩
  refine' ⟨⟨update v i vi, insert i v.carrier, _, _, _, _⟩, _, _⟩
  · intro j
    by_cases h : j = i <;> simp [h, ovi, v.is_open]
  · refine' fun x hx => mem_Union.2 _
    rcases em (∃ (j : _)(_ : j ≠ i), x ∈ v j) with (⟨j, hji, hj⟩ | h)
    · use j
      rwa [update_noteq hji]
    · push_neg  at h
      use i
      rw [update_same]
      exact hvi ⟨hx, mem_bInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_same, ← v.apply_eq hi]
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff, not_or] at hj
    rw [update_noteq hj.1, v.apply_eq hj.2]
  · refine' ⟨subset_insert _ _, fun j hj => _⟩
    exact (update_noteq (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
#align shrinking_lemma.partial_refinement.exists_gt ShrinkingLemma.PartialRefinement.exists_gt

end PartialRefinement

end ShrinkingLemma

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X}

#print exists_subset_unionᵢ_closure_subset /-
/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_subset_unionᵢ_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ unionᵢ v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i := by
  classical
    haveI : Nonempty (partial_refinement u s) :=
      ⟨⟨u, ∅, uo, us, fun _ => False.elim, fun _ _ => rfl⟩⟩
    have :
      ∀ c : Set (partial_refinement u s), IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
      fun c hc ne =>
      ⟨partial_refinement.chain_Sup c hc Ne uf us, fun v hv =>
        partial_refinement.le_chain_Sup _ _ _ _ hv⟩
    rcases zorn_nonempty_partialOrder this with ⟨v, hv⟩
    suffices : ∀ i, i ∈ v.carrier
    exact ⟨v, v.subset_Union, fun i => v.is_open _, fun i => v.closure_subset (this i)⟩
    contrapose! hv
    rcases hv with ⟨i, hi⟩
    rcases v.exists_gt hs i hi with ⟨v', hlt⟩
    exact ⟨v', hlt.le, hlt.ne'⟩
#align exists_subset_Union_closure_subset exists_subset_unionᵢ_closure_subset
-/

#print exists_subset_unionᵢ_closed_subset /-
/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each new closed set is contained in the corresponding original open
set. See also `exists_subset_Union_closure_subset` for a stronger statement. -/
theorem exists_subset_unionᵢ_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ unionᵢ v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, hvo, hv⟩ := exists_subset_unionᵢ_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (unionᵢ_mono fun i => subset_closure), fun i =>
    isClosed_closure, hv⟩
#align exists_subset_Union_closed_subset exists_subset_unionᵢ_closed_subset
-/

#print exists_unionᵢ_eq_closure_subset /-
/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
theorem exists_unionᵢ_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : (⋃ i, u i) = univ) :
    ∃ v : ι → Set X, unionᵢ v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_unionᵢ_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩
#align exists_Union_eq_closure_subset exists_unionᵢ_eq_closure_subset
-/

#print exists_unionᵢ_eq_closed_subset /-
/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_Union_eq_closure_subset` for a stronger statement. -/
theorem exists_unionᵢ_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : (⋃ i, u i) = univ) :
    ∃ v : ι → Set X, unionᵢ v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_unionᵢ_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩
#align exists_Union_eq_closed_subset exists_unionᵢ_eq_closed_subset
-/

