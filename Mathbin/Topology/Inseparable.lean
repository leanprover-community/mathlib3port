/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.inseparable
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.ContinuousOn
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.Tfae

/-!
# Inseparable points in a topological space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* `specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `x ⤳ y`: notation for `specializes x y`;
- `x ~ y` is used as a local notation for `inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/


open Set Filter Function

open Topology Filter

variable {X Y Z α ι : Type _} {π : ι → Type _} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (π i)] {x y z : X} {s : Set X} {f : X → Y}

/-!
### `specializes` relation
-/


#print Specializes /-
/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop :=
  𝓝 x ≤ 𝓝 y
#align specializes Specializes
-/

-- mathport name: «expr ⤳ »
infixl:300 " ⤳ " => Specializes

/- warning: specializes_tfae -> specializes_TFAE is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X) (y : X), List.TFAE (List.cons.{0} Prop (Specializes.{u1} X _inst_1 x y) (List.cons.{0} Prop (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} X x) (nhds.{u1} X _inst_1 y)) (List.cons.{0} Prop (forall (s : Set.{u1} X), (IsOpen.{u1} X _inst_1 s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s)) (List.cons.{0} Prop (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s)) (List.cons.{0} Prop (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) x))) (List.cons.{0} Prop (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) y)) (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) x))) (List.cons.{0} Prop (ClusterPt.{u1} X _inst_1 y (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} X x)) (List.nil.{0} Prop))))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X) (y : X), List.TFAE (List.cons.{0} Prop (Specializes.{u1} X _inst_1 x y) (List.cons.{0} Prop (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} X x) (nhds.{u1} X _inst_1 y)) (List.cons.{0} Prop (forall (s : Set.{u1} X), (IsOpen.{u1} X _inst_1 s) -> (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) y s) -> (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x s)) (List.cons.{0} Prop (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x s) -> (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) y s)) (List.cons.{0} Prop (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) y (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x))) (List.cons.{0} Prop (HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) y)) (closure.{u1} X _inst_1 (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x))) (List.cons.{0} Prop (ClusterPt.{u1} X _inst_1 y (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} X x)) (List.nil.{0} Prop))))))))
Case conversion may be inaccurate. Consider using '#align specializes_tfae specializes_TFAEₓ'. -/
/-- A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
below. -/
theorem specializes_TFAE (x y : X) :
    TFAE
      [x ⤳ y, pure x ≤ 𝓝 y, ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s,
        ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s, y ∈ closure ({x} : Set X),
        closure ({y} : Set X) ⊆ closure {x}, ClusterPt y (pure x)] :=
  by
  tfae_have 1 → 2; exact (pure_le_nhds _).trans
  tfae_have 2 → 3; exact fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 → 4; exact fun h s hsc hx => of_not_not fun hy => h (sᶜ) hsc.isOpen_compl hy hx
  tfae_have 4 → 5; exact fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5; exact is_closed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7; · rw [mem_closure_iff_clusterPt, principal_singleton]
  tfae_have 5 → 1
  · refine' fun h => (nhds_basis_opens _).ge_iff.2 _
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish
#align specializes_tfae specializes_TFAE

/- warning: specializes_iff_nhds -> specializes_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} X _inst_1 x y) (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (nhds.{u1} X _inst_1 x) (nhds.{u1} X _inst_1 y))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} X _inst_1 x y) (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (nhds.{u1} X _inst_1 x) (nhds.{u1} X _inst_1 y))
Case conversion may be inaccurate. Consider using '#align specializes_iff_nhds specializes_iff_nhdsₓ'. -/
theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl
#align specializes_iff_nhds specializes_iff_nhds

/- warning: specializes_iff_pure -> specializes_iff_pure is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} X _inst_1 x y) (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} X x) (nhds.{u1} X _inst_1 y))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} X _inst_1 x y) (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} X x) (nhds.{u1} X _inst_1 y))
Case conversion may be inaccurate. Consider using '#align specializes_iff_pure specializes_iff_pureₓ'. -/
theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_TFAE x y).out 0 1
#align specializes_iff_pure specializes_iff_pure

/- warning: specializes.nhds_le_nhds -> Specializes.nhds_le_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, (Specializes.{u1} X _inst_1 x y) -> (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (nhds.{u1} X _inst_1 x) (nhds.{u1} X _inst_1 y))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, (Specializes.{u1} X _inst_1 x y) -> (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (nhds.{u1} X _inst_1 x) (nhds.{u1} X _inst_1 y))
Case conversion may be inaccurate. Consider using '#align specializes.nhds_le_nhds Specializes.nhds_le_nhdsₓ'. -/
alias specializes_iff_nhds ↔ Specializes.nhds_le_nhds _
#align specializes.nhds_le_nhds Specializes.nhds_le_nhds

/- warning: specializes.pure_le_nhds -> Specializes.pure_le_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, (Specializes.{u1} X _inst_1 x y) -> (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} X x) (nhds.{u1} X _inst_1 y))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, (Specializes.{u1} X _inst_1 x y) -> (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} X x) (nhds.{u1} X _inst_1 y))
Case conversion may be inaccurate. Consider using '#align specializes.pure_le_nhds Specializes.pure_le_nhdsₓ'. -/
alias specializes_iff_pure ↔ Specializes.pure_le_nhds _
#align specializes.pure_le_nhds Specializes.pure_le_nhds

#print specializes_iff_forall_open /-
theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_TFAE x y).out 0 2
#align specializes_iff_forall_open specializes_iff_forall_open
-/

#print Specializes.mem_open /-
theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy
#align specializes.mem_open Specializes.mem_open
-/

#print IsOpen.not_specializes /-
theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h =>
  hx <| h.mem_open hs hy
#align is_open.not_specializes IsOpen.not_specializes
-/

#print specializes_iff_forall_closed /-
theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_TFAE x y).out 0 3
#align specializes_iff_forall_closed specializes_iff_forall_closed
-/

#print Specializes.mem_closed /-
theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx
#align specializes.mem_closed Specializes.mem_closed
-/

#print IsClosed.not_specializes /-
theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx
#align is_closed.not_specializes IsClosed.not_specializes
-/

#print specializes_iff_mem_closure /-
theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : Set X) :=
  (specializes_TFAE x y).out 0 4
#align specializes_iff_mem_closure specializes_iff_mem_closure
-/

alias specializes_iff_mem_closure ↔ Specializes.mem_closure _
#align specializes.mem_closure Specializes.mem_closure

#print specializes_iff_closure_subset /-
theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) ⊆ closure {x} :=
  (specializes_TFAE x y).out 0 5
#align specializes_iff_closure_subset specializes_iff_closure_subset
-/

alias specializes_iff_closure_subset ↔ Specializes.closure_subset _
#align specializes.closure_subset Specializes.closure_subset

#print Filter.HasBasis.specializes_iff /-
theorem Filter.HasBasis.specializes_iff {ι} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
  specializes_iff_pure.trans h.ge_iff
#align filter.has_basis.specializes_iff Filter.HasBasis.specializes_iff
-/

#print specializes_rfl /-
theorem specializes_rfl : x ⤳ x :=
  le_rfl
#align specializes_rfl specializes_rfl
-/

#print specializes_refl /-
@[refl]
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl
#align specializes_refl specializes_refl
-/

#print Specializes.trans /-
@[trans]
theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
  le_trans
#align specializes.trans Specializes.trans
-/

#print specializes_of_eq /-
theorem specializes_of_eq (e : x = y) : x ⤳ y :=
  e ▸ specializes_refl x
#align specializes_of_eq specializes_of_eq
-/

/- warning: specializes_of_nhds_within -> specializes_of_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {s : Set.{u1} X}, (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.partialOrder.{u1} X))) (nhdsWithin.{u1} X _inst_1 x s) (nhdsWithin.{u1} X _inst_1 y s)) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Specializes.{u1} X _inst_1 x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X} {s : Set.{u1} X}, (LE.le.{u1} (Filter.{u1} X) (Preorder.toLE.{u1} (Filter.{u1} X) (PartialOrder.toPreorder.{u1} (Filter.{u1} X) (Filter.instPartialOrderFilter.{u1} X))) (nhdsWithin.{u1} X _inst_1 x s) (nhdsWithin.{u1} X _inst_1 y s)) -> (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x s) -> (Specializes.{u1} X _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align specializes_of_nhds_within specializes_of_nhdsWithinₓ'. -/
theorem specializes_of_nhdsWithin (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
  specializes_iff_pure.2 <|
    calc
      pure x ≤ 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ ≤ 𝓝[s] y := h₁
      _ ≤ 𝓝 y := inf_le_left
      
#align specializes_of_nhds_within specializes_of_nhdsWithin

/- warning: specializes.map_of_continuous_at -> Specializes.map_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Specializes.{u1} X _inst_1 x y) -> (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 f y) -> (Specializes.{u2} Y _inst_2 (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Specializes.{u2} X _inst_1 x y) -> (ContinuousAt.{u2, u1} X Y _inst_1 _inst_2 f y) -> (Specializes.{u1} Y _inst_2 (f x) (f y))
Case conversion may be inaccurate. Consider using '#align specializes.map_of_continuous_at Specializes.map_of_continuousAtₓ'. -/
theorem Specializes.map_of_continuousAt (h : x ⤳ y) (hy : ContinuousAt f y) : f x ⤳ f y :=
  specializes_iff_pure.2 fun s hs =>
    mem_pure.2 <| mem_preimage.1 <| mem_of_mem_nhds <| hy.mono_left h hs
#align specializes.map_of_continuous_at Specializes.map_of_continuousAt

/- warning: specializes.map -> Specializes.map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Specializes.{u1} X _inst_1 x y) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Specializes.{u2} Y _inst_2 (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Specializes.{u2} X _inst_1 x y) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 f) -> (Specializes.{u1} Y _inst_2 (f x) (f y))
Case conversion may be inaccurate. Consider using '#align specializes.map Specializes.mapₓ'. -/
theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuousAt hf.ContinuousAt
#align specializes.map Specializes.map

/- warning: inducing.specializes_iff -> Inducing.specializes_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Inducing.{u1, u2} X Y _inst_1 _inst_2 f) -> (Iff (Specializes.{u2} Y _inst_2 (f x) (f y)) (Specializes.{u1} X _inst_1 x y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Inducing.{u2, u1} X Y _inst_1 _inst_2 f) -> (Iff (Specializes.{u1} Y _inst_2 (f x) (f y)) (Specializes.{u2} X _inst_1 x y))
Case conversion may be inaccurate. Consider using '#align inducing.specializes_iff Inducing.specializes_iffₓ'. -/
theorem Inducing.specializes_iff (hf : Inducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [specializes_iff_mem_closure, hf.closure_eq_preimage_closure_image, image_singleton,
    mem_preimage]
#align inducing.specializes_iff Inducing.specializes_iff

#print subtype_specializes_iff /-
theorem subtype_specializes_iff {p : X → Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  inducing_subtype_val.specializes_iff.symm
#align subtype_specializes_iff subtype_specializes_iff
-/

/- warning: specializes_prod -> specializes_prod is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, Iff (Specializes.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂)) (And (Specializes.{u1} X _inst_1 x₁ x₂) (Specializes.{u2} Y _inst_2 y₁ y₂))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, Iff (Specializes.{max u2 u1} (Prod.{u1, u2} X Y) (instTopologicalSpaceProd.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂)) (And (Specializes.{u1} X _inst_1 x₁ x₂) (Specializes.{u2} Y _inst_2 y₁ y₂))
Case conversion may be inaccurate. Consider using '#align specializes_prod specializes_prodₓ'. -/
@[simp]
theorem specializes_prod {x₁ x₂ : X} {y₁ y₂ : Y} : (x₁, y₁) ⤳ (x₂, y₂) ↔ x₁ ⤳ x₂ ∧ y₁ ⤳ y₂ := by
  simp only [Specializes, nhds_prod_eq, prod_le_prod]
#align specializes_prod specializes_prod

/- warning: specializes.prod -> Specializes.prod is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, (Specializes.{u1} X _inst_1 x₁ x₂) -> (Specializes.{u2} Y _inst_2 y₁ y₂) -> (Specializes.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, (Specializes.{u2} X _inst_1 x₁ x₂) -> (Specializes.{u1} Y _inst_2 y₁ y₂) -> (Specializes.{max u1 u2} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y x₁ y₁) (Prod.mk.{u2, u1} X Y x₂ y₂))
Case conversion may be inaccurate. Consider using '#align specializes.prod Specializes.prodₓ'. -/
theorem Specializes.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ⤳ x₂) (hy : y₁ ⤳ y₂) :
    (x₁, y₁) ⤳ (x₂, y₂) :=
  specializes_prod.2 ⟨hx, hy⟩
#align specializes.prod Specializes.prod

/- warning: specializes_pi -> specializes_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_4 : forall (i : ι), TopologicalSpace.{u2} (π i)] {f : forall (i : ι), π i} {g : forall (i : ι), π i}, Iff (Specializes.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_4 a)) f g) (forall (i : ι), Specializes.{u2} (π i) (_inst_4 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_4 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : forall (i : ι), π i} {g : forall (i : ι), π i}, Iff (Specializes.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_4 a)) f g) (forall (i : ι), Specializes.{u1} (π i) (_inst_4 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align specializes_pi specializes_piₓ'. -/
@[simp]
theorem specializes_pi {f g : ∀ i, π i} : f ⤳ g ↔ ∀ i, f i ⤳ g i := by
  simp only [Specializes, nhds_pi, pi_le_pi]
#align specializes_pi specializes_pi

#print not_specializes_iff_exists_open /-
theorem not_specializes_iff_exists_open : ¬x ⤳ y ↔ ∃ S : Set X, IsOpen S ∧ y ∈ S ∧ x ∉ S :=
  by
  rw [specializes_iff_forall_open]
  push_neg
  rfl
#align not_specializes_iff_exists_open not_specializes_iff_exists_open
-/

#print not_specializes_iff_exists_closed /-
theorem not_specializes_iff_exists_closed : ¬x ⤳ y ↔ ∃ S : Set X, IsClosed S ∧ x ∈ S ∧ y ∉ S :=
  by
  rw [specializes_iff_forall_closed]
  push_neg
  rfl
#align not_specializes_iff_exists_closed not_specializes_iff_exists_closed
-/

variable (X)

#print specializationPreorder /-
/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorder X :=
  {
    Preorder.lift (OrderDual.toDual ∘
        𝓝) with
    le := fun x y => y ⤳ x
    lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }
#align specialization_preorder specializationPreorder
-/

variable {X}

/- warning: continuous.specialization_monotone -> Continuous.specialization_monotone is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y}, (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Monotone.{u1, u2} X Y (specializationPreorder.{u1} X _inst_1) (specializationPreorder.{u2} Y _inst_2) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y}, (Continuous.{u2, u1} X Y _inst_1 _inst_2 f) -> (Monotone.{u2, u1} X Y (specializationPreorder.{u2} X _inst_1) (specializationPreorder.{u1} Y _inst_2) f)
Case conversion may be inaccurate. Consider using '#align continuous.specialization_monotone Continuous.specialization_monotoneₓ'. -/
/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) :
    @Monotone _ _ (specializationPreorder X) (specializationPreorder Y) f := fun x y h => h.map hf
#align continuous.specialization_monotone Continuous.specialization_monotone

/-!
### `inseparable` relation
-/


#print Inseparable /-
/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y
#align inseparable Inseparable
-/

-- mathport name: «expr ~ »
local infixl:0 " ~ " => Inseparable

#print inseparable_def /-
theorem inseparable_def : (x ~ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl
#align inseparable_def inseparable_def
-/

#print inseparable_iff_specializes_and /-
theorem inseparable_iff_specializes_and : (x ~ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iff
#align inseparable_iff_specializes_and inseparable_iff_specializes_and
-/

#print Inseparable.specializes /-
theorem Inseparable.specializes (h : x ~ y) : x ⤳ y :=
  h.le
#align inseparable.specializes Inseparable.specializes
-/

#print Inseparable.specializes' /-
theorem Inseparable.specializes' (h : x ~ y) : y ⤳ x :=
  h.ge
#align inseparable.specializes' Inseparable.specializes'
-/

#print Specializes.antisymm /-
theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ y :=
  le_antisymm h₁ h₂
#align specializes.antisymm Specializes.antisymm
-/

#print inseparable_iff_forall_open /-
theorem inseparable_iff_forall_open : (x ~ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_open, ← forall_and, ← iff_def,
    Iff.comm]
#align inseparable_iff_forall_open inseparable_iff_forall_open
-/

#print not_inseparable_iff_exists_open /-
theorem not_inseparable_iff_exists_open : ¬(x ~ y) ↔ ∃ s : Set X, IsOpen s ∧ Xor' (x ∈ s) (y ∈ s) :=
  by simp [inseparable_iff_forall_open, ← xor_iff_not_iff]
#align not_inseparable_iff_exists_open not_inseparable_iff_exists_open
-/

#print inseparable_iff_forall_closed /-
theorem inseparable_iff_forall_closed : (x ~ y) ↔ ∀ s : Set X, IsClosed s → (x ∈ s ↔ y ∈ s) := by
  simp only [inseparable_iff_specializes_and, specializes_iff_forall_closed, ← forall_and, ←
    iff_def]
#align inseparable_iff_forall_closed inseparable_iff_forall_closed
-/

#print inseparable_iff_mem_closure /-
theorem inseparable_iff_mem_closure :
    (x ~ y) ↔ x ∈ closure ({y} : Set X) ∧ y ∈ closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by simp only [specializes_iff_mem_closure, and_comm']
#align inseparable_iff_mem_closure inseparable_iff_mem_closure
-/

#print inseparable_iff_closure_eq /-
theorem inseparable_iff_closure_eq : (x ~ y) ↔ closure ({x} : Set X) = closure {y} := by
  simp only [inseparable_iff_specializes_and, specializes_iff_closure_subset, ← subset_antisymm_iff,
    eq_comm]
#align inseparable_iff_closure_eq inseparable_iff_closure_eq
-/

#print inseparable_of_nhdsWithin_eq /-
theorem inseparable_of_nhdsWithin_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ y :=
  (specializes_of_nhdsWithin h.le hx).antisymm (specializes_of_nhdsWithin h.ge hy)
#align inseparable_of_nhds_within_eq inseparable_of_nhdsWithin_eq
-/

/- warning: inducing.inseparable_iff -> Inducing.inseparable_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Inducing.{u1, u2} X Y _inst_1 _inst_2 f) -> (Iff (Inseparable.{u2} Y _inst_2 (f x) (f y)) (Inseparable.{u1} X _inst_1 x y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Inducing.{u2, u1} X Y _inst_1 _inst_2 f) -> (Iff (Inseparable.{u1} Y _inst_2 (f x) (f y)) (Inseparable.{u2} X _inst_1 x y))
Case conversion may be inaccurate. Consider using '#align inducing.inseparable_iff Inducing.inseparable_iffₓ'. -/
theorem Inducing.inseparable_iff (hf : Inducing f) : (f x ~ f y) ↔ (x ~ y) := by
  simp only [inseparable_iff_specializes_and, hf.specializes_iff]
#align inducing.inseparable_iff Inducing.inseparable_iff

#print subtype_inseparable_iff /-
theorem subtype_inseparable_iff {p : X → Prop} (x y : Subtype p) : (x ~ y) ↔ ((x : X) ~ y) :=
  inducing_subtype_val.inseparable_iff.symm
#align subtype_inseparable_iff subtype_inseparable_iff
-/

/- warning: inseparable_prod -> inseparable_prod is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, Iff (Inseparable.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂)) (And (Inseparable.{u1} X _inst_1 x₁ x₂) (Inseparable.{u2} Y _inst_2 y₁ y₂))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, Iff (Inseparable.{max u2 u1} (Prod.{u1, u2} X Y) (instTopologicalSpaceProd.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂)) (And (Inseparable.{u1} X _inst_1 x₁ x₂) (Inseparable.{u2} Y _inst_2 y₁ y₂))
Case conversion may be inaccurate. Consider using '#align inseparable_prod inseparable_prodₓ'. -/
@[simp]
theorem inseparable_prod {x₁ x₂ : X} {y₁ y₂ : Y} : ((x₁, y₁) ~ (x₂, y₂)) ↔ (x₁ ~ x₂) ∧ (y₁ ~ y₂) :=
  by simp only [Inseparable, nhds_prod_eq, prod_inj]
#align inseparable_prod inseparable_prod

/- warning: inseparable.prod -> Inseparable.prod is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, (Inseparable.{u1} X _inst_1 x₁ x₂) -> (Inseparable.{u2} Y _inst_2 y₁ y₂) -> (Inseparable.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x₁ y₁) (Prod.mk.{u1, u2} X Y x₂ y₂))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x₁ : X} {x₂ : X} {y₁ : Y} {y₂ : Y}, (Inseparable.{u2} X _inst_1 x₁ x₂) -> (Inseparable.{u1} Y _inst_2 y₁ y₂) -> (Inseparable.{max u1 u2} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y x₁ y₁) (Prod.mk.{u2, u1} X Y x₂ y₂))
Case conversion may be inaccurate. Consider using '#align inseparable.prod Inseparable.prodₓ'. -/
theorem Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ x₂) (hy : y₁ ~ y₂) :
    (x₁, y₁) ~ (x₂, y₂) :=
  inseparable_prod.2 ⟨hx, hy⟩
#align inseparable.prod Inseparable.prod

/- warning: inseparable_pi -> inseparable_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_4 : forall (i : ι), TopologicalSpace.{u2} (π i)] {f : forall (i : ι), π i} {g : forall (i : ι), π i}, Iff (Inseparable.{max u1 u2} (forall (i : ι), π i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_4 a)) f g) (forall (i : ι), Inseparable.{u2} (π i) (_inst_4 i) (f i) (g i))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_4 : forall (i : ι), TopologicalSpace.{u1} (π i)] {f : forall (i : ι), π i} {g : forall (i : ι), π i}, Iff (Inseparable.{max u2 u1} (forall (i : ι), π i) (Pi.topologicalSpace.{u2, u1} ι (fun (i : ι) => π i) (fun (a : ι) => _inst_4 a)) f g) (forall (i : ι), Inseparable.{u1} (π i) (_inst_4 i) (f i) (g i))
Case conversion may be inaccurate. Consider using '#align inseparable_pi inseparable_piₓ'. -/
@[simp]
theorem inseparable_pi {f g : ∀ i, π i} : (f ~ g) ↔ ∀ i, f i ~ g i := by
  simp only [Inseparable, nhds_pi, funext_iff, pi_inj]
#align inseparable_pi inseparable_pi

namespace Inseparable

#print Inseparable.refl /-
@[refl]
theorem refl (x : X) : x ~ x :=
  Eq.refl (𝓝 x)
#align inseparable.refl Inseparable.refl
-/

#print Inseparable.rfl /-
theorem rfl : x ~ x :=
  refl x
#align inseparable.rfl Inseparable.rfl
-/

#print Inseparable.of_eq /-
theorem of_eq (e : x = y) : Inseparable x y :=
  e ▸ refl x
#align inseparable.of_eq Inseparable.of_eq
-/

#print Inseparable.symm /-
@[symm]
theorem symm (h : x ~ y) : y ~ x :=
  h.symm
#align inseparable.symm Inseparable.symm
-/

#print Inseparable.trans /-
@[trans]
theorem trans (h₁ : x ~ y) (h₂ : y ~ z) : x ~ z :=
  h₁.trans h₂
#align inseparable.trans Inseparable.trans
-/

#print Inseparable.nhds_eq /-
theorem nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y :=
  h
#align inseparable.nhds_eq Inseparable.nhds_eq
-/

#print Inseparable.mem_open_iff /-
theorem mem_open_iff (h : x ~ y) (hs : IsOpen s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_open.1 h s hs
#align inseparable.mem_open_iff Inseparable.mem_open_iff
-/

#print Inseparable.mem_closed_iff /-
theorem mem_closed_iff (h : x ~ y) (hs : IsClosed s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_closed.1 h s hs
#align inseparable.mem_closed_iff Inseparable.mem_closed_iff
-/

/- warning: inseparable.map_of_continuous_at -> Inseparable.map_of_continuousAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Inseparable.{u1} X _inst_1 x y) -> (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 f x) -> (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 f y) -> (Inseparable.{u2} Y _inst_2 (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Inseparable.{u2} X _inst_1 x y) -> (ContinuousAt.{u2, u1} X Y _inst_1 _inst_2 f x) -> (ContinuousAt.{u2, u1} X Y _inst_1 _inst_2 f y) -> (Inseparable.{u1} Y _inst_2 (f x) (f y))
Case conversion may be inaccurate. Consider using '#align inseparable.map_of_continuous_at Inseparable.map_of_continuousAtₓ'. -/
theorem map_of_continuousAt (h : x ~ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) :
    f x ~ f y :=
  (h.Specializes.map_of_continuousAt hy).antisymm (h.specializes'.map_of_continuousAt hx)
#align inseparable.map_of_continuous_at Inseparable.map_of_continuousAt

/- warning: inseparable.map -> Inseparable.map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {x : X} {y : X} {f : X -> Y}, (Inseparable.{u1} X _inst_1 x y) -> (Continuous.{u1, u2} X Y _inst_1 _inst_2 f) -> (Inseparable.{u2} Y _inst_2 (f x) (f y))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {x : X} {y : X} {f : X -> Y}, (Inseparable.{u2} X _inst_1 x y) -> (Continuous.{u2, u1} X Y _inst_1 _inst_2 f) -> (Inseparable.{u1} Y _inst_2 (f x) (f y))
Case conversion may be inaccurate. Consider using '#align inseparable.map Inseparable.mapₓ'. -/
theorem map (h : x ~ y) (hf : Continuous f) : f x ~ f y :=
  h.map_of_continuousAt hf.ContinuousAt hf.ContinuousAt
#align inseparable.map Inseparable.map

end Inseparable

#print IsClosed.not_inseparable /-
theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx
#align is_closed.not_inseparable IsClosed.not_inseparable
-/

#print IsOpen.not_inseparable /-
theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx
#align is_open.not_inseparable IsOpen.not_inseparable
-/

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `inseparable` relation.
-/


variable (X)

#print inseparableSetoid /-
/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparableSetoid : Setoid X :=
  { Setoid.comap 𝓝 ⊥ with R := (· ~ ·) }
#align inseparable_setoid inseparableSetoid
-/

#print SeparationQuotient /-
/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a T₀ space. -/
def SeparationQuotient :=
  Quotient (inseparableSetoid X)deriving TopologicalSpace
#align separation_quotient SeparationQuotient
-/

variable {X} {t : Set (SeparationQuotient X)}

namespace SeparationQuotient

#print SeparationQuotient.mk /-
/-- The natural map from a topological space to its separation quotient. -/
def mk : X → SeparationQuotient X :=
  Quotient.mk''
#align separation_quotient.mk SeparationQuotient.mk
-/

#print SeparationQuotient.quotientMap_mk /-
theorem quotientMap_mk : QuotientMap (mk : X → SeparationQuotient X) :=
  quotientMap_quot_mk
#align separation_quotient.quotient_map_mk SeparationQuotient.quotientMap_mk
-/

#print SeparationQuotient.continuous_mk /-
theorem continuous_mk : Continuous (mk : X → SeparationQuotient X) :=
  continuous_quot_mk
#align separation_quotient.continuous_mk SeparationQuotient.continuous_mk
-/

#print SeparationQuotient.mk_eq_mk /-
@[simp]
theorem mk_eq_mk : mk x = mk y ↔ (x ~ y) :=
  Quotient.eq''
#align separation_quotient.mk_eq_mk SeparationQuotient.mk_eq_mk
-/

#print SeparationQuotient.surjective_mk /-
theorem surjective_mk : Surjective (mk : X → SeparationQuotient X) :=
  surjective_quot_mk _
#align separation_quotient.surjective_mk SeparationQuotient.surjective_mk
-/

#print SeparationQuotient.range_mk /-
@[simp]
theorem range_mk : range (mk : X → SeparationQuotient X) = univ :=
  surjective_mk.range_eq
#align separation_quotient.range_mk SeparationQuotient.range_mk
-/

instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›

instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩

instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.Subsingleton

#print SeparationQuotient.preimage_image_mk_open /-
theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' (mk '' s) = s :=
  by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys
#align separation_quotient.preimage_image_mk_open SeparationQuotient.preimage_image_mk_open
-/

#print SeparationQuotient.isOpenMap_mk /-
theorem isOpenMap_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  quotientMap_mk.isOpen_preimage.1 <| by rwa [preimage_image_mk_open hs]
#align separation_quotient.is_open_map_mk SeparationQuotient.isOpenMap_mk
-/

#print SeparationQuotient.preimage_image_mk_closed /-
theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' (mk '' s) = s :=
  by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys
#align separation_quotient.preimage_image_mk_closed SeparationQuotient.preimage_image_mk_closed
-/

#print SeparationQuotient.inducing_mk /-
theorem inducing_mk : Inducing (mk : X → SeparationQuotient X) :=
  ⟨le_antisymm (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, isOpenMap_mk s hs, preimage_image_mk_open hs⟩⟩
#align separation_quotient.inducing_mk SeparationQuotient.inducing_mk
-/

#print SeparationQuotient.isClosedMap_mk /-
theorem isClosedMap_mk : IsClosedMap (mk : X → SeparationQuotient X) :=
  inducing_mk.IsClosedMap <| by
    rw [range_mk]
    exact isClosed_univ
#align separation_quotient.is_closed_map_mk SeparationQuotient.isClosedMap_mk
-/

#print SeparationQuotient.comap_mk_nhds_mk /-
@[simp]
theorem comap_mk_nhds_mk : comap mk (𝓝 (mk x)) = 𝓝 x :=
  (inducing_mk.nhds_eq_comap _).symm
#align separation_quotient.comap_mk_nhds_mk SeparationQuotient.comap_mk_nhds_mk
-/

#print SeparationQuotient.comap_mk_nhdsSet_image /-
@[simp]
theorem comap_mk_nhdsSet_image : comap mk (𝓝ˢ (mk '' s)) = 𝓝ˢ s :=
  (inducing_mk.nhdsSet_eq_comap _).symm
#align separation_quotient.comap_mk_nhds_set_image SeparationQuotient.comap_mk_nhdsSet_image
-/

#print SeparationQuotient.map_mk_nhds /-
theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [← comap_mk_nhds_mk, map_comap_of_surjective surjective_mk]
#align separation_quotient.map_mk_nhds SeparationQuotient.map_mk_nhds
-/

#print SeparationQuotient.map_mk_nhdsSet /-
theorem map_mk_nhdsSet : map mk (𝓝ˢ s) = 𝓝ˢ (mk '' s) := by
  rw [← comap_mk_nhds_set_image, map_comap_of_surjective surjective_mk]
#align separation_quotient.map_mk_nhds_set SeparationQuotient.map_mk_nhdsSet
-/

#print SeparationQuotient.comap_mk_nhdsSet /-
theorem comap_mk_nhdsSet : comap mk (𝓝ˢ t) = 𝓝ˢ (mk ⁻¹' t) := by
  conv_lhs => rw [← image_preimage_eq t surjective_mk, comap_mk_nhds_set_image]
#align separation_quotient.comap_mk_nhds_set SeparationQuotient.comap_mk_nhdsSet
-/

#print SeparationQuotient.preimage_mk_closure /-
theorem preimage_mk_closure : mk ⁻¹' closure t = closure (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_closure_eq_closure_preimage continuous_mk t
#align separation_quotient.preimage_mk_closure SeparationQuotient.preimage_mk_closure
-/

#print SeparationQuotient.preimage_mk_interior /-
theorem preimage_mk_interior : mk ⁻¹' interior t = interior (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_interior_eq_interior_preimage continuous_mk t
#align separation_quotient.preimage_mk_interior SeparationQuotient.preimage_mk_interior
-/

#print SeparationQuotient.preimage_mk_frontier /-
theorem preimage_mk_frontier : mk ⁻¹' frontier t = frontier (mk ⁻¹' t) :=
  isOpenMap_mk.preimage_frontier_eq_frontier_preimage continuous_mk t
#align separation_quotient.preimage_mk_frontier SeparationQuotient.preimage_mk_frontier
-/

#print SeparationQuotient.image_mk_closure /-
theorem image_mk_closure : mk '' closure s = closure (mk '' s) :=
  (image_closure_subset_closure_image continuous_mk).antisymm <|
    isClosedMap_mk.closure_image_subset _
#align separation_quotient.image_mk_closure SeparationQuotient.image_mk_closure
-/

/- warning: separation_quotient.map_prod_map_mk_nhds -> SeparationQuotient.map_prod_map_mk_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (x : X) (y : Y), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))) (Filter.map.{max u1 u2, max u1 u2} (Prod.{u1, u2} X Y) (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u1, u1, u2, u2} X (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) (nhds.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x y))) (nhds.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) (Prod.mk.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] (x : X) (y : Y), Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.{u1} Y _inst_2))) (Filter.map.{max u1 u2, max u1 u2} (Prod.{u2, u1} X Y) (Prod.{u2, u1} (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.{u1} Y _inst_2)) (Prod.map.{u2, u2, u1, u1} X (SeparationQuotient.{u2} X _inst_1) Y (SeparationQuotient.{u1} Y _inst_2) (SeparationQuotient.mk.{u2} X _inst_1) (SeparationQuotient.mk.{u1} Y _inst_2)) (nhds.{max u2 u1} (Prod.{u2, u1} X Y) (instTopologicalSpaceProd.{u2, u1} X Y _inst_1 _inst_2) (Prod.mk.{u2, u1} X Y x y))) (nhds.{max u1 u2} (Prod.{u2, u1} (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.{u1} Y _inst_2)) (instTopologicalSpaceProd.{u2, u1} (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.{u1} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u1} Y _inst_2)) (Prod.mk.{u2, u1} (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.{u1} Y _inst_2) (SeparationQuotient.mk.{u2} X _inst_1 x) (SeparationQuotient.mk.{u1} Y _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align separation_quotient.map_prod_map_mk_nhds SeparationQuotient.map_prod_map_mk_nhdsₓ'. -/
theorem map_prod_map_mk_nhds (x : X) (y : Y) : map (Prod.map mk mk) (𝓝 (x, y)) = 𝓝 (mk x, mk y) :=
  by rw [nhds_prod_eq, ← prod_map_map_eq', map_mk_nhds, map_mk_nhds, nhds_prod_eq]
#align separation_quotient.map_prod_map_mk_nhds SeparationQuotient.map_prod_map_mk_nhds

#print SeparationQuotient.map_mk_nhdsWithin_preimage /-
theorem map_mk_nhdsWithin_preimage (s : Set (SeparationQuotient X)) (x : X) :
    map mk (𝓝[mk ⁻¹' s] x) = 𝓝[s] mk x := by
  rw [nhdsWithin, ← comap_principal, Filter.push_pull, nhdsWithin, map_mk_nhds]
#align separation_quotient.map_mk_nhds_within_preimage SeparationQuotient.map_mk_nhdsWithin_preimage
-/

#print SeparationQuotient.lift /-
/-- Lift a map `f : X → α` such that `inseparable x y → f x = f y` to a map
`separation_quotient X → α`. -/
def lift (f : X → α) (hf : ∀ x y, (x ~ y) → f x = f y) : SeparationQuotient X → α := fun x =>
  Quotient.liftOn' x f hf
#align separation_quotient.lift SeparationQuotient.lift
-/

/- warning: separation_quotient.lift_mk -> SeparationQuotient.lift_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> α} (hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} α (f x) (f y))) (x : X), Eq.{succ u2} α (SeparationQuotient.lift.{u1, u2} X α _inst_1 f hf (SeparationQuotient.mk.{u1} X _inst_1 x)) (f x)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> α} (hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} α (f x) (f y))) (x : X), Eq.{succ u1} α (SeparationQuotient.lift.{u2, u1} X α _inst_1 f hf (SeparationQuotient.mk.{u2} X _inst_1 x)) (f x)
Case conversion may be inaccurate. Consider using '#align separation_quotient.lift_mk SeparationQuotient.lift_mkₓ'. -/
@[simp]
theorem lift_mk {f : X → α} (hf : ∀ x y, (x ~ y) → f x = f y) (x : X) : lift f hf (mk x) = f x :=
  rfl
#align separation_quotient.lift_mk SeparationQuotient.lift_mk

/- warning: separation_quotient.lift_comp_mk -> SeparationQuotient.lift_comp_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> α} (hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} α (f x) (f y))), Eq.{max (succ u1) (succ u2)} (X -> α) (Function.comp.{succ u1, succ u1, succ u2} X (SeparationQuotient.{u1} X _inst_1) α (SeparationQuotient.lift.{u1, u2} X α _inst_1 f hf) (SeparationQuotient.mk.{u1} X _inst_1)) f
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> α} (hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} α (f x) (f y))), Eq.{max (succ u2) (succ u1)} (X -> α) (Function.comp.{succ u2, succ u2, succ u1} X (SeparationQuotient.{u2} X _inst_1) α (SeparationQuotient.lift.{u2, u1} X α _inst_1 f hf) (SeparationQuotient.mk.{u2} X _inst_1)) f
Case conversion may be inaccurate. Consider using '#align separation_quotient.lift_comp_mk SeparationQuotient.lift_comp_mkₓ'. -/
@[simp]
theorem lift_comp_mk {f : X → α} (hf : ∀ x y, (x ~ y) → f x = f y) : lift f hf ∘ mk = f :=
  rfl
#align separation_quotient.lift_comp_mk SeparationQuotient.lift_comp_mk

/- warning: separation_quotient.tendsto_lift_nhds_mk -> SeparationQuotient.tendsto_lift_nhds_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> α} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} α (f x) (f y))} {x : X} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (SeparationQuotient.{u1} X _inst_1) α (SeparationQuotient.lift.{u1, u2} X α _inst_1 f hf) (nhds.{u1} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.mk.{u1} X _inst_1 x)) l) (Filter.Tendsto.{u1, u2} X α f (nhds.{u1} X _inst_1 x) l)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> α} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} α (f x) (f y))} {x : X} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u2, u1} (SeparationQuotient.{u2} X _inst_1) α (SeparationQuotient.lift.{u2, u1} X α _inst_1 f hf) (nhds.{u2} (SeparationQuotient.{u2} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) (SeparationQuotient.mk.{u2} X _inst_1 x)) l) (Filter.Tendsto.{u2, u1} X α f (nhds.{u2} X _inst_1 x) l)
Case conversion may be inaccurate. Consider using '#align separation_quotient.tendsto_lift_nhds_mk SeparationQuotient.tendsto_lift_nhds_mkₓ'. -/
@[simp]
theorem tendsto_lift_nhds_mk {f : X → α} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X} {l : Filter α} :
    Tendsto (lift f hf) (𝓝 <| mk x) l ↔ Tendsto f (𝓝 x) l := by
  simp only [← map_mk_nhds, tendsto_map'_iff, lift_comp_mk]
#align separation_quotient.tendsto_lift_nhds_mk SeparationQuotient.tendsto_lift_nhds_mk

/- warning: separation_quotient.tendsto_lift_nhds_within_mk -> SeparationQuotient.tendsto_lift_nhdsWithin_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {f : X -> α} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} α (f x) (f y))} {x : X} {s : Set.{u1} (SeparationQuotient.{u1} X _inst_1)} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (SeparationQuotient.{u1} X _inst_1) α (SeparationQuotient.lift.{u1, u2} X α _inst_1 f hf) (nhdsWithin.{u1} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.mk.{u1} X _inst_1 x) s) l) (Filter.Tendsto.{u1, u2} X α f (nhdsWithin.{u1} X _inst_1 x (Set.preimage.{u1, u1} X (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.mk.{u1} X _inst_1) s)) l)
but is expected to have type
  forall {X : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] {f : X -> α} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} α (f x) (f y))} {x : X} {s : Set.{u2} (SeparationQuotient.{u2} X _inst_1)} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{u2, u1} (SeparationQuotient.{u2} X _inst_1) α (SeparationQuotient.lift.{u2, u1} X α _inst_1 f hf) (nhdsWithin.{u2} (SeparationQuotient.{u2} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) (SeparationQuotient.mk.{u2} X _inst_1 x) s) l) (Filter.Tendsto.{u2, u1} X α f (nhdsWithin.{u2} X _inst_1 x (Set.preimage.{u2, u2} X (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.mk.{u2} X _inst_1) s)) l)
Case conversion may be inaccurate. Consider using '#align separation_quotient.tendsto_lift_nhds_within_mk SeparationQuotient.tendsto_lift_nhdsWithin_mkₓ'. -/
@[simp]
theorem tendsto_lift_nhdsWithin_mk {f : X → α} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X}
    {s : Set (SeparationQuotient X)} {l : Filter α} :
    Tendsto (lift f hf) (𝓝[s] mk x) l ↔ Tendsto f (𝓝[mk ⁻¹' s] x) l := by
  simp only [← map_mk_nhds_within_preimage, tendsto_map'_iff, lift_comp_mk]
#align separation_quotient.tendsto_lift_nhds_within_mk SeparationQuotient.tendsto_lift_nhdsWithin_mk

/- warning: separation_quotient.continuous_at_lift -> SeparationQuotient.continuousAt_lift is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} Y (f x) (f y))} {x : X}, Iff (ContinuousAt.{u1, u2} (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.topologicalSpace.{u1} X _inst_1) _inst_2 (SeparationQuotient.lift.{u1, u2} X Y _inst_1 f hf) (SeparationQuotient.mk.{u1} X _inst_1 x)) (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 f x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} Y (f x) (f y))} {x : X}, Iff (ContinuousAt.{u2, u1} (SeparationQuotient.{u2} X _inst_1) Y (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) _inst_2 (SeparationQuotient.lift.{u2, u1} X Y _inst_1 f hf) (SeparationQuotient.mk.{u2} X _inst_1 x)) (ContinuousAt.{u2, u1} X Y _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_at_lift SeparationQuotient.continuousAt_liftₓ'. -/
@[simp]
theorem continuousAt_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y} {x : X} :
    ContinuousAt (lift f hf) (mk x) ↔ ContinuousAt f x :=
  tendsto_lift_nhds_mk
#align separation_quotient.continuous_at_lift SeparationQuotient.continuousAt_lift

/- warning: separation_quotient.continuous_within_at_lift -> SeparationQuotient.continuousWithinAt_lift is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} Y (f x) (f y))} {s : Set.{u1} (SeparationQuotient.{u1} X _inst_1)} {x : X}, Iff (ContinuousWithinAt.{u1, u2} (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.topologicalSpace.{u1} X _inst_1) _inst_2 (SeparationQuotient.lift.{u1, u2} X Y _inst_1 f hf) s (SeparationQuotient.mk.{u1} X _inst_1 x)) (ContinuousWithinAt.{u1, u2} X Y _inst_1 _inst_2 f (Set.preimage.{u1, u1} X (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.mk.{u1} X _inst_1) s) x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} Y (f x) (f y))} {s : Set.{u2} (SeparationQuotient.{u2} X _inst_1)} {x : X}, Iff (ContinuousWithinAt.{u2, u1} (SeparationQuotient.{u2} X _inst_1) Y (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) _inst_2 (SeparationQuotient.lift.{u2, u1} X Y _inst_1 f hf) s (SeparationQuotient.mk.{u2} X _inst_1 x)) (ContinuousWithinAt.{u2, u1} X Y _inst_1 _inst_2 f (Set.preimage.{u2, u2} X (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.mk.{u2} X _inst_1) s) x)
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_within_at_lift SeparationQuotient.continuousWithinAt_liftₓ'. -/
@[simp]
theorem continuousWithinAt_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y}
    {s : Set (SeparationQuotient X)} {x : X} :
    ContinuousWithinAt (lift f hf) s (mk x) ↔ ContinuousWithinAt f (mk ⁻¹' s) x :=
  tendsto_lift_nhdsWithin_mk
#align separation_quotient.continuous_within_at_lift SeparationQuotient.continuousWithinAt_lift

/- warning: separation_quotient.continuous_on_lift -> SeparationQuotient.continuousOn_lift is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} Y (f x) (f y))} {s : Set.{u1} (SeparationQuotient.{u1} X _inst_1)}, Iff (ContinuousOn.{u1, u2} (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.topologicalSpace.{u1} X _inst_1) _inst_2 (SeparationQuotient.lift.{u1, u2} X Y _inst_1 f hf) s) (ContinuousOn.{u1, u2} X Y _inst_1 _inst_2 f (Set.preimage.{u1, u1} X (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.mk.{u1} X _inst_1) s))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} Y (f x) (f y))} {s : Set.{u2} (SeparationQuotient.{u2} X _inst_1)}, Iff (ContinuousOn.{u2, u1} (SeparationQuotient.{u2} X _inst_1) Y (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) _inst_2 (SeparationQuotient.lift.{u2, u1} X Y _inst_1 f hf) s) (ContinuousOn.{u2, u1} X Y _inst_1 _inst_2 f (Set.preimage.{u2, u2} X (SeparationQuotient.{u2} X _inst_1) (SeparationQuotient.mk.{u2} X _inst_1) s))
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_on_lift SeparationQuotient.continuousOn_liftₓ'. -/
@[simp]
theorem continuousOn_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y}
    {s : Set (SeparationQuotient X)} : ContinuousOn (lift f hf) s ↔ ContinuousOn f (mk ⁻¹' s) := by
  simp only [ContinuousOn, surjective_mk.forall, continuous_within_at_lift, mem_preimage]
#align separation_quotient.continuous_on_lift SeparationQuotient.continuousOn_lift

/- warning: separation_quotient.continuous_lift -> SeparationQuotient.continuous_lift is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u1} X _inst_1 x y) -> (Eq.{succ u2} Y (f x) (f y))}, Iff (Continuous.{u1, u2} (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.topologicalSpace.{u1} X _inst_1) _inst_2 (SeparationQuotient.lift.{u1, u2} X Y _inst_1 f hf)) (Continuous.{u1, u2} X Y _inst_1 _inst_2 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] {f : X -> Y} {hf : forall (x : X) (y : X), (Inseparable.{u2} X _inst_1 x y) -> (Eq.{succ u1} Y (f x) (f y))}, Iff (Continuous.{u2, u1} (SeparationQuotient.{u2} X _inst_1) Y (instTopologicalSpaceSeparationQuotient.{u2} X _inst_1) _inst_2 (SeparationQuotient.lift.{u2, u1} X Y _inst_1 f hf)) (Continuous.{u2, u1} X Y _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_lift SeparationQuotient.continuous_liftₓ'. -/
@[simp]
theorem continuous_lift {f : X → Y} {hf : ∀ x y, (x ~ y) → f x = f y} :
    Continuous (lift f hf) ↔ Continuous f := by
  simp only [continuous_iff_continuousOn_univ, continuous_on_lift, preimage_univ]
#align separation_quotient.continuous_lift SeparationQuotient.continuous_lift

#print SeparationQuotient.lift₂ /-
/-- Lift a map `f : X → Y → α` such that `inseparable a b → inseparable c d → f a c = f b d` to a
map `separation_quotient X → separation_quotient Y → α`. -/
def lift₂ (f : X → Y → α) (hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d) :
    SeparationQuotient X → SeparationQuotient Y → α := fun x y => Quotient.liftOn₂' x y f hf
#align separation_quotient.lift₂ SeparationQuotient.lift₂
-/

/- warning: separation_quotient.lift₂_mk -> SeparationQuotient.lift₂_mk is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} (hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} α (f a b) (f c d))) (x : X) (y : Y), Eq.{succ u3} α (SeparationQuotient.lift₂.{u1, u2, u3} X Y α _inst_1 _inst_2 f hf (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y)) (f x y)
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} (hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} α (f a b) (f c d))) (x : X) (y : Y), Eq.{succ u1} α (SeparationQuotient.lift₂.{u3, u2, u1} X Y α _inst_1 _inst_2 f hf (SeparationQuotient.mk.{u3} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y)) (f x y)
Case conversion may be inaccurate. Consider using '#align separation_quotient.lift₂_mk SeparationQuotient.lift₂_mkₓ'. -/
@[simp]
theorem lift₂_mk {f : X → Y → α} (hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d) (x : X)
    (y : Y) : lift₂ f hf (mk x) (mk y) = f x y :=
  rfl
#align separation_quotient.lift₂_mk SeparationQuotient.lift₂_mk

/- warning: separation_quotient.tendsto_lift₂_nhds -> SeparationQuotient.tendsto_lift₂_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} α (f a b) (f c d))} {x : X} {y : Y} {l : Filter.{u3} α}, Iff (Filter.Tendsto.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) α (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) α (SeparationQuotient.lift₂.{u1, u2, u3} X Y α _inst_1 _inst_2 f hf)) (nhds.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) (Prod.mk.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) l) (Filter.Tendsto.{max u1 u2, u3} (Prod.{u1, u2} X Y) α (Function.uncurry.{u1, u2, u3} X Y α f) (nhds.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x y)) l)
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} α (f a b) (f c d))} {x : X} {y : Y} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) α (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) α (SeparationQuotient.lift₂.{u3, u2, u1} X Y α _inst_1 _inst_2 f hf)) (nhds.{max u3 u2} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) (Prod.mk.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) l) (Filter.Tendsto.{max u2 u3, u1} (Prod.{u3, u2} X Y) α (Function.uncurry.{u3, u2, u1} X Y α f) (nhds.{max u3 u2} (Prod.{u3, u2} X Y) (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) (Prod.mk.{u3, u2} X Y x y)) l)
Case conversion may be inaccurate. Consider using '#align separation_quotient.tendsto_lift₂_nhds SeparationQuotient.tendsto_lift₂_nhdsₓ'. -/
@[simp]
theorem tendsto_lift₂_nhds {f : X → Y → α} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝 (mk x, mk y)) l ↔ Tendsto (uncurry f) (𝓝 (x, y)) l :=
  by
  rw [← map_prod_map_mk_nhds, tendsto_map'_iff]
  rfl
#align separation_quotient.tendsto_lift₂_nhds SeparationQuotient.tendsto_lift₂_nhds

/- warning: separation_quotient.tendsto_lift₂_nhds_within -> SeparationQuotient.tendsto_lift₂_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} α (f a b) (f c d))} {x : X} {y : Y} {s : Set.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))} {l : Filter.{u3} α}, Iff (Filter.Tendsto.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) α (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) α (SeparationQuotient.lift₂.{u1, u2, u3} X Y α _inst_1 _inst_2 f hf)) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) (Prod.mk.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y)) s) l) (Filter.Tendsto.{max u1 u2, u3} (Prod.{u1, u2} X Y) α (Function.uncurry.{u1, u2, u3} X Y α f) (nhdsWithin.{max u1 u2} (Prod.{u1, u2} X Y) (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) (Prod.mk.{u1, u2} X Y x y) (Set.preimage.{max u1 u2, max u1 u2} (Prod.{u1, u2} X Y) (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u1, u1, u2, u2} X (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s)) l)
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] {f : X -> Y -> α} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} α (f a b) (f c d))} {x : X} {y : Y} {s : Set.{max u2 u3} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))} {l : Filter.{u1} α}, Iff (Filter.Tendsto.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) α (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) α (SeparationQuotient.lift₂.{u3, u2, u1} X Y α _inst_1 _inst_2 f hf)) (nhdsWithin.{max u3 u2} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) (Prod.mk.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y)) s) l) (Filter.Tendsto.{max u2 u3, u1} (Prod.{u3, u2} X Y) α (Function.uncurry.{u3, u2, u1} X Y α f) (nhdsWithin.{max u3 u2} (Prod.{u3, u2} X Y) (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) (Prod.mk.{u3, u2} X Y x y) (Set.preimage.{max u3 u2, max u2 u3} (Prod.{u3, u2} X Y) (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u3, u3, u2, u2} X (SeparationQuotient.{u3} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s)) l)
Case conversion may be inaccurate. Consider using '#align separation_quotient.tendsto_lift₂_nhds_within SeparationQuotient.tendsto_lift₂_nhdsWithinₓ'. -/
@[simp]
theorem tendsto_lift₂_nhdsWithin {f : X → Y → α} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} {s : Set (SeparationQuotient X × SeparationQuotient Y)} {l : Filter α} :
    Tendsto (uncurry <| lift₂ f hf) (𝓝[s] (mk x, mk y)) l ↔
      Tendsto (uncurry f) (𝓝[Prod.map mk mk ⁻¹' s] (x, y)) l :=
  by
  rw [nhdsWithin, ← map_prod_map_mk_nhds, ← Filter.push_pull, comap_principal]
  rfl
#align separation_quotient.tendsto_lift₂_nhds_within SeparationQuotient.tendsto_lift₂_nhdsWithin

/- warning: separation_quotient.continuous_at_lift₂ -> SeparationQuotient.continuousAt_lift₂ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} Z (f a b) (f c d))} {x : X} {y : Y}, Iff (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u1, u2, u3} X Y Z _inst_1 _inst_2 f hf)) (Prod.mk.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) (ContinuousAt.{max u1 u2, u3} (Prod.{u1, u2} X Y) Z (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} X Y Z f) (Prod.mk.{u1, u2} X Y x y))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u1} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} Z (f a b) (f c d))} {x : X} {y : Y}, Iff (ContinuousAt.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u3, u2, u1} X Y Z _inst_1 _inst_2 f hf)) (Prod.mk.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) (ContinuousAt.{max u2 u3, u1} (Prod.{u3, u2} X Y) Z (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u3, u2, u1} X Y Z f) (Prod.mk.{u3, u2} X Y x y))
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_at_lift₂ SeparationQuotient.continuousAt_lift₂ₓ'. -/
@[simp]
theorem continuousAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {x : X} {y : Y} :
    ContinuousAt (uncurry <| lift₂ f hf) (mk x, mk y) ↔ ContinuousAt (uncurry f) (x, y) :=
  tendsto_lift₂_nhds
#align separation_quotient.continuous_at_lift₂ SeparationQuotient.continuousAt_lift₂

/- warning: separation_quotient.continuous_within_at_lift₂ -> SeparationQuotient.continuousWithinAt_lift₂ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} Z (f a b) (f c d))} {s : Set.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))} {x : X} {y : Y}, Iff (ContinuousWithinAt.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u1, u2, u3} X Y Z _inst_1 _inst_2 f hf)) s (Prod.mk.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) (ContinuousWithinAt.{max u1 u2, u3} (Prod.{u1, u2} X Y) Z (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} X Y Z f) (Set.preimage.{max u1 u2, max u1 u2} (Prod.{u1, u2} X Y) (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u1, u1, u2, u2} X (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s) (Prod.mk.{u1, u2} X Y x y))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u1} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} Z (f a b) (f c d))} {s : Set.{max u2 u3} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))} {x : X} {y : Y}, Iff (ContinuousWithinAt.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u3, u2, u1} X Y Z _inst_1 _inst_2 f hf)) s (Prod.mk.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1 x) (SeparationQuotient.mk.{u2} Y _inst_2 y))) (ContinuousWithinAt.{max u2 u3, u1} (Prod.{u3, u2} X Y) Z (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u3, u2, u1} X Y Z f) (Set.preimage.{max u3 u2, max u2 u3} (Prod.{u3, u2} X Y) (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u3, u3, u2, u2} X (SeparationQuotient.{u3} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s) (Prod.mk.{u3, u2} X Y x y))
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_within_at_lift₂ SeparationQuotient.continuousWithinAt_lift₂ₓ'. -/
@[simp]
theorem continuousWithinAt_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} {x : X} {y : Y} :
    ContinuousWithinAt (uncurry <| lift₂ f hf) s (mk x, mk y) ↔
      ContinuousWithinAt (uncurry f) (Prod.map mk mk ⁻¹' s) (x, y) :=
  tendsto_lift₂_nhdsWithin
#align separation_quotient.continuous_within_at_lift₂ SeparationQuotient.continuousWithinAt_lift₂

/- warning: separation_quotient.continuous_on_lift₂ -> SeparationQuotient.continuousOn_lift₂ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} Z (f a b) (f c d))} {s : Set.{max u1 u2} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))}, Iff (ContinuousOn.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u1, u2, u3} X Y Z _inst_1 _inst_2 f hf)) s) (ContinuousOn.{max u1 u2, u3} (Prod.{u1, u2} X Y) Z (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} X Y Z f) (Set.preimage.{max u1 u2, max u1 u2} (Prod.{u1, u2} X Y) (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u1, u1, u2, u2} X (SeparationQuotient.{u1} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u1} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u1} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} Z (f a b) (f c d))} {s : Set.{max u2 u3} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2))}, Iff (ContinuousOn.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u3, u2, u1} X Y Z _inst_1 _inst_2 f hf)) s) (ContinuousOn.{max u2 u3, u1} (Prod.{u3, u2} X Y) Z (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u3, u2, u1} X Y Z f) (Set.preimage.{max u3 u2, max u2 u3} (Prod.{u3, u2} X Y) (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) (Prod.map.{u3, u3, u2, u2} X (SeparationQuotient.{u3} X _inst_1) Y (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.mk.{u3} X _inst_1) (SeparationQuotient.mk.{u2} Y _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_on_lift₂ SeparationQuotient.continuousOn_lift₂ₓ'. -/
@[simp]
theorem continuousOn_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d}
    {s : Set (SeparationQuotient X × SeparationQuotient Y)} :
    ContinuousOn (uncurry <| lift₂ f hf) s ↔ ContinuousOn (uncurry f) (Prod.map mk mk ⁻¹' s) :=
  by
  simp_rw [ContinuousOn, (surjective_mk.prod_map surjective_mk).forall, Prod.forall, Prod.map,
    continuous_within_at_lift₂]
  rfl
#align separation_quotient.continuous_on_lift₂ SeparationQuotient.continuousOn_lift₂

/- warning: separation_quotient.continuous_lift₂ -> SeparationQuotient.continuous_lift₂ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u3} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u1} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u3} Z (f a b) (f c d))}, Iff (Continuous.{max u1 u2, u3} (Prod.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (Prod.topologicalSpace.{u1, u2} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (SeparationQuotient.topologicalSpace.{u1} X _inst_1) (SeparationQuotient.topologicalSpace.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u1, u2, u3} (SeparationQuotient.{u1} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u1, u2, u3} X Y Z _inst_1 _inst_2 f hf))) (Continuous.{max u1 u2, u3} (Prod.{u1, u2} X Y) Z (Prod.topologicalSpace.{u1, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u1, u2, u3} X Y Z f))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_3 : TopologicalSpace.{u1} Z] {f : X -> Y -> Z} {hf : forall (a : X) (b : Y) (c : X) (d : Y), (Inseparable.{u3} X _inst_1 a c) -> (Inseparable.{u2} Y _inst_2 b d) -> (Eq.{succ u1} Z (f a b) (f c d))}, Iff (Continuous.{max u2 u3, u1} (Prod.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2)) Z (instTopologicalSpaceProd.{u3, u2} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) (instTopologicalSpaceSeparationQuotient.{u3} X _inst_1) (instTopologicalSpaceSeparationQuotient.{u2} Y _inst_2)) _inst_3 (Function.uncurry.{u3, u2, u1} (SeparationQuotient.{u3} X _inst_1) (SeparationQuotient.{u2} Y _inst_2) Z (SeparationQuotient.lift₂.{u3, u2, u1} X Y Z _inst_1 _inst_2 f hf))) (Continuous.{max u2 u3, u1} (Prod.{u3, u2} X Y) Z (instTopologicalSpaceProd.{u3, u2} X Y _inst_1 _inst_2) _inst_3 (Function.uncurry.{u3, u2, u1} X Y Z f))
Case conversion may be inaccurate. Consider using '#align separation_quotient.continuous_lift₂ SeparationQuotient.continuous_lift₂ₓ'. -/
@[simp]
theorem continuous_lift₂ {f : X → Y → Z} {hf : ∀ a b c d, (a ~ c) → (b ~ d) → f a b = f c d} :
    Continuous (uncurry <| lift₂ f hf) ↔ Continuous (uncurry f) := by
  simp only [continuous_iff_continuousOn_univ, continuous_on_lift₂, preimage_univ]
#align separation_quotient.continuous_lift₂ SeparationQuotient.continuous_lift₂

end SeparationQuotient

