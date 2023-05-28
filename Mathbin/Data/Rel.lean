/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.rel
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.GaloisConnection

/-!
# Relations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled relations. A relation between `α` and `β` is a function `α → β → Prop`.
Relations are also known as set-valued functions, or partial multifunctions.

## Main declarations

* `rel α β`: Relation between `α` and `β`.
* `rel.inv`: `r.inv` is the `rel β α` obtained by swapping the arguments of `r`.
* `rel.dom`: Domain of a relation. `x ∈ r.dom` iff there exists `y` such that `r x y`.
* `rel.codom`: Codomain, aka range, of a relation. `y ∈ r.codom` iff there exists `x` such that
  `r x y`.
* `rel.comp`: Relation composition. Note that the arguments order follows the `category_theory/`
  one, so `r.comp s x z ↔ ∃ y, r x y ∧ s y z`.
* `rel.image`: Image of a set under a relation. `r.image s` is the set of `f x` over all `x ∈ s`.
* `rel.preimage`: Preimage of a set under a relation. Note that `r.preimage = r.inv.image`.
* `rel.core`: Core of a set. For `s : set β`, `r.core s` is the set of `x : α` such that all `y`
  related to `x` are in `s`.
* `rel.restrict_domain`: Domain-restriction of a relation to a subtype.
* `function.graph`: Graph of a function as a relation.
-/


variable {α β γ : Type _}

#print Rel /-
/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction -/
def Rel (α β : Type _) :=
  α → β → Prop deriving CompleteLattice, Inhabited
#align rel Rel
-/

namespace Rel

variable {δ : Type _} (r : Rel α β)

#print Rel.inv /-
/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def inv : Rel β α :=
  flip r
#align rel.inv Rel.inv
-/

/- warning: rel.inv_def -> Rel.inv_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (x : α) (y : β), Iff (Rel.inv.{u1, u2} α β r y x) (r x y)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β) (x : α) (y : β), Iff (Rel.inv.{u2, u1} α β r y x) (r x y)
Case conversion may be inaccurate. Consider using '#align rel.inv_def Rel.inv_defₓ'. -/
theorem inv_def (x : α) (y : β) : r.inv y x ↔ r x y :=
  Iff.rfl
#align rel.inv_def Rel.inv_def

/- warning: rel.inv_inv -> Rel.inv_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (Rel.{u1, u2} α β) (Rel.inv.{u2, u1} β α (Rel.inv.{u1, u2} α β r)) r
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (Rel.{u2, u1} α β) (Rel.inv.{u1, u2} β α (Rel.inv.{u2, u1} α β r)) r
Case conversion may be inaccurate. Consider using '#align rel.inv_inv Rel.inv_invₓ'. -/
theorem inv_inv : inv (inv r) = r := by ext (x y); rfl
#align rel.inv_inv Rel.inv_inv

#print Rel.dom /-
/-- Domain of a relation -/
def dom :=
  { x | ∃ y, r x y }
#align rel.dom Rel.dom
-/

/- warning: rel.dom_mono -> Rel.dom_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : Rel.{u1, u2} α β} {s : Rel.{u1, u2} α β}, (LE.le.{max u1 u2} (Rel.{u1, u2} α β) (Preorder.toHasLe.{max u1 u2} (Rel.{u1, u2} α β) (PartialOrder.toPreorder.{max u1 u2} (Rel.{u1, u2} α β) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Rel.{u1, u2} α β) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Rel.{u1, u2} α β) (Rel.completeLattice.{u1, u2} α β))))) r s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Rel.dom.{u1, u2} α β r) (Rel.dom.{u1, u2} α β s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : Rel.{u2, u1} α β} {s : Rel.{u2, u1} α β}, (LE.le.{max u2 u1} (Rel.{u2, u1} α β) (Preorder.toLE.{max u2 u1} (Rel.{u2, u1} α β) (PartialOrder.toPreorder.{max u2 u1} (Rel.{u2, u1} α β) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Rel.{u2, u1} α β) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Rel.{u2, u1} α β) (instCompleteLatticeRel.{u2, u1} α β))))) r s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Rel.dom.{u2, u1} α β r) (Rel.dom.{u2, u1} α β s))
Case conversion may be inaccurate. Consider using '#align rel.dom_mono Rel.dom_monoₓ'. -/
theorem dom_mono {r s : Rel α β} (h : r ≤ s) : dom r ⊆ dom s := fun a ⟨b, hx⟩ => ⟨b, h a b hx⟩
#align rel.dom_mono Rel.dom_mono

#print Rel.codom /-
/-- Codomain aka range of a relation -/
def codom :=
  { y | ∃ x, r x y }
#align rel.codom Rel.codom
-/

/- warning: rel.codom_inv -> Rel.codom_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (Rel.codom.{u2, u1} β α (Rel.inv.{u1, u2} α β r)) (Rel.dom.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (Rel.codom.{u1, u2} β α (Rel.inv.{u2, u1} α β r)) (Rel.dom.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align rel.codom_inv Rel.codom_invₓ'. -/
theorem codom_inv : r.inv.codom = r.dom := by ext (x y); rfl
#align rel.codom_inv Rel.codom_inv

#print Rel.dom_inv /-
theorem dom_inv : r.inv.dom = r.codom := by ext (x y); rfl
#align rel.dom_inv Rel.dom_inv
-/

#print Rel.comp /-
/-- Composition of relation; note that it follows the `category_theory/` order of arguments. -/
def comp (r : Rel α β) (s : Rel β γ) : Rel α γ := fun x z => ∃ y, r x y ∧ s y z
#align rel.comp Rel.comp
-/

-- mathport name: rel.comp
local infixr:0 " ∘ " => Rel.comp

/- warning: rel.comp_assoc -> Rel.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (r : Rel.{u1, u2} α β) (s : Rel.{u2, u3} β γ) (t : Rel.{u3, u4} γ δ), Eq.{max (succ u1) (succ u4)} (Rel.{u1, u4} α δ) (Rel.comp.{u1, u3, u4} α γ δ (Rel.comp.{u1, u2, u3} α β γ r s) t) (Rel.comp.{u1, u2, u4} α β δ r (Rel.comp.{u2, u3, u4} β γ δ s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u4}} (r : Rel.{u3, u2} α β) (s : Rel.{u2, u1} β γ) (t : Rel.{u1, u4} γ δ), Eq.{max (succ u3) (succ u4)} (Rel.{u3, u4} α δ) (Rel.comp.{u3, u1, u4} α γ δ (Rel.comp.{u3, u2, u1} α β γ r s) t) (Rel.comp.{u3, u2, u4} α β δ r (Rel.comp.{u2, u1, u4} β γ δ s t))
Case conversion may be inaccurate. Consider using '#align rel.comp_assoc Rel.comp_assocₓ'. -/
theorem comp_assoc (r : Rel α β) (s : Rel β γ) (t : Rel γ δ) : ((r ∘ s) ∘ t) = (r ∘ s ∘ t) :=
  by
  unfold comp; ext (x w); constructor
  · rintro ⟨z, ⟨y, rxy, syz⟩, tzw⟩; exact ⟨y, rxy, z, syz, tzw⟩
  rintro ⟨y, rxy, z, syz, tzw⟩; exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩
#align rel.comp_assoc Rel.comp_assoc

/- warning: rel.comp_right_id -> Rel.comp_right_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (Rel.{u1, u2} α β) (Rel.comp.{u1, u2, u2} α β β r (Eq.{succ u2} β)) r
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (Rel.{u2, u1} α β) (Rel.comp.{u2, u1, u1} α β β r (Eq.{succ u1} β)) r
Case conversion may be inaccurate. Consider using '#align rel.comp_right_id Rel.comp_right_idₓ'. -/
@[simp]
theorem comp_right_id (r : Rel α β) : (r ∘ @Eq β) = r := by unfold comp; ext y; simp
#align rel.comp_right_id Rel.comp_right_id

/- warning: rel.comp_left_id -> Rel.comp_left_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{max (succ u1) (succ u2)} (Rel.{u1, u2} α β) (Rel.comp.{u1, u1, u2} α α β (Eq.{succ u1} α) r) r
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{max (succ u2) (succ u1)} (Rel.{u2, u1} α β) (Rel.comp.{u2, u2, u1} α α β (Eq.{succ u2} α) r) r
Case conversion may be inaccurate. Consider using '#align rel.comp_left_id Rel.comp_left_idₓ'. -/
@[simp]
theorem comp_left_id (r : Rel α β) : (@Eq α ∘ r) = r := by unfold comp; ext x; simp
#align rel.comp_left_id Rel.comp_left_id

#print Rel.inv_id /-
theorem inv_id : inv (@Eq α) = @Eq α := by ext (x y); constructor <;> apply Eq.symm
#align rel.inv_id Rel.inv_id
-/

/- warning: rel.inv_comp -> Rel.inv_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (r : Rel.{u1, u2} α β) (s : Rel.{u2, u3} β γ), Eq.{max (succ u3) (succ u1)} (Rel.{u3, u1} γ α) (Rel.inv.{u1, u3} α γ (Rel.comp.{u1, u2, u3} α β γ r s)) (Rel.comp.{u3, u2, u1} γ β α (Rel.inv.{u2, u3} β γ s) (Rel.inv.{u1, u2} α β r))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (r : Rel.{u3, u2} α β) (s : Rel.{u2, u1} β γ), Eq.{max (succ u3) (succ u1)} (Rel.{u1, u3} γ α) (Rel.inv.{u3, u1} α γ (Rel.comp.{u3, u2, u1} α β γ r s)) (Rel.comp.{u1, u2, u3} γ β α (Rel.inv.{u2, u1} β γ s) (Rel.inv.{u3, u2} α β r))
Case conversion may be inaccurate. Consider using '#align rel.inv_comp Rel.inv_compₓ'. -/
theorem inv_comp (r : Rel α β) (s : Rel β γ) : inv (r ∘ s) = (inv s ∘ inv r) := by ext (x z);
  simp [comp, inv, flip, and_comm]
#align rel.inv_comp Rel.inv_comp

#print Rel.image /-
/-- Image of a set under a relation -/
def image (s : Set α) : Set β :=
  { y | ∃ x ∈ s, r x y }
#align rel.image Rel.image
-/

/- warning: rel.mem_image -> Rel.mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (y : β) (s : Set.{u1} α), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y (Rel.image.{u1, u2} α β r s)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => r x y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β) (y : β) (s : Set.{u2} α), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y (Rel.image.{u2, u1} α β r s)) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (r x y)))
Case conversion may be inaccurate. Consider using '#align rel.mem_image Rel.mem_imageₓ'. -/
theorem mem_image (y : β) (s : Set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
  Iff.rfl
#align rel.mem_image Rel.mem_image

/- warning: rel.image_subset -> Rel.image_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Relator.LiftFun.{succ u1, succ u1, succ u2, succ u2} (Set.{u1} α) (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β)) (Rel.image.{u1, u2} α β r) (Rel.image.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Relator.LiftFun.{succ u2, succ u2, succ u1, succ u1} (Set.{u2} α) (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (fun (x._@.Mathlib.Data.Rel._hyg.1441 : Set.{u2} α) (x._@.Mathlib.Data.Rel._hyg.1443 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Rel._hyg.1441 x._@.Mathlib.Data.Rel._hyg.1443) (fun (x._@.Mathlib.Data.Rel._hyg.1456 : Set.{u1} β) (x._@.Mathlib.Data.Rel._hyg.1458 : Set.{u1} β) => HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) x._@.Mathlib.Data.Rel._hyg.1456 x._@.Mathlib.Data.Rel._hyg.1458) (Rel.image.{u2, u1} α β r) (Rel.image.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align rel.image_subset Rel.image_subsetₓ'. -/
theorem image_subset : ((· ⊆ ·) ⇒ (· ⊆ ·)) r.image r.image := fun s t h y ⟨x, xs, rxy⟩ =>
  ⟨x, h xs, rxy⟩
#align rel.image_subset Rel.image_subset

/- warning: rel.image_mono -> Rel.image_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Monotone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (Rel.image.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Monotone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)))))))) (Rel.image.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align rel.image_mono Rel.image_monoₓ'. -/
theorem image_mono : Monotone r.image :=
  r.image_subset
#align rel.image_mono Rel.image_mono

/- warning: rel.image_inter -> Rel.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Rel.image.{u1, u2} α β r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Rel.image.{u1, u2} α β r s) (Rel.image.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β) (s : Set.{u2} α) (t : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Rel.image.{u2, u1} α β r (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Rel.image.{u2, u1} α β r s) (Rel.image.{u2, u1} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.image_inter Rel.image_interₓ'. -/
theorem image_inter (s t : Set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
  r.image_mono.map_inf_le s t
#align rel.image_inter Rel.image_inter

/- warning: rel.image_union -> Rel.image_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Rel.image.{u1, u2} α β r (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Rel.image.{u1, u2} α β r s) (Rel.image.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β) (s : Set.{u2} α) (t : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Rel.image.{u2, u1} α β r (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Rel.image.{u2, u1} α β r s) (Rel.image.{u2, u1} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.image_union Rel.image_unionₓ'. -/
theorem image_union (s t : Set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
  le_antisymm
    (fun y ⟨x, xst, rxy⟩ =>
      xst.elim (fun xs => Or.inl ⟨x, ⟨xs, rxy⟩⟩) fun xt => Or.inr ⟨x, ⟨xt, rxy⟩⟩)
    (r.image_mono.le_map_sup s t)
#align rel.image_union Rel.image_union

#print Rel.image_id /-
@[simp]
theorem image_id (s : Set α) : image (@Eq α) s = s := by ext x; simp [mem_image]
#align rel.image_id Rel.image_id
-/

/- warning: rel.image_comp -> Rel.image_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (r : Rel.{u1, u2} α β) (s : Rel.{u2, u3} β γ) (t : Set.{u1} α), Eq.{succ u3} (Set.{u3} γ) (Rel.image.{u1, u3} α γ (Rel.comp.{u1, u2, u3} α β γ r s) t) (Rel.image.{u2, u3} β γ s (Rel.image.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (r : Rel.{u1, u3} α β) (s : Rel.{u3, u2} β γ) (t : Set.{u1} α), Eq.{succ u2} (Set.{u2} γ) (Rel.image.{u1, u2} α γ (Rel.comp.{u1, u3, u2} α β γ r s) t) (Rel.image.{u3, u2} β γ s (Rel.image.{u1, u3} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.image_comp Rel.image_compₓ'. -/
theorem image_comp (s : Rel β γ) (t : Set α) : image (r ∘ s) t = image s (image r t) :=
  by
  ext z; simp only [mem_image]; constructor
  · rintro ⟨x, xt, y, rxy, syz⟩; exact ⟨y, ⟨x, xt, rxy⟩, syz⟩
  rintro ⟨y, ⟨x, xt, rxy⟩, syz⟩; exact ⟨x, xt, y, rxy, syz⟩
#align rel.image_comp Rel.image_comp

#print Rel.image_univ /-
theorem image_univ : r.image Set.univ = r.codom := by ext y; simp [mem_image, codom]
#align rel.image_univ Rel.image_univ
-/

#print Rel.preimage /-
/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : Set β) : Set α :=
  r.inv.image s
#align rel.preimage Rel.preimage
-/

/- warning: rel.mem_preimage -> Rel.mem_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (x : α) (s : Set.{u2} β), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Rel.preimage.{u1, u2} α β r s)) (Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) => r x y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (x : α) (s : Set.{u2} β), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Rel.preimage.{u1, u2} α β r s)) (Exists.{succ u2} β (fun (y : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) (r x y)))
Case conversion may be inaccurate. Consider using '#align rel.mem_preimage Rel.mem_preimageₓ'. -/
theorem mem_preimage (x : α) (s : Set β) : x ∈ r.Preimage s ↔ ∃ y ∈ s, r x y :=
  Iff.rfl
#align rel.mem_preimage Rel.mem_preimage

/- warning: rel.preimage_def -> Rel.preimage_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α β r s) (setOf.{u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) => r x y))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α β r s) (setOf.{u1} α (fun (x : α) => Exists.{succ u2} β (fun (y : β) => And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) (r x y))))
Case conversion may be inaccurate. Consider using '#align rel.preimage_def Rel.preimage_defₓ'. -/
theorem preimage_def (s : Set β) : preimage r s = { x | ∃ y ∈ s, r x y } :=
  Set.ext fun x => mem_preimage _ _ _
#align rel.preimage_def Rel.preimage_def

#print Rel.preimage_mono /-
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : r.Preimage s ⊆ r.Preimage t :=
  image_mono _ h
#align rel.preimage_mono Rel.preimage_mono
-/

/- warning: rel.preimage_inter -> Rel.preimage_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Rel.preimage.{u1, u2} α β r (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Rel.preimage.{u1, u2} α β r s) (Rel.preimage.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Rel.preimage.{u1, u2} α β r (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Rel.preimage.{u1, u2} α β r s) (Rel.preimage.{u1, u2} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.preimage_inter Rel.preimage_interₓ'. -/
theorem preimage_inter (s t : Set β) : r.Preimage (s ∩ t) ⊆ r.Preimage s ∩ r.Preimage t :=
  image_inter _ s t
#align rel.preimage_inter Rel.preimage_inter

/- warning: rel.preimage_union -> Rel.preimage_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Rel.preimage.{u1, u2} α β r s) (Rel.preimage.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Rel.preimage.{u1, u2} α β r s) (Rel.preimage.{u1, u2} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.preimage_union Rel.preimage_unionₓ'. -/
theorem preimage_union (s t : Set β) : r.Preimage (s ∪ t) = r.Preimage s ∪ r.Preimage t :=
  image_union _ s t
#align rel.preimage_union Rel.preimage_union

#print Rel.preimage_id /-
theorem preimage_id (s : Set α) : preimage (@Eq α) s = s := by
  simp only [preimage, inv_id, image_id]
#align rel.preimage_id Rel.preimage_id
-/

/- warning: rel.preimage_comp -> Rel.preimage_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (r : Rel.{u1, u2} α β) (s : Rel.{u2, u3} β γ) (t : Set.{u3} γ), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u3} α γ (Rel.comp.{u1, u2, u3} α β γ r s) t) (Rel.preimage.{u1, u2} α β r (Rel.preimage.{u2, u3} β γ s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (r : Rel.{u1, u3} α β) (s : Rel.{u3, u2} β γ) (t : Set.{u2} γ), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α γ (Rel.comp.{u1, u3, u2} α β γ r s) t) (Rel.preimage.{u1, u3} α β r (Rel.preimage.{u3, u2} β γ s t))
Case conversion may be inaccurate. Consider using '#align rel.preimage_comp Rel.preimage_compₓ'. -/
theorem preimage_comp (s : Rel β γ) (t : Set γ) : preimage (r ∘ s) t = preimage r (preimage s t) :=
  by simp only [preimage, inv_comp, image_comp]
#align rel.preimage_comp Rel.preimage_comp

/- warning: rel.preimage_univ -> Rel.preimage_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (Rel.preimage.{u1, u2} α β r (Set.univ.{u2} β)) (Rel.dom.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (Rel.preimage.{u2, u1} α β r (Set.univ.{u1} β)) (Rel.dom.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align rel.preimage_univ Rel.preimage_univₓ'. -/
theorem preimage_univ : r.Preimage Set.univ = r.dom := by rw [preimage, image_univ, codom_inv]
#align rel.preimage_univ Rel.preimage_univ

#print Rel.core /-
/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only*
to elements of `s`. Other generalization of `function.preimage`. -/
def core (s : Set β) :=
  { x | ∀ y, r x y → y ∈ s }
#align rel.core Rel.core
-/

#print Rel.mem_core /-
theorem mem_core (x : α) (s : Set β) : x ∈ r.core s ↔ ∀ y, r x y → y ∈ s :=
  Iff.rfl
#align rel.mem_core Rel.mem_core
-/

#print Rel.core_subset /-
theorem core_subset : ((· ⊆ ·) ⇒ (· ⊆ ·)) r.core r.core := fun s t h x h' y rxy => h (h' y rxy)
#align rel.core_subset Rel.core_subset
-/

/- warning: rel.core_mono -> Rel.core_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Monotone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (Rel.core.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Monotone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (Rel.core.{u1, u2} α β r)
Case conversion may be inaccurate. Consider using '#align rel.core_mono Rel.core_monoₓ'. -/
theorem core_mono : Monotone r.core :=
  r.core_subset
#align rel.core_mono Rel.core_mono

/- warning: rel.core_inter -> Rel.core_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.core.{u1, u2} α β r (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Rel.core.{u1, u2} α β r s) (Rel.core.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Rel.core.{u1, u2} α β r (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Rel.core.{u1, u2} α β r s) (Rel.core.{u1, u2} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.core_inter Rel.core_interₓ'. -/
theorem core_inter (s t : Set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
  Set.ext (by simp [mem_core, imp_and, forall_and])
#align rel.core_inter Rel.core_inter

/- warning: rel.core_union -> Rel.core_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Rel.core.{u1, u2} α β r s) (Rel.core.{u1, u2} α β r t)) (Rel.core.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u2} β) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Rel.core.{u1, u2} α β r s) (Rel.core.{u1, u2} α β r t)) (Rel.core.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t))
Case conversion may be inaccurate. Consider using '#align rel.core_union Rel.core_unionₓ'. -/
theorem core_union (s t : Set β) : r.core s ∪ r.core t ⊆ r.core (s ∪ t) :=
  r.core_mono.le_map_sup s t
#align rel.core_union Rel.core_union

/- warning: rel.core_univ -> Rel.core_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), Eq.{succ u1} (Set.{u1} α) (Rel.core.{u1, u2} α β r (Set.univ.{u2} β)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), Eq.{succ u2} (Set.{u2} α) (Rel.core.{u2, u1} α β r (Set.univ.{u1} β)) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align rel.core_univ Rel.core_univₓ'. -/
@[simp]
theorem core_univ : r.core Set.univ = Set.univ :=
  Set.ext (by simp [mem_core])
#align rel.core_univ Rel.core_univ

#print Rel.core_id /-
theorem core_id (s : Set α) : core (@Eq α) s = s := by simp [core]
#align rel.core_id Rel.core_id
-/

/- warning: rel.core_comp -> Rel.core_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (r : Rel.{u1, u2} α β) (s : Rel.{u2, u3} β γ) (t : Set.{u3} γ), Eq.{succ u1} (Set.{u1} α) (Rel.core.{u1, u3} α γ (Rel.comp.{u1, u2, u3} α β γ r s) t) (Rel.core.{u1, u2} α β r (Rel.core.{u2, u3} β γ s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (r : Rel.{u1, u3} α β) (s : Rel.{u3, u2} β γ) (t : Set.{u2} γ), Eq.{succ u1} (Set.{u1} α) (Rel.core.{u1, u2} α γ (Rel.comp.{u1, u3, u2} α β γ r s) t) (Rel.core.{u1, u3} α β r (Rel.core.{u3, u2} β γ s t))
Case conversion may be inaccurate. Consider using '#align rel.core_comp Rel.core_compₓ'. -/
theorem core_comp (s : Rel β γ) (t : Set γ) : core (r ∘ s) t = core r (core s t) :=
  by
  ext x; simp [core, comp]; constructor
  · exact fun h y rxy z => h z y rxy
  · exact fun h z y rzy => h y rzy z
#align rel.core_comp Rel.core_comp

#print Rel.restrictDomain /-
/-- Restrict the domain of a relation to a subtype. -/
def restrictDomain (s : Set α) : Rel { x // x ∈ s } β := fun x y => r x.val y
#align rel.restrict_domain Rel.restrictDomain
-/

/- warning: rel.image_subset_iff -> Rel.image_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β) (s : Set.{u1} α) (t : Set.{u2} β), Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Rel.image.{u1, u2} α β r s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Rel.core.{u1, u2} α β r t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β) (s : Set.{u2} α) (t : Set.{u1} β), Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Rel.image.{u2, u1} α β r s) t) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Rel.core.{u2, u1} α β r t))
Case conversion may be inaccurate. Consider using '#align rel.image_subset_iff Rel.image_subset_iffₓ'. -/
theorem image_subset_iff (s : Set α) (t : Set β) : image r s ⊆ t ↔ s ⊆ core r t :=
  Iff.intro (fun h x xs y rxy => h ⟨x, xs, rxy⟩) fun h y ⟨x, xs, rxy⟩ => h xs y rxy
#align rel.image_subset_iff Rel.image_subset_iff

/- warning: rel.image_core_gc -> Rel.image_core_gc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : Rel.{u1, u2} α β), GaloisConnection.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (Rel.image.{u1, u2} α β r) (Rel.core.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : Rel.{u2, u1} α β), GaloisConnection.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeInf.{u2} (Set.{u2} α) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} α) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} α) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)))))))) (Rel.image.{u2, u1} α β r) (Rel.core.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align rel.image_core_gc Rel.image_core_gcₓ'. -/
theorem image_core_gc : GaloisConnection r.image r.core :=
  image_subset_iff _
#align rel.image_core_gc Rel.image_core_gc

end Rel

namespace Function

#print Function.graph /-
/-- The graph of a function as a relation. -/
def graph (f : α → β) : Rel α β := fun x y => f x = y
#align function.graph Function.graph
-/

end Function

namespace Set

/- warning: set.image_eq -> Set.image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f s) (Rel.image.{u1, u2} α β (Function.graph.{u1, u2} α β f) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f s) (Rel.image.{u2, u1} α β (Function.graph.{u2, u1} α β f) s)
Case conversion may be inaccurate. Consider using '#align set.image_eq Set.image_eqₓ'. -/
-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional
theorem image_eq (f : α → β) (s : Set α) : f '' s = (Function.graph f).image s := by
  simp [Set.image, Function.graph, Rel.image]
#align set.image_eq Set.image_eq

#print Set.preimage_eq /-
theorem preimage_eq (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).Preimage s := by
  simp [Set.preimage, Function.graph, Rel.preimage, Rel.inv, flip, Rel.image]
#align set.preimage_eq Set.preimage_eq
-/

#print Set.preimage_eq_core /-
theorem preimage_eq_core (f : α → β) (s : Set β) : f ⁻¹' s = (Function.graph f).core s := by
  simp [Set.preimage, Function.graph, Rel.core]
#align set.preimage_eq_core Set.preimage_eq_core
-/

end Set

