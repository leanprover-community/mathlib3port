/-
Copyright (c) 2023 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle

! This file was ported from Lean 3 source module combinatorics.quiver.single_obj
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Cast
import Mathbin.Combinatorics.Quiver.Symmetric

/-!
# Single-object quiver

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `single_obj α` is the `unit` type, whose single object is called `star α`, with
`quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`to_hom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `path_equiv_list`.
-/


namespace Quiver

#print Quiver.SingleObj /-
/-- Type tag on `unit` used to define single-object quivers. -/
@[nolint unused_arguments]
def SingleObj (α : Type _) : Type :=
  Unit deriving Unique
#align quiver.single_obj Quiver.SingleObj
-/

namespace SingleObj

variable (α β γ : Type _)

instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

#print Quiver.SingleObj.star /-
/-- The single object in `single_obj α`. -/
def star : SingleObj α :=
  Unit.unit
#align quiver.single_obj.star Quiver.SingleObj.star
-/

instance : Inhabited (SingleObj α) :=
  ⟨star α⟩

variable {α β γ}

#print Quiver.SingleObj.hasReverse /-
-- See note [reducible non-instances]
/-- Equip `single_obj α` with a reverse operation. -/
@[reducible]
def hasReverse (rev : α → α) : HasReverse (SingleObj α) :=
  ⟨fun _ _ => rev⟩
#align quiver.single_obj.has_reverse Quiver.SingleObj.hasReverse
-/

#print Quiver.SingleObj.hasInvolutiveReverse /-
-- See note [reducible non-instances]
/-- Equip `single_obj α` with an involutive reverse operation. -/
@[reducible]
def hasInvolutiveReverse (rev : α → α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α)
    where
  toHasReverse := hasReverse rev
  inv' _ _ := h
#align quiver.single_obj.has_involutive_reverse Quiver.SingleObj.hasInvolutiveReverse
-/

#print Quiver.SingleObj.toHom /-
/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps]
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _
#align quiver.single_obj.to_hom Quiver.SingleObj.toHom
-/

#print Quiver.SingleObj.toPrefunctor /-
/-- Prefunctors between two `single_obj` quivers correspond to functions between the corresponding
arrows types.
-/
@[simps]
def toPrefunctor : (α → β) ≃ SingleObj α ⥤q SingleObj β
    where
  toFun f := ⟨id, fun _ _ => f⟩
  invFun f a := f.map (toHom a)
  left_inv _ := rfl
  right_inv f := by cases f <;> obviously
#align quiver.single_obj.to_prefunctor Quiver.SingleObj.toPrefunctor
-/

#print Quiver.SingleObj.toPrefunctor_id /-
theorem toPrefunctor_id : toPrefunctor id = 𝟭q (SingleObj α) :=
  rfl
#align quiver.single_obj.to_prefunctor_id Quiver.SingleObj.toPrefunctor_id
-/

#print Quiver.SingleObj.toPrefunctor_symm_id /-
@[simp]
theorem toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl
#align quiver.single_obj.to_prefunctor_symm_id Quiver.SingleObj.toPrefunctor_symm_id
-/

/- warning: quiver.single_obj.to_prefunctor_comp -> Quiver.SingleObj.toPrefunctor_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : α -> β) (g : β -> γ), Eq.{max 1 (succ u1) (succ u3)} (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (coeFn.{max 1 (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (α -> γ) (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (fun (_x : Equiv.{max (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (α -> γ) (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) => (α -> γ) -> (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (α -> γ) (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (Quiver.SingleObj.toPrefunctor.{u1, u3} α γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Prefunctor.comp.{0, succ u1, 0, succ u2, 0, succ u3} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ) (coeFn.{max 1 (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (α -> β) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β))) (fun (_x : Equiv.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (α -> β) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β))) => (α -> β) -> (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (α -> β) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β))) (Quiver.SingleObj.toPrefunctor.{u1, u2} α β) f) (coeFn.{max 1 (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (β -> γ) (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (fun (_x : Equiv.{max (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (β -> γ) (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) => (β -> γ) -> (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (β -> γ) (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ))) (Quiver.SingleObj.toPrefunctor.{u2, u3} β γ) g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (f : α -> β) (g : β -> γ), Eq.{max (succ u3) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α -> γ) => Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ)) (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (α -> γ) (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ))) (α -> γ) (fun (_x : α -> γ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α -> γ) => Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (α -> γ) (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ))) (Quiver.SingleObj.toPrefunctor.{u3, u2} α γ) (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (Prefunctor.comp.{0, succ u3, 0, succ u1, 0, succ u2} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ) (FunLike.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (α -> β) (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β))) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α -> β) => Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (α -> β) (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β))) (Quiver.SingleObj.toPrefunctor.{u3, u1} α β) f) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (β -> γ) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ))) (β -> γ) (fun (_x : β -> γ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β -> γ) => Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (β -> γ) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} β) (Quiver.SingleObj.instQuiverSingleObj.{u1} β) (Quiver.SingleObj.{u2} γ) (Quiver.SingleObj.instQuiverSingleObj.{u2} γ))) (Quiver.SingleObj.toPrefunctor.{u1, u2} β γ) g))
Case conversion may be inaccurate. Consider using '#align quiver.single_obj.to_prefunctor_comp Quiver.SingleObj.toPrefunctor_compₓ'. -/
theorem toPrefunctor_comp (f : α → β) (g : β → γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl
#align quiver.single_obj.to_prefunctor_comp Quiver.SingleObj.toPrefunctor_comp

/- warning: quiver.single_obj.to_prefunctor_symm_comp -> Quiver.SingleObj.toPrefunctor_symm_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) (g : Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max 1 (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (Equiv.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (α -> γ)) (fun (_x : Equiv.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (α -> γ)) => (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) -> α -> γ) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (α -> γ)) (Equiv.symm.{max (succ u1) (succ u3), max 1 (succ u1) (succ u3)} (α -> γ) (Prefunctor.{succ u1, succ u3, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (Quiver.SingleObj.toPrefunctor.{u1, u3} α γ)) (Prefunctor.comp.{0, succ u1, 0, succ u2, 0, succ u3} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ) f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max 1 (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (Equiv.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (β -> γ)) (fun (_x : Equiv.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (β -> γ)) => (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) -> β -> γ) (Equiv.hasCoeToFun.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (β -> γ)) (Equiv.symm.{max (succ u2) (succ u3), max 1 (succ u2) (succ u3)} (β -> γ) (Prefunctor.{succ u2, succ u3, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β) (Quiver.SingleObj.{u3} γ) (Quiver.SingleObj.quiver.{u3} γ)) (Quiver.SingleObj.toPrefunctor.{u2, u3} β γ)) g) (coeFn.{max 1 (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) (α -> β)) (fun (_x : Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) (α -> β)) => (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) -> α -> β) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) (α -> β)) (Equiv.symm.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (α -> β) (Prefunctor.{succ u1, succ u2, 0, 0} (Quiver.SingleObj.{u1} α) (Quiver.SingleObj.quiver.{u1} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.quiver.{u2} β)) (Quiver.SingleObj.toPrefunctor.{u1, u2} α β)) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) (g : Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)), Eq.{max (succ u3) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) => α -> γ) (Prefunctor.comp.{0, succ u3, 0, succ u2, 0, succ u1} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ) f g)) (FunLike.coe.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (α -> γ)) (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (fun (_x : Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) => α -> γ) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (α -> γ)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (α -> γ) (Prefunctor.{succ u3, succ u1, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (Quiver.SingleObj.toPrefunctor.{u3, u1} α γ)) (Prefunctor.comp.{0, succ u3, 0, succ u2, 0, succ u1} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ) f g)) (Function.comp.{succ u3, succ u2, succ u1} α β γ (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (β -> γ)) (Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (fun (_x : Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) => β -> γ) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (β -> γ)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (β -> γ) (Prefunctor.{succ u2, succ u1, 0, 0} (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β) (Quiver.SingleObj.{u1} γ) (Quiver.SingleObj.instQuiverSingleObj.{u1} γ)) (Quiver.SingleObj.toPrefunctor.{u2, u1} β γ)) g) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) (α -> β)) (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) (fun (_x : Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) => α -> β) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) (α -> β)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (α -> β) (Prefunctor.{succ u3, succ u2, 0, 0} (Quiver.SingleObj.{u3} α) (Quiver.SingleObj.instQuiverSingleObj.{u3} α) (Quiver.SingleObj.{u2} β) (Quiver.SingleObj.instQuiverSingleObj.{u2} β)) (Quiver.SingleObj.toPrefunctor.{u3, u2} α β)) f))
Case conversion may be inaccurate. Consider using '#align quiver.single_obj.to_prefunctor_symm_comp Quiver.SingleObj.toPrefunctor_symm_compₓ'. -/
@[simp]
theorem toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, to_prefunctor_comp, Equiv.apply_symm_apply]
#align quiver.single_obj.to_prefunctor_symm_comp Quiver.SingleObj.toPrefunctor_symm_comp

#print Quiver.SingleObj.pathToList /-
/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`.
-/
@[simp]
def pathToList : ∀ {x : SingleObj α}, Path (star α) x → List α
  | _, path.nil => []
  | _, path.cons p a => a :: path_to_list p
#align quiver.single_obj.path_to_list Quiver.SingleObj.pathToList
-/

#print Quiver.SingleObj.listToPath /-
/-- Auxiliary definition for `quiver.single_obj.path_equiv_list`.
Converts a list of elements of type `α` into a path in the quiver `single_obj α`.
-/
@[simp]
def listToPath : List α → Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (list_to_path l).cons a
#align quiver.single_obj.list_to_path Quiver.SingleObj.listToPath
-/

#print Quiver.SingleObj.listToPath_pathToList /-
theorem listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl Unit.ext :=
  by
  induction' p with y z p a ih
  rfl
  tidy
#align quiver.single_obj.path_to_list_to_path Quiver.SingleObj.listToPath_pathToList
-/

#print Quiver.SingleObj.pathToList_listToPath /-
theorem pathToList_listToPath (l : List α) : pathToList (listToPath l) = l :=
  by
  induction' l with a l ih
  rfl
  simp [ih]
#align quiver.single_obj.list_to_path_to_list Quiver.SingleObj.pathToList_listToPath
-/

#print Quiver.SingleObj.pathEquivList /-
/-- Paths in `single_obj α` quiver correspond to lists of elements of type `α`. -/
def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩
#align quiver.single_obj.path_equiv_list Quiver.SingleObj.pathEquivList
-/

#print Quiver.SingleObj.pathEquivList_nil /-
@[simp]
theorem pathEquivList_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl
#align quiver.single_obj.path_equiv_list_nil Quiver.SingleObj.pathEquivList_nil
-/

#print Quiver.SingleObj.pathEquivList_cons /-
@[simp]
theorem pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl
#align quiver.single_obj.path_equiv_list_cons Quiver.SingleObj.pathEquivList_cons
-/

#print Quiver.SingleObj.pathEquivList_symm_nil /-
@[simp]
theorem pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_nil Quiver.SingleObj.pathEquivList_symm_nil
-/

#print Quiver.SingleObj.pathEquivList_symm_cons /-
@[simp]
theorem pathEquivList_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl
#align quiver.single_obj.path_equiv_list_symm_cons Quiver.SingleObj.pathEquivList_symm_cons
-/

end SingleObj

end Quiver

