/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.bornology.hom
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Bornology.Basic

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `locally_bounded_map`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `locally_bounded_map_class`
-/


open Bornology Filter Function Set

variable {F α β γ δ : Type _}

#print LocallyBoundedMap /-
/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure LocallyBoundedMap (α β : Type _) [Bornology α] [Bornology β] where
  toFun : α → β
  comap_cobounded_le' : (cobounded β).comap to_fun ≤ cobounded α
#align locally_bounded_map LocallyBoundedMap
-/

section

#print LocallyBoundedMapClass /-
/-- `locally_bounded_map_class F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `locally_bounded_map`. -/
class LocallyBoundedMapClass (F : Type _) (α β : outParam <| Type _) [Bornology α]
  [Bornology β] extends FunLike F α fun _ => β where
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α
#align locally_bounded_map_class LocallyBoundedMapClass
-/

end

export LocallyBoundedMapClass (comap_cobounded_le)

/- warning: is_bounded.image -> IsBounded.image is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u3} β] [_inst_3 : LocallyBoundedMapClass.{u1, u2, u3} F α β _inst_1 _inst_2] {f : F} {s : Set.{u2} α}, (Bornology.IsBounded.{u2} α _inst_1 s) -> (Bornology.IsBounded.{u3} β _inst_2 (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (LocallyBoundedMapClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f) s))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Bornology.{u3} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : LocallyBoundedMapClass.{u1, u3, u2} F α β _inst_1 _inst_2] {f : F} {s : Set.{u3} α}, (Bornology.IsBounded.{u3} α _inst_1 s) -> (Bornology.IsBounded.{u2} β _inst_2 (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3) f) s))
Case conversion may be inaccurate. Consider using '#align is_bounded.image IsBounded.imageₓ'. -/
theorem IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] {f : F}
    {s : Set α} (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs
#align is_bounded.image IsBounded.image

instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] :
    CoeTC F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
  comap_cobounded_le f := f.comap_cobounded_le'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LocallyBoundedMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: locally_bounded_map.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: locally_bounded_map.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] {f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (LocallyBoundedMap.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {f : LocallyBoundedMap α β} : f.toFun = (f : α → β) :=
  rfl
#align locally_bounded_map.to_fun_eq_coe [anonymous]

/- warning: locally_bounded_map.ext -> LocallyBoundedMap.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] {f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2} {g : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] {f : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2} {g : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.ext LocallyBoundedMap.extₓ'. -/
@[ext]
theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align locally_bounded_map.ext LocallyBoundedMap.ext

/- warning: locally_bounded_map.copy -> LocallyBoundedMap.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u2, u1, u2} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2)) f)) -> (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.copy LocallyBoundedMap.copyₓ'. -/
/-- Copy of a `locally_bounded_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩
#align locally_bounded_map.copy LocallyBoundedMap.copy

/- warning: locally_bounded_map.coe_copy -> LocallyBoundedMap.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) (LocallyBoundedMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.coe_copy LocallyBoundedMap.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align locally_bounded_map.coe_copy LocallyBoundedMap.coe_copy

/- warning: locally_bounded_map.copy_eq -> LocallyBoundedMap.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) (LocallyBoundedMap.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.copy_eq LocallyBoundedMap.copy_eqₓ'. -/
theorem copy_eq (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align locally_bounded_map.copy_eq LocallyBoundedMap.copy_eq

#print LocallyBoundedMap.ofMapBounded /-
/-- Construct a `locally_bounded_map` from the fact that the function maps bounded sets to bounded
sets. -/
def ofMapBounded (f : α → β) (h) : LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩
#align locally_bounded_map.of_map_bounded LocallyBoundedMap.ofMapBounded
-/

/- warning: locally_bounded_map.coe_of_map_bounded -> LocallyBoundedMap.coe_ofMapBounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : α -> β) {h : forall {{s : Set.{u1} α}}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u2} β _inst_2 (Set.image.{u1, u2} α β f s))}, Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.ofMapBounded.{u1, u2} α β _inst_1 _inst_2 f h)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : α -> β) {h : forall {{s : Set.{u2} α}}, (Bornology.IsBounded.{u2} α _inst_1 s) -> (Bornology.IsBounded.{u1} β _inst_2 (Set.image.{u2, u1} α β f s))}, Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) (LocallyBoundedMap.ofMapBounded.{u2, u1} α β _inst_1 _inst_2 f h)) f
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.coe_of_map_bounded LocallyBoundedMap.coe_ofMapBoundedₓ'. -/
@[simp]
theorem coe_ofMapBounded (f : α → β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl
#align locally_bounded_map.coe_of_map_bounded LocallyBoundedMap.coe_ofMapBounded

/- warning: locally_bounded_map.of_map_bounded_apply -> LocallyBoundedMap.ofMapBounded_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : α -> β) {h : forall {{s : Set.{u1} α}}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u2} β _inst_2 (Set.image.{u1, u2} α β f s))} (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.ofMapBounded.{u1, u2} α β _inst_1 _inst_2 f h) a) (f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : α -> β) {h : forall {{s : Set.{u2} α}}, (Bornology.IsBounded.{u2} α _inst_1 s) -> (Bornology.IsBounded.{u1} β _inst_2 (Set.image.{u2, u1} α β f s))} (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u2 u1, u2, u1} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2)) (LocallyBoundedMap.ofMapBounded.{u2, u1} α β _inst_1 _inst_2 f h) a) (f a)
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.of_map_bounded_apply LocallyBoundedMap.ofMapBounded_applyₓ'. -/
@[simp]
theorem ofMapBounded_apply (f : α → β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl
#align locally_bounded_map.of_map_bounded_apply LocallyBoundedMap.ofMapBounded_apply

variable (α)

#print LocallyBoundedMap.id /-
/-- `id` as a `locally_bounded_map`. -/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩
#align locally_bounded_map.id LocallyBoundedMap.id
-/

instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

/- warning: locally_bounded_map.coe_id -> LocallyBoundedMap.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Bornology.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (LocallyBoundedMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (LocallyBoundedMap.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Bornology.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => α) _x) (LocallyBoundedMapClass.toFunLike.{u1, u1, u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1)) (LocallyBoundedMap.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.coe_id LocallyBoundedMap.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl
#align locally_bounded_map.coe_id LocallyBoundedMap.coe_id

variable {α}

/- warning: locally_bounded_map.id_apply -> LocallyBoundedMap.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) (fun (_x : LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) => α -> α) (LocallyBoundedMap.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (LocallyBoundedMap.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => α) _x) (LocallyBoundedMapClass.toFunLike.{u1, u1, u1} (LocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u1} α α _inst_1 _inst_1)) (LocallyBoundedMap.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.id_apply LocallyBoundedMap.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl
#align locally_bounded_map.id_apply LocallyBoundedMap.id_apply

#print LocallyBoundedMap.comp /-
/-- Composition of `locally_bounded_map`s as a `locally_bounded_map`. -/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ
    where
  toFun := f ∘ g
  comap_cobounded_le' :=
    comap_comap.ge.trans <| (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'
#align locally_bounded_map.comp LocallyBoundedMap.comp
-/

/- warning: locally_bounded_map.coe_comp -> LocallyBoundedMap.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u3} γ] (f : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (g : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (LocallyBoundedMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocallyBoundedMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u3} β] [_inst_3 : Bornology.{u2} γ] (f : LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) (g : LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => γ) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u2, u1, u2} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3)) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : β) => γ) _x) (LocallyBoundedMapClass.toFunLike.{max u3 u2, u3, u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u3, u1, u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.coe_comp LocallyBoundedMap.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align locally_bounded_map.coe_comp LocallyBoundedMap.coe_comp

/- warning: locally_bounded_map.comp_apply -> LocallyBoundedMap.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u3} γ] (f : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (g : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (LocallyBoundedMap.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocallyBoundedMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u3} β] [_inst_3 : Bornology.{u2} γ] (f : LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) (g : LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => γ) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u2, u1, u2} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3)) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : β) => γ) _x) (LocallyBoundedMapClass.toFunLike.{max u3 u2, u3, u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u3, u1, u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.comp_apply LocallyBoundedMap.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) :
    f.comp g a = f (g a) :=
  rfl
#align locally_bounded_map.comp_apply LocallyBoundedMap.comp_apply

/- warning: locally_bounded_map.comp_assoc -> LocallyBoundedMap.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u3} γ] [_inst_4 : Bornology.{u4} δ] (f : LocallyBoundedMap.{u3, u4} γ δ _inst_3 _inst_4) (g : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (h : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (LocallyBoundedMap.{u1, u4} α δ _inst_1 _inst_4) (LocallyBoundedMap.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (LocallyBoundedMap.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (LocallyBoundedMap.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u4} γ] [_inst_4 : Bornology.{u3} δ] (f : LocallyBoundedMap.{u4, u3} γ δ _inst_3 _inst_4) (g : LocallyBoundedMap.{u2, u4} β γ _inst_2 _inst_3) (h : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α δ _inst_1 _inst_4) (LocallyBoundedMap.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (LocallyBoundedMap.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (LocallyBoundedMap.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (LocallyBoundedMap.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.comp_assoc LocallyBoundedMap.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ)
    (h : LocallyBoundedMap α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align locally_bounded_map.comp_assoc LocallyBoundedMap.comp_assoc

/- warning: locally_bounded_map.comp_id -> LocallyBoundedMap.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (LocallyBoundedMap.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) (LocallyBoundedMap.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (LocallyBoundedMap.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.comp_id LocallyBoundedMap.comp_idₓ'. -/
@[simp]
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun a => rfl
#align locally_bounded_map.comp_id LocallyBoundedMap.comp_id

/- warning: locally_bounded_map.id_comp -> LocallyBoundedMap.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] (f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (LocallyBoundedMap.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (LocallyBoundedMap.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Bornology.{u1} β] (f : LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (LocallyBoundedMap.{u2, u1} α β _inst_1 _inst_2) (LocallyBoundedMap.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (LocallyBoundedMap.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.id_comp LocallyBoundedMap.id_compₓ'. -/
@[simp]
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun a => rfl
#align locally_bounded_map.id_comp LocallyBoundedMap.id_comp

/- warning: locally_bounded_map.cancel_right -> LocallyBoundedMap.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u3} γ] {g₁ : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3} {g₂ : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3} {f : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (LocallyBoundedMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u3} β] [_inst_3 : Bornology.{u2} γ] {g₁ : LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3} {g₂ : LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3} {f : LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : α) => β) _x) (LocallyBoundedMapClass.toFunLike.{max u1 u3, u1, u3} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.cancel_right LocallyBoundedMap.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align locally_bounded_map.cancel_right LocallyBoundedMap.cancel_right

/- warning: locally_bounded_map.cancel_left -> LocallyBoundedMap.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] [_inst_3 : Bornology.{u3} γ] {g : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3} {f₁ : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2} {f₂ : LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : LocallyBoundedMap.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (LocallyBoundedMap.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (LocallyBoundedMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u3} β] [_inst_3 : Bornology.{u2} γ] {g : LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3} {f₁ : LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2} {f₂ : LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Topology.Bornology.Hom._hyg.92 : β) => γ) _x) (LocallyBoundedMapClass.toFunLike.{max u3 u2, u3, u2} (LocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (LocallyBoundedMap.instLocallyBoundedMapClassLocallyBoundedMap.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (LocallyBoundedMap.{u1, u2} α γ _inst_1 _inst_3) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (LocallyBoundedMap.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (LocallyBoundedMap.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align locally_bounded_map.cancel_left LocallyBoundedMap.cancel_leftₓ'. -/
theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align locally_bounded_map.cancel_left LocallyBoundedMap.cancel_left

end LocallyBoundedMap

