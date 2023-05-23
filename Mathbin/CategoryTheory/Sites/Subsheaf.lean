/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.sites.subsheaf
! leanprover-community/mathlib commit 2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Elementwise
import Mathbin.CategoryTheory.Adjunction.Evaluation
import Mathbin.CategoryTheory.Sites.Sheafification

/-!

# Subsheaf of types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the sub(pre)sheaf of a type valued presheaf.

## Main results

- `category_theory.grothendieck_topology.subpresheaf` :
  A subpresheaf of a presheaf of types.
- `category_theory.grothendieck_topology.subpresheaf.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `category_theory.grothendieck_topology.subpresheaf.sheafify_is_sheaf` :
  The sheafification is a sheaf
- `category_theory.grothendieck_topology.subpresheaf.sheafify_lift` :
  The descent of a map into a sheaf to the sheafification.
- `category_theory.grothendieck_topology.image_sheaf` : The image sheaf of a morphism.
- `category_theory.grothendieck_topology.image_factorization` : The image sheaf as a
  `limits.image_factorization`.
-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

#print CategoryTheory.GrothendieckTopology.Subpresheaf /-
/-- A subpresheaf of a presheaf consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure Subpresheaf (F : Cᵒᵖ ⥤ Type w) where
  obj : ∀ U, Set (F.obj U)
  map : ∀ {U V : Cᵒᵖ} (i : U ⟶ V), obj U ⊆ F.map i ⁻¹' obj V
#align category_theory.grothendieck_topology.subpresheaf CategoryTheory.GrothendieckTopology.Subpresheaf
-/

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subpresheaf F)

instance : PartialOrder (Subpresheaf F) :=
  PartialOrder.lift Subpresheaf.obj Subpresheaf.ext

instance : Top (Subpresheaf F) :=
  ⟨⟨fun U => ⊤, fun U V i x h => trivial⟩⟩

instance : Nonempty (Subpresheaf F) :=
  inferInstance

#print CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf /-
/-- The subpresheaf as a presheaf. -/
@[simps]
def Subpresheaf.toPresheaf : Cᵒᵖ ⥤ Type w
    where
  obj U := G.obj U
  map U V i x := ⟨F.map i x, G.map i x.Prop⟩
  map_id' X := by
    ext ⟨x, _⟩
    dsimp
    rw [F.map_id]
    rfl
  map_comp' X Y Z i j := by
    ext ⟨x, _⟩
    dsimp
    rw [F.map_comp]
    rfl
#align category_theory.grothendieck_topology.subpresheaf.to_presheaf CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf
-/

instance {U} : Coe (G.toPresheaf.obj U) (F.obj U) :=
  coeSubtype

#print CategoryTheory.GrothendieckTopology.Subpresheaf.ι /-
/-- The inclusion of a subpresheaf to the original presheaf. -/
@[simps]
def Subpresheaf.ι : G.toPresheaf ⟶ F where app U x := x
#align category_theory.grothendieck_topology.subpresheaf.ι CategoryTheory.GrothendieckTopology.Subpresheaf.ι
-/

instance : Mono G.ι :=
  ⟨fun H f₁ f₂ e =>
    NatTrans.ext f₁ f₂ <|
      funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/- warning: category_theory.grothendieck_topology.subpresheaf.hom_of_le -> CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} {G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F}, (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F))) G G') -> (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G'))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} {G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F}, (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F))) G G') -> (Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G'))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.hom_of_le CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLeₓ'. -/
/-- The inclusion of a subpresheaf to a larger subpresheaf -/
@[simps]
def Subpresheaf.homOfLe {G G' : Subpresheaf F} (h : G ≤ G') : G.toPresheaf ⟶ G'.toPresheaf
    where app U x := ⟨x, h U x.Prop⟩
#align category_theory.grothendieck_topology.subpresheaf.hom_of_le CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe

instance {G G' : Subpresheaf F} (h : G ≤ G') : Mono (Subpresheaf.homOfLe h) :=
  ⟨fun H f₁ f₂ e =>
    NatTrans.ext f₁ f₂ <|
      funext fun U =>
        funext fun x =>
          Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x : _) : _)⟩

/- warning: category_theory.grothendieck_topology.subpresheaf.hom_of_le_ι -> CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} {G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} (h : LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F))) G G'), Eq.{succ (max u3 u1)} (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F) (CategoryTheory.CategoryStruct.comp.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G') F (CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe.{u1, u2, u3} C _inst_1 F G G' h) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G')) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} {G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F} (h : LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F))) G G'), Eq.{max (succ u3) (succ u1)} (Quiver.Hom.{succ (max u3 u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F) (CategoryTheory.CategoryStruct.comp.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G') F (CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe.{u1, u2, u3} C _inst_1 F G G' h) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G')) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.hom_of_le_ι CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe_ιₓ'. -/
@[simp, reassoc]
theorem Subpresheaf.homOfLe_ι {G G' : Subpresheaf F} (h : G ≤ G') :
    Subpresheaf.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl
#align category_theory.grothendieck_topology.subpresheaf.hom_of_le_ι CategoryTheory.GrothendieckTopology.Subpresheaf.homOfLe_ι

instance : IsIso (Subpresheaf.ι (⊤ : Subpresheaf F)) :=
  by
  apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
  · intro X
    rw [is_iso_iff_bijective]
    exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

/- warning: category_theory.grothendieck_topology.subpresheaf.eq_top_iff_is_iso -> CategoryTheory.GrothendieckTopology.Subpresheaf.eq_top_iff_isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), Iff (Eq.{max (succ u3) (succ u1)} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) G (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.hasTop.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.IsIso.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), Iff (Eq.{max (succ u3) (succ u1)} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) G (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instTopSubpresheaf.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.IsIso.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.eq_top_iff_is_iso CategoryTheory.GrothendieckTopology.Subpresheaf.eq_top_iff_isIsoₓ'. -/
theorem Subpresheaf.eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι :=
  by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext (U x)
    apply (iff_true_iff _).mpr
    rw [← is_iso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2
#align category_theory.grothendieck_topology.subpresheaf.eq_top_iff_is_iso CategoryTheory.GrothendieckTopology.Subpresheaf.eq_top_iff_isIso

/- warning: category_theory.grothendieck_topology.subpresheaf.lift -> CategoryTheory.GrothendieckTopology.Subpresheaf.lift is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F), (forall (U : Opposite.{succ u3} C) (x : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' U), Membership.Mem.{u1, u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Set.hasMem.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' F f U x) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)) -> (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F), (forall (U : Opposite.{succ u3} C) (x : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F') U), Membership.mem.{u1, u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Set.instMembershipSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' F f U x) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)) -> (Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.lift CategoryTheory.GrothendieckTopology.Subpresheaf.liftₓ'. -/
/-- If the image of a morphism falls in a subpresheaf, then the morphism factors through it. -/
@[simps]
def Subpresheaf.lift (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) : F' ⟶ G.toPresheaf
    where
  app U x := ⟨f.app U x, hf U x⟩
  naturality' := by
    have := elementwise_of f.naturality
    intros
    ext
    simp [this]
#align category_theory.grothendieck_topology.subpresheaf.lift CategoryTheory.GrothendieckTopology.Subpresheaf.lift

/- warning: category_theory.grothendieck_topology.subpresheaf.lift_ι -> CategoryTheory.GrothendieckTopology.Subpresheaf.lift_ι is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F) (hf : forall (U : Opposite.{succ u3} C) (x : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' U), Membership.Mem.{u1, u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Set.hasMem.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' F f U x) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)), Eq.{succ (max u3 u1)} (Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F) (CategoryTheory.CategoryStruct.comp.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F (CategoryTheory.GrothendieckTopology.Subpresheaf.lift.{u1, u2, u3} C _inst_1 F F' G f hf) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G)) f
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F) (hf : forall (U : Opposite.{succ u3} C) (x : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F') U), Membership.mem.{u1, u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Set.instMembershipSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' F f U x) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)), Eq.{max (succ u3) (succ u1)} (Quiver.Hom.{succ (max u3 u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F) (CategoryTheory.CategoryStruct.comp.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) F (CategoryTheory.GrothendieckTopology.Subpresheaf.lift.{u1, u2, u3} C _inst_1 F F' G f hf) (CategoryTheory.GrothendieckTopology.Subpresheaf.ι.{u1, u2, u3} C _inst_1 F G)) f
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.lift_ι CategoryTheory.GrothendieckTopology.Subpresheaf.lift_ιₓ'. -/
@[simp, reassoc]
theorem Subpresheaf.lift_ι (f : F' ⟶ F) (hf : ∀ U x, f.app U x ∈ G.obj U) : G.lift f hf ≫ G.ι = f :=
  by
  ext
  rfl
#align category_theory.grothendieck_topology.subpresheaf.lift_ι CategoryTheory.GrothendieckTopology.Subpresheaf.lift_ι

/- warning: category_theory.grothendieck_topology.subpresheaf.sieve_of_section -> CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) -> (forall {U : Opposite.{succ u3} C}, (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) -> (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) -> (forall {U : Opposite.{succ u3} C}, (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) -> (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U)))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.sieve_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSectionₓ'. -/
/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
def Subpresheaf.sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U)
    where
  arrows V f := F.map f.op s ∈ G.obj (op V)
  downward_closed' V W i hi j :=
    by
    rw [op_comp, functor_to_types.map_comp_apply]
    exact G.map _ hi
#align category_theory.grothendieck_topology.subpresheaf.sieve_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection

/- warning: category_theory.grothendieck_topology.subpresheaf.family_of_elements_of_section -> CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSection is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) {U : Opposite.{succ u3} C} (s : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U), CategoryTheory.Presieve.FamilyOfElements.{u1, u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.Sieve.arrows.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) {U : Opposite.{succ u3} C} (s : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U), CategoryTheory.Presieve.FamilyOfElements.{u1, u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (CategoryTheory.Sieve.arrows.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSectionₓ'. -/
/-- Given a `F`-section `s` on `U` and a subpresheaf `G`, we may define a family of elements in
`G` consisting of the restrictions of `s` -/
def Subpresheaf.familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toPresheaf := fun V i hi => ⟨F.map i.op s, hi⟩
#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_of_section CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSection

/- warning: category_theory.grothendieck_topology.subpresheaf.family_of_elements_compatible -> CategoryTheory.GrothendieckTopology.Subpresheaf.family_of_elements_compatible is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) {U : Opposite.{succ u3} C} (s : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U), CategoryTheory.Presieve.FamilyOfElements.Compatible.{u1, u2, u3} C _inst_1 (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (Opposite.unop.{succ u3} C U) (CategoryTheory.Sieve.arrows.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s)) (CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSection.{u1, u2, u3} C _inst_1 F G U s)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) {U : Opposite.{succ u3} C} (s : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U), CategoryTheory.Presieve.FamilyOfElements.Compatible.{u1, u2, u3} C _inst_1 (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) (Opposite.unop.{succ u3} C U) (CategoryTheory.Sieve.arrows.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s)) (CategoryTheory.GrothendieckTopology.Subpresheaf.familyOfElementsOfSection.{u1, u2, u3} C _inst_1 F G U s)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_compatible CategoryTheory.GrothendieckTopology.Subpresheaf.family_of_elements_compatibleₓ'. -/
theorem Subpresheaf.family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible :=
  by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  ext1
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply, ← op_comp, ← op_comp, e]
#align category_theory.grothendieck_topology.subpresheaf.family_of_elements_compatible CategoryTheory.GrothendieckTopology.Subpresheaf.family_of_elements_compatible

/- warning: category_theory.grothendieck_topology.subpresheaf.nat_trans_naturality -> CategoryTheory.GrothendieckTopology.Subpresheaf.nat_trans_naturality is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G)) {U : Opposite.{succ u3} C} {V : Opposite.{succ u3} C} (i : Quiver.Hom.{succ u2, u3} (Opposite.{succ u3} C) (Quiver.opposite.{u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1))) U V) (x : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' U), Eq.{succ u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V) (Subtype.val.{succ u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V) (fun (x : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V) => Membership.Mem.{u1, u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V) (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V)) (Set.hasMem.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F V)) x (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G V)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) f V (CategoryTheory.Functor.map.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' U V i x))) (CategoryTheory.Functor.map.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U V i (Subtype.val.{succ u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) (fun (x : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) => Membership.Mem.{u1, u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Set.hasMem.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) x (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) f U x)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (f : Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G)) {U : Opposite.{succ u3} C} {V : Opposite.{succ u3} C} (i : Quiver.Hom.{succ u2, u3} (Opposite.{succ u3} C) (Quiver.opposite.{u3, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1))) U V) (x : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F') U), Eq.{succ u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V) (Subtype.val.{succ u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V) (fun (x : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V) => Membership.mem.{u1, u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V) (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V)) (Set.instMembershipSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) V)) x (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G V)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) f V (Prefunctor.map.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F') U V i x))) (Prefunctor.map.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U V i (Subtype.val.{succ u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) (fun (x : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) => Membership.mem.{u1, u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Set.instMembershipSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) x (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U)) (CategoryTheory.NatTrans.app.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F' (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G) f U x)))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.nat_trans_naturality CategoryTheory.GrothendieckTopology.Subpresheaf.nat_trans_naturalityₓ'. -/
theorem Subpresheaf.nat_trans_naturality (f : F' ⟶ G.toPresheaf) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congr_arg Subtype.val (FunctorToTypes.naturality _ _ f i x)
#align category_theory.grothendieck_topology.subpresheaf.nat_trans_naturality CategoryTheory.GrothendieckTopology.Subpresheaf.nat_trans_naturality

include J

#print CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify /-
/-- The sheafification of a subpresheaf as a subpresheaf.
Note that this is a sheaf only when the whole presheaf is a sheaf. -/
def Subpresheaf.sheafify : Subpresheaf F
    where
  obj U := { s | G.sieveOfSection s ∈ J (unop U) }
  map := by
    rintro U V i s hs
    refine' J.superset_covering _ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h⊢
    rwa [← functor_to_types.map_comp_apply]
#align category_theory.grothendieck_topology.subpresheaf.sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify
-/

/- warning: category_theory.grothendieck_topology.subpresheaf.le_sheafify -> CategoryTheory.GrothendieckTopology.Subpresheaf.le_sheafify is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F))) G (CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify.{u1, u2, u3} C _inst_1 J F G)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F))) G (CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify.{u1, u2, u3} C _inst_1 J F G)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.le_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.le_sheafifyₓ'. -/
theorem Subpresheaf.le_sheafify : G ≤ G.sheafify J :=
  by
  intro U s hs
  change _ ∈ J _
  convert J.top_mem _
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs
#align category_theory.grothendieck_topology.subpresheaf.le_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.le_sheafify

variable {J}

#print CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify /-
theorem Subpresheaf.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toPresheaf) :
    G = G.sheafify J := by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s
    by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).IsSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) : _)
#align category_theory.grothendieck_topology.subpresheaf.eq_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify
-/

#print CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_isSheaf /-
theorem Subpresheaf.sheafify_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (G.sheafify J).toPresheaf :=
  by
  intro U S hS x hx
  let S' := sieve.bind S fun Y f hf => G.sieve_of_section (x f hf).1
  have := fun {V} {i : V ⟶ U} (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂
  dsimp [-sieve.bind_apply] at *
  let x'' : presieve.family_of_elements F S' := fun V i hi => F.map (i₁ hi).op (x _ (hi₂ hi))
  have H : ∀ s, x.is_amalgamation s ↔ x''.is_amalgamation s.1 :=
    by
    intro s
    constructor
    · intro H V i hi
      dsimp only [x'']
      conv_lhs => rw [← h₂ hi]
      rw [← H _ (hi₂ hi)]
      exact functor_to_types.map_comp_apply F (i₂ hi).op (i₁ hi).op _
    · intro H V i hi
      ext1
      apply (hF _ (x i hi).2).IsSeparatedFor.ext
      intro V' i' hi'
      have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
      have := H _ hi''
      rw [op_comp, F.map_comp] at this
      refine' this.trans (congr_arg Subtype.val (hx _ _ (hi₂ hi'') hi (h₂ hi'')))
  have : x''.compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply]
    exact
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ S₁) (g₂ ≫ i₁ S₂) (hi₂ S₁) (hi₂ S₂) (by simp only [category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine' ⟨⟨t, _⟩, (H ⟨t, _⟩).mpr ht, fun y hy => Subtype.ext (ht' _ ((H _).mp hy))⟩
  show G.sieve_of_section t ∈ J _
  refine' J.superset_covering _ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ hi
#align category_theory.grothendieck_topology.subpresheaf.sheafify_is_sheaf CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_isSheaf
-/

#print CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify_iff /-
theorem Subpresheaf.eq_sheafify_iff (h : Presieve.IsSheaf J F) :
    G = G.sheafify J ↔ Presieve.IsSheaf J G.toPresheaf :=
  ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩
#align category_theory.grothendieck_topology.subpresheaf.eq_sheafify_iff CategoryTheory.GrothendieckTopology.Subpresheaf.eq_sheafify_iff
-/

/- warning: category_theory.grothendieck_topology.subpresheaf.is_sheaf_iff -> CategoryTheory.GrothendieckTopology.Subpresheaf.isSheaf_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J F) -> (Iff (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G)) (forall (U : Opposite.{succ u3} C) (s : CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U), (Membership.Mem.{max u3 u2, max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U)) (Set.{max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U))) (Set.hasMem.{max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U))) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ (max u3 u2))} (CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) (fun (_x : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1) => forall (X : C), Set.{max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 X)) (CategoryTheory.GrothendieckTopology.hasCoeToFun.{u2, u3} C _inst_1) J (Opposite.unop.{succ u3} C U))) -> (Membership.Mem.{u1, u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U) (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Set.hasMem.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) s (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J F) -> (Iff (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G)) (forall (U : Opposite.{succ u3} C) (s : Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U), (Membership.mem.{max u3 u2, max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U)) (Set.{max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U))) (Set.instMembershipSet.{max u3 u2} (CategoryTheory.Sieve.{u2, u3} C _inst_1 (Opposite.unop.{succ u3} C U))) (CategoryTheory.GrothendieckTopology.Subpresheaf.sieveOfSection.{u1, u2, u3} C _inst_1 F G U s) (CategoryTheory.GrothendieckTopology.sieves.{u2, u3} C _inst_1 J (Opposite.unop.{succ u3} C U))) -> (Membership.mem.{u1, u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U) (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Set.instMembershipSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) s (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F G U))))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.is_sheaf_iff CategoryTheory.GrothendieckTopology.Subpresheaf.isSheaf_iffₓ'. -/
theorem Subpresheaf.isSheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toPresheaf ↔
      ∀ (U) (s : F.obj U), G.sieveOfSection s ∈ J (unop U) → s ∈ G.obj U :=
  by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J ≤ G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩
#align category_theory.grothendieck_topology.subpresheaf.is_sheaf_iff CategoryTheory.GrothendieckTopology.Subpresheaf.isSheaf_iff

#print CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_sheafify /-
theorem Subpresheaf.sheafify_sheafify (h : Presieve.IsSheaf J F) :
    (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subpresheaf.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm
#align category_theory.grothendieck_topology.subpresheaf.sheafify_sheafify CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_sheafify
-/

#print CategoryTheory.GrothendieckTopology.Subpresheaf.sheafifyLift /-
/-- The lift of a presheaf morphism onto the sheafification subpresheaf.  -/
noncomputable def Subpresheaf.sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toPresheaf ⟶ F'
    where
  app U s := (h _ s.Prop).amalgamate _ ((G.family_of_elements_compatible ↑s).compPresheafMap f)
  naturality' := by
    intro U V i
    ext s
    apply (h _ ((subpresheaf.sheafify J G).toPresheaf.map i s).Prop).IsSeparatedFor.ext
    intro W j hj
    refine' (presieve.is_sheaf_for.valid_glue _ _ _ hj).trans _
    dsimp
    conv_rhs => rw [← functor_to_types.map_comp_apply]
    change _ = F'.map (j ≫ i.unop).op _
    refine' Eq.trans _ (presieve.is_sheaf_for.valid_glue _ _ _ _).symm
    · dsimp at hj⊢
      rwa [functor_to_types.map_comp_apply]
    · dsimp [presieve.family_of_elements.comp_presheaf_map]
      congr 1
      ext1
      exact (functor_to_types.map_comp_apply _ _ _ _).symm
#align category_theory.grothendieck_topology.subpresheaf.sheafify_lift CategoryTheory.GrothendieckTopology.Subpresheaf.sheafifyLift
-/

#print CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafifyLift /-
theorem Subpresheaf.to_sheafifyLift (f : G.toPresheaf ⟶ F') (h : Presieve.IsSheaf J F') :
    Subpresheaf.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f :=
  by
  ext (U s)
  apply (h _ ((subpresheaf.hom_of_le (G.le_sheafify J)).app U s).Prop).IsSeparatedFor.ext
  intro V i hi
  have := elementwise_of f.naturality
  exact (presieve.is_sheaf_for.valid_glue _ _ _ hi).trans (this _ _)
#align category_theory.grothendieck_topology.subpresheaf.to_sheafify_lift CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafifyLift
-/

#print CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafify_lift_unique /-
theorem Subpresheaf.to_sheafify_lift_unique (h : Presieve.IsSheaf J F')
    (l₁ l₂ : (G.sheafify J).toPresheaf ⟶ F')
    (e : Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₁ = Subpresheaf.homOfLe (G.le_sheafify J) ≫ l₂) :
    l₁ = l₂ := by
  ext (U⟨s, hs⟩)
  apply (h _ hs).IsSeparatedFor.ext
  rintro V i hi
  dsimp at hi
  erw [← functor_to_types.naturality, ← functor_to_types.naturality]
  exact (congr_fun (congr_app e <| op V) ⟨_, hi⟩ : _)
#align category_theory.grothendieck_topology.subpresheaf.to_sheafify_lift_unique CategoryTheory.GrothendieckTopology.Subpresheaf.to_sheafify_lift_unique
-/

/- warning: category_theory.grothendieck_topology.subpresheaf.sheafify_le -> CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_le is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F))) G G') -> (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J F) -> (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G')) -> (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify.{u1, u2, u3} C _inst_1 J F G) G')
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (G : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (G' : CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F), (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F))) G G') -> (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J F) -> (CategoryTheory.Presieve.IsSheaf.{u1, u2, u3} C _inst_1 J (CategoryTheory.GrothendieckTopology.Subpresheaf.toPresheaf.{u1, u2, u3} C _inst_1 F G')) -> (LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify.{u1, u2, u3} C _inst_1 J F G) G')
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.subpresheaf.sheafify_le CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_leₓ'. -/
theorem Subpresheaf.sheafify_le (h : G ≤ G') (hF : Presieve.IsSheaf J F)
    (hG' : Presieve.IsSheaf J G'.toPresheaf) : G.sheafify J ≤ G' :=
  by
  intro U x hx
  convert((G.sheafify_lift (subpresheaf.hom_of_le h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).IsSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.to_presheaf ⟶ G'.to_presheaf => (nat_trans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafify_lift (subpresheaf.hom_of_le h) hG')
  convert this.symm
  erw [← subpresheaf.nat_trans_naturality]
  rfl
#align category_theory.grothendieck_topology.subpresheaf.sheafify_le CategoryTheory.GrothendieckTopology.Subpresheaf.sheafify_le

omit J

section Image

#print CategoryTheory.GrothendieckTopology.imagePresheaf /-
/-- The image presheaf of a morphism, whose components are the set-theoretic images. -/
@[simps]
def imagePresheaf (f : F' ⟶ F) : Subpresheaf F
    where
  obj U := Set.range (f.app U)
  map U V i := by
    rintro _ ⟨x, rfl⟩
    have := elementwise_of f.naturality
    exact ⟨_, this i x⟩
#align category_theory.grothendieck_topology.image_presheaf CategoryTheory.GrothendieckTopology.imagePresheaf
-/

/- warning: category_theory.grothendieck_topology.top_subpresheaf_obj -> CategoryTheory.GrothendieckTopology.top_subpresheaf_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (U : Opposite.{succ u3} C), Eq.{succ u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.hasTop.{u1, u2, u3} C _inst_1 F)) U) (Top.top.{u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CompleteLattice.toHasTop.{u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)) (Set.completeBooleanAlgebra.{u1} (CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F U)))))))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (U : Opposite.{succ u3} C), Eq.{succ u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CategoryTheory.GrothendieckTopology.Subpresheaf.obj.{u1, u2, u3} C _inst_1 F (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instTopSubpresheaf.{u1, u2, u3} C _inst_1 F)) U) (Top.top.{u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CompleteLattice.toTop.{u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)) (Set.instCompleteBooleanAlgebraSet.{u1} (Prefunctor.obj.{succ u2, succ u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.toCategoryStruct.{u2, u3} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) U)))))))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.top_subpresheaf_obj CategoryTheory.GrothendieckTopology.top_subpresheaf_objₓ'. -/
@[simp]
theorem top_subpresheaf_obj (U) : (⊤ : Subpresheaf F).obj U = ⊤ :=
  rfl
#align category_theory.grothendieck_topology.top_subpresheaf_obj CategoryTheory.GrothendieckTopology.top_subpresheaf_obj

/- warning: category_theory.grothendieck_topology.image_presheaf_id -> CategoryTheory.GrothendieckTopology.imagePresheaf_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, Eq.{max (succ u3) (succ u1)} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F F (CategoryTheory.CategoryStruct.id.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F)) (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.Subpresheaf.hasTop.{u1, u2, u3} C _inst_1 F))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, Eq.{max (succ u3) (succ u1)} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F F (CategoryTheory.CategoryStruct.id.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F)) (Top.top.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F) (CategoryTheory.GrothendieckTopology.instTopSubpresheaf.{u1, u2, u3} C _inst_1 F))
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.image_presheaf_id CategoryTheory.GrothendieckTopology.imagePresheaf_idₓ'. -/
@[simp]
theorem imagePresheaf_id : imagePresheaf (𝟙 F) = ⊤ :=
  by
  ext
  simp
#align category_theory.grothendieck_topology.image_presheaf_id CategoryTheory.GrothendieckTopology.imagePresheaf_id

#print CategoryTheory.GrothendieckTopology.toImagePresheaf /-
/-- A morphism factors through the image presheaf. -/
@[simps]
def toImagePresheaf (f : F' ⟶ F) : F' ⟶ (imagePresheaf f).toPresheaf :=
  (imagePresheaf f).lift f fun U x => Set.mem_range_self _
#align category_theory.grothendieck_topology.to_image_presheaf CategoryTheory.GrothendieckTopology.toImagePresheaf
-/

variable (J)

#print CategoryTheory.GrothendieckTopology.toImagePresheafSheafify /-
/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps]
def toImagePresheafSheafify (f : F' ⟶ F) : F' ⟶ ((imagePresheaf f).sheafify J).toPresheaf :=
  toImagePresheaf f ≫ Subpresheaf.homOfLe ((imagePresheaf f).le_sheafify J)
#align category_theory.grothendieck_topology.to_image_presheaf_sheafify CategoryTheory.GrothendieckTopology.toImagePresheafSheafify
-/

variable {J}

#print CategoryTheory.GrothendieckTopology.toImagePresheaf_ι /-
@[simp, reassoc]
theorem toImagePresheaf_ι (f : F' ⟶ F) : toImagePresheaf f ≫ (imagePresheaf f).ι = f :=
  (imagePresheaf f).lift_ι _ _
#align category_theory.grothendieck_topology.to_image_presheaf_ι CategoryTheory.GrothendieckTopology.toImagePresheaf_ι
-/

/- warning: category_theory.grothendieck_topology.image_presheaf_comp_le -> CategoryTheory.GrothendieckTopology.imagePresheaf_comp_le is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F'' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (f₁ : Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F F') (f₂ : Quiver.Hom.{succ (max u3 u1), max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F''), LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (Preorder.toHasLe.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (CategoryTheory.GrothendieckTopology.Subpresheaf.partialOrder.{u1, u2, u3} C _inst_1 F''))) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F'' F (CategoryTheory.CategoryStruct.comp.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max u2 u1 u3 (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F F' F'' f₁ f₂)) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F'' F' f₂)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {F : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} {F'' : CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}} (f₁ : Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F F') (f₂ : Quiver.Hom.{max (succ u3) (succ u1), max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) F' F''), LE.le.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (Preorder.toLE.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (PartialOrder.toPreorder.{max u3 u1} (CategoryTheory.GrothendieckTopology.Subpresheaf.{u1, u2, u3} C _inst_1 F'') (CategoryTheory.GrothendieckTopology.instPartialOrderSubpresheaf.{u1, u2, u3} C _inst_1 F''))) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F'' F (CategoryTheory.CategoryStruct.comp.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u3 u1, max (max u3 u2) (succ u1)} (CategoryTheory.Functor.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u2, u1, u3, succ u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) Type.{u1} CategoryTheory.types.{u1})) F F' F'' f₁ f₂)) (CategoryTheory.GrothendieckTopology.imagePresheaf.{u1, u2, u3} C _inst_1 F'' F' f₂)
Case conversion may be inaccurate. Consider using '#align category_theory.grothendieck_topology.image_presheaf_comp_le CategoryTheory.GrothendieckTopology.imagePresheaf_comp_leₓ'. -/
theorem imagePresheaf_comp_le (f₁ : F ⟶ F') (f₂ : F' ⟶ F'') :
    imagePresheaf (f₁ ≫ f₂) ≤ imagePresheaf f₂ := fun U x hx => ⟨f₁.app U hx.some, hx.choose_spec⟩
#align category_theory.grothendieck_topology.image_presheaf_comp_le CategoryTheory.GrothendieckTopology.imagePresheaf_comp_le

instance {F F' : Cᵒᵖ ⥤ Type max v w} (f : F ⟶ F') [hf : Mono f] : IsIso (toImagePresheaf f) :=
  by
  apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
  intro X
  rw [is_iso_iff_bijective]
  constructor
  · intro x y e
    have := (nat_trans.mono_iff_mono_app _ _).mp hf X
    rw [mono_iff_injective] at this
    exact this (congr_arg Subtype.val e : _)
  · rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩

#print CategoryTheory.GrothendieckTopology.imageSheaf /-
/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
def imageSheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
  ⟨((imagePresheaf f.1).sheafify J).toPresheaf,
    by
    rw [is_sheaf_iff_is_sheaf_of_type]
    apply subpresheaf.sheafify_is_sheaf
    rw [← is_sheaf_iff_is_sheaf_of_type]
    exact F'.2⟩
#align category_theory.grothendieck_topology.image_sheaf CategoryTheory.GrothendieckTopology.imageSheaf
-/

#print CategoryTheory.GrothendieckTopology.toImageSheaf /-
/-- A morphism factors through the image sheaf. -/
@[simps]
def toImageSheaf {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ imageSheaf f :=
  ⟨toImagePresheafSheafify J f.1⟩
#align category_theory.grothendieck_topology.to_image_sheaf CategoryTheory.GrothendieckTopology.toImageSheaf
-/

#print CategoryTheory.GrothendieckTopology.imageSheafι /-
/-- The inclusion of the image sheaf to the target. -/
@[simps]
def imageSheafι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : imageSheaf f ⟶ F' :=
  ⟨Subpresheaf.ι _⟩
#align category_theory.grothendieck_topology.image_sheaf_ι CategoryTheory.GrothendieckTopology.imageSheafι
-/

#print CategoryTheory.GrothendieckTopology.toImageSheaf_ι /-
@[simp, reassoc]
theorem toImageSheaf_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    toImageSheaf f ≫ imageSheafι f = f := by
  ext1
  simp [to_image_presheaf_sheafify]
#align category_theory.grothendieck_topology.to_image_sheaf_ι CategoryTheory.GrothendieckTopology.toImageSheaf_ι
-/

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Mono (imageSheafι f) :=
  (sheafToPresheaf J _).mono_of_mono_map
    (by
      dsimp
      infer_instance)

instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Epi (toImageSheaf f) :=
  by
  refine' ⟨fun G' g₁ g₂ e => _⟩
  ext (U⟨s, hx⟩)
  apply ((is_sheaf_iff_is_sheaf_of_type J _).mp G'.2 _ hx).IsSeparatedFor.ext
  rintro V i ⟨y, e'⟩
  change (g₁.val.app _ ≫ G'.val.map _) _ = (g₂.val.app _ ≫ G'.val.map _) _
  rw [← nat_trans.naturality, ← nat_trans.naturality]
  have E : (to_image_sheaf f).val.app (op V) y = (image_sheaf f).val.map i.op ⟨s, hx⟩ :=
    Subtype.ext e'
  have := congr_arg (fun f : F ⟶ G' => (Sheaf.hom.val f).app _ y) e
  dsimp at this⊢
  convert this <;> exact E.symm

#print CategoryTheory.GrothendieckTopology.imageMonoFactorization /-
/-- The mono factorization given by `image_sheaf` for a morphism. -/
def imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Limits.MonoFactorisation f
    where
  i := imageSheaf f
  m := imageSheafι f
  e := toImageSheaf f
#align category_theory.grothendieck_topology.image_mono_factorization CategoryTheory.GrothendieckTopology.imageMonoFactorization
-/

#print CategoryTheory.GrothendieckTopology.imageFactorization /-
/-- The mono factorization given by `image_sheaf` for a morphism is an image. -/
noncomputable def imageFactorization {F F' : Sheaf J (Type max v u)} (f : F ⟶ F') :
    Limits.ImageFactorisation f where
  f := imageMonoFactorization f
  IsImage :=
    { lift := fun I =>
        by
        haveI := (Sheaf.hom.mono_iff_presheaf_mono J _ _).mp I.m_mono
        refine' ⟨subpresheaf.hom_of_le _ ≫ inv (to_image_presheaf I.m.1)⟩
        apply subpresheaf.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply image_presheaf_comp_le
        · rw [← is_sheaf_iff_is_sheaf_of_type]
          exact F'.2
        · apply presieve.is_sheaf_iso J (as_iso <| to_image_presheaf I.m.1)
          rw [← is_sheaf_iff_is_sheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [image_mono_factorization]
        generalize_proofs h
        rw [← subpresheaf.hom_of_le_ι h, category.assoc]
        congr 1
        rw [is_iso.inv_comp_eq, to_image_presheaf_ι] }
#align category_theory.grothendieck_topology.image_factorization CategoryTheory.GrothendieckTopology.imageFactorization
-/

instance : Limits.HasImages (Sheaf J (Type max v u)) :=
  ⟨fun _ _ f => ⟨⟨imageFactorization f⟩⟩⟩

end Image

end CategoryTheory.GrothendieckTopology

