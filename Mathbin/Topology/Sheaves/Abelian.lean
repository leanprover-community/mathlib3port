/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang

! This file was ported from Lean 3 source module topology.sheaves.abelian
! leanprover-community/mathlib commit ac3ae212f394f508df43e37aa093722fa9b65d31
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.FunctorCategory
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Preadditive.FunctorCategory
import Mathbin.CategoryTheory.Abelian.Transfer
import Mathbin.CategoryTheory.Sites.LeftExact

/-!
# Category of sheaves is abelian
Let `C, D` be categories and `J` be a grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`Sheaf_is_abelian`).

Hence, `presheaf_to_Sheaf` is an additive functor (`presheaf_to_Sheaf_additive`).

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

section Abelian

universe w v u

variable {C : Type max v u} [Category.{v} C]

variable {D : Type w} [Category.{max v u} D] [Abelian D]

variable {J : GrothendieckTopology C}

-- This needs to be specified manually because of universe level.
instance : Abelian (Cᵒᵖ ⥤ D) :=
  @Abelian.functorCategoryAbelian.{v} Cᵒᵖ _ D _ _

-- This also needs to be specified manually, but I don't know why.
instance : HasFiniteProducts (Sheaf J D) where out j := { HasLimit := fun F => by infer_instance }

-- sheafification assumptions
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)]

variable [ReflectsIsomorphisms (forget D)]

/- warning: category_theory.Sheaf_is_abelian -> CategoryTheory.sheafIsAbelian is a dubious translation:
lean 3 declaration is
  forall {C : Type.{max u2 u3}} [_inst_1 : CategoryTheory.Category.{u2, max u2 u3} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_3 : CategoryTheory.Abelian.{max u2 u3, u1} D _inst_2] {J : CategoryTheory.GrothendieckTopology.{u2, max u2 u3} C _inst_1} [_inst_4 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} C) (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u2 u3} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, max u2 u3} C _inst_1 X J D _inst_2 S P)] [_inst_5 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u2 u3, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u2 u3, max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (Preorder.smallCategory.{max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, max u2 u3} C _inst_1 J X))) D _inst_2] [_inst_6 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_7 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u2 u3, max u2 u3, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u2 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u2 u3, max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (Preorder.smallCategory.{max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, max u2 u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)] [_inst_10 : CategoryTheory.Limits.HasFiniteLimits.{max u2 u3, u1} D _inst_2], CategoryTheory.Abelian.{max u2 u3, max u1 u2 u3} (CategoryTheory.Sheaf.{u2, max u2 u3, max u2 u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, max u2 u3, u1} C _inst_1 J D _inst_2)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_3 : CategoryTheory.Abelian.{max u3 u2, u1} D _inst_2] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} [_inst_4 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_5 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_6 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_7 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)] [_inst_10 : CategoryTheory.Limits.HasFiniteLimits.{max u3 u2, u1} D _inst_2], CategoryTheory.Abelian.{max u3 u2, max (max (max u1 u3) u3 u2) u2} (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.Sheaf_is_abelian CategoryTheory.sheafIsAbelianₓ'. -/
instance sheafIsAbelian [HasFiniteLimits D] : Abelian (Sheaf J D) :=
  let adj := sheafificationAdjunction J D
  abelianOfAdjunction _ _ (asIso adj.counit) adj
#align category_theory.Sheaf_is_abelian CategoryTheory.sheafIsAbelian

attribute [local instance] preserves_binary_biproducts_of_preserves_binary_products

/- warning: category_theory.presheaf_to_Sheaf_additive -> CategoryTheory.presheafToSheaf_additive is a dubious translation:
lean 3 declaration is
  forall {C : Type.{max u2 u3}} [_inst_1 : CategoryTheory.Category.{u2, max u2 u3} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_3 : CategoryTheory.Abelian.{max u2 u3, u1} D _inst_2] {J : CategoryTheory.GrothendieckTopology.{u2, max u2 u3} C _inst_1} [_inst_4 : forall (P : CategoryTheory.Functor.{u2, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} C) (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u2 u3, u1, max u2 u3} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, max u2 u3} C _inst_1 X J D _inst_2 S P)] [_inst_5 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u2 u3, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u2 u3, max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (Preorder.smallCategory.{max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, max u2 u3} C _inst_1 J X))) D _inst_2] [_inst_6 : CategoryTheory.ConcreteCategory.{max u2 u3, max u2 u3, u1} D _inst_2] [_inst_7 : CategoryTheory.Limits.PreservesLimits.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u2 u3, max u2 u3, max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (Opposite.{succ (max u2 u3)} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u2 u3, max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (Preorder.smallCategory.{max u2 u3} (CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.Cover.preorder.{u2, max u2 u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u2 u3, max u2 u3, u1, succ (max u2 u3)} D _inst_2 Type.{max u2 u3} CategoryTheory.types.{max u2 u3} (CategoryTheory.forget.{u1, max u2 u3, max u2 u3} D _inst_2 _inst_6)], CategoryTheory.Functor.Additive.{max u2 (max u2 u3) u1, max u1 u2 u3, max u2 u3, max u2 u3} (CategoryTheory.Functor.{u2, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} C) (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) D _inst_2) (CategoryTheory.Sheaf.{u2, max u2 u3, max u2 u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.category.{u2, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} C) (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) D _inst_2) (CategoryTheory.Sheaf.CategoryTheory.category.{u2, max u2 u3, max u2 u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.functorCategoryPreadditive.{max u2 u3, u1, u2, max u2 u3} (Opposite.{succ (max u2 u3)} C) D (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) _inst_2 (CategoryTheory.Abelian.toPreadditive.{max u2 u3, u1} D _inst_2 _inst_3)) (CategoryTheory.Sheaf.preadditive.{u2, max u2 u3, max u2 u3, u1} C _inst_1 J D _inst_2 (CategoryTheory.Abelian.toPreadditive.{max u2 u3, u1} D _inst_2 _inst_3)) (CategoryTheory.presheafToSheaf.{u1, u2, max u2 u3} C _inst_1 J D _inst_2 _inst_6 _inst_7 (fun (P : CategoryTheory.Functor.{u2, max u2 u3, max u2 u3, u1} (Opposite.{succ (max u2 u3)} C) (CategoryTheory.Category.opposite.{u2, max u2 u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, max u2 u3} C _inst_1 J X) => _inst_4 P X S) (fun (X : C) => _inst_5 X) (fun (X : C) => _inst_8 X) _inst_9)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u1}} [_inst_2 : CategoryTheory.Category.{max u2 u3, u1} D] [_inst_3 : CategoryTheory.Abelian.{max u3 u2, u1} D _inst_2] {J : CategoryTheory.GrothendieckTopology.{u2, u3} C _inst_1} [_inst_4 : forall (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X), CategoryTheory.Limits.HasMultiequalizer.{max u3 u2, u1, max u3 u2} D _inst_2 (CategoryTheory.GrothendieckTopology.Cover.index.{u1, u2, u3} C _inst_1 X J D _inst_2 S P)] [_inst_5 : forall (X : C), CategoryTheory.Limits.HasColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, u1} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) D _inst_2] [_inst_6 : CategoryTheory.ConcreteCategory.{max u2 u3, max u3 u2, u1} D _inst_2] [_inst_7 : CategoryTheory.Limits.PreservesLimits.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)] [_inst_8 : forall (X : C), CategoryTheory.Limits.PreservesColimitsOfShape.{max u3 u2, max u3 u2, max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (Opposite.{max (succ u3) (succ u2)} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X)) (CategoryTheory.Category.opposite.{max u3 u2, max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (Preorder.smallCategory.{max u3 u2} (CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) (CategoryTheory.GrothendieckTopology.instPreorderCover.{u2, u3} C _inst_1 J X))) (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)] [_inst_9 : CategoryTheory.ReflectsIsomorphisms.{max u3 u2, max u3 u2, u1, max (succ u3) (succ u2)} D _inst_2 Type.{max u3 u2} CategoryTheory.types.{max u3 u2} (CategoryTheory.forget.{u1, max u3 u2, max u3 u2} D _inst_2 _inst_6)], CategoryTheory.Functor.Additive.{max (max u3 u2) u1, max (max u3 u2) u1, max u3 u2, max u3 u2} (CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Sheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.Functor.category.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (CategoryTheory.Sheaf.instCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2) (CategoryTheory.functorCategoryPreadditive.{u3, u1, u2, max u3 u2} (Opposite.{succ u3} C) D (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) _inst_2 (CategoryTheory.Abelian.toPreadditive.{max u3 u2, u1} D _inst_2 _inst_3)) (CategoryTheory.instPreadditiveSheafInstCategorySheaf.{u2, max u3 u2, u3, u1} C _inst_1 J D _inst_2 (CategoryTheory.Abelian.toPreadditive.{max u3 u2, u1} D _inst_2 _inst_3)) (CategoryTheory.presheafToSheaf.{u1, u2, u3} C _inst_1 J D _inst_2 _inst_6 _inst_7 (fun (P : CategoryTheory.Functor.{u2, max u3 u2, u3, u1} (Opposite.{succ u3} C) (CategoryTheory.Category.opposite.{u2, u3} C _inst_1) D _inst_2) (X : C) (S : CategoryTheory.GrothendieckTopology.Cover.{u2, u3} C _inst_1 J X) => _inst_4 P X S) (fun (X : C) => _inst_5 X) (fun (X : C) => _inst_8 X) _inst_9)
Case conversion may be inaccurate. Consider using '#align category_theory.presheaf_to_Sheaf_additive CategoryTheory.presheafToSheaf_additiveₓ'. -/
instance presheafToSheaf_additive : (presheafToSheaf J D).Additive :=
  (presheafToSheaf J D).additive_of_preservesBinaryBiproducts
#align category_theory.presheaf_to_Sheaf_additive CategoryTheory.presheafToSheaf_additive

end Abelian

end CategoryTheory

