/-
Copyright (c) 2020 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.limits.preserves.shapes.products from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# Preserving products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `pi_comparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J → C)

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
#print CategoryTheory.Limits.isLimitMapConeFanMkEquiv /-
/-- The map of a fan is a limit iff the fan consisting of the mapped morphisms is a limit. This
essentially lets us commute `fan.mk` with `functor.map_cone`.
-/
def isLimitMapConeFanMkEquiv {P : C} (g : ∀ j, P ⟶ f j) :
    IsLimit (G.mapCone (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  by
  refine' (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
  refine' discrete.nat_iso fun j => iso.refl (G.obj (f j.as))
  refine'
    cones.ext (iso.refl _) fun j => by
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]";
      dsimp; simp
#align category_theory.limits.is_limit_map_cone_fan_mk_equiv CategoryTheory.Limits.isLimitMapConeFanMkEquiv
-/

#print CategoryTheory.Limits.isLimitFanMkObjOfIsLimit /-
/-- The property of preserving products expressed in terms of fans. -/
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (PreservesLimit.preserves t)
#align category_theory.limits.is_limit_fan_mk_obj_of_is_limit CategoryTheory.Limits.isLimitFanMkObjOfIsLimit
-/

#print CategoryTheory.Limits.isLimitOfIsLimitFanMkObj /-
/-- The property of reflecting products expressed in terms of fans. -/
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : ∀ j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  ReflectsLimit.reflects ((isLimitMapConeFanMkEquiv _ _ _).symm t)
#align category_theory.limits.is_limit_of_is_limit_fan_mk_obj CategoryTheory.Limits.isLimitOfIsLimitFanMkObj
-/

section

variable [HasProduct f]

#print CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit /-
/--
If `G` preserves products and `C` has them, then the fan constructed of the mapped projection of a
product is a limit.
-/
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)
#align category_theory.limits.is_limit_of_has_product_of_preserves_limit CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit
-/

variable [HasProduct fun j : J => G.obj (f j)]

#print CategoryTheory.Limits.PreservesProduct.ofIsoComparison /-
/-- If `pi_comparison G f` is an isomorphism, then `G` preserves the limit of `f`. -/
def PreservesProduct.ofIsoComparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G :=
  by
  apply preserves_limit_of_preserves_limit_cone (product_is_product f)
  apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (discrete.functor fun j : J => G.obj (f j)))
  apply i
#align category_theory.limits.preserves_product.of_iso_comparison CategoryTheory.Limits.PreservesProduct.ofIsoComparison
-/

variable [PreservesLimit (Discrete.functor f) G]

#print CategoryTheory.Limits.PreservesProduct.iso /-
/--
If `G` preserves limits, we have an isomorphism from the image of a product to the product of the
images.
-/
def PreservesProduct.iso : G.obj (∏ f) ≅ ∏ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)
#align category_theory.limits.preserves_product.iso CategoryTheory.Limits.PreservesProduct.iso
-/

#print CategoryTheory.Limits.PreservesProduct.iso_hom /-
@[simp]
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).Hom = piComparison G f :=
  rfl
#align category_theory.limits.preserves_product.iso_hom CategoryTheory.Limits.PreservesProduct.iso_hom
-/

instance : IsIso (piComparison G f) :=
  by
  rw [← preserves_product.iso_hom]
  infer_instance

end

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[] -/
#print CategoryTheory.Limits.isColimitMapCoconeCofanMkEquiv /-
/-- The map of a cofan is a colimit iff the cofan consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofan.mk` with `functor.map_cocone`.
-/
def isColimitMapCoconeCofanMkEquiv {P : C} (g : ∀ j, f j ⟶ P) :
    IsColimit (G.mapCocone (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  by
  refine' (is_colimit.precompose_hom_equiv _ _).symm.trans (is_colimit.equiv_iso_colimit _)
  refine' discrete.nat_iso fun j => iso.refl (G.obj (f j.as))
  refine'
    cocones.ext (iso.refl _) fun j => by
      trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `discrete_cases #[]";
      dsimp; simp
#align category_theory.limits.is_colimit_map_cocone_cofan_mk_equiv CategoryTheory.Limits.isColimitMapCoconeCofanMkEquiv
-/

#print CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit /-
/-- The property of preserving coproducts expressed in terms of cofans. -/
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (PreservesColimit.preserves t)
#align category_theory.limits.is_colimit_cofan_mk_obj_of_is_colimit CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit
-/

#print CategoryTheory.Limits.isColimitOfIsColimitCofanMkObj /-
/-- The property of reflecting coproducts expressed in terms of cofans. -/
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : ∀ j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  ReflectsColimit.reflects ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)
#align category_theory.limits.is_colimit_of_is_colimit_cofan_mk_obj CategoryTheory.Limits.isColimitOfIsColimitCofanMkObj
-/

section

variable [HasCoproduct f]

#print CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit /-
/-- If `G` preserves coproducts and `C` has them,
then the cofan constructed of the mapped inclusion of a coproduct is a colimit.
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)
#align category_theory.limits.is_colimit_of_has_coproduct_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit
-/

variable [HasCoproduct fun j : J => G.obj (f j)]

#print CategoryTheory.Limits.PreservesCoproduct.ofIsoComparison /-
/-- If `sigma_comparison G f` is an isomorphism, then `G` preserves the colimit of `f`. -/
def PreservesCoproduct.ofIsoComparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (coproduct_is_coproduct f)
  apply (is_colimit_map_cocone_cofan_mk_equiv _ _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (discrete.functor fun j : J => G.obj (f j)))
  apply i
#align category_theory.limits.preserves_coproduct.of_iso_comparison CategoryTheory.Limits.PreservesCoproduct.ofIsoComparison
-/

variable [PreservesColimit (Discrete.functor f) G]

#print CategoryTheory.Limits.PreservesCoproduct.iso /-
/-- If `G` preserves colimits,
we have an isomorphism from the image of a coproduct to the coproduct of the images.
-/
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)
#align category_theory.limits.preserves_coproduct.iso CategoryTheory.Limits.PreservesCoproduct.iso
-/

#print CategoryTheory.Limits.PreservesCoproduct.inv_hom /-
@[simp]
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f :=
  rfl
#align category_theory.limits.preserves_coproduct.inv_hom CategoryTheory.Limits.PreservesCoproduct.inv_hom
-/

instance : IsIso (sigmaComparison G f) :=
  by
  rw [← preserves_coproduct.inv_hom]
  infer_instance

end

end CategoryTheory.Limits

