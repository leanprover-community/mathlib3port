/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.functor.flat
! leanprover-community/mathlib commit 39478763114722f0ec7613cb2f3f7701f9b86c8d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathbin.CategoryTheory.Limits.Bicones
import Mathbin.CategoryTheory.Limits.Comma
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness.

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preserves_finite_limits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preserves_finite_limits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preserves_finite_limits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left_exact.
* `Lan_preserves_finite_limits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_Lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preserves_finite_limits_iff_Lan_preserves_finite_limits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

namespace StructuredArrowCone

open StructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

variable {J : Type w} [SmallCategory J]

variable {K : J ⥤ C} (F : C ⥤ D) (c : Cone K)

#print CategoryTheory.StructuredArrowCone.toDiagram /-
/-- Given a cone `c : cone K` and a map `f : X ⟶ c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point. This is the underlying diagram.
-/
@[simps]
def toDiagram : J ⥤ StructuredArrow c.pt K
    where
  obj j := StructuredArrow.mk (c.π.app j)
  map j k g := StructuredArrow.homMk g (by simpa)
#align category_theory.structured_arrow_cone.to_diagram CategoryTheory.StructuredArrowCone.toDiagram
-/

#print CategoryTheory.StructuredArrowCone.diagramToCone /-
/-- Given a diagram of `structured_arrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps]
def diagramToCone {X : D} (G : J ⥤ StructuredArrow X F) : Cone (G ⋙ proj X F ⋙ F) :=
  { pt
    π := { app := fun j => (G.obj j).Hom } }
#align category_theory.structured_arrow_cone.diagram_to_cone CategoryTheory.StructuredArrowCone.diagramToCone
-/

/- warning: category_theory.structured_arrow_cone.to_cone -> CategoryTheory.StructuredArrowCone.toCone is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u2, u2, u3, u4} C _inst_1 D _inst_2) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_3 C _inst_1 K) {X : D} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) X (CategoryTheory.Functor.obj.{u2, u2, u3, u4} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} J _inst_3 C _inst_1 K c))), CategoryTheory.Limits.Cone.{u1, u2, u1, max u3 u2} J _inst_3 (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrow.category.{u2, u4, u3, u2} C _inst_1 D _inst_2 X F) (CategoryTheory.Functor.comp.{u1, max u2 u1, u2, u1, max u1 u2, max u3 u2} J _inst_3 (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.category.{u2, u4, u1, u1} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrow.category.{u2, u4, u3, u2} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrowCone.toDiagram.{u1, u2, u4} D _inst_2 J _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{max u2 u1, max u2 u1, u2, max u1 u2, max u1 u2, max u3 u2} (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.category.{u2, u4, u1, u1} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 X (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.category.{u2, u4, u1, u1} J _inst_3 D _inst_2 X (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrow.category.{u2, u4, u3, u2} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrow.map.{u1, u2, u1, u4} J _inst_3 D _inst_2 X (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) f) (CategoryTheory.StructuredArrow.pre.{u2, u2, u1, u3, u4, u1} C _inst_1 D _inst_2 J _inst_3 X K F)))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] {K : CategoryTheory.Functor.{u1, u2, u1, u3} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u2, u2, u3, u4} C _inst_1 D _inst_2) (c : CategoryTheory.Limits.Cone.{u1, u2, u1, u3} J _inst_3 C _inst_1 K) {X : D} (f : Quiver.Hom.{succ u2, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) X (Prefunctor.obj.{succ u2, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u3, u4} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u3} J _inst_3 C _inst_1 K c))), CategoryTheory.Limits.Cone.{u1, u2, u1, max u3 u2} J _inst_3 (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.instCategoryStructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.Functor.comp.{u1, max u2 u1, u2, u1, max u2 u1, max u3 u2} J _inst_3 (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.instCategoryStructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.instCategoryStructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrowCone.toDiagram.{u1, u2, u4} D _inst_2 J _inst_3 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{max u2 u1, max u2 u1, u2, max u2 u1, max u2 u1, max u3 u2} (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.instCategoryStructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 X (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.instCategoryStructuredArrow.{u1, u2, u1, u4} J _inst_3 D _inst_2 X (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F)) (CategoryTheory.StructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.instCategoryStructuredArrow.{u2, u2, u3, u4} C _inst_1 D _inst_2 X F) (CategoryTheory.StructuredArrow.map.{u1, u2, u1, u4} J _inst_3 D _inst_2 X (CategoryTheory.Limits.Cone.pt.{u1, u2, u1, u4} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 F K c)) (CategoryTheory.Functor.comp.{u1, u2, u2, u1, u3, u4} J _inst_3 C _inst_1 D _inst_2 K F) f) (CategoryTheory.StructuredArrow.pre.{u2, u2, u1, u3, u4, u1} C _inst_1 D _inst_2 J _inst_3 X K F)))
Case conversion may be inaccurate. Consider using '#align category_theory.structured_arrow_cone.to_cone CategoryTheory.StructuredArrowCone.toConeₓ'. -/
/-- Given a cone `c : cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
def toCone {X : D} (f : X ⟶ F.obj c.pt) : Cone (toDiagram (F.mapCone c) ⋙ map f ⋙ pre _ K F)
    where
  pt := mk f
  π :=
    { app := fun j => homMk (c.π.app j) rfl
      naturality' := fun j k g => by
        ext
        dsimp
        simp }
#align category_theory.structured_arrow_cone.to_cone CategoryTheory.StructuredArrowCone.toCone

end StructuredArrowCone

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

#print CategoryTheory.RepresentablyFlat /-
/-- A functor `F : C ⥤ D` is representably-flat functor if the comma category `(X/F)`
is cofiltered for each `X : C`.
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : ∀ X : D, IsCofiltered (StructuredArrow X F)
#align category_theory.representably_flat CategoryTheory.RepresentablyFlat
-/

attribute [instance] representably_flat.cofiltered

attribute [local instance] is_cofiltered.nonempty

#print CategoryTheory.RepresentablyFlat.id /-
instance RepresentablyFlat.id : RepresentablyFlat (𝟭 C) :=
  by
  constructor
  intro X
  haveI : Nonempty (structured_arrow X (𝟭 C)) := ⟨structured_arrow.mk (𝟙 _)⟩
  rsuffices : is_cofiltered_or_empty (structured_arrow X (𝟭 C))
  · constructor
  constructor
  · intro Y Z
    use structured_arrow.mk (𝟙 _)
    use structured_arrow.hom_mk Y.hom (by erw [functor.id_map, category.id_comp])
    use structured_arrow.hom_mk Z.hom (by erw [functor.id_map, category.id_comp])
  · intro Y Z f g
    use structured_arrow.mk (𝟙 _)
    use structured_arrow.hom_mk Y.hom (by erw [functor.id_map, category.id_comp])
    ext
    trans Z.hom <;> simp
#align category_theory.representably_flat.id CategoryTheory.RepresentablyFlat.id
-/

#print CategoryTheory.RepresentablyFlat.comp /-
instance RepresentablyFlat.comp (F : C ⥤ D) (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) :=
  by
  constructor
  intro X
  have : Nonempty (structured_arrow X (F ⋙ G)) :=
    by
    have f₁ : structured_arrow X G := Nonempty.some inferInstance
    have f₂ : structured_arrow f₁.right F := Nonempty.some inferInstance
    exact ⟨structured_arrow.mk (f₁.hom ≫ G.map f₂.hom)⟩
  rsuffices : is_cofiltered_or_empty (structured_arrow X (F ⋙ G))
  · constructor
  constructor
  · intro Y Z
    let W :=
      @is_cofiltered.min (structured_arrow X G) _ _ (structured_arrow.mk Y.hom)
        (structured_arrow.mk Z.hom)
    let Y' : W ⟶ _ := is_cofiltered.min_to_left _ _
    let Z' : W ⟶ _ := is_cofiltered.min_to_right _ _
    let W' :=
      @is_cofiltered.min (structured_arrow W.right F) _ _ (structured_arrow.mk Y'.right)
        (structured_arrow.mk Z'.right)
    let Y'' : W' ⟶ _ := is_cofiltered.min_to_left _ _
    let Z'' : W' ⟶ _ := is_cofiltered.min_to_right _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use structured_arrow.hom_mk Y''.right (by simp [← G.map_comp])
    use structured_arrow.hom_mk Z''.right (by simp [← G.map_comp])
  · intro Y Z f g
    let W :=
      @is_cofiltered.eq (structured_arrow X G) _ _ (structured_arrow.mk Y.hom)
        (structured_arrow.mk Z.hom) (structured_arrow.hom_mk (F.map f.right) (structured_arrow.w f))
        (structured_arrow.hom_mk (F.map g.right) (structured_arrow.w g))
    let h : W ⟶ _ := is_cofiltered.eq_hom _ _
    let h_cond : h ≫ _ = h ≫ _ := is_cofiltered.eq_condition _ _
    let W' :=
      @is_cofiltered.eq (structured_arrow W.right F) _ _ (structured_arrow.mk h.right)
        (structured_arrow.mk (h.right ≫ F.map f.right)) (structured_arrow.hom_mk f.right rfl)
        (structured_arrow.hom_mk g.right (congr_arg comma_morphism.right h_cond).symm)
    let h' : W' ⟶ _ := is_cofiltered.eq_hom _ _
    let h'_cond : h' ≫ _ = h' ≫ _ := is_cofiltered.eq_condition _ _
    use structured_arrow.mk (W.hom ≫ G.map W'.hom)
    use structured_arrow.hom_mk h'.right (by simp [← G.map_comp])
    ext
    exact (congr_arg comma_morphism.right h'_cond : _)
#align category_theory.representably_flat.comp CategoryTheory.RepresentablyFlat.comp
-/

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]

attribute [local instance] has_finite_limits_of_has_finite_limits_of_size

#print CategoryTheory.cofiltered_of_hasFiniteLimits /-
theorem cofiltered_of_hasFiniteLimits [HasFiniteLimits C] : IsCofiltered C :=
  { cone_objs := fun A B => ⟨Limits.prod A B, Limits.prod.fst, Limits.prod.snd, trivial⟩
    cone_maps := fun A B f g => ⟨equalizer f g, equalizer.ι f g, equalizer.condition f g⟩
    Nonempty := ⟨⊤_ C⟩ }
#align category_theory.cofiltered_of_has_finite_limits CategoryTheory.cofiltered_of_hasFiniteLimits
-/

#print CategoryTheory.flat_of_preservesFiniteLimits /-
theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : has_finite_limits (structured_arrow X F) :=
      by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (structured_arrow X F)
      intro J sJ fJ; skip; constructor
    cofiltered_of_has_finite_limits⟩
#align category_theory.flat_of_preserves_finite_limits CategoryTheory.flat_of_preservesFiniteLimits
-/

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

open StructuredArrowCone

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}

variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

include hc

/- warning: category_theory.preserves_finite_limits_of_flat.lift -> CategoryTheory.PreservesFiniteLimitsOfFlat.lift is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) -> (forall (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)), Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) -> (forall (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)), Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)))
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_finite_limits_of_flat.lift CategoryTheory.PreservesFiniteLimitsOfFlat.liftₓ'. -/
/-- (Implementation).
Given a limit cone `c : cone K` and a cone `s : cone (K ⋙ F)` with `F` representably flat,
`s` can factor through `F.map_cone c`.
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (toDiagram s ⋙ StructuredArrow.pre _ K F)
  s'.pt.Hom ≫
    (F.map <|
      hc.lift <|
        (Cones.postcompose
              ({  app := fun X => 𝟙 _
                  naturality' := by simp } : (toDiagram s ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')
#align category_theory.preserves_finite_limits_of_flat.lift CategoryTheory.PreservesFiniteLimitsOfFlat.lift

/- warning: category_theory.preserves_finite_limits_of_flat.fac -> CategoryTheory.PreservesFiniteLimitsOfFlat.fac is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K} (hc : CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) (x : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) x)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) x) (CategoryTheory.PreservesFiniteLimitsOfFlat.lift.{u1, u2, u3} C _inst_1 D _inst_2 J _inst_3 _inst_4 K F _inst_5 c hc s) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c)) x)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) x)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K} (hc : CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) (x : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) x)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) x) (CategoryTheory.PreservesFiniteLimitsOfFlat.lift.{u1, u2, u3} C _inst_1 D _inst_2 J _inst_3 _inst_4 K F _inst_5 c hc s) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c)) x)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) x)
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_finite_limits_of_flat.fac CategoryTheory.PreservesFiniteLimitsOfFlat.facₓ'. -/
theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simpa [lift, ← functor.map_comp]
#align category_theory.preserves_finite_limits_of_flat.fac CategoryTheory.PreservesFiniteLimitsOfFlat.fac

attribute [local simp] eq_to_hom_map

/- warning: category_theory.preserves_finite_limits_of_flat.uniq -> CategoryTheory.PreservesFiniteLimitsOfFlat.uniq is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) -> (forall (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) (f₁ : Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))) (f₂ : Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))), (forall (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) j)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) j) f₁ (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c)) j)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) j)) -> (forall (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) j)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (CategoryTheory.Functor.obj.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) j) f₂ (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F c)) j)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.obj.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) j)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (CategoryTheory.Functor.obj.{u1, u1, u2, u3} C _inst_1 D _inst_2 F (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))) f₁ f₂))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u1, u3} D] {J : Type.{u1}} [_inst_3 : CategoryTheory.SmallCategory.{u1} J] [_inst_4 : CategoryTheory.FinCategory.{u1} J _inst_3] (F : CategoryTheory.Functor.{u1, u1, u2, u3} C _inst_1 D _inst_2) [_inst_5 : CategoryTheory.RepresentablyFlat.{u1, u1, u2, u3} C _inst_1 D _inst_2 F] {K : CategoryTheory.Functor.{u1, u1, u1, u2} J _inst_3 C _inst_1} {c : CategoryTheory.Limits.Cone.{u1, u1, u1, u2} J _inst_3 C _inst_1 K}, (CategoryTheory.Limits.IsLimit.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c) -> (forall (s : CategoryTheory.Limits.Cone.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) (f₁ : Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))) (f₂ : Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))), (forall (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) j)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) j) f₁ (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c)) j)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) j)) -> (forall (j : J), Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) j)) (CategoryTheory.CategoryStruct.comp.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c)) (Prefunctor.obj.{succ u1, succ u1, u1, u3} J (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} J (CategoryTheory.Category.toCategoryStruct.{u1, u1} J _inst_3)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F)) j) f₂ (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c))) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Functor.mapCone.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 F K c)) j)) (CategoryTheory.NatTrans.app.{u1, u1, u1, u3} J _inst_3 D _inst_2 (Prefunctor.obj.{succ u1, succ u1, u3, max u1 u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u3} (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u3, max u1 u3} D _inst_2 (CategoryTheory.Functor.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.category.{u1, u1, u1, u3} J _inst_3 D _inst_2) (CategoryTheory.Functor.const.{u1, u1, u1, u3} J _inst_3 D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s)) (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) (CategoryTheory.Limits.Cone.π.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) j)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u3} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u3} J _inst_3 D _inst_2 (CategoryTheory.Functor.comp.{u1, u1, u1, u1, u2, u3} J _inst_3 C _inst_1 D _inst_2 K F) s) (Prefunctor.obj.{succ u1, succ u1, u2, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} D (CategoryTheory.Category.toCategoryStruct.{u1, u3} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, u3} C _inst_1 D _inst_2 F) (CategoryTheory.Limits.Cone.pt.{u1, u1, u1, u2} J _inst_3 C _inst_1 K c))) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align category_theory.preserves_finite_limits_of_flat.uniq CategoryTheory.PreservesFiniteLimitsOfFlat.uniqₓ'. -/
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : ∀ j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : ∀ j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ :=
  by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : to_diagram (F.map_cone c) ⋙ map f₁ ⟶ to_diagram s :=
    { app := fun X => eq_to_hom (by simp [← h₁])
      naturality' := fun _ _ _ => by
        ext
        simp }
  let α₂ : to_diagram (F.map_cone c) ⋙ map f₂ ⟶ to_diagram s :=
    { app := fun X => eq_to_hom (by simp [← h₂])
      naturality' := fun _ _ _ => by
        ext
        simp }
  let c₁ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₁ (pre s.X K F) : _)).obj (to_cone F c f₁)
  let c₂ : cone (to_diagram s ⋙ pre s.X K F) :=
    (cones.postcompose (whisker_right α₂ (pre s.X K F) : _)).obj (to_cone F c f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `structured_arrow s.X F` is cofiltered.
  let c₀ := is_cofiltered.cone (bicone_mk _ c₁ c₂)
  let g₁ : c₀.X ⟶ c₁.X := c₀.π.app bicone.left
  let g₂ : c₀.X ⟶ c₂.X := c₀.π.app bicone.right
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : ∀ j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j :=
    by
    intro j
    injection c₀.π.naturality (bicone_hom.left j) with _ e₁
    injection c₀.π.naturality (bicone_hom.right j) with _ e₂
    simpa using e₁.symm.trans e₂
  have : c.extend g₁.right = c.extend g₂.right :=
    by
    unfold cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right
  calc
    g₁.right = hc.lift (c.extend g₁.right) :=
      by
      apply hc.uniq (c.extend _)
      tidy
    _ = hc.lift (c.extend g₂.right) := by
      congr
      exact this
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      tidy
    
  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc
    f₁ = 𝟙 _ ≫ f₁ := by simp
    _ = c₀.X.hom ≫ F.map g₁.right := g₁.w
    _ = c₀.X.hom ≫ F.map g₂.right := by rw [this]
    _ = 𝟙 _ ≫ f₂ := g₂.w.symm
    _ = f₂ := by simp
    
#align category_theory.preserves_finite_limits_of_flat.uniq CategoryTheory.PreservesFiniteLimitsOfFlat.uniq

end PreservesFiniteLimitsOfFlat

#print CategoryTheory.preservesFiniteLimitsOfFlat /-
/-- Representably flat functors preserve finite limits. -/
noncomputable def preservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F :=
  by
  apply preserves_finite_limits_of_preserves_finite_limits_of_size
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  exact
    { lift := preserves_finite_limits_of_flat.lift F hc
      fac := preserves_finite_limits_of_flat.fac F hc
      uniq := fun s m h => by
        apply preserves_finite_limits_of_flat.uniq F hc
        exact h
        exact preserves_finite_limits_of_flat.fac F hc s }
#align category_theory.preserves_finite_limits_of_flat CategoryTheory.preservesFiniteLimitsOfFlat
-/

#print CategoryTheory.preservesFiniteLimitsIffFlat /-
/-- If `C` is finitely cocomplete, then `F : C ⥤ D` is representably flat iff it preserves
finite limits.
-/
noncomputable def preservesFiniteLimitsIffFlat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ≃ PreservesFiniteLimits F
    where
  toFun _ := preserves_finite_limits_of_flat F
  invFun _ := flat_of_preserves_finite_limits F
  left_inv _ := proof_irrel _ _
  right_inv x := by
    cases x
    unfold preserves_finite_limits_of_flat
    dsimp only [preserves_finite_limits_of_preserves_finite_limits_of_size]
    congr
#align category_theory.preserves_finite_limits_iff_flat CategoryTheory.preservesFiniteLimitsIffFlat
-/

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]

/- warning: category_theory.Lan_evaluation_iso_colim -> CategoryTheory.lanEvaluationIsoColim is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} {D : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] [_inst_2 : CategoryTheory.SmallCategory.{u1} D] (E : Type.{u2}) [_inst_3 : CategoryTheory.Category.{u1, u2} E] (F : CategoryTheory.Functor.{u1, u1, u1, u1} C _inst_1 D _inst_2) (X : D) [_inst_4 : forall (X : D), CategoryTheory.Limits.HasColimitsOfShape.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) E _inst_3) (CategoryTheory.Functor.comp.{u1, u1, u1, max u1 u2, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3 (CategoryTheory.lan.{u1, u1, u1, u1, u1, u2} C D E _inst_1 _inst_2 _inst_3 F (CategoryTheory.lanEvaluationIsoColim._proof_1.{u1, u2} C D _inst_1 _inst_2 E _inst_3 F _inst_4)) (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u1 u2} D _inst_2 (CategoryTheory.Functor.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.evaluation.{u1, u1, u1, u2} D _inst_2 E _inst_3) X)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u1 u2, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) E _inst_3 (CategoryTheory.Functor.obj.{u1, max u1 u2, u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Functor.{u1, u1, max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.whiskeringLeft.{u1, u1, u1, u1, u2, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1 E _inst_3) (CategoryTheory.CostructuredArrow.proj.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X)) (CategoryTheory.Limits.colim.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.CostructuredArrow.category.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3 (_inst_4 X)))
but is expected to have type
  forall {C : Type.{u1}} {D : Type.{u1}} [_inst_1 : CategoryTheory.SmallCategory.{u1} C] [_inst_2 : CategoryTheory.SmallCategory.{u1} D] (E : Type.{u2}) [_inst_3 : CategoryTheory.Category.{u1, u2} E] (F : CategoryTheory.Functor.{u1, u1, u1, u1} C _inst_1 D _inst_2) (X : D) [_inst_4 : forall (X : D), CategoryTheory.Limits.HasColimitsOfShape.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3], CategoryTheory.Iso.{max u1 u2, max u2 u1} (CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) E _inst_3) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3 (CategoryTheory.lan.{u1, u1, u1, u1, u1, u2} C D E _inst_1 _inst_2 _inst_3 F (fun (X : D) => _inst_4 X)) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max u1 u2} D (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} D (CategoryTheory.Category.toCategoryStruct.{u1, u1} D _inst_2)) (CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max u1 u2} D _inst_2 (CategoryTheory.Functor.{u1, u1, max u2 u1, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} D _inst_2 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} D _inst_2 E _inst_3) E _inst_3) (CategoryTheory.evaluation.{u1, u1, u1, u2} D _inst_2 E _inst_3)) X)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u1 u2, max u1 u2, u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) E _inst_3 (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Functor.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Functor.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1))) (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)))) (CategoryTheory.Functor.toPrefunctor.{u1, max u1 u2, u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u1, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1) (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u1 u2, max u1 u2} (CategoryTheory.Functor.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} C _inst_1 E _inst_3) (CategoryTheory.Functor.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3) (CategoryTheory.Functor.category.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3)) (CategoryTheory.whiskeringLeft.{u1, u1, u1, u1, u2, u1} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) C _inst_1 E _inst_3)) (CategoryTheory.CostructuredArrow.proj.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X)) (CategoryTheory.Limits.colim.{u1, u1, u1, u2} (CategoryTheory.CostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) (CategoryTheory.instCategoryCostructuredArrow.{u1, u1, u1, u1} C _inst_1 D _inst_2 F X) E _inst_3 (_inst_4 X)))
Case conversion may be inaccurate. Consider using '#align category_theory.Lan_evaluation_iso_colim CategoryTheory.lanEvaluationIsoColimₓ'. -/
/-- (Implementation)
The evaluation of `Lan F` at `X` is the colimit over the costructured arrows over `X`.
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    lan F ⋙ (evaluation D E).obj X ≅
      (whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G => colim.mapIso (Iso.refl _))
    (by
      intro G H i
      ext
      simp only [functor.comp_map, colimit.ι_desc_assoc, functor.map_iso_refl, evaluation_obj_map,
        whiskering_left_obj_map, category.comp_id, Lan_map_app, category.assoc]
      erw [colimit.ι_pre_assoc (Lan.diagram F H X) (costructured_arrow.map j.hom), category.id_comp,
        category.comp_id, colimit.ι_map]
      rcases j with ⟨j_left, ⟨⟨⟩⟩, j_hom⟩
      congr
      rw [costructured_arrow.map_mk, category.id_comp, costructured_arrow.mk])
#align category_theory.Lan_evaluation_iso_colim CategoryTheory.lanEvaluationIsoColim

variable [ConcreteCategory.{u₁} E] [HasLimits E] [HasColimits E]

variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]

variable [PreservesLimits (forget E)]

#print CategoryTheory.lanPreservesFiniteLimitsOfFlat /-
/-- If `F : C ⥤ D` is a representably flat functor between small categories, then the functor
`Lan F.op` that takes presheaves over `C` to presheaves over `D` preserves finite limits.
-/
noncomputable instance lanPreservesFiniteLimitsOfFlat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
  intro J _ _; skip
  apply preserves_limits_of_shape_of_evaluation (Lan F.op : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  haveI : is_filtered (costructured_arrow F.op K) :=
    is_filtered.of_equivalence (structured_arrow_op_equivalence F (unop K))
  exact preserves_limits_of_shape_of_nat_iso (Lan_evaluation_iso_colim _ _ _).symm
#align category_theory.Lan_preserves_finite_limits_of_flat CategoryTheory.lanPreservesFiniteLimitsOfFlat
-/

#print CategoryTheory.lan_flat_of_flat /-
instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _
#align category_theory.Lan_flat_of_flat CategoryTheory.lan_flat_of_flat
-/

variable [HasFiniteLimits C]

#print CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits /-
noncomputable instance lanPreservesFiniteLimitsOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ E) :=
  by
  haveI := flat_of_preserves_finite_limits F
  infer_instance
#align category_theory.Lan_preserves_finite_limits_of_preserves_finite_limits CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits
-/

#print CategoryTheory.flat_iff_lan_flat /-
theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun H => inferInstance, fun H => by
    skip
    haveI := preserves_finite_limits_of_flat (Lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    haveI : preserves_finite_limits F :=
      by
      apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
      intros ; skip; apply preserves_limit_of_Lan_preserves_limit
    apply flat_of_preserves_finite_limits⟩
#align category_theory.flat_iff_Lan_flat CategoryTheory.flat_iff_lan_flat
-/

#print CategoryTheory.preservesFiniteLimitsIffLanPreservesFiniteLimits /-
/-- If `C` is finitely complete, then `F : C ⥤ D` preserves finite limits iff
`Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` preserves finite limits.
-/
noncomputable def preservesFiniteLimitsIffLanPreservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ≃ PreservesFiniteLimits (lan F.op : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    where
  toFun _ := inferInstance
  invFun _ := by
    apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{u₁}
    intros ; skip; apply preserves_limit_of_Lan_preserves_limit
  left_inv x := by
    cases x; unfold preserves_finite_limits_of_flat
    dsimp only [preserves_finite_limits_of_preserves_finite_limits_of_size]; congr
  right_inv x := by
    cases x
    unfold preserves_finite_limits_of_flat
    congr
    unfold
      CategoryTheory.lanPreservesFiniteLimitsOfPreservesFiniteLimits CategoryTheory.lanPreservesFiniteLimitsOfFlat
    dsimp only [preserves_finite_limits_of_preserves_finite_limits_of_size]; congr
#align category_theory.preserves_finite_limits_iff_Lan_preserves_finite_limits CategoryTheory.preservesFiniteLimitsIffLanPreservesFiniteLimits
-/

end SmallCategory

end CategoryTheory

