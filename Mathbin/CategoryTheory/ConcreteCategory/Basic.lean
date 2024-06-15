/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import CategoryTheory.Types
import CategoryTheory.Functor.EpiMono
import CategoryTheory.Limits.Constructions.EpiMono

#align_import category_theory.concrete_category.basic from "leanprover-community/mathlib"@"311ef8c4b4ae2804ea76b8a611bc5ea1d9c16872"

/-!
# Concrete categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`,
see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/


universe w v v' u u'

namespace CategoryTheory

open CategoryTheory.Limits

#print CategoryTheory.ConcreteCategory /-
/- ././././Mathport/Syntax/Translate/Command.lean:400:30: infer kinds are unsupported in Lean 4: #[`forget] [] -/
/-- A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`.

Note that `concrete_category` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class ConcreteCategory (C : Type u) [Category.{v} C] where
  forget : C ⥤ Type w
  [forget_faithful : CategoryTheory.Functor.Faithful forget]
#align category_theory.concrete_category CategoryTheory.ConcreteCategory
-/

attribute [instance] concrete_category.forget_faithful

#print CategoryTheory.forget /-
/-- The forgetful functor from a concrete category to `Type u`. -/
@[reducible]
def forget (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C] : C ⥤ Type w :=
  ConcreteCategory.forget C
#align category_theory.forget CategoryTheory.forget
-/

#print CategoryTheory.ConcreteCategory.types /-
instance ConcreteCategory.types : ConcreteCategory (Type u) where forget := 𝟭 _
#align category_theory.concrete_category.types CategoryTheory.ConcreteCategory.types
-/

#print CategoryTheory.ConcreteCategory.hasCoeToSort /-
/-- Provide a coercion to `Type u` for a concrete category. This is not marked as an instance
as it could potentially apply to every type, and so is too expensive in typeclass search.

You can use it on particular examples as:
```
instance : has_coe_to_sort X := concrete_category.has_coe_to_sort X
```
-/
def ConcreteCategory.hasCoeToSort (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C] :
    CoeSort C (Type w) :=
  ⟨(ConcreteCategory.forget C).obj⟩
#align category_theory.concrete_category.has_coe_to_sort CategoryTheory.ConcreteCategory.hasCoeToSort
-/

section

attribute [local instance] concrete_category.has_coe_to_sort

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{w} C]

@[simp]
theorem forget_obj_eq_coe {X : C} : (forget C).obj X = X :=
  rfl
#align category_theory.forget_obj_eq_coe CategoryTheory.forget_obj_eq_coe

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as a global instance. -/
def ConcreteCategory.hasCoeToFun {X Y : C} : CoeFun (X ⟶ Y) fun f => X → Y :=
  ⟨fun f => (forget _).map f⟩
#align category_theory.concrete_category.has_coe_to_fun CategoryTheory.ConcreteCategory.hasCoeToFun

attribute [local instance] concrete_category.has_coe_to_fun

#print CategoryTheory.ConcreteCategory.hom_ext /-
/-- In any concrete category, we can test equality of morphisms by pointwise evaluations.-/
theorem ConcreteCategory.hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x : X, f x = g x) : f = g :=
  by
  apply faithful.map_injective (forget C)
  ext
  exact w x
#align category_theory.concrete_category.hom_ext CategoryTheory.ConcreteCategory.hom_ext
-/

#print CategoryTheory.forget_map_eq_coe /-
@[simp]
theorem forget_map_eq_coe {X Y : C} (f : X ⟶ Y) : (forget C).map f = f :=
  rfl
#align category_theory.forget_map_eq_coe CategoryTheory.forget_map_eq_coe
-/

#print CategoryTheory.congr_hom /-
/-- Analogue of `congr_fun h x`,
when `h : f = g` is an equality between morphisms in a concrete category.
-/
theorem congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_fun (congr_arg (fun k : X ⟶ Y => (k : X → Y)) h) x
#align category_theory.congr_hom CategoryTheory.congr_hom
-/

#print CategoryTheory.coe_id /-
theorem coe_id {X : C} : (𝟙 X : X → X) = id :=
  (forget _).map_id X
#align category_theory.coe_id CategoryTheory.coe_id
-/

#print CategoryTheory.coe_comp /-
theorem coe_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  (forget _).map_comp f g
#align category_theory.coe_comp CategoryTheory.coe_comp
-/

#print CategoryTheory.id_apply /-
@[simp]
theorem id_apply {X : C} (x : X) : (𝟙 X : X → X) x = x :=
  congr_fun ((forget _).map_id X) x
#align category_theory.id_apply CategoryTheory.id_apply
-/

#print CategoryTheory.comp_apply /-
@[simp]
theorem comp_apply {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  congr_fun ((forget _).map_comp _ _) x
#align category_theory.comp_apply CategoryTheory.comp_apply
-/

#print CategoryTheory.ConcreteCategory.congr_hom /-
theorem ConcreteCategory.congr_hom {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
  congr_fun (congr_arg (fun f : X ⟶ Y => (f : X → Y)) h) x
#align category_theory.concrete_category.congr_hom CategoryTheory.ConcreteCategory.congr_hom
-/

#print CategoryTheory.ConcreteCategory.congr_arg /-
theorem ConcreteCategory.congr_arg {X Y : C} (f : X ⟶ Y) {x x' : X} (h : x = x') : f x = f x' :=
  congr_arg (f : X → Y) h
#align category_theory.concrete_category.congr_arg CategoryTheory.ConcreteCategory.congr_arg
-/

#print CategoryTheory.ConcreteCategory.mono_of_injective /-
/-- In any concrete category, injective morphisms are monomorphisms. -/
theorem ConcreteCategory.mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) :
    Mono f :=
  (forget C).mono_of_mono_map ((mono_iff_injective f).2 i)
#align category_theory.concrete_category.mono_of_injective CategoryTheory.ConcreteCategory.mono_of_injective
-/

#print CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback /-
theorem ConcreteCategory.injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f]
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Function.Injective f :=
  (mono_iff_injective ((forget C).map f)).mp inferInstance
#align category_theory.concrete_category.injective_of_mono_of_preserves_pullback CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback
-/

#print CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback /-
theorem ConcreteCategory.mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y)
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Mono f ↔ Function.Injective f :=
  ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)
#align category_theory.concrete_category.mono_iff_injective_of_preserves_pullback CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback
-/

#print CategoryTheory.ConcreteCategory.epi_of_surjective /-
/-- In any concrete category, surjective morphisms are epimorphisms. -/
theorem ConcreteCategory.epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) :
    Epi f :=
  (forget C).epi_of_epi_map ((epi_iff_surjective f).2 s)
#align category_theory.concrete_category.epi_of_surjective CategoryTheory.ConcreteCategory.epi_of_surjective
-/

#print CategoryTheory.ConcreteCategory.surjective_of_epi_of_preservesPushout /-
theorem ConcreteCategory.surjective_of_epi_of_preservesPushout {X Y : C} (f : X ⟶ Y) [Epi f]
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Function.Surjective f :=
  (epi_iff_surjective ((forget C).map f)).mp inferInstance
#align category_theory.concrete_category.surjective_of_epi_of_preserves_pushout CategoryTheory.ConcreteCategory.surjective_of_epi_of_preservesPushout
-/

#print CategoryTheory.ConcreteCategory.epi_iff_surjective_of_preservesPushout /-
theorem ConcreteCategory.epi_iff_surjective_of_preservesPushout {X Y : C} (f : X ⟶ Y)
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Epi f ↔ Function.Surjective f :=
  ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)
#align category_theory.concrete_category.epi_iff_surjective_of_preserves_pushout CategoryTheory.ConcreteCategory.epi_iff_surjective_of_preservesPushout
-/

#print CategoryTheory.ConcreteCategory.bijective_of_isIso /-
theorem ConcreteCategory.bijective_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective ((forget C).map f) := by rw [← is_iso_iff_bijective]; infer_instance
#align category_theory.concrete_category.bijective_of_is_iso CategoryTheory.ConcreteCategory.bijective_of_isIso
-/

#print CategoryTheory.ConcreteCategory.hasCoeToFun_Type /-
@[simp]
theorem ConcreteCategory.hasCoeToFun_Type {X Y : Type u} (f : X ⟶ Y) : coeFn f = f :=
  rfl
#align category_theory.concrete_category.has_coe_to_fun_Type CategoryTheory.ConcreteCategory.hasCoeToFun_Type
-/

end

#print CategoryTheory.HasForget₂ /-
/-- `has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class HasForget₂ (C : Type u) (D : Type u') [Category.{v} C] [ConcreteCategory.{w} C]
    [Category.{v'} D] [ConcreteCategory.{w} D] where
  forget₂ : C ⥤ D
  forget_comp : forget₂ ⋙ forget D = forget C := by obviously
#align category_theory.has_forget₂ CategoryTheory.HasForget₂
-/

#print CategoryTheory.forget₂ /-
/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget₂ C `. -/
@[reducible]
def forget₂ (C : Type u) (D : Type u') [Category.{v} C] [ConcreteCategory.{w} C] [Category.{v'} D]
    [ConcreteCategory.{w} D] [HasForget₂ C D] : C ⥤ D :=
  HasForget₂.forget₂
#align category_theory.forget₂ CategoryTheory.forget₂
-/

#print CategoryTheory.forget₂_faithful /-
instance forget₂_faithful (C : Type u) (D : Type u') [Category.{v} C] [ConcreteCategory.{w} C]
    [Category.{v'} D] [ConcreteCategory.{w} D] [HasForget₂ C D] :
    CategoryTheory.Functor.Faithful (forget₂ C D) :=
  HasForget₂.forget_comp.faithful_of_comp
#align category_theory.forget₂_faithful CategoryTheory.forget₂_faithful
-/

#print CategoryTheory.ConcreteCategory.forget₂_preservesMonomorphisms /-
instance CategoryTheory.ConcreteCategory.forget₂_preservesMonomorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [ConcreteCategory.{w} C] [Category.{v'} D] [ConcreteCategory.{w} D]
    [HasForget₂ C D] [(forget C).PreservesMonomorphisms] : (forget₂ C D).PreservesMonomorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by simp only [has_forget₂.forget_comp];
    infer_instance
  functor.preserves_monomorphisms_of_preserves_of_reflects _ (forget D)
#align category_theory.forget₂_preserves_monomorphisms CategoryTheory.ConcreteCategory.forget₂_preservesMonomorphisms
-/

#print CategoryTheory.ConcreteCategory.forget₂_preservesEpimorphisms /-
instance CategoryTheory.ConcreteCategory.forget₂_preservesEpimorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [ConcreteCategory.{w} C] [Category.{v'} D] [ConcreteCategory.{w} D]
    [HasForget₂ C D] [(forget C).PreservesEpimorphisms] : (forget₂ C D).PreservesEpimorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by simp only [has_forget₂.forget_comp];
    infer_instance
  functor.preserves_epimorphisms_of_preserves_of_reflects _ (forget D)
#align category_theory.forget₂_preserves_epimorphisms CategoryTheory.ConcreteCategory.forget₂_preservesEpimorphisms
-/

#print CategoryTheory.InducedCategory.concreteCategory /-
instance InducedCategory.concreteCategory {C : Type u} {D : Type u'} [Category.{v'} D]
    [ConcreteCategory.{w} D] (f : C → D) : ConcreteCategory.{w} (InducedCategory D f)
    where forget := inducedFunctor f ⋙ forget D
#align category_theory.induced_category.concrete_category CategoryTheory.InducedCategory.concreteCategory
-/

#print CategoryTheory.InducedCategory.hasForget₂ /-
instance InducedCategory.hasForget₂ {C : Type u} {D : Type u'} [Category.{v'} D]
    [ConcreteCategory.{w} D] (f : C → D) : HasForget₂ (InducedCategory D f) D
    where
  forget₂ := inducedFunctor f
  forget_comp := rfl
#align category_theory.induced_category.has_forget₂ CategoryTheory.InducedCategory.hasForget₂
-/

instance FullSubcategory.concreteCategory {C : Type u} [Category.{v} C] [ConcreteCategory.{w} C]
    (Z : C → Prop) : ConcreteCategory (FullSubcategory Z)
    where forget := fullSubcategoryInclusion Z ⋙ forget C
#align category_theory.full_subcategory.concrete_category CategoryTheory.FullSubcategoryₓ.concreteCategory

instance FullSubcategory.hasForget₂ {C : Type u} [Category.{v} C] [ConcreteCategory.{w} C]
    (Z : C → Prop) : HasForget₂ (FullSubcategory Z) C
    where
  forget₂ := fullSubcategoryInclusion Z
  forget_comp := rfl
#align category_theory.full_subcategory.has_forget₂ CategoryTheory.FullSubcategoryₓ.hasForget₂

#print CategoryTheory.HasForget₂.mk' /-
/-- In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def HasForget₂.mk' {C : Type u} {D : Type u'} [Category.{v} C] [ConcreteCategory.{w} C]
    [Category.{v'} D] [ConcreteCategory.{w} D] (obj : C → D)
    (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
    (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y} {f : X ⟶ Y}, HEq ((forget D).map (map f)) ((forget C).map f)) : HasForget₂ C D
    where
  forget₂ := CategoryTheory.Functor.Faithful.div _ _ _ @h_obj _ @h_map
  forget_comp := by apply faithful.div_comp
#align category_theory.has_forget₂.mk' CategoryTheory.HasForget₂.mk'
-/

#print CategoryTheory.hasForgetToType /-
/-- Every forgetful functor factors through the identity functor. This is not a global instance as
    it is prone to creating type class resolution loops. -/
def hasForgetToType (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C] : HasForget₂ C (Type w)
    where
  forget₂ := forget C
  forget_comp := Functor.comp_id _
#align category_theory.has_forget_to_Type CategoryTheory.hasForgetToType
-/

end CategoryTheory

