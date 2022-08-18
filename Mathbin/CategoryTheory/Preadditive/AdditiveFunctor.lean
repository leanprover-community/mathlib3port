/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.ExactFunctor
import Mathbin.CategoryTheory.Limits.Preserves.Finite
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathbin.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.
Conversely, if `F : C ⥤ D` is a functor between preadditive categories, where `C` has binary
biproducts, and if `F` preserves binary biproducts, then `F` is additive.

We also define the category of bundled additive functors.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that for every two objects `X` and
`Y`, the map `F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian groups.

-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- A functor `F` is additive provided `F.map` is an additive homomorphism. -/
class Functor.Additive {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) : Prop where
  map_add' : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g := by
    run_tac
      obviously

section Preadditive

namespace Functor

section

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [Functor.Additive F]

@[simp]
theorem map_add {X Y : C} {f g : X ⟶ Y} : F.map (f + g) = F.map f + F.map g :=
  functor.additive.map_add'

/-- `F.map_add_hom` is an additive homomorphism whose underlying function is `F.map`. -/
@[simps (config := { fullyApplied := false })]
def mapAddHom {X Y : C} : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y) :=
  AddMonoidHom.mk' (fun f => F.map f) fun f g => F.map_add

theorem coe_map_add_hom {X Y : C} : ⇑(F.mapAddHom : (X ⟶ Y) →+ _) = @map C _ D _ F X Y :=
  rfl

instance (priority := 100) preserves_zero_morphisms_of_additive :
    PreservesZeroMorphisms F where map_zero' := fun X Y => F.mapAddHom.map_zero

instance : Additive (𝟭 C) where

instance {E : Type _} [Category E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] : Additive (F ⋙ G) where

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_neg _

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_sub _ _

theorem map_nsmul {X Y : C} {f : X ⟶ Y} {n : ℕ} : F.map (n • f) = n • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_nsmul _ _

-- You can alternatively just use `functor.map_smul` here, with an explicit `(r : ℤ)` argument.
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  (F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)).map_zsmul _ _

open BigOperators

@[simp]
theorem map_sum {X Y : C} {α : Type _} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  (F.mapAddHom : (X ⟶ Y) →+ _).map_sum f s

end

section InducedCategory

variable {C : Type _} {D : Type _} [Category D] [Preadditive D] (F : C → D)

instance induced_functor_additive : Functor.Additive (inducedFunctor F) where

end InducedCategory

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D] (F : C ⥤ D)

open CategoryTheory.Limits

open CategoryTheory.Preadditive

instance (priority := 100) preservesFiniteBiproductsOfAdditive [Additive F] :
    PreservesFiniteBiproducts
      F where preserves := fun J _ =>
    { preserves := fun f =>
        { preserves := fun b hb =>
            is_bilimit_of_total _
              (by
                simp_rw [F.map_bicone_π, F.map_bicone_ι, ← F.map_comp, ← F.map_sum]
                dsimp' only [← map_bicone_X]
                simp_rw [← F.map_id]
                refine' congr_arg _ (hb.is_limit.hom_ext fun j => hb.is_colimit.hom_ext fun j' => _)
                cases j
                cases j'
                dsimp' only [← limits.bicone.to_cone_π_app]
                simp [← sum_comp, ← comp_sum, ← bicone.ι_π, ← comp_dite, ← dite_comp]) } }

theorem additive_of_preserves_binary_biproducts [HasBinaryBiproducts C] [PreservesZeroMorphisms F]
    [PreservesBinaryBiproducts F] : Additive F :=
  { map_add' := fun X Y f g => by
      rw [biprod.add_eq_lift_id_desc, F.map_comp, ← biprod.lift_map_biprod, ← biprod.map_biprod_hom_desc,
        category.assoc, iso.inv_hom_id_assoc, F.map_id, biprod.add_eq_lift_id_desc] }

end

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D]

instance inverse_additive (e : C ≌ D) [e.Functor.Additive] :
    e.inverse.Additive where map_add' := fun X Y f g => by
    apply e.functor.map_injective
    simp

end Equivalenceₓ

section

variable (C D : Type _) [Category C] [Category D] [Preadditive C] [Preadditive D]

/-- Bundled additive functors. -/
@[nolint has_nonempty_instance]
def AdditiveFunctor :=
  FullSubcategory fun F : C ⥤ D => F.Additive deriving Category

-- mathport name: «expr ⥤+ »
infixr:26 " ⥤+ " => AdditiveFunctor

instance : Preadditive (C ⥤+ D) :=
  Preadditive.InducedCategory.category _

/-- An additive functor is in particular a functor. -/
def AdditiveFunctor.forget : (C ⥤+ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _ deriving Full, Faithful

variable {C D}

/-- Turn an additive functor into an object of the category `AdditiveFunctor C D`. -/
def AdditiveFunctor.of (F : C ⥤ D) [F.Additive] : C ⥤+ D :=
  ⟨F, inferInstance⟩

@[simp]
theorem AdditiveFunctor.of_fst (F : C ⥤ D) [F.Additive] : (AdditiveFunctor.of F).1 = F :=
  rfl

@[simp]
theorem AdditiveFunctor.forget_obj (F : C ⥤+ D) : (AdditiveFunctor.forget C D).obj F = F.1 :=
  rfl

theorem AdditiveFunctor.forget_obj_of (F : C ⥤ D) [F.Additive] :
    (AdditiveFunctor.forget C D).obj (AdditiveFunctor.of F) = F :=
  rfl

@[simp]
theorem AdditiveFunctor.forget_map (F G : C ⥤+ D) (α : F ⟶ G) : (AdditiveFunctor.forget C D).map α = α :=
  rfl

instance : Functor.Additive (AdditiveFunctor.forget C D) where map_add' := fun F G α β => rfl

instance (F : C ⥤+ D) : Functor.Additive F.1 :=
  F.2

end

section Exact

open CategoryTheory.Limits

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]

variable [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasBinaryBiproducts C]

section

attribute [local instance] preserves_binary_biproducts_of_preserves_binary_products

attribute [local instance] preserves_binary_biproducts_of_preserves_binary_coproducts

/-- Turn a left exact functor into an additive functor. -/
def AdditiveFunctor.ofLeftExact : (C ⥤ₗ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful

/-- Turn a right exact functor into an additive functor. -/
def AdditiveFunctor.ofRightExact : (C ⥤ᵣ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful

/-- Turn an exact functor into an additive functor. -/
def AdditiveFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤+ D :=
  FullSubcategory.map fun F h =>
    let hF := Classical.choice h.1
    functor.additive_of_preserves_binary_biproducts F deriving
  Full, Faithful

end

variable {C D}

@[simp]
theorem AdditiveFunctor.of_left_exact_obj_fst (F : C ⥤ₗ D) : ((AdditiveFunctor.ofLeftExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.of_right_exact_obj_fst (F : C ⥤ᵣ D) : ((AdditiveFunctor.ofRightExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.of_exact_obj_fst (F : C ⥤ₑ D) : ((AdditiveFunctor.ofExact C D).obj F).obj = F.obj :=
  rfl

@[simp]
theorem AdditiveFunctor.of_left_exact_map {F G : C ⥤ₗ D} (α : F ⟶ G) : (AdditiveFunctor.ofLeftExact C D).map α = α :=
  rfl

@[simp]
theorem AdditiveFunctor.of_right_exact_map {F G : C ⥤ᵣ D} (α : F ⟶ G) : (AdditiveFunctor.ofRightExact C D).map α = α :=
  rfl

@[simp]
theorem AdditiveFunctor.of_exact_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (AdditiveFunctor.ofExact C D).map α = α :=
  rfl

end Exact

end Preadditive

end CategoryTheory

