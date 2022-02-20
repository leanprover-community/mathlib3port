/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Additive Functors

A functor between two preadditive categories is called *additive*
provided that the induced map on hom types is a morphism of abelian
groups.

An additive functor between preadditive categories creates and preserves biproducts.

# Implementation details

`functor.additive` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of abelian
groups.

# Project:

- Prove that a functor is additive if it preserves finite biproducts
  (See https://stacks.math.columbia.edu/tag/010M.)
-/


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

instance (priority := 100) preserves_zero_morphisms_of_additive : PreservesZeroMorphisms F where
  map_zero' := fun X Y => F.mapAddHom.map_zero

instance : Additive (𝟭 C) :=
  {  }

instance {E : Type _} [Category E] [Preadditive E] (G : D ⥤ E) [Functor.Additive G] : Additive (F ⋙ G) :=
  {  }

@[simp]
theorem map_neg {X Y : C} {f : X ⟶ Y} : F.map (-f) = -F.map f :=
  F.mapAddHom.map_neg _

@[simp]
theorem map_sub {X Y : C} {f g : X ⟶ Y} : F.map (f - g) = F.map f - F.map g :=
  F.mapAddHom.map_sub _ _

-- You can alternatively just use `functor.map_smul` here, with an explicit `(r : ℤ)` argument.
theorem map_zsmul {X Y : C} {f : X ⟶ Y} {r : ℤ} : F.map (r • f) = r • F.map f :=
  F.mapAddHom.map_zsmul _ _

open_locale BigOperators

@[simp]
theorem map_sum {X Y : C} {α : Type _} (f : α → (X ⟶ Y)) (s : Finset α) :
    F.map (∑ a in s, f a) = ∑ a in s, F.map (f a) :=
  (F.mapAddHom : (X ⟶ Y) →+ _).map_sum f s

end

section InducedCategory

variable {C : Type _} {D : Type _} [Category D] [Preadditive D] (F : C → D)

instance induced_functor_additive : Functor.Additive (inducedFunctor F) :=
  {  }

end InducedCategory

section

-- To talk about preservation of biproducts we need to specify universes explicitly.
noncomputable section

universe v u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [Functor.Additive F]

open CategoryTheory.Limits

/-- An additive functor between preadditive categories creates finite biproducts.
-/
instance map_has_biproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [HasBiproduct f] :
    HasBiproduct fun j => F.obj (f j) :=
  has_biproduct_of_total
    { x := F.obj (⨁ f), π := fun j => F.map (biproduct.π f j), ι := fun j => F.map (biproduct.ι f j),
      ι_π := fun j j' => by
        simp only [← F.map_comp]
        split_ifs
        · subst h
          simp
          
        · simp [h]
           }
    (by
      simp_rw [← F.map_comp, ← F.map_sum, biproduct.total, Functor.map_id])

/-- An additive functor between preadditive categories preserves finite biproducts.
-/
-- This essentially repeats the work of the previous instance,
-- but gives good definitional reduction to `biproduct.lift` and `biproduct.desc`.
@[simps]
def mapBiproduct {J : Type v} [Fintype J] [DecidableEq J] (f : J → C) [HasBiproduct f] :
    F.obj (⨁ f) ≅ ⨁ fun j => F.obj (f j) where
  Hom := biproduct.lift fun j => F.map (biproduct.π f j)
  inv := biproduct.desc fun j => F.map (biproduct.ι f j)
  hom_inv_id' := by
    simp only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum, biproduct.total, F.map_id]
  inv_hom_id' := by
    ext j j'
    simp only [category.comp_id, category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, ← F.map_comp, biproduct.ι_π,
      F.map_dite, dif_ctx_congr, eq_to_hom_map, F.map_zero]

end

end Functor

namespace Equivalenceₓ

variable {C D : Type _} [Category C] [Category D] [Preadditive C] [Preadditive D]

instance inverse_additive (e : C ≌ D) [e.Functor.Additive] : e.inverse.Additive where
  map_add' := fun X Y f g => by
    apply e.functor.map_injective
    simp

end Equivalenceₓ

end Preadditive

end CategoryTheory

