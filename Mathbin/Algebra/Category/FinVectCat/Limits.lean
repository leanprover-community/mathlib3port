/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.FinVectCat
import Mathbin.Algebra.Category.ModuleCat.Limits
import Mathbin.Algebra.Category.ModuleCat.Products
import Mathbin.Algebra.Category.ModuleCat.EpiMono
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# `forget₂ (FinVect K) (Module K)` creates all finite limits.

And hence `FinVect K` has all finite limits.

## Future work
After generalising `FinVect` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace FinVectCat

variable {J : Type} [SmallCategory J] [FinCategory J]

variable {k : Type v} [Field k]

instance {J : Type} [Fintype J] (Z : J → ModuleCat.{v} k) [∀ j, FiniteDimensional k (Z j)] :
    FiniteDimensional k (∏ fun j => Z j : ModuleCat.{v} k) :=
  haveI : FiniteDimensional k (ModuleCat.of k (∀ j, Z j)) := by
    dsimp
    infer_instance
  FiniteDimensional.ofInjective (ModuleCat.piIsoPi _).Hom ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

/-- Finite limits of finite finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FinVectCat k) :
    FiniteDimensional k (limit (F ⋙ forget₂ (FinVectCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : ∀ j, FiniteDimensional k ((F ⋙ forget₂ (FinVectCat k) (ModuleCat.{v} k)).obj j) := by
    intro j
    change FiniteDimensional k (F.obj j).obj
    infer_instance
  FiniteDimensional.ofInjective (limit_subobject_product (F ⋙ forget₂ (FinVectCat k) (ModuleCat.{v} k)))
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

/-- The forgetful functor from `FinVect k` to `Module k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FinVectCat k) : CreatesLimit F (forget₂ (FinVectCat k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FinVectCat k) (ModuleCat.{v} k)) : ModuleCat.{v} k), by infer_instance⟩ (Iso.refl _)
#align FinVect.forget₂_creates_limit FinVectCat.forget₂CreatesLimit

instance :
    CreatesLimitsOfShape J (forget₂ (FinVectCat k) (ModuleCat.{v} k)) where CreatesLimit F := forget₂CreatesLimit F

instance :
    HasFiniteLimits
      (FinVectCat
        k) where out J _ _ :=
    has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (forget₂ (FinVectCat k) (ModuleCat.{v} k))

instance :
    PreservesFiniteLimits (forget₂ (FinVectCat k) (ModuleCat.{v} k)) where PreservesFiniteLimits J _ _ := inferInstance

end FinVectCat

