/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.fgModule.limits
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.FgModule.Basic
import Mathbin.Algebra.Category.ModuleCat.Limits
import Mathbin.Algebra.Category.ModuleCat.Products
import Mathbin.Algebra.Category.ModuleCat.EpiMono
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# `forget₂ (fgModule K) (Module K)` creates all finite limits.

And hence `fgModule K` has all finite limits.

## Future work
After generalising `fgModule` to allow the ring and the module to live in different universes,
generalize this construction so we can take limits over smaller diagrams,
as is done for the other algebraic categories.

Analogous constructions for Noetherian modules.
-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace FgModule

variable {J : Type} [SmallCategory J] [FinCategory J]

variable {k : Type v} [Field k]

instance {J : Type} [Fintype J] (Z : J → ModuleCat.{v} k) [∀ j, FiniteDimensional k (Z j)] :
    FiniteDimensional k (∏ fun j => Z j : ModuleCat.{v} k) :=
  haveI : FiniteDimensional k (ModuleCat.of k (∀ j, Z j)) :=
    by
    dsimp
    infer_instance
  FiniteDimensional.of_injective (ModuleCat.piIsoPi _).Hom
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

/-- Finite limits of finite dimensional vectors spaces are finite dimensional,
because we can realise them as subobjects of a finite product. -/
instance (F : J ⥤ FgModule k) :
    FiniteDimensional k (limit (F ⋙ forget₂ (FgModule k) (ModuleCat.{v} k)) : ModuleCat.{v} k) :=
  haveI : ∀ j, FiniteDimensional k ((F ⋙ forget₂ (FgModule k) (ModuleCat.{v} k)).obj j) :=
    by
    intro j
    change FiniteDimensional k (F.obj j).obj
    infer_instance
  FiniteDimensional.of_injective
    (limit_subobject_product (F ⋙ forget₂ (FgModule k) (ModuleCat.{v} k)))
    ((ModuleCat.mono_iff_injective _).1 (by infer_instance))

/-- The forgetful functor from `fgModule k` to `Module k` creates all finite limits. -/
def forget₂CreatesLimit (F : J ⥤ FgModule k) :
    CreatesLimit F (forget₂ (FgModule k) (ModuleCat.{v} k)) :=
  createsLimitOfFullyFaithfulOfIso
    ⟨(limit (F ⋙ forget₂ (FgModule k) (ModuleCat.{v} k)) : ModuleCat.{v} k), by infer_instance⟩
    (Iso.refl _)
#align fgModule.forget₂_creates_limit FgModule.forget₂CreatesLimit

instance : CreatesLimitsOfShape J (forget₂ (FgModule k) (ModuleCat.{v} k))
    where CreatesLimit F := forget₂CreatesLimit F

instance : HasFiniteLimits (FgModule k)
    where out J _ _ :=
    has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape
      (forget₂ (FgModule k) (ModuleCat.{v} k))

instance : PreservesFiniteLimits (forget₂ (FgModule k) (ModuleCat.{v} k))
    where PreservesFiniteLimits J _ _ := inferInstance

end FgModule

