/-
Copyright (c) 2021 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.LinearAlgebra.Quotient
import Mathbin.Algebra.Category.Module.Basic

#align_import algebra.category.Module.epi_mono from "leanprover-community/mathlib"@"4f4a1c875d0baa92ab5d92f3fb1bb258ad9f3e5b"

/-!
# Monomorphisms in `Module R`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/


universe v u

open CategoryTheory

open ModuleCat

open scoped ModuleCat

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

#print ModuleCat.ker_eq_bot_of_mono /-
theorem ker_eq_bot_of_mono [Mono f] : f.ker = ⊥ :=
  LinearMap.ker_eq_bot_of_cancel fun u v => (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1
#align Module.ker_eq_bot_of_mono ModuleCat.ker_eq_bot_of_mono
-/

#print ModuleCat.range_eq_top_of_epi /-
theorem range_eq_top_of_epi [Epi f] : f.range = ⊤ :=
  LinearMap.range_eq_top_of_cancel fun u v => (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1
#align Module.range_eq_top_of_epi ModuleCat.range_eq_top_of_epi
-/

#print ModuleCat.mono_iff_ker_eq_bot /-
theorem mono_iff_ker_eq_bot : Mono f ↔ f.ker = ⊥ :=
  ⟨fun hf => ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| LinearMap.ker_eq_bot.1 hf⟩
#align Module.mono_iff_ker_eq_bot ModuleCat.mono_iff_ker_eq_bot
-/

#print ModuleCat.mono_iff_injective /-
theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]
#align Module.mono_iff_injective ModuleCat.mono_iff_injective
-/

#print ModuleCat.epi_iff_range_eq_top /-
theorem epi_iff_range_eq_top : Epi f ↔ f.range = ⊤ :=
  ⟨fun hf => range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| LinearMap.range_eq_top.1 hf⟩
#align Module.epi_iff_range_eq_top ModuleCat.epi_iff_range_eq_top
-/

#print ModuleCat.epi_iff_surjective /-
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top, LinearMap.range_eq_top]
#align Module.epi_iff_surjective ModuleCat.epi_iff_surjective
-/

#print ModuleCat.uniqueOfEpiZero /-
/-- If the zero morphism is an epi then the codomain is trivial. -/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)
#align Module.unique_of_epi_zero ModuleCat.uniqueOfEpiZero
-/

#print ModuleCat.mono_as_hom'_subtype /-
instance mono_as_hom'_subtype (U : Submodule R X) : Mono (↾U.Subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)
#align Module.mono_as_hom'_subtype ModuleCat.mono_as_hom'_subtype
-/

#print ModuleCat.epi_as_hom''_mkQ /-
instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (↿U.mkQ) :=
  (epi_iff_range_eq_top _).mpr <| Submodule.range_mkQ _
#align Module.epi_as_hom''_mkq ModuleCat.epi_as_hom''_mkQ
-/

#print ModuleCat.forget_preservesEpimorphisms /-
instance forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorphisms
    where preserves X Y f hf := by
    rwa [forget_map_eq_coe, CategoryTheory.epi_iff_surjective, ← epi_iff_surjective]
#align Module.forget_preserves_epimorphisms ModuleCat.forget_preservesEpimorphisms
-/

#print ModuleCat.forget_preservesMonomorphisms /-
instance forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomorphisms
    where preserves X Y f hf := by
    rwa [forget_map_eq_coe, CategoryTheory.mono_iff_injective, ← mono_iff_injective]
#align Module.forget_preserves_monomorphisms ModuleCat.forget_preservesMonomorphisms
-/

end ModuleCat

