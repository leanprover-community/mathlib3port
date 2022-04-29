/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.CategoryTheory.Simple
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.RingTheory.SimpleModule

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are simple objects in the category of `R`-modules.
TODO : prove that reciprocally, a simple object in the category of `R`-modules is indeed
a simple module.
-/


section Category

variable {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

open CategoryTheory

open ModuleCat

instance is_simple_module_of [H : IsSimpleModule R M] : IsSimpleModule R (of R M) :=
  H

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_is_simple_module [IsSimpleModule R M] : Simple (of R M) where
  mono_is_iso_iff_nonzero := fun N f inj => by
    constructor
    · rintro h rfl
      have : Unique M := unique_of_epi_zero N
      have : Nontrivial M := IsSimpleModule.nontrivial R M
      exact false_of_nontrivial_of_subsingleton M
      
    · intro h
      have : epi f := by
        rw [epi_iff_range_eq_top]
        refine' (eq_bot_or_eq_top f.range).resolve_left _
        exact mt linear_map.range_eq_bot.mp h
      exact is_iso_of_mono_of_epi _
      

end Category

