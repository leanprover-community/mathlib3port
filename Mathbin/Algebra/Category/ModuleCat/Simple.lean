/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Scott Morrison
-/
import Mathbin.CategoryTheory.Simple
import Mathbin.Algebra.Category.ModuleCat.Abelian
import Mathbin.Algebra.Category.ModuleCat.Subobject
import Mathbin.RingTheory.SimpleModule

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/


variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

theorem simple_iff_is_simple_module : Simple (of R M) ↔ IsSimpleModule R M :=
  (simple_iff_subobject_is_simple_order _).trans (subobjectModule (of R M)).is_simple_order_iff
#align simple_iff_is_simple_module simple_iff_is_simple_module

/-- A simple module is a simple object in the category of modules. -/
instance simple_of_is_simple_module [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_is_simple_module.mpr ‹_›
#align simple_of_is_simple_module simple_of_is_simple_module

/-- A simple object in the category of modules is a simple module. -/
instance is_simple_module_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_is_simple_module.mp (Simple.of_iso (ofSelfIso M))
#align is_simple_module_of_simple is_simple_module_of_simple

