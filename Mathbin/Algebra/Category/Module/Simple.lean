/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Scott Morrison
-/
import CategoryTheory.Simple
import Algebra.Category.Module.Subobject
import Algebra.Category.Module.Algebra
import RingTheory.SimpleModule
import LinearAlgebra.FiniteDimensional

#align_import algebra.category.Module.simple from "leanprover-community/mathlib"@"44e2ae8cffc713925494e4975ee31ec1d06929b3"

/-!
# Simple objects in the category of `R`-modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/


variable {R M : Type _} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

#print simple_iff_isSimpleModule /-
theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M :=
  (simple_iff_subobject_isSimpleOrder _).trans (subobjectModule (of R M)).isSimpleOrder_iff
#align simple_iff_is_simple_module simple_iff_isSimpleModule
-/

#print simple_iff_isSimpleModule' /-
theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  (Simple.iff_of_iso (ofSelfIso M).symm).trans simple_iff_isSimpleModule
#align simple_iff_is_simple_module' simple_iff_isSimpleModule'
-/

#print simple_of_isSimpleModule /-
/-- A simple module is a simple object in the category of modules. -/
instance simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_isSimpleModule.mpr ‹_›
#align simple_of_is_simple_module simple_of_isSimpleModule
-/

#print isSimpleModule_of_simple /-
/-- A simple object in the category of modules is a simple module. -/
instance isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_isSimpleModule.mp (Simple.of_iso (ofSelfIso M))
#align is_simple_module_of_simple isSimpleModule_of_simple
-/

open FiniteDimensional

attribute [local instance] module_of_algebra_Module is_scalar_tower_of_algebra_Module

#print simple_of_finrank_eq_one /-
/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
theorem simple_of_finrank_eq_one {k : Type _} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
  (simple_iff_isSimpleModule' V).mpr (is_simple_module_of_finrank_eq_one h)
#align simple_of_finrank_eq_one simple_of_finrank_eq_one
-/

