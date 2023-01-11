/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.algebra
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.CategoryTheory.Linear.Basic
import Mathbin.Algebra.Category.ModuleCat.Basic

/-!
# Additional typeclass for modules over an algebra

For an object in `M : Module A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `module k M` and `is_scalar_tower k A M`.
These are not made into instances by default.

We provide the `linear k (Module A)` instance.

## Note

If you begin with a `[module k M] [module A M] [is_scalar_tower k A M]`,
and build a bundled module via `Module.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `Module' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses,
requiring users to write `Module' ℤ A` when `A` is merely a ring.)
-/


universe v u w

open CategoryTheory

namespace ModuleCat

variable {k : Type u} [Field k]

variable {A : Type w} [Ring A] [Algebra k A]

/-- Type synonym for considering a module over a `k`-algebra as a `k`-module.
-/
def moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M :=
  RestrictScalars.module k A M
#align Module.module_of_algebra_Module ModuleCat.moduleOfAlgebraModule

attribute [scoped instance] ModuleCat.moduleOfAlgebraModule

theorem is_scalar_tower_of_algebra_Module (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  RestrictScalars.is_scalar_tower k A M
#align Module.is_scalar_tower_of_algebra_Module ModuleCat.is_scalar_tower_of_algebra_Module

attribute [scoped instance] ModuleCat.is_scalar_tower_of_algebra_Module

-- We verify that the morphism spaces become `k`-modules.
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := by infer_instance

instance linearOverField : Linear k (ModuleCat.{v} A) where homModule M N := by infer_instance
#align Module.linear_over_field ModuleCat.linearOverField

end ModuleCat

