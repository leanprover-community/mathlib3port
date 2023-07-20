/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import Mathbin.Topology.Category.Top.Basic
import Mathbin.CategoryTheory.Adjunction.Basic

#align_import topology.category.Top.adjunctions from "leanprover-community/mathlib"@"814d76e2247d5ba8bc024843552da1278bfe9e5c"

/-!
# Adjunctions regarding the category of topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `Top.discrete`, resp. `Top.trivial`, the functors which equip a type with the
discrete, resp. trivial, topology.
-/


universe u

open CategoryTheory

open TopCat

namespace TopCat

#print TopCat.adj₁ /-
/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₁ : discrete ⊣ forget TopCat.{u} :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun X => id }
      counit := { app := fun X => ⟨id, continuous_bot⟩ } }
#align Top.adj₁ TopCat.adj₁
-/

#print TopCat.adj₂ /-
/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₂ : forget TopCat.{u} ⊣ trivial :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun X => ⟨id, continuous_top⟩ }
      counit := { app := fun X => id } }
#align Top.adj₂ TopCat.adj₂
-/

instance : IsRightAdjoint (forget TopCat.{u}) :=
  ⟨_, adj₁⟩

instance : IsLeftAdjoint (forget TopCat.{u}) :=
  ⟨_, adj₂⟩

end TopCat

