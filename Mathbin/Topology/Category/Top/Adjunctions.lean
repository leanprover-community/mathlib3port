import Mathbin.Topology.Category.Top.Basic
import Mathbin.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `Top.discrete`, resp. `Top.trivial`, the functors which equip a type with the
discrete, resp. trivial, topology.
-/


universe u

open CategoryTheory

open Top

namespace Top

/--  Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₁ : discrete ⊣ forget Top.{u} :=
  adjunction.mk_of_unit_counit { Unit := { app := fun X => id }, counit := { app := fun X => ⟨id, continuous_bot⟩ } }

/--  Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps Unit counit]
def adj₂ : forget Top.{u} ⊣ trivialₓ :=
  adjunction.mk_of_unit_counit { Unit := { app := fun X => ⟨id, continuous_top⟩ }, counit := { app := fun X => id } }

instance : is_right_adjoint (forget Top.{u}) :=
  ⟨_, adj₁⟩

end Top

