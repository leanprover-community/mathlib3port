import Mathbin.Algebra.Category.Group.ZModuleEquivalence 
import Mathbin.Algebra.Category.Module.Subobject

/-!
# The category of abelian groups is well-powered
-/


open CategoryTheory

universe u

namespace AddCommGroupₓₓ

instance well_powered_AddCommGroup : well_powered AddCommGroupₓₓ.{u} :=
  well_powered_of_equiv (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).asEquivalence

end AddCommGroupₓₓ

