import Mathbin.Data.Fintype.Basic 
import Mathbin.CategoryTheory.DiscreteCategory 
import Mathbin.CategoryTheory.Opposites

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation

We also ask for decidable equality of objects and morphisms, but it may be reasonable to just
go classical in future.
-/


universe v u

namespace CategoryTheory

instance discrete_fintype {α : Type _} [Fintype α] : Fintype (discrete α) :=
  by 
    dsimp [discrete]
    infer_instance

instance discrete_hom_fintype {α : Type _} [DecidableEq α] (X Y : discrete α) : Fintype (X ⟶ Y) :=
  by 
    apply Ulift.fintype

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category(J : Type v)[small_category J] where 
  decidableEqObj : DecidableEq J :=  by 
  runTac 
    tactic.apply_instance 
  fintypeObj : Fintype J :=  by 
  runTac 
    tactic.apply_instance 
  decidableEqHom : ∀ (j j' : J), DecidableEq (j ⟶ j') :=  by 
  runTac 
    tactic.apply_instance 
  fintypeHom : ∀ (j j' : J), Fintype (j ⟶ j') :=  by 
  runTac 
    tactic.apply_instance

attribute [instance] fin_category.decidable_eq_obj fin_category.fintype_obj fin_category.decidable_eq_hom
  fin_category.fintype_hom

instance fin_category_discrete_of_decidable_fintype (J : Type v) [DecidableEq J] [Fintype J] :
  fin_category (discrete J) :=
  {  }

open Opposite

/--
The opposite of a finite category is finite.
-/
def fin_category_opposite {J : Type v} [small_category J] [fin_category J] : fin_category («expr ᵒᵖ» J) :=
  { decidableEqObj := Equiv.decidableEq equiv_to_opposite.symm, fintypeObj := Fintype.ofEquiv _ equiv_to_opposite,
    decidableEqHom := fun j j' => Equiv.decidableEq (op_equiv j j'),
    fintypeHom := fun j j' => Fintype.ofEquiv _ (op_equiv j j').symm }

end CategoryTheory

