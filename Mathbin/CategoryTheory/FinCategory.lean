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
class fin_category (J : Type v) [small_category J] where 
  decidableEqObj : DecidableEq J :=  by 
  runTac 
    tactic.apply_instance 
  fintypeObj : Fintype J :=  by 
  runTac 
    tactic.apply_instance 
  decidableEqHom : ∀ j j' : J, DecidableEq (j ⟶ j') :=  by 
  runTac 
    tactic.apply_instance 
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') :=  by 
  runTac 
    tactic.apply_instance

attribute [instance] fin_category.decidable_eq_obj fin_category.fintype_obj fin_category.decidable_eq_hom
  fin_category.fintype_hom

instance fin_category_discrete_of_decidable_fintype (J : Type v) [DecidableEq J] [Fintype J] :
  fin_category (discrete J) :=
  {  }

namespace FinCategory

variable (α : Type _) [Fintype α] [small_category α] [fin_category α]

/-- A fin_category `α` is equivalent to a category with objects in `Type`. -/
@[nolint unused_arguments]
abbrev obj_as_type : Type :=
  induced_category α (Fintype.equivFin α).symm

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def obj_as_type_equiv : obj_as_type α ≌ α :=
  (induced_functor (Fintype.equivFin α).symm).asEquivalence

/-- A fin_category `α` is equivalent to a fin_category with in `Type`. -/
@[nolint unused_arguments]
abbrev as_type : Type :=
  Finₓ (Fintype.card α)

@[simps (config := lemmasOnly) hom id comp]
noncomputable instance category_as_type : small_category (as_type α) :=
  { hom := fun i j => Finₓ (Fintype.card (@Quiver.Hom (obj_as_type α) _ i j)), id := fun i => Fintype.equivFin _ (𝟙 i),
    comp := fun i j k f g => Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g) }

attribute [local simp] category_as_type_hom category_as_type_id category_as_type_comp

/-- The constructed category (`as_type α`) is equivalent to `obj_as_type α`. -/
noncomputable def obj_as_type_equiv_as_type : as_type α ≌ obj_as_type α :=
  { Functor :=
      { obj := id, map := fun i j f => (Fintype.equivFin _).symm f,
        map_comp' :=
          fun _ _ _ _ _ =>
            by 
              dsimp 
              simp  },
    inverse :=
      { obj := id, map := fun i j f => Fintype.equivFin _ f,
        map_comp' :=
          fun _ _ _ _ _ =>
            by 
              dsimp 
              simp  },
    unitIso :=
      nat_iso.of_components iso.refl
        fun _ _ _ =>
          by 
            dsimp 
            simp ,
    counitIso :=
      nat_iso.of_components iso.refl
        fun _ _ _ =>
          by 
            dsimp 
            simp  }

noncomputable instance as_type_fin_category : fin_category (as_type α) :=
  {  }

/-- The constructed category (`as_type α`) is indeed equivalent to `α`. -/
noncomputable def equiv_as_type : as_type α ≌ α :=
  (obj_as_type_equiv_as_type α).trans (obj_as_type_equiv α)

end FinCategory

open Opposite

/--
The opposite of a finite category is finite.
-/
def fin_category_opposite {J : Type v} [small_category J] [fin_category J] : fin_category (Jᵒᵖ) :=
  { decidableEqObj := Equivₓ.decidableEq equiv_to_opposite.symm, fintypeObj := Fintype.ofEquiv _ equiv_to_opposite,
    decidableEqHom := fun j j' => Equivₓ.decidableEq (op_equiv j j'),
    fintypeHom := fun j j' => Fintype.ofEquiv _ (op_equiv j j').symm }

end CategoryTheory

