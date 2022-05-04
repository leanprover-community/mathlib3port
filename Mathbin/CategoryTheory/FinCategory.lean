/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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

instance discreteFintype {α : Type _} [Fintype α] : Fintype (Discrete α) := by
  dsimp' [discrete]
  infer_instance

instance discreteHomFintype {α : Type _} [DecidableEq α] (X Y : Discrete α) : Fintype (X ⟶ Y) := by
  apply ULift.fintype

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class FinCategory (J : Type v) [SmallCategory J] where
  decidableEqObj : DecidableEq J := by
    run_tac
      tactic.apply_instance
  fintypeObj : Fintype J := by
    run_tac
      tactic.apply_instance
  decidableEqHom : ∀ j j' : J, DecidableEq (j ⟶ j') := by
    run_tac
      tactic.apply_instance
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') := by
    run_tac
      tactic.apply_instance

attribute [instance]
  fin_category.decidable_eq_obj fin_category.fintype_obj fin_category.decidable_eq_hom fin_category.fintype_hom

-- We need a `decidable_eq` instance here to construct `fintype` on the morphism spaces.
instance finCategoryDiscreteOfDecidableFintype (J : Type v) [DecidableEq J] [Fintype J] : FinCategory (Discrete J) :=
  {  }

namespace FinCategory

variable (α : Type _) [Fintype α] [SmallCategory α] [FinCategory α]

/-- A fin_category `α` is equivalent to a category with objects in `Type`. -/
@[nolint unused_arguments]
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

/-- A fin_category `α` is equivalent to a fin_category with in `Type`. -/
@[nolint unused_arguments]
abbrev AsType : Type :=
  Finₓ (Fintype.card α)

@[simps (config := lemmasOnly) hom id comp]
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  hom := fun i j => Finₓ (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id := fun i => Fintype.equivFin _ (𝟙 i)
  comp := fun i j k f g => Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] category_as_type_hom category_as_type_id category_as_type_comp

/-- The "identity" functor from `as_type α` to `obj_as_type α`. -/
@[simps]
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map := fun i j => (Fintype.equivFin _).symm

/-- The "identity" functor from `obj_as_type α` to `as_type α`. -/
@[simps]
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map := fun i j => Fintype.equivFin _

/-- The constructed category (`as_type α`) is equivalent to `obj_as_type α`. -/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α :=
  Equivalence.mk (asTypeToObjAsType α) (objAsTypeToAsType α)
    ((NatIso.ofComponents Iso.refl) fun _ _ _ => by
      dsimp'
      simp )
    ((NatIso.ofComponents Iso.refl) fun _ _ _ => by
      dsimp'
      simp )

noncomputable instance asTypeFinCategory : FinCategory (AsType α) :=
  {  }

/-- The constructed category (`as_type α`) is indeed equivalent to `α`. -/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

open Opposite

/-- The opposite of a finite category is finite.
-/
instance finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCategory Jᵒᵖ where
  decidableEqObj := Equivₓ.decidableEq equivToOpposite.symm
  fintypeObj := Fintype.ofEquiv _ equivToOpposite
  decidableEqHom := fun j j' => Equivₓ.decidableEq (opEquiv j j')
  fintypeHom := fun j j' => Fintype.ofEquiv _ (opEquiv j j').symm

end CategoryTheory

