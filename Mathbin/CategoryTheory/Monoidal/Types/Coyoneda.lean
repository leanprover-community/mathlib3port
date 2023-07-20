/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import Mathbin.CategoryTheory.Monoidal.Types.Basic
import Mathbin.CategoryTheory.Monoidal.CoherenceLemmas

#align_import category_theory.monoidal.types.coyoneda from "leanprover-community/mathlib"@"6b31d1eebd64eab86d5bd9936bfaada6ca8b5842"

/-!
# `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

open CategoryTheory.Limits

open Tactic

universe v u

namespace CategoryTheory

open Opposite

open MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.coyonedaTensorUnit /-
/-- `(𝟙_ C ⟶ -)` is a lax monoidal functor to `Type`. -/
def coyonedaTensorUnit (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    LaxMonoidalFunctor C (Type v) :=
  { coyoneda.obj (op (𝟙_ C)) with
    ε := fun p => 𝟙 _
    μ := fun X Y p => (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ p.2)
    μ_natural' := by tidy
    associativity' := fun X Y Z => by
      ext ⟨⟨f, g⟩, h⟩; dsimp at f g h 
      dsimp; simp only [iso.cancel_iso_inv_left, category.assoc]
      conv_lhs =>
        rw [← category.id_comp h, tensor_comp, category.assoc, associator_naturality, ←
          category.assoc, unitors_inv_equal, triangle_assoc_comp_right_inv]
      conv_rhs => rw [← category.id_comp f, tensor_comp]
    left_unitality' := by tidy
    right_unitality' := fun X => by
      ext ⟨f, ⟨⟩⟩; dsimp at f 
      dsimp; simp only [category.assoc]
      rw [right_unitor_naturality, unitors_inv_equal, iso.inv_hom_id_assoc] }
#align category_theory.coyoneda_tensor_unit CategoryTheory.coyonedaTensorUnit
-/

end CategoryTheory

