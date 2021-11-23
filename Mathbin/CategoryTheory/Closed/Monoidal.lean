import Mathbin.CategoryTheory.Monoidal.Category 
import Mathbin.CategoryTheory.Adjunction.Basic

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/


universe v u u₂

namespace CategoryTheory

open Category MonoidalCategory

/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class closed{C : Type u}[category.{v} C][monoidal_category.{v} C](X : C) where 
  isAdj : is_left_adjoint (tensor_left X)

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class monoidal_closed(C : Type u)[category.{v} C][monoidal_category.{v} C] where 
  Closed : ∀ X : C, closed X

attribute [instance] monoidal_closed.closed

/--
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unit_closed {C : Type u} [category.{v} C] [monoidal_category.{v} C] : closed (𝟙_ C) :=
  { isAdj :=
      { right := 𝟭 C,
        adj :=
          adjunction.mk_of_hom_equiv
            { homEquiv :=
                fun X _ =>
                  { toFun := fun a => (left_unitor X).inv ≫ a, invFun := fun a => (left_unitor X).Hom ≫ a,
                    left_inv :=
                      by 
                        tidy,
                    right_inv :=
                      by 
                        tidy },
              hom_equiv_naturality_left_symm' :=
                fun X' X Y f g =>
                  by 
                    dsimp 
                    rw [left_unitor_naturality_assoc] } } }

end CategoryTheory

