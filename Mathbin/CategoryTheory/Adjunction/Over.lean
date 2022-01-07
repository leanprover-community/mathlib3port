import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Monad.Products
import Mathbin.CategoryTheory.Over

/-!
# Adjunctions related to the over category

Construct the left adjoint `star X` to `over.forget X : over X ⥤ C`.

## TODO
Show `star X` itself has a left adjoint provided `C` is locally cartesian closed.
-/


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [category.{v} C] (X : C)

/-- The functor from `C` to `over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps]
def star [has_binary_products C] : C ⥤ over X :=
  cofree _ ⋙ coalgebra_to_over X

/-- The functor `over.forget X : over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forget_adj_star [has_binary_products C] : over.forget X ⊣ star X :=
  (coalgebra_equiv_over X).symm.toAdjunction.comp _ _ (adj _)

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [has_binary_products C] : is_left_adjoint (over.forget X) :=
  ⟨_, forget_adj_star X⟩

end CategoryTheory

