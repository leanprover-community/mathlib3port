import Mathbin.CategoryTheory.Limits.Presheaf 
import Mathbin.CategoryTheory.Limits.Preserves.FunctorCategory 
import Mathbin.CategoryTheory.Limits.Shapes.Types 
import Mathbin.CategoryTheory.Closed.Cartesian

/-!
# Cartesian closure of Type

Show that `Type u₁` is cartesian closed, and `C ⥤ Type u₁` is cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is cartesian closed.
-/


namespace CategoryTheory

noncomputable theory

open Category Limits

universe v₁ v₂ u₁ u₂

variable{C : Type v₂}[category.{v₁} C]

section CartesianClosed

-- error in CategoryTheory.Closed.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance (X : Type v₁) : is_left_adjoint (types.binary_product_functor.obj X) :=
{ right := { obj := λ Y, «expr ⟶ »(X, Y), map := λ Y₁ Y₂ f g, «expr ≫ »(g, f) },
  adj := adjunction.mk_of_unit_counit { unit := { app := λ (Z) (z : Z) (x), ⟨x, z⟩ },
    counit := { app := λ Z xf, xf.2 xf.1 } } }

instance  : has_finite_products (Type v₁) :=
  has_finite_products_of_has_products _

instance  : cartesian_closed (Type v₁) :=
  { closed := fun X => { isAdj := adjunction.left_adjoint_of_nat_iso (types.binary_product_iso_prod.app X) } }

instance  {C : Type u₁} [category.{v₁} C] : has_finite_products (C ⥤ Type u₁) :=
  has_finite_products_of_has_products _

-- error in CategoryTheory.Closed.Types: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance {C : Type v₁} [small_category C] : cartesian_closed «expr ⥤ »(C, Type v₁) :=
{ closed := λ
  F, { is_adj := begin
      letI [] [] [":=", expr functor_category.prod_preserves_colimits F],
      apply [expr is_left_adjoint_of_preserves_colimits (prod.functor.obj F)]
    end } }

end CartesianClosed

end CategoryTheory

