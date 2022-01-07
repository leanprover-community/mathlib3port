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

noncomputable section

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [category.{v₁} C]

section CartesianClosed

instance (X : Type v₁) : is_left_adjoint (types.binary_product_functor.obj X) where
  right := { obj := fun Y => X ⟶ Y, map := fun Y₁ Y₂ f g => g ≫ f }
  adj :=
    adjunction.mk_of_unit_counit
      { Unit := { app := fun Z z : Z x => ⟨x, z⟩ }, counit := { app := fun Z xf => xf.2 xf.1 } }

instance : has_finite_products (Type v₁) :=
  has_finite_products_of_has_products _

instance : cartesian_closed (Type v₁) where
  closed := fun X => { isAdj := adjunction.left_adjoint_of_nat_iso (types.binary_product_iso_prod.app X) }

instance {C : Type u₁} [category.{v₁} C] : has_finite_products (C ⥤ Type u₁) :=
  has_finite_products_of_has_products _

instance {C : Type v₁} [small_category C] : cartesian_closed (C ⥤ Type v₁) where
  closed := fun F =>
    { isAdj := by
        let this' := functor_category.prod_preserves_colimits F
        apply is_left_adjoint_of_preserves_colimits (prod.functor.obj F) }

end CartesianClosed

end CategoryTheory

