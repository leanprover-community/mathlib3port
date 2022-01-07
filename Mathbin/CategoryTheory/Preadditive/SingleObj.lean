import Mathbin.CategoryTheory.Preadditive.Default
import Mathbin.CategoryTheory.SingleObj

/-!
# `single_obj α` is preadditive when `α` is a ring.

-/


namespace CategoryTheory

variable {α : Type _} [Ringₓ α]

instance : preadditive (single_obj α) where
  add_comp' := fun _ _ _ f f' g => mul_addₓ g f f'
  comp_add' := fun _ _ _ f g g' => add_mulₓ g g' f

end CategoryTheory

