import Mathbin.Algebra.Category.Group.Basic
import Mathbin.CategoryTheory.Limits.Shapes.Zero

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace Groupₓₓ

-- failed to format: format: uncaught backtrack exception
@[ to_additive AddGroupₓₓ.hasZeroObject ]
  instance
    : has_zero_object Groupₓₓ
    where
      zero := 1
        uniqueTo X := ⟨ ⟨ 1 ⟩ , fun f => by ext cases x erw [ MonoidHom.map_one ] rfl ⟩
        uniqueFrom X := ⟨ ⟨ 1 ⟩ , fun f => by ext ⟩

end Groupₓₓ

namespace CommGroupₓₓ

-- failed to format: format: uncaught backtrack exception
@[ to_additive AddCommGroupₓₓ.hasZeroObject ]
  instance
    : has_zero_object CommGroupₓₓ
    where
      zero := 1
        uniqueTo X := ⟨ ⟨ 1 ⟩ , fun f => by ext cases x erw [ MonoidHom.map_one ] rfl ⟩
        uniqueFrom X := ⟨ ⟨ 1 ⟩ , fun f => by ext ⟩

end CommGroupₓₓ

