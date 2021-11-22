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

@[toAdditive AddGroupₓₓ.hasZeroObject]
instance  : has_zero_object Groupₓₓ :=
  { zero := 1,
    uniqueTo :=
      fun X =>
        ⟨⟨1⟩,
          fun f =>
            by 
              ext 
              cases x 
              erw [MonoidHom.map_one]
              rfl⟩,
    uniqueFrom :=
      fun X =>
        ⟨⟨1⟩,
          fun f =>
            by 
              ext⟩ }

end Groupₓₓ

namespace CommGroupₓₓ

@[toAdditive AddCommGroupₓₓ.hasZeroObject]
instance  : has_zero_object CommGroupₓₓ :=
  { zero := 1,
    uniqueTo :=
      fun X =>
        ⟨⟨1⟩,
          fun f =>
            by 
              ext 
              cases x 
              erw [MonoidHom.map_one]
              rfl⟩,
    uniqueFrom :=
      fun X =>
        ⟨⟨1⟩,
          fun f =>
            by 
              ext⟩ }

end CommGroupₓₓ

