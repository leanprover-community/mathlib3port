/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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

@[to_additive AddGroupₓₓ.hasZeroObject]
instance : HasZeroObject Groupₓₓ where
  zero := 1
  uniqueTo := fun X =>
    ⟨⟨1⟩, fun f => by
      ext
      cases x
      erw [MonoidHom.map_one]
      rfl⟩
  uniqueFrom := fun X =>
    ⟨⟨1⟩, fun f => by
      ext⟩

end Groupₓₓ

namespace CommGroupₓₓ

@[to_additive AddCommGroupₓₓ.hasZeroObject]
instance : HasZeroObject CommGroupₓₓ where
  zero := 1
  uniqueTo := fun X =>
    ⟨⟨1⟩, fun f => by
      ext
      cases x
      erw [MonoidHom.map_one]
      rfl⟩
  uniqueFrom := fun X =>
    ⟨⟨1⟩, fun f => by
      ext⟩

end CommGroupₓₓ

