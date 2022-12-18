/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.zero
! leanprover-community/mathlib commit dcf2250875895376a142faeeac5eabff32c48655
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.GroupCat.Basic
import Mathbin.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace GroupCat

@[to_additive]
theorem is_zero_of_subsingleton (G : GroupCat) [Subsingleton G] : IsZero G := by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
#align Group.is_zero_of_subsingleton GroupCat.is_zero_of_subsingleton

@[to_additive AddGroupCat.has_zero_object]
instance : HasZeroObject GroupCat :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

end GroupCat

namespace CommGroupCat

@[to_additive]
theorem is_zero_of_subsingleton (G : CommGroupCat) [Subsingleton G] : IsZero G := by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    apply Subsingleton.elim
#align CommGroup.is_zero_of_subsingleton CommGroupCat.is_zero_of_subsingleton

@[to_additive AddCommGroupCat.has_zero_object]
instance : HasZeroObject CommGroupCat :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩

end CommGroupCat

