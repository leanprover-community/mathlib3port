/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.preadditive
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.GroupCat.Basic
import Mathbin.CategoryTheory.Preadditive.Basic

/-!
# The category of additive commutative groups is preadditive.
-/


open CategoryTheory

universe u

namespace AddCommGroupCat

instance : Preadditive AddCommGroupCat
    where
  add_comp' P Q R f f' g :=
    show (f + f') ≫ g = f ≫ g + f' ≫ g by
      ext
      simp
  comp_add' P Q R f g g' :=
    show f ≫ (g + g') = f ≫ g + f ≫ g' by
      ext
      simp

end AddCommGroupCat

