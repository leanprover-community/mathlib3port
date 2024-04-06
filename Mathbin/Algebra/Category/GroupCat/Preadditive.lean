/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Algebra.Category.GroupCat.Basic
import CategoryTheory.Preadditive.Basic

#align_import algebra.category.Group.preadditive from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# The category of additive commutative groups is preadditive.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open CategoryTheory

universe u

namespace AddCommGroupCat

instance : Preadditive AddCommGroupCat
    where
  add_comp P Q R f f' g := show (f + f') ≫ g = f ≫ g + f' ≫ g by ext; simp
  comp_add P Q R f g g' := show f ≫ (g + g') = f ≫ g + f ≫ g' by ext; simp

end AddCommGroupCat

