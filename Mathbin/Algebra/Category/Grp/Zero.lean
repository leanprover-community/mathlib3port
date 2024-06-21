/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Category.Grp.Basic
import CategoryTheory.Limits.Shapes.ZeroObjects

#align_import algebra.category.Group.zero from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# The category of (commutative) (additive) groups has a zero object.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

namespace Grp

#print Grp.isZero_of_subsingleton /-
@[to_additive]
theorem isZero_of_subsingleton (G : Grp) [Subsingleton G] : IsZero G :=
  by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext; have : x = 1 := Subsingleton.elim _ _; rw [this, map_one, map_one]
  · ext; apply Subsingleton.elim
#align Group.is_zero_of_subsingleton Grp.isZero_of_subsingleton
#align AddGroup.is_zero_of_subsingleton AddGrp.isZero_of_subsingleton
-/

@[to_additive AddGrp.hasZeroObject]
instance : HasZeroObject Grp :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end Grp

namespace CommGrp

#print CommGrp.isZero_of_subsingleton /-
@[to_additive]
theorem isZero_of_subsingleton (G : CommGrp) [Subsingleton G] : IsZero G :=
  by
  refine' ⟨fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => _⟩⟩⟩
  · ext; have : x = 1 := Subsingleton.elim _ _; rw [this, map_one, map_one]
  · ext; apply Subsingleton.elim
#align CommGroup.is_zero_of_subsingleton CommGrp.isZero_of_subsingleton
#align AddCommGroup.is_zero_of_subsingleton AddCommGrp.isZero_of_subsingleton
-/

@[to_additive AddCommGrp.hasZeroObject]
instance : HasZeroObject CommGrp :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

end CommGrp

