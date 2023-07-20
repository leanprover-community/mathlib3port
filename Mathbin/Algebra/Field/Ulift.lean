/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.Ring.Ulift

#align_import algebra.field.ulift from "leanprover-community/mathlib"@"932872382355f00112641d305ba0619305dc8642"

/-!
# Field instances for `ulift`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for field, semifield and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance [HasRatCast α] : HasRatCast (ULift α) :=
  ⟨fun a => up a⟩

#print ULift.up_ratCast /-
@[simp, norm_cast]
theorem up_ratCast [HasRatCast α] (q : ℚ) : up (q : α) = q :=
  rfl
#align ulift.up_rat_cast ULift.up_ratCast
-/

#print ULift.down_ratCast /-
@[simp, norm_cast]
theorem down_ratCast [HasRatCast α] (q : ℚ) : down (q : ULift α) = q :=
  rfl
#align ulift.down_rat_cast ULift.down_ratCast
-/

#print ULift.divisionSemiring /-
instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) := by
  refine' down_injective.division_semiring down _ _ _ _ _ _ _ _ _ _ <;> intros <;> rfl
#align ulift.division_semiring ULift.divisionSemiring
-/

#print ULift.semifield /-
instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }
#align ulift.semifield ULift.semifield
-/

#print ULift.divisionRing /-
instance divisionRing [DivisionRing α] : DivisionRing (ULift α) :=
  { ULift.divisionSemiring, ULift.addGroup with }
#align ulift.division_ring ULift.divisionRing
-/

#print ULift.field /-
instance field [Field α] : Field (ULift α) :=
  { ULift.semifield, ULift.divisionRing with }
#align ulift.field ULift.field
-/

end ULift

