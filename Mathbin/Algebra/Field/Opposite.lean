/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Algebra.Field.Defs
import Algebra.Ring.Opposite
import Data.Int.Cast.Lemmas

#align_import algebra.field.opposite from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Field structure on the multiplicative/additive opposite

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable (α : Type _)

namespace MulOpposite

@[to_additive]
instance [HasRatCast α] : HasRatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

variable {α}

#print MulOpposite.op_ratCast /-
@[simp, norm_cast, to_additive]
theorem op_ratCast [HasRatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast
-/

#print MulOpposite.unop_ratCast /-
@[simp, norm_cast, to_additive]
theorem unop_ratCast [HasRatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q :=
  rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast
-/

variable (α)

instance [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.semiring α with }

instance [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α,
    MulOpposite.ring α with
    ratCast := fun q => op q
    ratCast_def := fun a b hb h =>
      by
      rw [Rat.cast_def, op_div, op_nat_cast, op_int_cast]
      exact Int.commute_cast _ _ }

instance [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.commSemiring α with }

instance [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.divisionRing α, MulOpposite.commRing α with }

end MulOpposite

namespace AddOpposite

instance [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.semiring α with }

instance [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.ring α, AddOpposite.groupWithZero α, AddOpposite.hasRatCast α with
    ratCast_def := fun a b hb h => by
      rw [← div_eq_mul_inv] <;> exact congr_arg op (Rat.cast_def _) }

instance [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring α, AddOpposite.commSemiring α with }

instance [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing α, AddOpposite.commRing α with }

end AddOpposite

