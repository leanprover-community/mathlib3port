/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.field.opposite
! leanprover-community/mathlib commit acebd8d49928f6ed8920e502a6c90674e75bd441
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Field.Defs
import Mathbin.Algebra.Ring.Opposite
import Mathbin.Data.Int.Cast.Lemmas

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

/- warning: mul_opposite.op_rat_cast -> MulOpposite.op_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HasRatCast.{u1} α] (q : Rat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α _inst_1))) q)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Rat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Rat (MulOpposite.{u1} α) (Rat.castCoe.{u1} (MulOpposite.{u1} α) (MulOpposite.hasRatCast.{u1} α _inst_1)))) q)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RatCast.{u1} α] (q : Rat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (Rat.cast.{u1} α _inst_1 q)) (Rat.cast.{u1} (MulOpposite.{u1} α) (MulOpposite.ratCast.{u1} α _inst_1) q)
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_rat_cast MulOpposite.op_ratCastₓ'. -/
@[simp, norm_cast, to_additive]
theorem op_ratCast [HasRatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast

/- warning: mul_opposite.unop_rat_cast -> MulOpposite.unop_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HasRatCast.{u1} α] (q : Rat), Eq.{succ u1} α (MulOpposite.unop.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Rat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Rat (MulOpposite.{u1} α) (Rat.castCoe.{u1} (MulOpposite.{u1} α) (MulOpposite.hasRatCast.{u1} α _inst_1)))) q)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α _inst_1))) q)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RatCast.{u1} α] (q : Rat), Eq.{succ u1} α (MulOpposite.unop.{u1} α (Rat.cast.{u1} (MulOpposite.{u1} α) (MulOpposite.ratCast.{u1} α _inst_1) q)) (Rat.cast.{u1} α _inst_1 q)
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCastₓ'. -/
@[simp, norm_cast, to_additive]
theorem unop_ratCast [HasRatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q :=
  rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast

variable (α)

instance [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.semiring α with }

instance [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α,
    MulOpposite.ring α with
    ratCast := fun q => op q
    ratCast_mk := fun a b hb h =>
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
  { AddOpposite.groupWithZero α, AddOpposite.ring α with }

instance [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring α, AddOpposite.commSemiring α with }

instance [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing α, AddOpposite.commRing α with }

end AddOpposite

