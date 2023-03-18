/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.field.ulift
! leanprover-community/mathlib commit 13e18cfa070ea337ea960176414f5ae3a1534aae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.Ring.Ulift

/-!
# Field instances for `ulift`

This file defines instances for field, semifield and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)
-/


universe u v

variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance [HasRatCast α] : HasRatCast (ULift α) :=
  ⟨fun a => up a⟩

/- warning: ulift.up_rat_cast -> ULift.up_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HasRatCast.{u1} α] (q : Rat), Eq.{succ (max u1 u2)} (ULift.{u2, u1} α) (ULift.up.{u2, u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α _inst_1))) q)) ((fun (a : Type) (b : Type.{max u1 u2}) [self : HasLiftT.{1, succ (max u1 u2)} a b] => self.0) Rat (ULift.{u2, u1} α) (HasLiftT.mk.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (CoeTCₓ.coe.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (Rat.castCoe.{max u1 u2} (ULift.{u2, u1} α) (ULift.hasRatCast.{u1, u2} α _inst_1)))) q)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : RatCast.{u2} α] (q : Rat), Eq.{max (succ u2) (succ u1)} (ULift.{u1, u2} α) (ULift.up.{u1, u2} α (Rat.cast.{u2} α _inst_1 q)) (Rat.cast.{max u2 u1} (ULift.{u1, u2} α) (ULift.instRatCastULift.{u2, u1} α _inst_1) q)
Case conversion may be inaccurate. Consider using '#align ulift.up_rat_cast ULift.up_ratCastₓ'. -/
@[simp, norm_cast]
theorem up_ratCast [HasRatCast α] (q : ℚ) : up (q : α) = q :=
  rfl
#align ulift.up_rat_cast ULift.up_ratCast

/- warning: ulift.down_rat_cast -> ULift.down_ratCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : HasRatCast.{u1} α] (q : Rat), Eq.{succ u1} α (ULift.down.{u2, u1} α ((fun (a : Type) (b : Type.{max u1 u2}) [self : HasLiftT.{1, succ (max u1 u2)} a b] => self.0) Rat (ULift.{u2, u1} α) (HasLiftT.mk.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (CoeTCₓ.coe.{1, succ (max u1 u2)} Rat (ULift.{u2, u1} α) (Rat.castCoe.{max u1 u2} (ULift.{u2, u1} α) (ULift.hasRatCast.{u1, u2} α _inst_1)))) q)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α _inst_1))) q)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : RatCast.{u2} α] (q : Rat), Eq.{succ u2} α (ULift.down.{u1, u2} α (Rat.cast.{max u2 u1} (ULift.{u1, u2} α) (ULift.instRatCastULift.{u2, u1} α _inst_1) q)) (Rat.cast.{u2} α _inst_1 q)
Case conversion may be inaccurate. Consider using '#align ulift.down_rat_cast ULift.down_ratCastₓ'. -/
@[simp, norm_cast]
theorem down_ratCast [HasRatCast α] (q : ℚ) : down (q : ULift α) = q :=
  rfl
#align ulift.down_rat_cast ULift.down_ratCast

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

