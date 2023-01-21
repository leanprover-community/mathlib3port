/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module algebra.order.ring.cone
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Ring.Defs

/-!
# Constructing an ordered ring from a ring with a specified positive cone.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


/-! ### Positive cones -/


variable {α : Type _} [Ring α] [Nontrivial α]

namespace Ring

#print Ring.PositiveCone /-
/-- A positive cone in a ring consists of a positive cone in underlying `add_comm_group`,
which contains `1` and such that the positive elements are closed under multiplication. -/
@[nolint has_nonempty_instance]
structure PositiveCone (α : Type _) [Ring α] extends AddCommGroup.PositiveCone α where
  one_nonneg : nonneg 1
  mul_pos : ∀ a b, Pos a → Pos b → Pos (a * b)
#align ring.positive_cone Ring.PositiveCone
-/

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc positive_cone.to_positive_cone

#print Ring.TotalPositiveCone /-
/-- A total positive cone in a nontrivial ring induces a linear order. -/
@[nolint has_nonempty_instance]
structure TotalPositiveCone (α : Type _) [Ring α] extends PositiveCone α,
  AddCommGroup.TotalPositiveCone α
#align ring.total_positive_cone Ring.TotalPositiveCone
-/

/-- Forget that a `total_positive_cone` in a ring is total. -/
add_decl_doc total_positive_cone.to_positive_cone

/-- Forget that a `total_positive_cone` in a ring respects the multiplicative structure. -/
add_decl_doc total_positive_cone.to_total_positive_cone

/- warning: ring.positive_cone.one_pos -> Ring.PositiveCone.one_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : Nontrivial.{u1} α] (C : Ring.PositiveCone.{u1} α _inst_1), Ring.PositiveCone.Pos.{u1} α _inst_1 C (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : Nontrivial.{u1} α] (C : Ring.PositiveCone.{u1} α _inst_1), AddCommGroup.PositiveCone.pos.{u1} α (Ring.toAddCommGroup.{u1} α _inst_1) (Ring.PositiveCone.toPositiveCone.{u1} α _inst_1 C) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ring.positive_cone.one_pos Ring.PositiveCone.one_posₓ'. -/
theorem PositiveCone.one_pos (C : PositiveCone α) : C.Pos 1 :=
  (C.pos_iff _).2 ⟨C.one_nonneg, fun h => one_neZero <| C.nonneg_antisymm C.one_nonneg h⟩
#align ring.positive_cone.one_pos Ring.PositiveCone.one_pos

end Ring

open Ring

#print StrictOrderedRing.mkOfPositiveCone /-
/-- Construct a `strict_ordered_ring` by designating a positive cone in an existing `ring`. -/
def StrictOrderedRing.mkOfPositiveCone (C : PositiveCone α) : StrictOrderedRing α :=
  { ‹Ring α›,
    OrderedAddCommGroup.mkOfPositiveCone
      C.toPositiveCone with
    exists_pair_ne := ⟨0, 1, fun h => by simpa [← h, C.pos_iff] using C.one_pos⟩
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      convert
        C.mul_pos x y
          (by
            convert xp
            simp)
          (by
            convert yp
            simp)
      simp }
#align strict_ordered_ring.mk_of_positive_cone StrictOrderedRing.mkOfPositiveCone
-/

#print LinearOrderedRing.mkOfPositiveCone /-
/-- Construct a `linear_ordered_ring` by
designating a positive cone in an existing `ring`. -/
def LinearOrderedRing.mkOfPositiveCone (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { StrictOrderedRing.mkOfPositiveCone C.toPositiveCone,
    LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone with }
#align linear_ordered_ring.mk_of_positive_cone LinearOrderedRing.mkOfPositiveCone
-/

