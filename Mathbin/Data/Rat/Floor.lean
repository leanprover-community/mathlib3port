/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann

! This file was ported from Lean 3 source module data.rat.floor
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Floor
import Mathbin.Algebra.EuclideanDomain.Instances
import Mathbin.Tactic.FieldSimp

/-!
# Floor Function for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`. Some technical lemmas relating
`floor` to integer division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/


open Int

namespace Rat

variable {α : Type _} [LinearOrderedField α] [FloorRing α]

#print Rat.floor /-
/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ
  | ⟨n, d, h, c⟩ => n / d
#align rat.floor Rat.floor
-/

/- warning: rat.le_floor -> Rat.le_floor is a dubious translation:
lean 3 declaration is
  forall {z : Int} {r : Rat}, Iff (LE.le.{0} Int Int.hasLe z (Rat.floor r)) (LE.le.{0} Rat Rat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) z) r)
but is expected to have type
  forall {z : Int} {r : Rat}, Iff (LE.le.{0} Int Int.instLEInt z (Rat.floor r)) (LE.le.{0} Rat Rat.instLERat (Int.cast.{0} Rat Rat.instIntCastRat z) r)
Case conversion may be inaccurate. Consider using '#align rat.le_floor Rat.le_floorₓ'. -/
protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ Rat.floor r ↔ (z : ℚ) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp [Rat.floor]
    rw [num_denom']
    have h' := Int.ofNat_lt.2 h
    conv =>
      rhs
      rw [coe_int_eq_mk, Rat.le_def zero_lt_one h', mul_one]
    exact Int.le_ediv_iff_mul_le h'
#align rat.le_floor Rat.le_floor

instance : FloorRing ℚ :=
  FloorRing.ofFloor ℚ Rat.floor fun a z => Rat.le_floor.symm

/- warning: rat.floor_def -> Rat.floor_def is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, Eq.{1} Int (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing q) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) (Rat.num q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)))
but is expected to have type
  forall {q : Rat}, Eq.{1} Int (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat q) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) (Rat.num q) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)))
Case conversion may be inaccurate. Consider using '#align rat.floor_def Rat.floor_defₓ'. -/
protected theorem floor_def {q : ℚ} : ⌊q⌋ = q.num / q.den :=
  by
  cases q
  rfl
#align rat.floor_def Rat.floor_def

/- warning: rat.floor_int_div_nat_eq_div -> Rat.floor_int_div_nat_eq_div is a dubious translation:
lean 3 declaration is
  forall {n : Int} {d : Nat}, Eq.{1} Int (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) d))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d))
but is expected to have type
  forall {n : Int} {d : Nat}, Eq.{1} Int (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Int.cast.{0} Rat Rat.instIntCastRat n) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) d))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) n (Nat.cast.{0} Int Int.instNatCastInt d))
Case conversion may be inaccurate. Consider using '#align rat.floor_int_div_nat_eq_div Rat.floor_int_div_nat_eq_divₓ'. -/
theorem floor_int_div_nat_eq_div {n : ℤ} {d : ℕ} : ⌊(↑n : ℚ) / (↑d : ℚ)⌋ = n / (↑d : ℤ) :=
  by
  rw [Rat.floor_def]
  obtain rfl | hd := @eq_zero_or_pos _ _ d
  · simp
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.denom :=
    by
    rw [q_eq]
    exact_mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (by exact_mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine' (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left _ <| Int.coe_nat_nonneg q.denom).symm
  rwa [← d_eq_c_mul_denom, Int.coe_nat_pos]
#align rat.floor_int_div_nat_eq_div Rat.floor_int_div_nat_eq_div

/- warning: rat.floor_cast -> Rat.floor_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (Int.floor.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) x)) (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (Int.floor.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 (RatCast.ratCast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) x)) (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat x)
Case conversion may be inaccurate. Consider using '#align rat.floor_cast Rat.floor_castₓ'. -/
@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (by exact_mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))
#align rat.floor_cast Rat.floor_cast

/- warning: rat.ceil_cast -> Rat.ceil_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (Int.ceil.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) x)) (Int.ceil.{0} Rat Rat.linearOrderedRing Rat.floorRing x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (Int.ceil.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 (RatCast.ratCast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) x)) (Int.ceil.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat x)
Case conversion may be inaccurate. Consider using '#align rat.ceil_cast Rat.ceil_castₓ'. -/
@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]
#align rat.ceil_cast Rat.ceil_cast

/- warning: rat.round_cast -> Rat.round_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (round.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) x)) (round.{0} Rat Rat.linearOrderedRing Rat.floorRing x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{1} Int (round.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 (RatCast.ratCast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) x)) (round.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat x)
Case conversion may be inaccurate. Consider using '#align rat.round_cast Rat.round_castₓ'. -/
@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x :=
  by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]
#align rat.round_cast Rat.round_cast

/- warning: rat.cast_fract -> Rat.cast_fract is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) (Int.fract.{0} Rat Rat.linearOrderedRing Rat.floorRing x)) (Int.fract.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat α (HasLiftT.mk.{1, succ u1} Rat α (CoeTCₓ.coe.{1, succ u1} Rat α (Rat.castCoe.{u1} α (DivisionRing.toHasRatCast.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : FloorRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))] (x : Rat), Eq.{succ u1} α (RatCast.ratCast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) (Int.fract.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat x)) (Int.fract.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)) _inst_2 (RatCast.ratCast.{u1} α (LinearOrderedField.toRatCast.{u1} α _inst_1) x))
Case conversion may be inaccurate. Consider using '#align rat.cast_fract Rat.cast_fractₓ'. -/
@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract x := by
  simp only [fract, cast_sub, cast_coe_int, floor_cast]
#align rat.cast_fract Rat.cast_fract

end Rat

/- warning: int.mod_nat_eq_sub_mul_floor_rat_div -> Int.mod_nat_eq_sub_mul_floor_rat_div is a dubious translation:
lean 3 declaration is
  forall {n : Int} {d : Nat}, Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.hasMod) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d)) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) n (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d) (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) d)))))
but is expected to have type
  forall {n : Int} {d : Nat}, Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.instModInt_1) n (Nat.cast.{0} Int Int.instNatCastInt d)) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) n (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Nat.cast.{0} Int Int.instNatCastInt d) (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Int.cast.{0} Rat Rat.instIntCastRat n) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) d)))))
Case conversion may be inaccurate. Consider using '#align int.mod_nat_eq_sub_mul_floor_rat_div Int.mod_nat_eq_sub_mul_floor_rat_divₓ'. -/
theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [eq_sub_of_add_eq <| Int.emod_add_ediv n d, Rat.floor_int_div_nat_eq_div]
#align int.mod_nat_eq_sub_mul_floor_rat_div Int.mod_nat_eq_sub_mul_floor_rat_div

/- warning: nat.coprime_sub_mul_floor_rat_div_of_coprime -> Nat.coprime_sub_mul_floor_rat_div_of_coprime is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {d : Nat}, (Nat.coprime n d) -> (Nat.coprime (Int.natAbs (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) d) (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) d)))))) d)
but is expected to have type
  forall {n : Nat} {d : Nat}, (Nat.coprime n d) -> (Nat.coprime (Int.natAbs (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (Nat.cast.{0} Int Int.instNatCastInt n) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Nat.cast.{0} Int Int.instNatCastInt d) (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) n) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.instLinearOrderedRingRat)))) d)))))) d)
Case conversion may be inaccurate. Consider using '#align nat.coprime_sub_mul_floor_rat_div_of_coprime Nat.coprime_sub_mul_floor_rat_div_of_coprimeₓ'. -/
theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.coprime d :=
  by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.coprime n := n_coprime_d.symm
  rwa [Nat.coprime, Nat.gcd_rec] at this
#align nat.coprime_sub_mul_floor_rat_div_of_coprime Nat.coprime_sub_mul_floor_rat_div_of_coprime

namespace Rat

/- warning: rat.num_lt_succ_floor_mul_denom -> Rat.num_lt_succ_floor_mul_den is a dubious translation:
lean 3 declaration is
  forall (q : Rat), LT.lt.{0} Int Int.hasLt (Rat.num q) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (Int.floor.{0} Rat Rat.linearOrderedRing Rat.floorRing q) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)))
but is expected to have type
  forall (q : Rat), LT.lt.{0} Int Int.instLTInt (Rat.num q) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (Int.floor.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat q) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)))
Case conversion may be inaccurate. Consider using '#align rat.num_lt_succ_floor_mul_denom Rat.num_lt_succ_floor_mul_denₓ'. -/
theorem num_lt_succ_floor_mul_den (q : ℚ) : q.num < (⌊q⌋ + 1) * q.den :=
  by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.denom by exact_mod_cast this
  suffices (q.num : ℚ) < (q - fract q + 1) * q.denom
    by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.denom
    by
    have : (q - fract q + 1) * q.denom = q.num + (1 - fract q) * q.denom
    calc
      (q - fract q + 1) * q.denom = (q + (1 - fract q)) * q.denom := by ring
      _ = q * q.denom + (1 - fract q) * q.denom := by rw [add_mul]
      _ = q.num + (1 - fract q) * q.denom := by simp
      
    rwa [this]
  suffices 0 < (1 - fract q) * q.denom
    by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact_mod_cast q.pos)
#align rat.num_lt_succ_floor_mul_denom Rat.num_lt_succ_floor_mul_den

/- warning: rat.fract_inv_num_lt_num_of_pos -> Rat.fract_inv_num_lt_num_of_pos is a dubious translation:
lean 3 declaration is
  forall {q : Rat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) -> (LT.lt.{0} Int Int.hasLt (Rat.num (Int.fract.{0} Rat Rat.linearOrderedRing Rat.floorRing (Inv.inv.{0} Rat Rat.hasInv q))) (Rat.num q))
but is expected to have type
  forall {q : Rat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) -> (LT.lt.{0} Int Int.instLTInt (Rat.num (Int.fract.{0} Rat Rat.instLinearOrderedRingRat Rat.instFloorRingRatInstLinearOrderedRingRat (Inv.inv.{0} Rat Rat.instInvRat q))) (Rat.num q))
Case conversion may be inaccurate. Consider using '#align rat.fract_inv_num_lt_num_of_pos Rat.fract_inv_num_lt_num_of_posₓ'. -/
theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num :=
  by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := rat.num_pos_iff_pos.elim_right q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.nat_abs : ℤ) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_inv := (q.denom : ℚ) / q.num with q_inv_def
  have q_inv_eq : q⁻¹ = q_inv := Rat.inv_def''
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  suffices ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num by
    field_simp [this, ne_of_gt q_num_pos]
  suffices (q.denom : ℤ) - q.num * ⌊q_inv⌋ < q.num
    by
    -- use that `q.num` and `q.denom` are coprime to show that the numerator stays unreduced
    have : ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.denom - q.num * ⌊q_inv⌋ :=
      by
      suffices ((q.denom : ℤ) - q.num * ⌊q_inv⌋).natAbs.coprime q.num.nat_abs by
        exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.cop.symm
      simpa only [Nat.cast_natAbs, abs_of_nonneg q_num_pos.le] using tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.den < q⁻¹.den :=
    by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.den := Rat.num_lt_succ_floor_mul_den q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.den + q⁻¹.den := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.denom` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.denom ∧ q_inv.denom = q.num.nat_abs :=
    by
    have coprime_q_denom_q_num : q.denom.coprime q.num.nat_abs := q.cop.symm
    have : Int.natAbs q.denom = q.denom := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.denom : ℚ) / q.num).den : ℤ) = q.num.nat_abs by exact_mod_cast this
      rw [q_num_abs_eq_q_num]
      exact_mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq
#align rat.fract_inv_num_lt_num_of_pos Rat.fract_inv_num_lt_num_of_pos

end Rat

