/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.int.char_zero
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Cast.Field

/-!
# Injectivity of `int.cast` into characteristic zero rings and fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

open Nat

namespace Int

/- warning: int.cast_eq_zero -> Int.cast_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {n : Int}, Iff (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))))))) (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {n : Int}, Iff (Eq.{succ u1} α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α _inst_1)))))))) (Eq.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cast_eq_zero Int.cast_eq_zeroₓ'. -/
@[simp]
theorem cast_eq_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
  ⟨fun h => by
    cases n
    · rw [Int.cast_ofNat] at h
      exact congr_arg coe (Nat.cast_eq_zero.1 h)
    · rw [cast_neg_succ_of_nat, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction, fun h => by rw [h, cast_zero]⟩
#align int.cast_eq_zero Int.cast_eq_zero

/- warning: int.cast_inj -> Int.cast_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {m : Int} {n : Int}, Iff (Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n)) (Eq.{1} Int m n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {m : Int} {n : Int}, Iff (Eq.{succ u1} α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) m) (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) n)) (Eq.{1} Int m n)
Case conversion may be inaccurate. Consider using '#align int.cast_inj Int.cast_injₓ'. -/
@[simp, norm_cast]
theorem cast_inj [AddGroupWithOne α] [CharZero α] {m n : ℤ} : (m : α) = n ↔ m = n := by
  rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]
#align int.cast_inj Int.cast_inj

/- warning: int.cast_injective -> Int.cast_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)], Function.Injective.{1, succ u1} Int α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)], Function.Injective.{1, succ u1} Int α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align int.cast_injective Int.cast_injectiveₓ'. -/
theorem cast_injective [AddGroupWithOne α] [CharZero α] : Function.Injective (coe : ℤ → α)
  | m, n => cast_inj.1
#align int.cast_injective Int.cast_injective

/- warning: int.cast_ne_zero -> Int.cast_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {n : Int}, Iff (Ne.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))))))) (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)] {n : Int}, Iff (Ne.{succ u1} α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α _inst_1)))))))) (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cast_ne_zero Int.cast_ne_zeroₓ'. -/
theorem cast_ne_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align int.cast_ne_zero Int.cast_ne_zero

/- warning: int.cast_div_char_zero -> Int.cast_div_charZero is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} [_inst_1 : Field.{u1} k] [_inst_2 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))] {m : Int} {n : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n m) -> (Eq.{succ u1} k ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int k (HasLiftT.mk.{1, succ u1} Int k (CoeTCₓ.coe.{1, succ u1} Int k (Int.castCoe.{u1} k (AddGroupWithOne.toHasIntCast.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) m n)) (HDiv.hDiv.{u1, u1, u1} k k k (instHDiv.{u1} k (DivInvMonoid.toHasDiv.{u1} k (DivisionRing.toDivInvMonoid.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int k (HasLiftT.mk.{1, succ u1} Int k (CoeTCₓ.coe.{1, succ u1} Int k (Int.castCoe.{u1} k (AddGroupWithOne.toHasIntCast.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int k (HasLiftT.mk.{1, succ u1} Int k (CoeTCₓ.coe.{1, succ u1} Int k (Int.castCoe.{u1} k (AddGroupWithOne.toHasIntCast.{u1} k (NonAssocRing.toAddGroupWithOne.{u1} k (Ring.toNonAssocRing.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1)))))))) n)))
but is expected to have type
  forall {k : Type.{u1}} [_inst_1 : Field.{u1} k] [_inst_2 : CharZero.{u1} k (AddGroupWithOne.toAddMonoidWithOne.{u1} k (Ring.toAddGroupWithOne.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))))] {m : Int} {n : Int}, (Dvd.dvd.{0} Int Int.instDvdInt n m) -> (Eq.{succ u1} k (Int.cast.{u1} k (Ring.toIntCast.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) m n)) (HDiv.hDiv.{u1, u1, u1} k k k (instHDiv.{u1} k (Field.toDiv.{u1} k _inst_1)) (Int.cast.{u1} k (Ring.toIntCast.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) m) (Int.cast.{u1} k (Ring.toIntCast.{u1} k (DivisionRing.toRing.{u1} k (Field.toDivisionRing.{u1} k _inst_1))) n)))
Case conversion may be inaccurate. Consider using '#align int.cast_div_char_zero Int.cast_div_charZeroₓ'. -/
@[simp, norm_cast]
theorem cast_div_charZero {k : Type _} [Field k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) :
    ((m / n : ℤ) : k) = m / n :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.div_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)
#align int.cast_div_char_zero Int.cast_div_charZero

end Int

/- warning: ring_hom.injective_int -> RingHom.injective_int is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (f : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))], Function.Injective.{1, succ u1} Int α (coeFn.{succ u1, succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (fun (_x : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) => Int -> α) (RingHom.hasCoeToFun.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (f : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) [_inst_2 : CharZero.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))], Function.Injective.{1, succ u1} Int α (FunLike.coe.{succ u1, 1, succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonUnitalNonAssocSemiring.toMul.{0} Int (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1) (RingHom.instRingHomClassRingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1))))) f)
Case conversion may be inaccurate. Consider using '#align ring_hom.injective_int RingHom.injective_intₓ'. -/
theorem RingHom.injective_int {α : Type _} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective
#align ring_hom.injective_int RingHom.injective_int

