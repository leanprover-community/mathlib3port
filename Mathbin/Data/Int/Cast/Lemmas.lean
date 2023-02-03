/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.int.cast.lemmas
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic
import Mathbin.Data.Nat.Cast.Basic

/-!
# Cast of integers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `data.int.cast.basic`.

## Main declarations

* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/


open Nat

variable {F ι α β : Type _}

namespace Int

/- warning: int.of_nat_hom -> Int.ofNatHom is a dubious translation:
lean 3 declaration is
  RingHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))
but is expected to have type
  RingHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))
Case conversion may be inaccurate. Consider using '#align int.of_nat_hom Int.ofNatHomₓ'. -/
/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def ofNatHom : ℕ →+* ℤ :=
  ⟨coe, rfl, Int.ofNat_mul, rfl, Int.ofNat_add⟩
#align int.of_nat_hom Int.ofNatHom

#print Int.coe_nat_pos /-
@[simp]
theorem coe_nat_pos {n : ℕ} : (0 : ℤ) < n ↔ 0 < n :=
  Nat.cast_pos
#align int.coe_nat_pos Int.coe_nat_pos
-/

#print Int.coe_nat_succ_pos /-
theorem coe_nat_succ_pos (n : ℕ) : 0 < (n.succ : ℤ) :=
  Int.coe_nat_pos.2 (succ_pos n)
#align int.coe_nat_succ_pos Int.coe_nat_succ_pos
-/

#print Int.toNat_lt' /-
theorem toNat_lt' {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.toNat < b ↔ a < b :=
  by
  rw [← to_nat_lt_to_nat, to_nat_coe_nat]
  exact coe_nat_pos.2 hb.bot_lt
#align int.to_nat_lt Int.toNat_lt'
-/

#print Int.natMod_lt /-
theorem natMod_lt {a : ℤ} {b : ℕ} (hb : b ≠ 0) : a.natMod b < b :=
  (toNat_lt' hb).2 <| emod_lt_of_pos _ <| coe_nat_pos.2 hb.bot_lt
#align int.nat_mod_lt Int.natMod_lt
-/

section cast

@[simp, norm_cast]
theorem cast_mul [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m =>
  Int.inductionOn' m 0 (by simp) (fun k _ ih n => by simp [add_mul, ih]) fun k _ ih n => by
    simp [sub_mul, ih]
#align int.cast_mul Int.cast_mulₓ

/- warning: int.cast_ite -> Int.cast_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (P : Prop) [_inst_2 : Decidable P] (m : Int) (n : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) (ite.{1} Int P _inst_2 m n)) (ite.{succ u1} α P _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (P : Prop) [_inst_2 : Decidable P] (m : Int) (n : Int), Eq.{succ u1} α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) (ite.{1} Int P _inst_2 m n)) (ite.{succ u1} α P _inst_2 (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) m) (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align int.cast_ite Int.cast_iteₓ'. -/
@[simp, norm_cast]
theorem cast_ite [AddGroupWithOne α] (P : Prop) [Decidable P] (m n : ℤ) :
    ((ite P m n : ℤ) : α) = ite P m n :=
  apply_ite _ _ _ _
#align int.cast_ite Int.cast_ite

/- warning: int.cast_add_hom -> Int.castAddHom is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : AddGroupWithOne.{u1} α], AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : AddGroupWithOne.{u1} α], AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align int.cast_add_hom Int.castAddHomₓ'. -/
/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def castAddHom (α : Type _) [AddGroupWithOne α] : ℤ →+ α :=
  ⟨coe, cast_zero, cast_add⟩
#align int.cast_add_hom Int.castAddHom

/- warning: int.coe_cast_add_hom -> Int.coe_castAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α], Eq.{succ u1} (Int -> α) (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) (fun (_x : AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) => Int -> α) (AddMonoidHom.hasCoeToFun.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) (Int.castAddHom.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α], Eq.{succ u1} (forall (ᾰ : Int), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) Int α (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))) Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1))) (AddMonoidHom.addMonoidHomClass.{0, u1} Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α _inst_1)))))) (Int.castAddHom.{u1} α _inst_1)) (fun (x : Int) => Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) x)
Case conversion may be inaccurate. Consider using '#align int.coe_cast_add_hom Int.coe_castAddHomₓ'. -/
@[simp]
theorem coe_castAddHom [AddGroupWithOne α] : ⇑(castAddHom α) = coe :=
  rfl
#align int.coe_cast_add_hom Int.coe_castAddHom

/- warning: int.cast_ring_hom -> Int.castRingHom is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : NonAssocRing.{u1} α], RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : NonAssocRing.{u1} α], RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align int.cast_ring_hom Int.castRingHomₓ'. -/
/-- `coe : ℤ → α` as a `ring_hom`. -/
def castRingHom (α : Type _) [NonAssocRing α] : ℤ →+* α :=
  ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩
#align int.cast_ring_hom Int.castRingHom

/- warning: int.coe_cast_ring_hom -> Int.coe_castRingHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α], Eq.{succ u1} (Int -> α) (coeFn.{succ u1, succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (fun (_x : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) => Int -> α) (RingHom.hasCoeToFun.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (Int.castRingHom.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α], Eq.{succ u1} (forall (ᾰ : Int), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) ᾰ) (FunLike.coe.{succ u1, 1, succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonUnitalNonAssocSemiring.toMul.{0} Int (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1) (RingHom.instRingHomClassRingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1))))) (Int.castRingHom.{u1} α _inst_1)) (fun (x : Int) => Int.cast.{u1} α (NonAssocRing.toIntCast.{u1} α _inst_1) x)
Case conversion may be inaccurate. Consider using '#align int.coe_cast_ring_hom Int.coe_castRingHomₓ'. -/
@[simp]
theorem coe_castRingHom [NonAssocRing α] : ⇑(castRingHom α) = coe :=
  rfl
#align int.coe_cast_ring_hom Int.coe_castRingHom

/- warning: int.cast_commute -> Int.cast_commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (m : Int) (x : α), Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) m) x
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (m : Int) (x : α), Commute.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1)) (Int.cast.{u1} α (NonAssocRing.toIntCast.{u1} α _inst_1) m) x
Case conversion may be inaccurate. Consider using '#align int.cast_commute Int.cast_commuteₓ'. -/
theorem cast_commute [NonAssocRing α] : ∀ (m : ℤ) (x : α), Commute (↑m) x
  | (n : ℕ), x => by simpa using n.cast_commute x
  | -[n+1], x => by
    simpa only [cast_neg_succ_of_nat, Commute.neg_left_iff, Commute.neg_right_iff] using
      (n + 1).cast_commute (-x)
#align int.cast_commute Int.cast_commute

/- warning: int.cast_comm -> Int.cast_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (m : Int) (x : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) m) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) x ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (m : Int) (x : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) (Int.cast.{u1} α (NonAssocRing.toIntCast.{u1} α _inst_1) m) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1))) x (Int.cast.{u1} α (NonAssocRing.toIntCast.{u1} α _inst_1) m))
Case conversion may be inaccurate. Consider using '#align int.cast_comm Int.cast_commₓ'. -/
theorem cast_comm [NonAssocRing α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
  (cast_commute m x).Eq
#align int.cast_comm Int.cast_comm

/- warning: int.commute_cast -> Int.commute_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (x : α) (m : Int), Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))) x ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α _inst_1))))) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (x : α) (m : Int), Commute.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_1)) x (Int.cast.{u1} α (NonAssocRing.toIntCast.{u1} α _inst_1) m)
Case conversion may be inaccurate. Consider using '#align int.commute_cast Int.commute_castₓ'. -/
theorem commute_cast [NonAssocRing α] (x : α) (m : ℤ) : Commute x m :=
  (m.cast_commute x).symm
#align int.commute_cast Int.commute_cast

/- warning: int.cast_mono -> Int.cast_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α], Monotone.{0, u1} Int α (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α], Monotone.{0, u1} Int α (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1)) (fun (x : Int) => Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) x)
Case conversion may be inaccurate. Consider using '#align int.cast_mono Int.cast_monoₓ'. -/
theorem cast_mono [OrderedRing α] : Monotone (coe : ℤ → α) :=
  by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to ℕ using h with k
  rw [← sub_nonneg, ← cast_sub, ← h_1, cast_coe_nat]
  exact k.cast_nonneg
#align int.cast_mono Int.cast_mono

/- warning: int.cast_nonneg -> Int.cast_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n)) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedRing.toOrderedSemiring.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n)) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) n)
Case conversion may be inaccurate. Consider using '#align int.cast_nonneg Int.cast_nonnegₓ'. -/
@[simp]
theorem cast_nonneg [OrderedRing α] [Nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    have : -(n : α) < 1 := lt_of_le_of_lt (by simp) zero_lt_one
    simpa [(neg_succ_lt_zero n).not_le, ← sub_eq_add_neg, le_neg] using this.not_le
#align int.cast_nonneg Int.cast_nonneg

/- warning: int.cast_le -> Int.cast_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {m : Int} {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n)) (LE.le.{0} Int Int.hasLe m n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {m : Int} {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) m) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n)) (LE.le.{0} Int Int.instLEInt m n)
Case conversion may be inaccurate. Consider using '#align int.cast_le Int.cast_leₓ'. -/
@[simp, norm_cast]
theorem cast_le [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]
#align int.cast_le Int.cast_le

/- warning: int.cast_strict_mono -> Int.cast_strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α], StrictMono.{0, u1} Int α (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α], StrictMono.{0, u1} Int α (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1)) (fun (x : Int) => Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) x)
Case conversion may be inaccurate. Consider using '#align int.cast_strict_mono Int.cast_strictMonoₓ'. -/
theorem cast_strictMono [OrderedRing α] [Nontrivial α] : StrictMono (coe : ℤ → α) :=
  strictMono_of_le_iff_le fun m n => cast_le.symm
#align int.cast_strict_mono Int.cast_strictMono

/- warning: int.cast_lt -> Int.cast_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {m : Int} {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n)) (LT.lt.{0} Int Int.hasLt m n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {m : Int} {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) m) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n)) (LT.lt.{0} Int Int.instLTInt m n)
Case conversion may be inaccurate. Consider using '#align int.cast_lt Int.cast_ltₓ'. -/
@[simp, norm_cast]
theorem cast_lt [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) < n ↔ m < n :=
  cast_strictMono.lt_iff_lt
#align int.cast_lt Int.cast_lt

/- warning: int.cast_nonpos -> Int.cast_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1)))))))))) (LE.le.{0} Int Int.hasLe n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedRing.toOrderedSemiring.{u1} α _inst_1))))))) (LE.le.{0} Int Int.instLEInt n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cast_nonpos Int.cast_nonposₓ'. -/
@[simp]
theorem cast_nonpos [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 := by
  rw [← cast_zero, cast_le]
#align int.cast_nonpos Int.cast_nonpos

/- warning: int.cast_pos -> Int.cast_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n)) (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedRing.toOrderedSemiring.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n)) (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) n)
Case conversion may be inaccurate. Consider using '#align int.cast_pos Int.cast_posₓ'. -/
@[simp]
theorem cast_pos [OrderedRing α] [Nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n := by
  rw [← cast_zero, cast_lt]
#align int.cast_pos Int.cast_pos

/- warning: int.cast_lt_zero -> Int.cast_lt_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (OrderedRing.toOrderedAddCommGroup.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1))))))) n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (OrderedRing.toRing.{u1} α _inst_1)))))))))) (LT.lt.{0} Int Int.hasLt n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Int}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedRing.toPartialOrder.{u1} α _inst_1))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (OrderedRing.toRing.{u1} α _inst_1)) n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedRing.toOrderedSemiring.{u1} α _inst_1))))))) (LT.lt.{0} Int Int.instLTInt n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.cast_lt_zero Int.cast_lt_zeroₓ'. -/
@[simp]
theorem cast_lt_zero [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 := by
  rw [← cast_zero, cast_lt]
#align int.cast_lt_zero Int.cast_lt_zero

section LinearOrderedRing

variable [LinearOrderedRing α] {a b : ℤ} (n : ℤ)

/- warning: int.cast_min -> Int.cast_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int} {b : Int}, Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) (LinearOrder.min.{0} Int Int.linearOrder a b)) (LinearOrder.min.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int} {b : Int}, Eq.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (Min.min.{0} Int Int.instMinInt a b)) (Min.min.{u1} α (LinearOrderedRing.toMin.{u1} α _inst_1) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) a) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align int.cast_min Int.cast_minₓ'. -/
@[simp, norm_cast]
theorem cast_min : (↑(min a b) : α) = min a b :=
  Monotone.map_min cast_mono
#align int.cast_min Int.cast_min

/- warning: int.cast_max -> Int.cast_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int} {b : Int}, Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) (LinearOrder.max.{0} Int Int.linearOrder a b)) (LinearOrder.max.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int} {b : Int}, Eq.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (Max.max.{0} Int Int.instMaxInt a b)) (Max.max.{u1} α (LinearOrderedRing.toMax.{u1} α _inst_1) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) a) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align int.cast_max Int.cast_maxₓ'. -/
@[simp, norm_cast]
theorem cast_max : (↑(max a b) : α) = max a b :=
  Monotone.map_max cast_mono
#align int.cast_max Int.cast_max

/- warning: int.cast_abs -> Int.cast_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.hasNeg (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (LinearOrder.toLattice.{0} Int Int.linearOrder)))) a)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, Eq.{succ u1} α (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.instNegInt (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (DistribLattice.toLattice.{0} Int (instDistribLattice.{0} Int Int.instLinearOrderInt))))) a)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) a))
Case conversion may be inaccurate. Consider using '#align int.cast_abs Int.cast_absₓ'. -/
@[simp, norm_cast]
theorem cast_abs : ((|a| : ℤ) : α) = |a| := by simp [abs_eq_max_neg]
#align int.cast_abs Int.cast_abs

/- warning: int.cast_one_le_of_pos -> Int.cast_one_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) a))
Case conversion may be inaccurate. Consider using '#align int.cast_one_le_of_pos Int.cast_one_le_of_posₓ'. -/
theorem cast_one_le_of_pos (h : 0 < a) : (1 : α) ≤ a := by exact_mod_cast Int.add_one_le_of_lt h
#align int.cast_one_le_of_pos Int.cast_one_le_of_pos

/- warning: int.cast_le_neg_one_of_neg -> Int.cast_le_neg_one_of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, (LT.lt.{0} Int Int.hasLt a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) a) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] {a : Int}, (LT.lt.{0} Int Int.instLTInt a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) a) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align int.cast_le_neg_one_of_neg Int.cast_le_neg_one_of_negₓ'. -/
theorem cast_le_neg_one_of_neg (h : a < 0) : (a : α) ≤ -1 :=
  by
  rw [← Int.cast_one, ← Int.cast_neg, cast_le]
  exact Int.le_sub_one_of_lt h
#align int.cast_le_neg_one_of_neg Int.cast_le_neg_one_of_neg

variable (α) {n}

/- warning: int.cast_le_neg_one_or_one_le_cast_of_ne_zero -> Int.cast_le_neg_one_or_one_le_cast_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : LinearOrderedRing.{u1} α] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Or (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : LinearOrderedRing.{u1} α] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Or (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) n) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) n)))
Case conversion may be inaccurate. Consider using '#align int.cast_le_neg_one_or_one_le_cast_of_ne_zero Int.cast_le_neg_one_or_one_le_cast_of_ne_zeroₓ'. -/
theorem cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n ≠ 0) : (n : α) ≤ -1 ∨ 1 ≤ (n : α) :=
  hn.lt_or_lt.imp cast_le_neg_one_of_neg cast_one_le_of_pos
#align int.cast_le_neg_one_or_one_le_cast_of_ne_zero Int.cast_le_neg_one_or_one_le_cast_of_ne_zero

variable {α} (n)

/- warning: int.nneg_mul_add_sq_of_abs_le_one -> Int.nneg_mul_add_sq_of_abs_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (n : Int) {x : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1))))) x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (n : Int) {x : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1)))))) x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedRing.toLinearOrderedSemiring.{u1} α _inst_1))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) n) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) n) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) n))))
Case conversion may be inaccurate. Consider using '#align int.nneg_mul_add_sq_of_abs_le_one Int.nneg_mul_add_sq_of_abs_le_oneₓ'. -/
theorem nneg_mul_add_sq_of_abs_le_one {x : α} (hx : |x| ≤ 1) : (0 : α) ≤ n * x + n * n :=
  by
  have hnx : 0 < n → 0 ≤ x + n := fun hn =>
    by
    convert add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rw [add_left_neg]
  have hnx' : n < 0 → x + n ≤ 0 := fun hn =>
    by
    convert add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rw [add_right_neg]
  rw [← mul_add, mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨by exact_mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨by exact_mod_cast h.le, hnx h⟩
#align int.nneg_mul_add_sq_of_abs_le_one Int.nneg_mul_add_sq_of_abs_le_one

/- warning: int.cast_nat_abs -> Int.cast_natAbs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (n : Int), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))) (Int.natAbs n)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (n : Int), Eq.{succ u1} α (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) (Int.natAbs n)) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.instNegInt (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (DistribLattice.toLattice.{0} Int (instDistribLattice.{0} Int Int.instLinearOrderInt))))) n))
Case conversion may be inaccurate. Consider using '#align int.cast_nat_abs Int.cast_natAbsₓ'. -/
theorem cast_natAbs : (n.natAbs : α) = |n| := by
  cases n
  · simp
  · simp only [Int.natAbs, Int.cast_negSucc, abs_neg, ← Nat.cast_succ, Nat.abs_cast]
#align int.cast_nat_abs Int.cast_natAbs

end LinearOrderedRing

/- warning: int.coe_int_dvd -> Int.coe_int_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (m : Int) (n : Int), (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) m n) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α _inst_1))))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] (m : Int) (n : Int), (Dvd.dvd.{0} Int Int.instDvdInt m n) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α _inst_1)))))) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (CommRing.toRing.{u1} α _inst_1)) m) (Int.cast.{u1} α (Ring.toIntCast.{u1} α (CommRing.toRing.{u1} α _inst_1)) n))
Case conversion may be inaccurate. Consider using '#align int.coe_int_dvd Int.coe_int_dvdₓ'. -/
theorem coe_int_dvd [CommRing α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Int.castRingHom α) h
#align int.coe_int_dvd Int.coe_int_dvd

end cast

end Int

open Int

namespace AddMonoidHom

variable {A : Type _}

/- warning: add_monoid_hom.ext_int -> AddMonoidHom.ext_int is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {f : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)} {g : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)}, (Eq.{succ u1} A (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (fun (_x : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) => Int -> A) (AddMonoidHom.hasCoeToFun.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) f (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (fun (_x : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) => Int -> A) (AddMonoidHom.hasCoeToFun.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) g (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) f g)
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {f : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)} {g : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)}, (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int A (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1) (AddMonoidHom.addMonoidHomClass.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)))) f (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int A (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1) (AddMonoidHom.addMonoidHomClass.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)))) g (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A _inst_1)) f g)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.ext_int AddMonoidHom.ext_intₓ'. -/
/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext]
theorem ext_int [AddMonoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat' _ _ h1
  have : ∀ n : ℕ, f n = g n := ext_iff.1 this
  ext fun n => Int.casesOn n this fun n => eq_on_neg _ _ (this <| n + 1)
#align add_monoid_hom.ext_int AddMonoidHom.ext_int

variable [AddGroupWithOne A]

/- warning: add_monoid_hom.eq_int_cast_hom -> AddMonoidHom.eq_int_castAddHom is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} A] (f : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))), (Eq.{succ u1} A (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) (fun (_x : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) => Int -> A) (AddMonoidHom.hasCoeToFun.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) f (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (OfNat.ofNat.{u1} A 1 (OfNat.mk.{u1} A 1 (One.one.{u1} A (AddMonoidWithOne.toOne.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) f (Int.castAddHom.{u1} A _inst_1))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} A] (f : AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))), (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) Int A (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1))) (AddMonoidHom.addMonoidHomClass.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))))) f (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (AddMonoidWithOne.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (AddGroupWithOne.toAddMonoidWithOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => A) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) _inst_1))))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Int A (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddGroupWithOne.toAddMonoidWithOne.{u1} A _inst_1)))) f (Int.castAddHom.{u1} A _inst_1))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.eq_int_cast_hom AddMonoidHom.eq_int_castAddHomₓ'. -/
theorem eq_int_castAddHom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by simp [h1]
#align add_monoid_hom.eq_int_cast_hom AddMonoidHom.eq_int_castAddHom

end AddMonoidHom

/- warning: eq_int_cast' -> eq_intCast' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddGroupWithOne.{u2} α] [_inst_2 : AddMonoidHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))] (f : F), (Eq.{succ u2} α (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (AddHomClass.toFunLike.{u1, 0, u2} F Int α (AddZeroClass.toHasAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (AddZeroClass.toHasAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1))) _inst_2))) f (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (AddMonoidWithOne.toOne.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))))) -> (forall (n : Int), Eq.{succ u2} α (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (AddHomClass.toFunLike.{u1, 0, u2} F Int α (AddZeroClass.toHasAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (AddZeroClass.toHasAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1))) _inst_2))) f n) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int α (HasLiftT.mk.{1, succ u2} Int α (CoeTCₓ.coe.{1, succ u2} Int α (Int.castCoe.{u2} α (AddGroupWithOne.toHasIntCast.{u2} α _inst_1)))) n))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddGroupWithOne.{u2} α] [_inst_2 : AddMonoidHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))] (f : F), (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) _x) (AddHomClass.toFunLike.{u1, 0, u2} F Int α (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1))) _inst_2)) f (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (AddMonoidWithOne.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (AddGroupWithOne.toAddMonoidWithOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) _inst_1))))) -> (forall (n : Int), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) n) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) _x) (AddHomClass.toFunLike.{u1, 0, u2} F Int α (AddZeroClass.toAdd.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (AddZeroClass.toAdd.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1)))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Int α (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{u2} α (AddMonoidWithOne.toAddMonoid.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α _inst_1))) _inst_2)) f n) (Int.cast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) n) (AddGroupWithOne.toIntCast.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Int) => α) n) _inst_1) n))
Case conversion may be inaccurate. Consider using '#align eq_int_cast' eq_intCast'ₓ'. -/
theorem eq_intCast' [AddGroupWithOne α] [AddMonoidHomClass F ℤ α] (f : F) (h₁ : f 1 = 1) :
    ∀ n : ℤ, f n = n :=
  AddMonoidHom.ext_iff.1 <| (f : ℤ →+ α).eq_int_castAddHom h₁
#align eq_int_cast' eq_intCast'

/- warning: int.cast_add_hom_int -> Int.castAddHom_int is a dubious translation:
lean 3 declaration is
  Eq.{1} (AddMonoidHom.{0, 0} Int Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid) (AddMonoid.toAddZeroClass.{0} Int (AddMonoidWithOne.toAddMonoid.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))))) (Int.castAddHom.{0} Int (NonAssocRing.toAddGroupWithOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (AddMonoidHom.id.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid))
but is expected to have type
  Eq.{1} (AddMonoidHom.{0, 0} Int Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt) (AddMonoid.toAddZeroClass.{0} Int (AddMonoidWithOne.toAddMonoid.{0} Int (AddGroupWithOne.toAddMonoidWithOne.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt))))) (Int.castAddHom.{0} Int (Ring.toAddGroupWithOne.{0} Int Int.instRingInt)) (AddMonoidHom.id.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt))
Case conversion may be inaccurate. Consider using '#align int.cast_add_hom_int Int.castAddHom_intₓ'. -/
@[simp]
theorem Int.castAddHom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_int_castAddHom rfl).symm
#align int.cast_add_hom_int Int.castAddHom_int

namespace MonoidHom

variable {M : Type _} [Monoid M]

open Multiplicative

/- warning: monoid_hom.ext_mint -> MonoidHom.ext_mint is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {f : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)} {g : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)}, (Eq.{succ u1} M (coeFn.{succ u1, succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) (fun (_x : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) => (Multiplicative.{0} Int) -> M) (MonoidHom.hasCoeToFun.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) f (coeFn.{1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) (fun (_x : Equiv.{1, 1} Int (Multiplicative.{0} Int)) => Int -> (Multiplicative.{0} Int)) (Equiv.hasCoeToFun.{1, 1} Int (Multiplicative.{0} Int)) (Multiplicative.ofAdd.{0} Int) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (coeFn.{succ u1, succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) (fun (_x : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) => (Multiplicative.{0} Int) -> M) (MonoidHom.hasCoeToFun.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) g (coeFn.{1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) (fun (_x : Equiv.{1, 1} Int (Multiplicative.{0} Int)) => Int -> (Multiplicative.{0} Int)) (Equiv.hasCoeToFun.{1, 1} Int (Multiplicative.{0} Int)) (Multiplicative.ofAdd.{0} Int) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) -> (Eq.{succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.addMonoid)) (Monoid.toMulOneClass.{u1} M _inst_1)) f g)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {f : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)} {g : MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)}, (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{0} Int) => M) (FunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (fun (a : Int) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Int) => Multiplicative.{0} Int) a) (Equiv.instFunLikeEquiv.{1, 1} Int (Multiplicative.{0} Int)) (Multiplicative.ofAdd.{0} Int) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) (fun (_x : Multiplicative.{0} Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{0} Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) M (MulOneClass.toMul.{0} (Multiplicative.{0} Int) (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt))) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1) (MonoidHom.monoidHomClass.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)))) f (FunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Int) => Multiplicative.{0} Int) _x) (Equiv.instFunLikeEquiv.{1, 1} Int (Multiplicative.{0} Int)) (Multiplicative.ofAdd.{0} Int) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) (fun (_x : Multiplicative.{0} Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{0} Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) M (MulOneClass.toMul.{0} (Multiplicative.{0} Int) (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt))) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1) (MonoidHom.monoidHomClass.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)))) g (FunLike.coe.{1, 1, 1} (Equiv.{1, 1} Int (Multiplicative.{0} Int)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Int) => Multiplicative.{0} Int) _x) (Equiv.instFunLikeEquiv.{1, 1} Int (Multiplicative.{0} Int)) (Multiplicative.ofAdd.{0} Int) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) -> (Eq.{succ u1} (MonoidHom.{0, u1} (Multiplicative.{0} Int) M (Multiplicative.mulOneClass.{0} Int (AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoidInt)) (Monoid.toMulOneClass.{u1} M _inst_1)) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.ext_mint MonoidHom.ext_mintₓ'. -/
@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.ext <| AddMonoidHom.ext_iff.mp <| @AddMonoidHom.ext_int _ _ f.toAdditive g.toAdditive h1
#align monoid_hom.ext_mint MonoidHom.ext_mint

/- warning: monoid_hom.ext_int -> MonoidHom.ext_int is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {f : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)} {g : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)}, (Eq.{succ u1} M (coeFn.{succ u1, succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) (fun (_x : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) => Int -> M) (MonoidHom.hasCoeToFun.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) f (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (coeFn.{succ u1, succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) (fun (_x : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) => Int -> M) (MonoidHom.hasCoeToFun.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) g (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) -> (Eq.{succ u1} (MonoidHom.{0, u1} Nat M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHom.comp.{0, 0, u1} Nat Int M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1) f (RingHom.toMonoidHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) Int.ofNatHom)) (MonoidHom.comp.{0, 0, u1} Nat Int M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1) g (RingHom.toMonoidHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) Int.ofNatHom))) -> (Eq.{succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (Monoid.toMulOneClass.{u1} M _inst_1)) f g)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {f : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)} {g : MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)}, (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int M (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1) (MonoidHom.monoidHomClass.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)))) f (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int M (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1) (MonoidHom.monoidHomClass.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)))) g (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) -> (Eq.{succ u1} (MonoidHom.{0, u1} Nat M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (Monoid.toMulOneClass.{u1} M _inst_1)) (MonoidHom.comp.{0, 0, u1} Nat Int M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1) f (RingHom.toMonoidHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.ofNatHom)) (MonoidHom.comp.{0, 0, u1} Nat Int M (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1) g (RingHom.toMonoidHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.ofNatHom))) -> (Eq.{succ u1} (MonoidHom.{0, u1} Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (Monoid.toMulOneClass.{u1} M _inst_1)) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.ext_int MonoidHom.ext_intₓ'. -/
/-- If two `monoid_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g :=
  by
  ext (x | x)
  · exact (MonoidHom.congr_fun h_nat x : _)
  · rw [Int.negSucc_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact_mod_cast (MonoidHom.congr_fun h_nat (x + 1) : _)
#align monoid_hom.ext_int MonoidHom.ext_int

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type _} [MonoidWithZero M]

/- warning: monoid_with_zero_hom.ext_int -> MonoidWithZeroHom.ext_int is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M] {f : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)} {g : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)}, (Eq.{succ u1} M (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (fun (_x : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) => Int -> M) (MonoidWithZeroHom.hasCoeToFun.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) f (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (fun (_x : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) => Int -> M) (MonoidWithZeroHom.hasCoeToFun.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) g (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Nat M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (MonoidWithZeroHom.comp.{0, 0, u1} Nat Int M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) f (RingHom.toMonoidWithZeroHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) Int.ofNatHom)) (MonoidWithZeroHom.comp.{0, 0, u1} Nat Int M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) g (RingHom.toMonoidWithZeroHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) Int.ofNatHom))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) f g)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M] {f : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)} {g : MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)}, (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1))))) f (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => M) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1))))) g (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Nat M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) (MonoidWithZeroHom.comp.{0, 0, u1} Nat Int M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) f (RingHom.toMonoidWithZeroHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.ofNatHom)) (MonoidWithZeroHom.comp.{0, 0, u1} Nat Int M (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1) g (RingHom.toMonoidWithZeroHom.{0, 0} Nat Int (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) Int.ofNatHom))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Int M (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u1} M _inst_1)) f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_int MonoidWithZeroHom.ext_intₓ'. -/
/-- If two `monoid_with_zero_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) :
    f = g :=
  toMonoidHom_injective <| MonoidHom.ext_int h_neg_one <| MonoidHom.ext (congr_fun h_nat : _)
#align monoid_with_zero_hom.ext_int MonoidWithZeroHom.ext_int

end MonoidWithZeroHom

/- warning: ext_int' -> ext_int' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} α] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)] {f : F} {g : F}, (Eq.{succ u2} α (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toHasMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (MulOneClass.toHasMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2)))) f (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))) (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toHasMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (MulOneClass.toHasMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2)))) g (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))) -> (forall (n : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u2} α (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toHasMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (MulOneClass.toHasMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2)))) f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toHasMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (MulOneClass.toHasMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2)))) g ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) -> (Eq.{succ u1} F f g)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} α] [_inst_2 : MonoidWithZeroHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)] {f : F} {g : F}, (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2))) f (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2))) g (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))) -> (forall (n : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) (Nat.cast.{0} Int Int.instNatCastInt n)) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2))) f (Nat.cast.{0} Int Int.instNatCastInt n)) (FunLike.coe.{succ u1, 1, succ u2} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))))) (MulOneClass.toMul.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, 0, u2} F Int α (MulZeroOneClass.toMulOneClass.{0} Int (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (MulZeroOneClass.toMulOneClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toMulZeroOneClass.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (MonoidWithZero.toMulZeroOneClass.{u2} α _inst_1) _inst_2))) g (Nat.cast.{0} Int Int.instNatCastInt n)))) -> (Eq.{succ u1} F f g)
Case conversion may be inaccurate. Consider using '#align ext_int' ext_int'ₓ'. -/
/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
theorem ext_int' [MonoidWithZero α] [MonoidWithZeroHomClass F ℤ α] {f g : F}
    (h_neg_one : f (-1) = g (-1)) (h_pos : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  FunLike.ext _ _ fun n =>
    haveI :=
      FunLike.congr_fun
        (@MonoidWithZeroHom.ext_int _ _ (f : ℤ →*₀ α) (g : ℤ →*₀ α) h_neg_one <|
          MonoidWithZeroHom.ext_nat h_pos)
        n
    this
#align ext_int' ext_int'

section NonAssocRing

variable [NonAssocRing α] [NonAssocRing β]

/- warning: eq_int_cast -> eq_intCast is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonAssocRing.{u2} α] [_inst_3 : RingHomClass.{u1, 0, u2} F Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)] (f : F) (n : Int), Eq.{succ u2} α (coeFn.{succ u1, succ u2} F (fun (_x : F) => Int -> α) (FunLike.hasCoeToFun.{succ u1, 1, succ u2} F Int (fun (_x : Int) => α) (MulHomClass.toFunLike.{u1, 0, u2} F Int α (Distrib.toHasMul.{0} Int (NonUnitalNonAssocSemiring.toDistrib.{0} Int (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))))) (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u2} F Int α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u2} F Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1) _inst_3)))) f n) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int α (HasLiftT.mk.{1, succ u2} Int α (CoeTCₓ.coe.{1, succ u2} Int α (Int.castCoe.{u2} α (AddGroupWithOne.toHasIntCast.{u2} α (NonAssocRing.toAddGroupWithOne.{u2} α _inst_1))))) n)
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] [_inst_3 : RingHomClass.{u2, 0, u1} F Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)] (f : F) (n : Int), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) n) (FunLike.coe.{succ u2, 1, succ u1} F Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) _x) (MulHomClass.toFunLike.{u2, 0, u1} F Int α (NonUnitalNonAssocSemiring.toMul.{0} Int (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1))) (NonUnitalRingHomClass.toMulHomClass.{u2, 0, u1} F Int α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) (RingHomClass.toNonUnitalRingHomClass.{u2, 0, u1} F Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1) _inst_3))) f n) (Int.cast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) n) (NonAssocRing.toIntCast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Int) => α) n) _inst_1) n)
Case conversion may be inaccurate. Consider using '#align eq_int_cast eq_intCastₓ'. -/
@[simp]
theorem eq_intCast [RingHomClass F ℤ α] (f : F) (n : ℤ) : f n = n :=
  eq_intCast' f (map_one _) n
#align eq_int_cast eq_intCast

/- warning: map_int_cast -> map_intCast is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : NonAssocRing.{u2} α] [_inst_2 : NonAssocRing.{u3} β] [_inst_3 : RingHomClass.{u1, u2, u3} F α β (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1) (NonAssocRing.toNonAssocSemiring.{u3} β _inst_2)] (f : F) (n : Int), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)))) (Distrib.toHasMul.{u3} β (NonUnitalNonAssocSemiring.toDistrib.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (NonAssocRing.toNonAssocSemiring.{u3} β _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u2, u3} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (NonAssocRing.toNonAssocSemiring.{u3} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{u1, u2, u3} F α β (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1) (NonAssocRing.toNonAssocSemiring.{u3} β _inst_2) _inst_3)))) f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int α (HasLiftT.mk.{1, succ u2} Int α (CoeTCₓ.coe.{1, succ u2} Int α (Int.castCoe.{u2} α (AddGroupWithOne.toHasIntCast.{u2} α (NonAssocRing.toAddGroupWithOne.{u2} α _inst_1))))) n)) ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Int β (HasLiftT.mk.{1, succ u3} Int β (CoeTCₓ.coe.{1, succ u3} Int β (Int.castCoe.{u3} β (AddGroupWithOne.toHasIntCast.{u3} β (NonAssocRing.toAddGroupWithOne.{u3} β _inst_2))))) n)
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NonAssocRing.{u2} α] [_inst_2 : NonAssocRing.{u1} β] [_inst_3 : RingHomClass.{u3, u2, u1} F α β (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1) (NonAssocRing.toNonAssocSemiring.{u1} β _inst_2)] (f : F) (n : Int), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (Int.cast.{u2} α (NonAssocRing.toIntCast.{u2} α _inst_1) n)) (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonAssocSemiring.{u1} β _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{u3, u2, u1} F α β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonAssocSemiring.{u1} β _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{u3, u2, u1} F α β (NonAssocRing.toNonAssocSemiring.{u2} α _inst_1) (NonAssocRing.toNonAssocSemiring.{u1} β _inst_2) _inst_3))) f (Int.cast.{u2} α (NonAssocRing.toIntCast.{u2} α _inst_1) n)) (Int.cast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (Int.cast.{u2} α (NonAssocRing.toIntCast.{u2} α _inst_1) n)) (NonAssocRing.toIntCast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (Int.cast.{u2} α (NonAssocRing.toIntCast.{u2} α _inst_1) n)) _inst_2) n)
Case conversion may be inaccurate. Consider using '#align map_int_cast map_intCastₓ'. -/
@[simp]
theorem map_intCast [RingHomClass F α β] (f : F) (n : ℤ) : f n = n :=
  eq_intCast ((f : α →+* β).comp (Int.castRingHom α)) n
#align map_int_cast map_intCast

namespace RingHom

/- warning: ring_hom.eq_int_cast' -> RingHom.eq_intCast' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (f : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)), Eq.{succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) f (Int.castRingHom.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocRing.{u1} α] (f : RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)), Eq.{succ u1} (RingHom.{0, u1} Int α (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{u1} α _inst_1)) f (Int.castRingHom.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align ring_hom.eq_int_cast' RingHom.eq_intCast'ₓ'. -/
theorem eq_intCast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext <| eq_intCast f
#align ring_hom.eq_int_cast' RingHom.eq_intCast'

/- warning: ring_hom.ext_int -> RingHom.ext_int is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_3 : NonAssocSemiring.{u1} R] (f : RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) _inst_3) (g : RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) _inst_3), Eq.{succ u1} (RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) _inst_3) f g
but is expected to have type
  forall {R : Type.{u1}} [_inst_3 : NonAssocSemiring.{u1} R] (f : RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) _inst_3) (g : RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) _inst_3), Eq.{succ u1} (RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) _inst_3) f g
Case conversion may be inaccurate. Consider using '#align ring_hom.ext_int RingHom.ext_intₓ'. -/
theorem ext_int {R : Type _} [NonAssocSemiring R] (f g : ℤ →+* R) : f = g :=
  coe_addMonoidHom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm
#align ring_hom.ext_int RingHom.ext_int

/- warning: ring_hom.int.subsingleton_ring_hom -> RingHom.Int.subsingleton_ringHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_3 : NonAssocSemiring.{u1} R], Subsingleton.{succ u1} (RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} [_inst_3 : NonAssocSemiring.{u1} R], Subsingleton.{succ u1} (RingHom.{0, u1} Int R (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) _inst_3)
Case conversion may be inaccurate. Consider using '#align ring_hom.int.subsingleton_ring_hom RingHom.Int.subsingleton_ringHomₓ'. -/
instance Int.subsingleton_ringHom {R : Type _} [NonAssocSemiring R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩
#align ring_hom.int.subsingleton_ring_hom RingHom.Int.subsingleton_ringHom

end RingHom

end NonAssocRing

@[simp, norm_cast]
theorem Int.cast_id (n : ℤ) : ↑n = n :=
  (eq_intCast (RingHom.id ℤ) _).symm
#align int.cast_id Int.cast_idₓ

/- warning: int.cast_ring_hom_int -> Int.castRingHom_int is a dubious translation:
lean 3 declaration is
  Eq.{1} (RingHom.{0, 0} Int Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring))) (Int.castRingHom.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)) (RingHom.id.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))
but is expected to have type
  Eq.{1} (RingHom.{0, 0} Int Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt))) (Int.castRingHom.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) (RingHom.id.{0} Int (NonAssocRing.toNonAssocSemiring.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))
Case conversion may be inaccurate. Consider using '#align int.cast_ring_hom_int Int.castRingHom_intₓ'. -/
@[simp]
theorem Int.castRingHom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_intCast'.symm
#align int.cast_ring_hom_int Int.castRingHom_int

namespace Pi

variable {π : ι → Type _} [∀ i, IntCast (π i)]

instance : IntCast (∀ i, π i) := by refine_struct { .. } <;> pi_instance_derive_field

#print Pi.int_apply /-
theorem int_apply (n : ℤ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl
#align pi.int_apply Pi.int_apply
-/

/- warning: pi.coe_int -> Pi.coe_int is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : forall (i : ι), IntCast.{u2} (π i)] (n : Int), Eq.{max (succ u1) (succ u2)} (forall (i : ι), π i) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (forall (i : ι), π i) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (forall (i : ι), π i) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (forall (i : ι), π i) (Int.castCoe.{max u1 u2} (forall (i : ι), π i) (Pi.hasIntCast.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i))))) n) (fun (_x : ι) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int (π _x) (HasLiftT.mk.{1, succ u2} Int (π _x) (CoeTCₓ.coe.{1, succ u2} Int (π _x) (Int.castCoe.{u2} (π _x) (_inst_1 _x)))) n)
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : forall (i : ι), IntCast.{u1} (π i)] (n : Int), Eq.{max (succ u2) (succ u1)} (forall (i : ι), π i) (Int.cast.{max u2 u1} (forall (i : ι), π i) (Pi.intCast.{u2, u1} ι (fun (i : ι) => π i) (fun (i : ι) => _inst_1 i)) n) (fun (_x : ι) => Int.cast.{u1} (π _x) (_inst_1 _x) n)
Case conversion may be inaccurate. Consider using '#align pi.coe_int Pi.coe_intₓ'. -/
@[simp]
theorem coe_int (n : ℤ) : (n : ∀ i, π i) = fun _ => n :=
  rfl
#align pi.coe_int Pi.coe_int

end Pi

/- warning: sum.elim_int_cast_int_cast -> Sum.elim_intCast_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : IntCast.{u3} γ] (n : Int), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ ((fun (a : Type) (b : Sort.{max (succ u1) (succ u3)}) [self : HasLiftT.{1, max (succ u1) (succ u3)} a b] => self.0) Int (α -> γ) (HasLiftT.mk.{1, max (succ u1) (succ u3)} Int (α -> γ) (CoeTCₓ.coe.{1, max (succ u1) (succ u3)} Int (α -> γ) (Int.castCoe.{max u1 u3} (α -> γ) (Pi.hasIntCast.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))))) n) ((fun (a : Type) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{1, max (succ u2) (succ u3)} a b] => self.0) Int (β -> γ) (HasLiftT.mk.{1, max (succ u2) (succ u3)} Int (β -> γ) (CoeTCₓ.coe.{1, max (succ u2) (succ u3)} Int (β -> γ) (Int.castCoe.{max u2 u3} (β -> γ) (Pi.hasIntCast.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))))) n)) ((fun (a : Type) (b : Sort.{max (max (succ u1) (succ u2)) (succ u3)}) [self : HasLiftT.{1, max (max (succ u1) (succ u2)) (succ u3)} a b] => self.0) Int ((Sum.{u1, u2} α β) -> γ) (HasLiftT.mk.{1, max (max (succ u1) (succ u2)) (succ u3)} Int ((Sum.{u1, u2} α β) -> γ) (CoeTCₓ.coe.{1, max (max (succ u1) (succ u2)) (succ u3)} Int ((Sum.{u1, u2} α β) -> γ) (Int.castCoe.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.hasIntCast.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (i : Sum.{u1, u2} α β) => _inst_1))))) n)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : IntCast.{u1} γ] (n : Int), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Sum.elim.{u3, u2, succ u1} α β γ (Int.cast.{max u3 u1} (α -> γ) (Pi.intCast.{u3, u1} α (fun (a._@.Mathlib.Data.Int.Cast.Lemmas._hyg.2986 : α) => γ) (fun (i : α) => _inst_1)) n) (Int.cast.{max u2 u1} (β -> γ) (Pi.intCast.{u2, u1} β (fun (a._@.Mathlib.Data.Int.Cast.Lemmas._hyg.2992 : β) => γ) (fun (i : β) => _inst_1)) n)) (Int.cast.{max (max u3 u2) u1} ((Sum.{u3, u2} α β) -> γ) (Pi.intCast.{max u3 u2, u1} (Sum.{u3, u2} α β) (fun (a._@.Mathlib.Data.Sum.Basic._hyg.1871 : Sum.{u3, u2} α β) => γ) (fun (i : Sum.{u3, u2} α β) => _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align sum.elim_int_cast_int_cast Sum.elim_intCast_intCastₓ'. -/
theorem Sum.elim_intCast_intCast {α β γ : Type _} [IntCast γ] (n : ℤ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n
#align sum.elim_int_cast_int_cast Sum.elim_intCast_intCast

namespace Pi

variable {π : ι → Type _} [∀ i, AddGroupWithOne (π i)]

instance : AddGroupWithOne (∀ i, π i) := by refine_struct { .. } <;> pi_instance_derive_field

end Pi

namespace MulOpposite

variable [AddGroupWithOne α]

/- warning: mul_opposite.op_int_cast -> MulOpposite.op_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (z : Int), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) z)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Int (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Int (MulOpposite.{u1} α) (Int.castCoe.{u1} (MulOpposite.{u1} α) (AddGroupWithOne.toHasIntCast.{u1} (MulOpposite.{u1} α) (MulOpposite.addGroupWithOne.{u1} α _inst_1))))) z)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (z : Int), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) z)) (Int.cast.{u1} (MulOpposite.{u1} α) (AddGroupWithOne.toIntCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instAddGroupWithOneMulOpposite.{u1} α _inst_1)) z)
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_int_cast MulOpposite.op_intCastₓ'. -/
@[simp, norm_cast]
theorem op_intCast (z : ℤ) : op (z : α) = z :=
  rfl
#align mul_opposite.op_int_cast MulOpposite.op_intCast

/- warning: mul_opposite.unop_int_cast -> MulOpposite.unop_intCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (n : Int), Eq.{succ u1} α (MulOpposite.unop.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Int (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Int (MulOpposite.{u1} α) (Int.castCoe.{u1} (MulOpposite.{u1} α) (AddGroupWithOne.toHasIntCast.{u1} (MulOpposite.{u1} α) (MulOpposite.addGroupWithOne.{u1} α _inst_1))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int α (HasLiftT.mk.{1, succ u1} Int α (CoeTCₓ.coe.{1, succ u1} Int α (Int.castCoe.{u1} α (AddGroupWithOne.toHasIntCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} α] (n : Int), Eq.{succ u1} α (MulOpposite.unop.{u1} α (Int.cast.{u1} (MulOpposite.{u1} α) (AddGroupWithOne.toIntCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instAddGroupWithOneMulOpposite.{u1} α _inst_1)) n)) (Int.cast.{u1} α (AddGroupWithOne.toIntCast.{u1} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_int_cast MulOpposite.unop_intCastₓ'. -/
@[simp, norm_cast]
theorem unop_intCast (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_int_cast MulOpposite.unop_intCast

end MulOpposite

/-! ### Order dual -/


open OrderDual

instance [h : IntCast α] : IntCast αᵒᵈ :=
  h

instance [h : AddGroupWithOne α] : AddGroupWithOne αᵒᵈ :=
  h

instance [h : AddCommGroupWithOne α] : AddCommGroupWithOne αᵒᵈ :=
  h

#print toDual_intCast /-
@[simp]
theorem toDual_intCast [IntCast α] (n : ℤ) : toDual (n : α) = n :=
  rfl
#align to_dual_int_cast toDual_intCast
-/

#print ofDual_intCast /-
@[simp]
theorem ofDual_intCast [IntCast α] (n : ℤ) : (ofDual n : α) = n :=
  rfl
#align of_dual_int_cast ofDual_intCast
-/

/-! ### Lexicographic order -/


instance [h : IntCast α] : IntCast (Lex α) :=
  h

instance [h : AddGroupWithOne α] : AddGroupWithOne (Lex α) :=
  h

instance [h : AddCommGroupWithOne α] : AddCommGroupWithOne (Lex α) :=
  h

#print toLex_intCast /-
@[simp]
theorem toLex_intCast [IntCast α] (n : ℤ) : toLex (n : α) = n :=
  rfl
#align to_lex_int_cast toLex_intCast
-/

#print ofLex_intCast /-
@[simp]
theorem ofLex_intCast [IntCast α] (n : ℤ) : (ofLex n : α) = n :=
  rfl
#align of_lex_int_cast ofLex_intCast
-/

