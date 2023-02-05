/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.basic
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Algebra.GroupWithZero.Commute
import Mathbin.Algebra.Hom.Ring
import Mathbin.Algebra.Order.Group.Abs
import Mathbin.Algebra.Ring.Commute
import Mathbin.Data.Nat.Order.Basic
import Mathbin.Algebra.Group.Opposite

/-!
# Cast of natural numbers (additional theorems)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves additional properties about the *canonical* homomorphism from
the natural numbers into an additive monoid with a one (`nat.cast`).

## Main declarations

* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/


variable {α β : Type _}

namespace Nat

#print Nat.castAddMonoidHom /-
/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def castAddMonoidHom (α : Type _) [AddMonoidWithOne α] : ℕ →+ α
    where
  toFun := coe
  map_add' := cast_add
  map_zero' := cast_zero
#align nat.cast_add_monoid_hom Nat.castAddMonoidHom
-/

/- warning: nat.coe_cast_add_monoid_hom -> Nat.coe_castAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α], Eq.{succ u1} ((fun (_x : AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) => Nat -> α) (Nat.castAddMonoidHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (fun (_x : AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) => Nat -> α) (AddMonoidHom.hasCoeToFun.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (Nat.castAddMonoidHom.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α], Eq.{succ u1} (forall (a : Nat), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => α) a) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => α) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) Nat α (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))) Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1)) (AddMonoidHom.addMonoidHomClass.{0, u1} Nat α (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α _inst_1))))) (Nat.castAddMonoidHom.{u1} α _inst_1)) (Nat.cast.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align nat.coe_cast_add_monoid_hom Nat.coe_castAddMonoidHomₓ'. -/
@[simp]
theorem coe_castAddMonoidHom [AddMonoidWithOne α] : (castAddMonoidHom α : ℕ → α) = coe :=
  rfl
#align nat.coe_cast_add_monoid_hom Nat.coe_castAddMonoidHom

/- warning: nat.cast_mul -> Nat.cast_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (m : Nat) (n : Nat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (m : Nat) (n : Nat), Eq.{succ u1} α (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) m) (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_mul Nat.cast_mulₓ'. -/
@[simp, norm_cast]
theorem cast_mul [NonAssocSemiring α] (m n : ℕ) : ((m * n : ℕ) : α) = m * n := by
  induction n <;> simp [mul_succ, mul_add, *]
#align nat.cast_mul Nat.cast_mul

#print Nat.castRingHom /-
/-- `coe : ℕ → α` as a `ring_hom` -/
def castRingHom (α : Type _) [NonAssocSemiring α] : ℕ →+* α :=
  { castAddMonoidHom α with
    toFun := coe
    map_one' := cast_one
    map_mul' := cast_mul }
#align nat.cast_ring_hom Nat.castRingHom
-/

/- warning: nat.coe_cast_ring_hom -> Nat.coe_castRingHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α], Eq.{succ u1} ((fun (_x : RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) => Nat -> α) (Nat.castRingHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) (fun (_x : RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) => Nat -> α) (RingHom.hasCoeToFun.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) (Nat.castRingHom.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α], Eq.{succ u1} (forall (a : Nat), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Nat) => α) a) (FunLike.coe.{succ u1, 1, succ u1} (RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Nat) => α) _x) (MulHomClass.toFunLike.{u1, 0, u1} (RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat α (NonUnitalNonAssocSemiring.toMul.{0} Nat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (NonUnitalRingHomClass.toMulHomClass.{u1, 0, u1} (RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1) (RingHomClass.toNonUnitalRingHomClass.{u1, 0, u1} (RingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1) Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1 (RingHom.instRingHomClassRingHom.{0, u1} Nat α (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring) _inst_1)))) (Nat.castRingHom.{u1} α _inst_1)) (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align nat.coe_cast_ring_hom Nat.coe_castRingHomₓ'. -/
@[simp]
theorem coe_castRingHom [NonAssocSemiring α] : (castRingHom α : ℕ → α) = coe :=
  rfl
#align nat.coe_cast_ring_hom Nat.coe_castRingHom

/- warning: nat.cast_commute -> Nat.cast_commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (n : Nat) (x : α), Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) n) x
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (n : Nat) (x : α), Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) n) x
Case conversion may be inaccurate. Consider using '#align nat.cast_commute Nat.cast_commuteₓ'. -/
theorem cast_commute [NonAssocSemiring α] (n : ℕ) (x : α) : Commute (↑n) x :=
  Nat.recOn n (by rw [cast_zero] <;> exact Commute.zero_left x) fun n ihn => by
    rw [cast_succ] <;> exact ihn.add_left (Commute.one_left x)
#align nat.cast_commute Nat.cast_commute

/- warning: nat.cast_comm -> Nat.cast_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (n : Nat) (x : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) n) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)))) x ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (n : Nat) (x : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) n) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) x (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_comm Nat.cast_commₓ'. -/
theorem cast_comm [NonAssocSemiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
  (cast_commute n x).Eq
#align nat.cast_comm Nat.cast_comm

/- warning: nat.commute_cast -> Nat.commute_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (x : α) (n : Nat), Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1))) x ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α _inst_1)))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} α] (x : α) (n : Nat), Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α _inst_1)) x (Nat.cast.{u1} α (NonAssocSemiring.toNatCast.{u1} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align nat.commute_cast Nat.commute_castₓ'. -/
theorem commute_cast [NonAssocSemiring α] (x : α) (n : ℕ) : Commute x n :=
  (n.cast_commute x).symm
#align nat.commute_cast Nat.commute_cast

section OrderedSemiring

variable [OrderedSemiring α]

#print Nat.mono_cast /-
@[mono]
theorem mono_cast : Monotone (coe : ℕ → α) :=
  monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succ] <;> exact le_add_of_nonneg_right zero_le_one
#align nat.mono_cast Nat.mono_cast
-/

/- warning: nat.cast_nonneg -> Nat.cast_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align nat.cast_nonneg Nat.cast_nonnegₓ'. -/
@[simp]
theorem cast_nonneg (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)
#align nat.cast_nonneg Nat.cast_nonneg

section Nontrivial

variable [Nontrivial α]

/- warning: nat.cast_add_one_pos -> Nat.cast_add_one_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] (n : Nat), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) n) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] (n : Nat), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)) n) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align nat.cast_add_one_pos Nat.cast_add_one_posₓ'. -/
theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  zero_lt_one.trans_le <| le_add_of_nonneg_left n.cast_nonneg
#align nat.cast_add_one_pos Nat.cast_add_one_pos

/- warning: nat.cast_pos -> Nat.cast_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Nat}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)))))))) n)) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α] {n : Nat}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1)) n)) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)
Case conversion may be inaccurate. Consider using '#align nat.cast_pos Nat.cast_posₓ'. -/
@[simp]
theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]
#align nat.cast_pos Nat.cast_pos

end Nontrivial

variable [CharZero α] {m n : ℕ}

#print Nat.StrictMono_cast /-
theorem StrictMono_cast : StrictMono (coe : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective
#align nat.strict_mono_cast Nat.StrictMono_cast
-/

#print Nat.castOrderEmbedding /-
/-- `coe : ℕ → α` as an `order_embedding` -/
@[simps (config := { fullyApplied := false })]
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono coe Nat.StrictMono_cast
#align nat.cast_order_embedding Nat.castOrderEmbedding
-/

#print Nat.cast_le /-
@[simp, norm_cast]
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  StrictMono_cast.le_iff_le
#align nat.cast_le Nat.cast_le
-/

#print Nat.cast_lt /-
@[simp, norm_cast, mono]
theorem cast_lt : (m : α) < n ↔ m < n :=
  StrictMono_cast.lt_iff_lt
#align nat.cast_lt Nat.cast_lt
-/

#print Nat.one_lt_cast /-
@[simp, norm_cast]
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]
#align nat.one_lt_cast Nat.one_lt_cast
-/

#print Nat.one_le_cast /-
@[simp, norm_cast]
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
#align nat.one_le_cast Nat.one_le_cast
-/

#print Nat.cast_lt_one /-
@[simp, norm_cast]
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, lt_succ_iff, ← bot_eq_zero, le_bot_iff]
#align nat.cast_lt_one Nat.cast_lt_one
-/

#print Nat.cast_le_one /-
@[simp, norm_cast]
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
#align nat.cast_le_one Nat.cast_le_one
-/

end OrderedSemiring

/- warning: nat.cast_tsub -> Nat.cast_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))))) _inst_2] [_inst_4 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))] (m : Nat) (n : Nat), Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))))) m) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))))) _inst_2] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Data.Nat.Cast.Basic._hyg.920 : α) (x._@.Mathlib.Data.Nat.Cast.Basic._hyg.922 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1)))))))) x._@.Mathlib.Data.Nat.Cast.Basic._hyg.920 x._@.Mathlib.Data.Nat.Cast.Basic._hyg.922) (fun (x._@.Mathlib.Data.Nat.Cast.Basic._hyg.935 : α) (x._@.Mathlib.Data.Nat.Cast.Basic._hyg.937 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} α _inst_1))))) x._@.Mathlib.Data.Nat.Cast.Basic._hyg.935 x._@.Mathlib.Data.Nat.Cast.Basic._hyg.937)] (m : Nat) (n : Nat), Eq.{succ u1} α (Nat.cast.{u1} α (CanonicallyOrderedCommSemiring.toNatCast.{u1} α _inst_1) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) m n)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) (Nat.cast.{u1} α (CanonicallyOrderedCommSemiring.toNatCast.{u1} α _inst_1) m) (Nat.cast.{u1} α (CanonicallyOrderedCommSemiring.toNatCast.{u1} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align nat.cast_tsub Nat.cast_tsubₓ'. -/
/-- A version of `nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) :=
  by
  cases' le_total m n with h h
  · rw [tsub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
#align nat.cast_tsub Nat.cast_tsub

/- warning: nat.cast_min -> Nat.cast_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : Nat} {b : Nat}, Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (LinearOrder.min.{0} Nat Nat.linearOrder a b)) (LinearOrder.min.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : Nat} {b : Nat}, Eq.{succ u1} α (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) (Min.min.{0} Nat instMinNat a b)) (Min.min.{u1} α (LinearOrderedSemiring.toMin.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) a) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align nat.cast_min Nat.cast_minₓ'. -/
@[simp, norm_cast]
theorem cast_min [LinearOrderedSemiring α] {a b : ℕ} : (↑(min a b) : α) = min a b :=
  (@mono_cast α _).map_min
#align nat.cast_min Nat.cast_min

/- warning: nat.cast_max -> Nat.cast_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : Nat} {b : Nat}, Eq.{succ u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) (LinearOrder.max.{0} Nat Nat.linearOrder a b)) (LinearOrder.max.{u1} α (LinearOrderedAddCommMonoid.toLinearOrder.{u1} α (LinearOrderedSemiring.toLinearOrderedAddCommMonoid.{u1} α _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemiring.{u1} α] {a : Nat} {b : Nat}, Eq.{succ u1} α (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) (Max.max.{0} Nat Nat.instMaxNat a b)) (Max.max.{u1} α (LinearOrderedSemiring.toMax.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) a) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align nat.cast_max Nat.cast_maxₓ'. -/
@[simp, norm_cast]
theorem cast_max [LinearOrderedSemiring α] {a b : ℕ} : (↑(max a b) : α) = max a b :=
  (@mono_cast α _).map_max
#align nat.cast_max Nat.cast_max

/- warning: nat.abs_cast -> Nat.abs_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (a : Nat), Eq.{succ u1} α (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))) a)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedRing.{u1} α] (a : Nat), Eq.{succ u1} α (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedRing.toLinearOrder.{u1} α _inst_1)))))) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) a)) (Nat.cast.{u1} α (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α (StrictOrderedRing.toRing.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align nat.abs_cast Nat.abs_castₓ'. -/
@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast

#print Nat.coe_nat_dvd /-
theorem coe_nat_dvd [Semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
  map_dvd (Nat.castRingHom α) h
#align nat.coe_nat_dvd Nat.coe_nat_dvd
-/

alias coe_nat_dvd ← _root_.has_dvd.dvd.nat_cast
#align has_dvd.dvd.nat_cast Dvd.Dvd.nat_cast

end Nat

section AddMonoidHomClass

variable {A B F : Type _} [AddMonoidWithOne B]

/- warning: ext_nat' -> ext_nat' is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {F : Type.{u2}} [_inst_2 : AddMonoid.{u1} A] [_inst_3 : AddMonoidHomClass.{u2, 0, u1} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)] (f : F) (g : F), (Eq.{succ u1} A (coeFn.{succ u2, succ u1} F (fun (_x : F) => Nat -> A) (FunLike.hasCoeToFun.{succ u2, 1, succ u1} F Nat (fun (_x : Nat) => A) (AddHomClass.toFunLike.{u2, 0, u1} F Nat A (AddZeroClass.toHasAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toHasAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u2, 0, u1} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2) _inst_3))) f (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (coeFn.{succ u2, succ u1} F (fun (_x : F) => Nat -> A) (FunLike.hasCoeToFun.{succ u2, 1, succ u1} F Nat (fun (_x : Nat) => A) (AddHomClass.toFunLike.{u2, 0, u1} F Nat A (AddZeroClass.toHasAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toHasAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u2, 0, u1} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2) _inst_3))) g (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Eq.{succ u2} F f g)
but is expected to have type
  forall {A : Type.{u2}} {F : Type.{u1}} [_inst_2 : AddMonoid.{u2} A] [_inst_3 : AddMonoidHomClass.{u1, 0, u2} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u2} A _inst_2)] (f : F) (g : F), (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FunLike.coe.{succ u1, 1, succ u2} F Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) _x) (AddHomClass.toFunLike.{u1, 0, u2} F Nat A (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u2} A _inst_2) _inst_3)) f (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FunLike.coe.{succ u1, 1, succ u2} F Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) _x) (AddHomClass.toFunLike.{u1, 0, u2} F Nat A (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u2} F Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u2} A _inst_2) _inst_3)) g (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Eq.{succ u1} F f g)
Case conversion may be inaccurate. Consider using '#align ext_nat' ext_nat'ₓ'. -/
theorem ext_nat' [AddMonoid A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  FunLike.ext f g <| by
    apply Nat.rec
    · simp only [Nat.zero_eq, map_zero]
    simp (config := { contextual := true }) [Nat.succ_eq_add_one, h]
#align ext_nat' ext_nat'

/- warning: add_monoid_hom.ext_nat -> AddMonoidHom.ext_nat is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_2 : AddMonoid.{u1} A] {f : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)} {g : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)}, (Eq.{succ u1} A (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (fun (_x : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) => Nat -> A) (AddMonoidHom.hasCoeToFun.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) f (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (fun (_x : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) => Nat -> A) (AddMonoidHom.hasCoeToFun.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) g (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) f g)
but is expected to have type
  forall {A : Type.{u1}} [_inst_2 : AddMonoid.{u1} A] {f : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)} {g : AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)}, (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat A (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2) (AddMonoidHom.addMonoidHomClass.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)))) f (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FunLike.coe.{succ u1, 1, succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Nat) => A) _x) (AddHomClass.toFunLike.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat A (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_2)) (AddMonoidHomClass.toAddHomClass.{u1, 0, u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2) (AddMonoidHom.addMonoidHomClass.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)))) g (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Eq.{succ u1} (AddMonoidHom.{0, u1} Nat A (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoid.toAddZeroClass.{u1} A _inst_2)) f g)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.ext_nat AddMonoidHom.ext_natₓ'. -/
@[ext]
theorem AddMonoidHom.ext_nat [AddMonoid A] : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g :=
  ext_nat'
#align add_monoid_hom.ext_nat AddMonoidHom.ext_nat

variable [AddMonoidWithOne A]

#print eq_natCast' /-
-- these versions are primed so that the `ring_hom_class` versions aren't
theorem eq_natCast' [AddMonoidHomClass F ℕ A] (f : F) (h1 : f 1 = 1) : ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by rw [map_add, h1, eq_natCast' n, Nat.cast_add_one]
#align eq_nat_cast' eq_natCast'
-/

#print map_natCast' /-
theorem map_natCast' {A} [AddMonoidWithOne A] [AddMonoidHomClass F A B] (f : F) (h : f 1 = 1) :
    ∀ n : ℕ, f n = n
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_add, map_add, Nat.cast_add, map_natCast', Nat.cast_one, h, Nat.cast_one]
#align map_nat_cast' map_natCast'
-/

end AddMonoidHomClass

section MonoidWithZeroHomClass

variable {A F : Type _} [MulZeroOneClass A]

#print ext_nat'' /-
/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [MonoidWithZeroHomClass F ℕ A] (f g : F) (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) :
    f = g := by
  apply FunLike.ext
  rintro (_ | n)
  · simp
  exact h_pos n.succ_pos
#align ext_nat'' ext_nat''
-/

/- warning: monoid_with_zero_hom.ext_nat -> MonoidWithZeroHom.ext_nat is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} A] {f : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1} {g : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1}, (forall {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Eq.{succ u1} A (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) (fun (_x : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) => Nat -> A) (MonoidWithZeroHom.hasCoeToFun.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) f n) (coeFn.{succ u1, succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) (fun (_x : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) => Nat -> A) (MonoidWithZeroHom.hasCoeToFun.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) g n))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) f g)
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} A] {f : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1} {g : MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1}, (forall {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Nat) => A) n) (FunLike.coe.{succ u1, 1, succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Nat) => A) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (MulOneClass.toMul.{0} Nat (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) (MulOneClass.toMul.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{u1} A _inst_1) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1 (MonoidWithZeroHom.monoidWithZeroHomClass.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1)))) f n) (FunLike.coe.{succ u1, 1, succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Nat) => A) _x) (MulHomClass.toFunLike.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (MulOneClass.toMul.{0} Nat (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) (MulOneClass.toMul.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A _inst_1)) (MonoidHomClass.toMulHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MulZeroOneClass.toMulOneClass.{u1} A _inst_1) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, 0, u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1 (MonoidWithZeroHom.monoidWithZeroHomClass.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1)))) g n))) -> (Eq.{succ u1} (MonoidWithZeroHom.{0, u1} Nat A (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_nat MonoidWithZeroHom.ext_natₓ'. -/
@[ext]
theorem MonoidWithZeroHom.ext_nat : ∀ {f g : ℕ →*₀ A}, (∀ {n : ℕ}, 0 < n → f n = g n) → f = g :=
  ext_nat''
#align monoid_with_zero_hom.ext_nat MonoidWithZeroHom.ext_nat

end MonoidWithZeroHomClass

section RingHomClass

variable {R S F : Type _} [NonAssocSemiring R] [NonAssocSemiring S]

#print eq_natCast /-
@[simp]
theorem eq_natCast [RingHomClass F ℕ R] (f : F) : ∀ n, f n = n :=
  eq_natCast' f <| map_one f
#align eq_nat_cast eq_natCast
-/

/- warning: map_nat_cast -> map_natCast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S] [_inst_3 : RingHomClass.{u3, u1, u2} F R S _inst_1 _inst_2] (f : F) (n : Nat), Eq.{succ u2} S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{u3, u1, u2} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{u3, u1, u2} F R S _inst_1 _inst_2 _inst_3)))) f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1)))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u2} Nat S (CoeTCₓ.coe.{1, succ u2} Nat S (Nat.castCoe.{u2} S (AddMonoidWithOne.toNatCast.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S _inst_2)))))) n)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} {F : Type.{u3}} [_inst_1 : NonAssocSemiring.{u2} R] [_inst_2 : NonAssocSemiring.{u1} S] [_inst_3 : RingHomClass.{u3, u2, u1} F R S _inst_1 _inst_2] (f : F) (n : Nat), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) (Nat.cast.{u2} R (NonAssocSemiring.toNatCast.{u2} R _inst_1) n)) (FunLike.coe.{succ u3, succ u2, succ u1} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u3, u2, u1} F R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{u3, u2, u1} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{u3, u2, u1} F R S _inst_1 _inst_2 _inst_3))) f (Nat.cast.{u2} R (NonAssocSemiring.toNatCast.{u2} R _inst_1) n)) (Nat.cast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) (Nat.cast.{u2} R (NonAssocSemiring.toNatCast.{u2} R _inst_1) n)) (NonAssocSemiring.toNatCast.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) (Nat.cast.{u2} R (NonAssocSemiring.toNatCast.{u2} R _inst_1) n)) _inst_2) n)
Case conversion may be inaccurate. Consider using '#align map_nat_cast map_natCastₓ'. -/
@[simp]
theorem map_natCast [RingHomClass F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
  map_natCast' f <| map_one f
#align map_nat_cast map_natCast

#print ext_nat /-
theorem ext_nat [RingHomClass F ℕ R] (f g : F) : f = g :=
  ext_nat' f g <| by simp only [map_one]
#align ext_nat ext_nat
-/

/- warning: ne_zero.nat_of_injective -> NeZero.nat_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : NonAssocSemiring.{u1} R] [_inst_2 : NonAssocSemiring.{u2} S] {n : Nat} [h : NeZero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1)))))) n)] [_inst_3 : RingHomClass.{u3, u1, u2} F R S _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{u3, u1, u2} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{u3, u1, u2} F R S _inst_1 _inst_2 _inst_3)))) f)) -> (NeZero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S _inst_2))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u2} Nat S (CoeTCₓ.coe.{1, succ u2} Nat S (Nat.castCoe.{u2} S (AddMonoidWithOne.toNatCast.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S _inst_2)))))) n))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u1}} {F : Type.{u2}} [_inst_1 : NonAssocSemiring.{u3} R] [_inst_2 : NonAssocSemiring.{u1} S] {n : Nat} [h : NeZero.{u3} R (MulZeroOneClass.toZero.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R _inst_1)) (Nat.cast.{u3} R (NonAssocSemiring.toNatCast.{u3} R _inst_1) n)] [_inst_3 : RingHomClass.{u2, u3, u1} F R S _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u1} R S (FunLike.coe.{succ u2, succ u3, succ u1} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{u2, u3, u1} F R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{u2, u3, u1} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S _inst_2) (RingHomClass.toNonUnitalRingHomClass.{u2, u3, u1} F R S _inst_1 _inst_2 _inst_3))) f)) -> (NeZero.{u1} S (MulZeroOneClass.toZero.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S _inst_2)) (Nat.cast.{u1} S (NonAssocSemiring.toNatCast.{u1} S _inst_2) n))
Case conversion may be inaccurate. Consider using '#align ne_zero.nat_of_injective NeZero.nat_of_injectiveₓ'. -/
theorem NeZero.nat_of_injective {n : ℕ} [h : NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h => NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero] ⟩
#align ne_zero.nat_of_injective NeZero.nat_of_injective

/- warning: ne_zero.nat_of_ne_zero -> NeZero.nat_of_neZero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_3 : Semiring.{u1} R] [_inst_4 : Semiring.{u2} S] {F : Type.{u3}} [_inst_5 : RingHomClass.{u3, u1, u2} F R S (Semiring.toNonAssocSemiring.{u1} R _inst_3) (Semiring.toNonAssocSemiring.{u2} S _inst_4)], F -> (forall {n : Nat} [hn : NeZero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_4)))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat S (HasLiftT.mk.{1, succ u2} Nat S (CoeTCₓ.coe.{1, succ u2} Nat S (Nat.castCoe.{u2} S (AddMonoidWithOne.toNatCast.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_4))))))) n)], NeZero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))))))) n))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} [_inst_3 : Semiring.{u3} R] [_inst_4 : Semiring.{u2} S] {F : Type.{u1}} [_inst_5 : RingHomClass.{u1, u3, u2} F R S (Semiring.toNonAssocSemiring.{u3} R _inst_3) (Semiring.toNonAssocSemiring.{u2} S _inst_4)], F -> (forall {n : Nat} [hn : NeZero.{u2} S (MonoidWithZero.toZero.{u2} S (Semiring.toMonoidWithZero.{u2} S _inst_4)) (Nat.cast.{u2} S (Semiring.toNatCast.{u2} S _inst_4) n)], NeZero.{u3} R (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_3)) (Nat.cast.{u3} R (Semiring.toNatCast.{u3} R _inst_3) n))
Case conversion may be inaccurate. Consider using '#align ne_zero.nat_of_ne_zero NeZero.nat_of_neZeroₓ'. -/
theorem NeZero.nat_of_neZero {R S} [Semiring R] [Semiring S] {F} [RingHomClass F R S] (f : F)
    {n : ℕ} [hn : NeZero (n : S)] : NeZero (n : R) :=
  by
  apply NeZero.of_map f
  simp only [map_natCast, hn]
#align ne_zero.nat_of_ne_zero NeZero.nat_of_neZero

end RingHomClass

namespace RingHom

#print RingHom.eq_natCast' /-
/-- This is primed to match `eq_int_cast'`. -/
theorem eq_natCast' {R} [NonAssocSemiring R] (f : ℕ →+* R) : f = Nat.castRingHom R :=
  RingHom.ext <| eq_natCast f
#align ring_hom.eq_nat_cast' RingHom.eq_natCast'
-/

end RingHom

#print Nat.cast_id /-
@[simp, norm_cast]
theorem Nat.cast_id (n : ℕ) : ↑n = n :=
  rfl
#align nat.cast_id Nat.cast_id
-/

#print Nat.castRingHom_nat /-
@[simp]
theorem Nat.castRingHom_nat : Nat.castRingHom ℕ = RingHom.id ℕ :=
  rfl
#align nat.cast_ring_hom_nat Nat.castRingHom_nat
-/

#print Nat.uniqueRingHom /-
-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance Nat.uniqueRingHom {R : Type _} [NonAssocSemiring R] : Unique (ℕ →+* R)
    where
  default := Nat.castRingHom R
  uniq := RingHom.eq_natCast'
#align nat.unique_ring_hom Nat.uniqueRingHom
-/

namespace MulOpposite

variable [AddMonoidWithOne α]

/- warning: mul_opposite.op_nat_cast -> MulOpposite.op_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] (n : Nat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1)))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Nat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Nat (MulOpposite.{u1} α) (Nat.castCoe.{u1} (MulOpposite.{u1} α) (AddMonoidWithOne.toNatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.addMonoidWithOne.{u1} α _inst_1))))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] (n : Nat), Eq.{succ u1} (MulOpposite.{u1} α) (MulOpposite.op.{u1} α (Nat.cast.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1) n)) (Nat.cast.{u1} (MulOpposite.{u1} α) (AddMonoidWithOne.toNatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instAddMonoidWithOneMulOpposite.{u1} α _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_nat_cast MulOpposite.op_natCastₓ'. -/
@[simp, norm_cast]
theorem op_natCast (n : ℕ) : op (n : α) = n :=
  rfl
#align mul_opposite.op_nat_cast MulOpposite.op_natCast

/- warning: mul_opposite.unop_nat_cast -> MulOpposite.unop_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] (n : Nat), Eq.{succ u1} α (MulOpposite.unop.{u1} α ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (MulOpposite.{u1} α) (HasLiftT.mk.{1, succ u1} Nat (MulOpposite.{u1} α) (CoeTCₓ.coe.{1, succ u1} Nat (MulOpposite.{u1} α) (Nat.castCoe.{u1} (MulOpposite.{u1} α) (AddMonoidWithOne.toNatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.addMonoidWithOne.{u1} α _inst_1))))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1)))) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} α] (n : Nat), Eq.{succ u1} α (MulOpposite.unop.{u1} α (Nat.cast.{u1} (MulOpposite.{u1} α) (AddMonoidWithOne.toNatCast.{u1} (MulOpposite.{u1} α) (MulOpposite.instAddMonoidWithOneMulOpposite.{u1} α _inst_1)) n)) (Nat.cast.{u1} α (AddMonoidWithOne.toNatCast.{u1} α _inst_1) n)
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_nat_cast MulOpposite.unop_natCastₓ'. -/
@[simp, norm_cast]
theorem unop_natCast (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_nat_cast MulOpposite.unop_natCast

end MulOpposite

namespace Pi

variable {π : α → Type _} [∀ a, NatCast (π a)]

instance : NatCast (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

#print Pi.nat_apply /-
theorem nat_apply (n : ℕ) (a : α) : (n : ∀ a, π a) a = n :=
  rfl
#align pi.nat_apply Pi.nat_apply
-/

/- warning: pi.coe_nat -> Pi.coe_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {π : α -> Type.{u2}} [_inst_1 : forall (a : α), NatCast.{u2} (π a)] (n : Nat), Eq.{max (succ u1) (succ u2)} (forall (a : α), π a) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (forall (a : α), π a) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (forall (a : α), π a) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (forall (a : α), π a) (Nat.castCoe.{max u1 u2} (forall (a : α), π a) (Pi.hasNatCast.{u1, u2} α (fun (a : α) => π a) (fun (a : α) => _inst_1 a))))) n) (fun (_x : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat (π _x) (HasLiftT.mk.{1, succ u2} Nat (π _x) (CoeTCₓ.coe.{1, succ u2} Nat (π _x) (Nat.castCoe.{u2} (π _x) (_inst_1 _x)))) n)
but is expected to have type
  forall {α : Type.{u2}} {π : α -> Type.{u1}} [_inst_1 : forall (a : α), NatCast.{u1} (π a)] (n : Nat), Eq.{max (succ u2) (succ u1)} (forall (a : α), π a) (Nat.cast.{max u2 u1} (forall (a : α), π a) (Pi.natCast.{u2, u1} α (fun (a : α) => π a) (fun (a : α) => _inst_1 a)) n) (fun (_x : α) => Nat.cast.{u1} (π _x) (_inst_1 _x) n)
Case conversion may be inaccurate. Consider using '#align pi.coe_nat Pi.coe_natₓ'. -/
@[simp]
theorem coe_nat (n : ℕ) : (n : ∀ a, π a) = fun _ => n :=
  rfl
#align pi.coe_nat Pi.coe_nat

end Pi

/- warning: sum.elim_nat_cast_nat_cast -> Sum.elim_natCast_natCast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : NatCast.{u3} γ] (n : Nat), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ ((fun (a : Type) (b : Sort.{max (succ u1) (succ u3)}) [self : HasLiftT.{1, max (succ u1) (succ u3)} a b] => self.0) Nat (α -> γ) (HasLiftT.mk.{1, max (succ u1) (succ u3)} Nat (α -> γ) (CoeTCₓ.coe.{1, max (succ u1) (succ u3)} Nat (α -> γ) (Nat.castCoe.{max u1 u3} (α -> γ) (Pi.hasNatCast.{u1, u3} α (fun (ᾰ : α) => γ) (fun (a : α) => _inst_1))))) n) ((fun (a : Type) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{1, max (succ u2) (succ u3)} a b] => self.0) Nat (β -> γ) (HasLiftT.mk.{1, max (succ u2) (succ u3)} Nat (β -> γ) (CoeTCₓ.coe.{1, max (succ u2) (succ u3)} Nat (β -> γ) (Nat.castCoe.{max u2 u3} (β -> γ) (Pi.hasNatCast.{u2, u3} β (fun (ᾰ : β) => γ) (fun (a : β) => _inst_1))))) n)) ((fun (a : Type) (b : Sort.{max (max (succ u1) (succ u2)) (succ u3)}) [self : HasLiftT.{1, max (max (succ u1) (succ u2)) (succ u3)} a b] => self.0) Nat ((Sum.{u1, u2} α β) -> γ) (HasLiftT.mk.{1, max (max (succ u1) (succ u2)) (succ u3)} Nat ((Sum.{u1, u2} α β) -> γ) (CoeTCₓ.coe.{1, max (max (succ u1) (succ u2)) (succ u3)} Nat ((Sum.{u1, u2} α β) -> γ) (Nat.castCoe.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.hasNatCast.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) => _inst_1))))) n)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : NatCast.{u1} γ] (n : Nat), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Sum.elim.{u3, u2, succ u1} α β γ (Nat.cast.{max u3 u1} (α -> γ) (Pi.natCast.{u3, u1} α (fun (a._@.Mathlib.Data.Nat.Cast.Basic._hyg.2256 : α) => γ) (fun (a : α) => _inst_1)) n) (Nat.cast.{max u2 u1} (β -> γ) (Pi.natCast.{u2, u1} β (fun (a._@.Mathlib.Data.Nat.Cast.Basic._hyg.2262 : β) => γ) (fun (a : β) => _inst_1)) n)) (Nat.cast.{max (max u3 u2) u1} ((Sum.{u3, u2} α β) -> γ) (Pi.natCast.{max u3 u2, u1} (Sum.{u3, u2} α β) (fun (a._@.Mathlib.Data.Sum.Basic._hyg.1871 : Sum.{u3, u2} α β) => γ) (fun (a : Sum.{u3, u2} α β) => _inst_1)) n)
Case conversion may be inaccurate. Consider using '#align sum.elim_nat_cast_nat_cast Sum.elim_natCast_natCastₓ'. -/
theorem Sum.elim_natCast_natCast {α β γ : Type _} [NatCast γ] (n : ℕ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  @Sum.elim_lam_const_lam_const α β γ n
#align sum.elim_nat_cast_nat_cast Sum.elim_natCast_natCast

namespace Pi

variable {π : α → Type _} [∀ a, AddMonoidWithOne (π a)]

instance : AddMonoidWithOne (∀ a, π a) := by refine_struct { .. } <;> pi_instance_derive_field

end Pi

/-! ### Order dual -/


open OrderDual

instance [h : NatCast α] : NatCast αᵒᵈ :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne αᵒᵈ :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵒᵈ :=
  h

#print toDual_natCast /-
@[simp]
theorem toDual_natCast [NatCast α] (n : ℕ) : toDual (n : α) = n :=
  rfl
#align to_dual_nat_cast toDual_natCast
-/

#print ofDual_natCast /-
@[simp]
theorem ofDual_natCast [NatCast α] (n : ℕ) : (ofDual n : α) = n :=
  rfl
#align of_dual_nat_cast ofDual_natCast
-/

/-! ### Lexicographic order -/


instance [h : NatCast α] : NatCast (Lex α) :=
  h

instance [h : AddMonoidWithOne α] : AddMonoidWithOne (Lex α) :=
  h

instance [h : AddCommMonoidWithOne α] : AddCommMonoidWithOne (Lex α) :=
  h

#print toLex_natCast /-
@[simp]
theorem toLex_natCast [NatCast α] (n : ℕ) : toLex (n : α) = n :=
  rfl
#align to_lex_nat_cast toLex_natCast
-/

#print ofLex_natCast /-
@[simp]
theorem ofLex_natCast [NatCast α] (n : ℕ) : (ofLex n : α) = n :=
  rfl
#align of_lex_nat_cast ofLex_natCast
-/

