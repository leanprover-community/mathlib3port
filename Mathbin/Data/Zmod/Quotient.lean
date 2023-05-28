/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.zmod.quotient
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.RingTheory.Int.Basic
import Mathbin.RingTheory.Ideal.QuotientOperations

/-!
# `zmod n` and quotient groups / rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file relates `zmod n` to the quotient group
`quotient_add_group.quotient (add_subgroup.zmultiples n)` and to the quotient ring
`(ideal.span {n}).quotient`.

## Main definitions

 - `zmod.quotient_zmultiples_nat_equiv_zmod` and `zmod.quotient_zmultiples_equiv_zmod`:
   `zmod n` is the group quotient of `ℤ` by `n ℤ := add_subgroup.zmultiples (n)`,
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.quotient_span_nat_equiv_zmod` and `zmod.quotient_span_equiv_zmod`:
   `zmod n` is the ring quotient of `ℤ` by `n ℤ : ideal.span {n}`
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.lift n f` is the map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group, quotient ring, ideal quotient
-/


open quotientAddGroup

open ZMod

variable (n : ℕ) {A R : Type _} [AddGroup A] [Ring R]

namespace Int

/- warning: int.quotient_zmultiples_nat_equiv_zmod -> Int.quotientZmultiplesNatEquivZMod is a dubious translation:
lean 3 declaration is
  forall (n : Nat), AddEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (ZMod n) (AddZeroClass.toHasAdd.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (AddMonoid.toAddZeroClass.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (SubNegMonoid.toAddMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (AddGroup.toSubNegMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))) (QuotientAddGroup.Quotient.addGroup.{0} Int Int.addGroup (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (Int.quotientZmultiplesNatEquivZMod._proof_1 n)))))) (Distrib.toHasAdd.{0} (ZMod n) (Ring.toDistrib.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))
but is expected to have type
  forall (n : Nat), AddEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n))) (ZMod n) (AddZeroClass.toAdd.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n))) (AddMonoid.toAddZeroClass.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n))) (SubNegMonoid.toAddMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n))) (AddGroup.toSubNegMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n))) (QuotientAddGroup.Quotient.addGroup.{0} Int Int.instAddGroupInt (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n)) (AddSubgroup.normal_of_comm.{0} Int Int.instAddCommGroupInt (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt n)))))))) (Distrib.toAdd.{0} (ZMod n) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
Case conversion may be inaccurate. Consider using '#align int.quotient_zmultiples_nat_equiv_zmod Int.quotientZmultiplesNatEquivZModₓ'. -/
/-- `ℤ` modulo multiples of `n : ℕ` is `zmod n`. -/
def quotientZmultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_int_castAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) coe int_cast_zmod_cast
#align int.quotient_zmultiples_nat_equiv_zmod Int.quotientZmultiplesNatEquivZMod

/- warning: int.quotient_zmultiples_equiv_zmod -> Int.quotientZmultiplesEquivZMod is a dubious translation:
lean 3 declaration is
  forall (a : Int), AddEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)) (ZMod (Int.natAbs a)) (AddZeroClass.toHasAdd.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)) (AddMonoid.toAddZeroClass.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)) (SubNegMonoid.toAddMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)) (AddGroup.toSubNegMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.addGroup) (quotientAddGroup.Subgroup.hasQuotient.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)) (QuotientAddGroup.Quotient.addGroup.{0} Int Int.addGroup (AddSubgroup.zmultiples.{0} Int Int.addGroup a) (Int.quotientZmultiplesEquivZMod._proof_1 a)))))) (Distrib.toHasAdd.{0} (ZMod (Int.natAbs a)) (Ring.toDistrib.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a)))))
but is expected to have type
  forall (a : Int), AddEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)) (ZMod (Int.natAbs a)) (AddZeroClass.toAdd.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)) (AddMonoid.toAddZeroClass.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)) (SubNegMonoid.toAddMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)) (AddGroup.toSubNegMonoid.{0} (HasQuotient.Quotient.{0, 0} Int (AddSubgroup.{0} Int Int.instAddGroupInt) (QuotientAddGroup.instHasQuotientAddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)) (QuotientAddGroup.Quotient.addGroup.{0} Int Int.instAddGroupInt (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a) (AddSubgroup.normal_of_comm.{0} Int Int.instAddCommGroupInt (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a))))))) (Distrib.toAdd.{0} (ZMod (Int.natAbs a)) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod (Int.natAbs a)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod (Int.natAbs a)) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod (Int.natAbs a)) (Ring.toNonAssocRing.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a))))))))
Case conversion may be inaccurate. Consider using '#align int.quotient_zmultiples_equiv_zmod Int.quotientZmultiplesEquivZModₓ'. -/
/-- `ℤ` modulo multiples of `a : ℤ` is `zmod a.nat_abs`. -/
def quotientZmultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZmultiplesNatEquivZMod a.natAbs)
#align int.quotient_zmultiples_equiv_zmod Int.quotientZmultiplesEquivZMod

/- warning: int.quotient_span_nat_equiv_zmod -> Int.quotientSpanNatEquivZMod is a dubious translation:
lean 3 declaration is
  forall (n : Nat), RingEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing)) (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (ZMod n) (Distrib.toHasMul.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Ring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Ideal.Quotient.commRing.{0} Int Int.commRing (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))))))) (Distrib.toHasAdd.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Ring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))) (Ideal.Quotient.commRing.{0} Int Int.commRing (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))))))) (Distrib.toHasMul.{0} (ZMod n) (Ring.toDistrib.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))) (Distrib.toHasAdd.{0} (ZMod n) (Ring.toDistrib.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))
but is expected to have type
  forall (n : Nat), RingEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (ZMod n) (NonUnitalNonAssocRing.toMul.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (Ring.toNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (Ideal.Quotient.commRing.{0} Int Int.instCommRingInt (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))))))) (NonUnitalNonAssocRing.toMul.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))))) (Distrib.toAdd.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (NonUnitalNonAssocSemiring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (Ring.toNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))) (Ideal.Quotient.commRing.{0} Int Int.instCommRingInt (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt n)))))))))) (Distrib.toAdd.{0} (ZMod n) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod n) (Ring.toNonAssocRing.{0} (ZMod n) (CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))))
Case conversion may be inaccurate. Consider using '#align int.quotient_span_nat_equiv_zmod Int.quotientSpanNatEquivZModₓ'. -/
/-- `ℤ` modulo the ideal generated by `n : ℕ` is `zmod n`. -/
def quotientSpanNatEquivZMod : ℤ ⧸ Ideal.span {↑n} ≃+* ZMod n :=
  (Ideal.quotEquivOfEq (ZMod.ker_int_castRingHom _)).symm.trans <|
    RingHom.quotientKerEquivOfRightInverse <|
      show Function.RightInverse coe (Int.castRingHom (ZMod n)) from int_cast_zmod_cast
#align int.quotient_span_nat_equiv_zmod Int.quotientSpanNatEquivZMod

/- warning: int.quotient_span_equiv_zmod -> Int.quotientSpanEquivZMod is a dubious translation:
lean 3 declaration is
  forall (a : Int), RingEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing)) (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (ZMod (Int.natAbs a)) (Distrib.toHasMul.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (Ring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (Ideal.Quotient.commRing.{0} Int Int.commRing (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a)))))) (Distrib.toHasAdd.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (Ring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int (Ring.toSemiring.{0} Int (CommRing.toRing.{0} Int Int.commRing))) (Ideal.hasQuotient.{0} Int Int.commRing) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))) (Ideal.Quotient.commRing.{0} Int Int.commRing (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a)))))) (Distrib.toHasMul.{0} (ZMod (Int.natAbs a)) (Ring.toDistrib.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a))))) (Distrib.toHasAdd.{0} (ZMod (Int.natAbs a)) (Ring.toDistrib.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a)))))
but is expected to have type
  forall (a : Int), RingEquiv.{0, 0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (ZMod (Int.natAbs a)) (NonUnitalNonAssocRing.toMul.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (Ring.toNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (Ideal.Quotient.commRing.{0} Int Int.instCommRingInt (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))))))) (NonUnitalNonAssocRing.toMul.{0} (ZMod (Int.natAbs a)) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod (Int.natAbs a)) (Ring.toNonAssocRing.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a)))))) (Distrib.toAdd.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (NonUnitalNonAssocSemiring.toDistrib.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (NonAssocRing.toNonUnitalNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (Ring.toNonAssocRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (CommRing.toRing.{0} (HasQuotient.Quotient.{0, 0} Int (Ideal.{0} Int Int.instSemiringInt) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{0} Int Int.instCommRingInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))) (Ideal.Quotient.commRing.{0} Int Int.instCommRingInt (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))))))))) (Distrib.toAdd.{0} (ZMod (Int.natAbs a)) (NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod (Int.natAbs a)) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod (Int.natAbs a)) (NonAssocRing.toNonUnitalNonAssocRing.{0} (ZMod (Int.natAbs a)) (Ring.toNonAssocRing.{0} (ZMod (Int.natAbs a)) (CommRing.toRing.{0} (ZMod (Int.natAbs a)) (ZMod.commRing (Int.natAbs a))))))))
Case conversion may be inaccurate. Consider using '#align int.quotient_span_equiv_zmod Int.quotientSpanEquivZModₓ'. -/
/-- `ℤ` modulo the ideal generated by `a : ℤ` is `zmod a.nat_abs`. -/
def quotientSpanEquivZMod (a : ℤ) : ℤ ⧸ Ideal.span ({a} : Set ℤ) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
#align int.quotient_span_equiv_zmod Int.quotientSpanEquivZMod

end Int

namespace AddAction

open AddSubgroup AddMonoidHom AddEquiv Function

variable {α β : Type _} [AddGroup α] (a : α) [AddAction α β] (b : β)

#print AddAction.zmultiplesQuotientStabilizerEquiv /-
/-- The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod ((· +ᵥ ·) a) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le, mem_comap, mem_stabilizer_iff, zmultiplesHom_apply, coe_nat_zsmul,
                ← vadd_iterate]
              exact is_periodic_pt_minimal_period ((· +ᵥ ·) a) b))
          ⟨by
            rw [← ker_eq_bot_iff, eq_bot_iff]
            refine' fun q => induction_on' q fun n hn => _
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimal_period_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on' q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZmultiplesNatEquivZMod (minimalPeriod ((· +ᵥ ·) a) b))
#align add_action.zmultiples_quotient_stabilizer_equiv AddAction.zmultiplesQuotientStabilizerEquiv
-/

#print AddAction.zmultiplesQuotientStabilizerEquiv_symm_apply /-
theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod ((· +ᵥ ·) a) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl
#align add_action.zmultiples_quotient_stabilizer_equiv_symm_apply AddAction.zmultiplesQuotientStabilizerEquiv_symm_apply
-/

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type _} [Group α] (a : α) [MulAction α β] (b : β)

attribute [local semireducible] MulOpposite

#print MulAction.zpowersQuotientStabilizerEquiv /-
/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((•) a) b`. -/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod ((· • ·) a) b)) :=
  let f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  ⟨f.toFun, f.invFun, f.left_inv, f.right_inv, f.map_add'⟩
#align mul_action.zpowers_quotient_stabilizer_equiv MulAction.zpowersQuotientStabilizerEquiv
-/

#print MulAction.zpowersQuotientStabilizerEquiv_symm_apply /-
theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod ((· • ·) a) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (n : ℤ) :=
  rfl
#align mul_action.zpowers_quotient_stabilizer_equiv_symm_apply MulAction.zpowersQuotientStabilizerEquiv_symm_apply
-/

/- warning: mul_action.orbit_zpowers_equiv -> MulAction.orbitZpowersEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β), Equiv.{succ u2, 1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Subgroup.toGroup.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a)))) (Subgroup.mulAction.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b)) (ZMod (Function.minimalPeriod.{u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4) a) b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β), Equiv.{succ u2, 1} (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))) β (Submonoid.toMonoid.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) (Subgroup.toSubmonoid.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b)) (ZMod (Function.minimalPeriod.{u2} β ((fun (x._@.Mathlib.Data.ZMod.Quotient._hyg.1708 : α) (x._@.Mathlib.Data.ZMod.Quotient._hyg.1710 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4)) x._@.Mathlib.Data.ZMod.Quotient._hyg.1708 x._@.Mathlib.Data.ZMod.Quotient._hyg.1710) a) b))
Case conversion may be inaccurate. Consider using '#align mul_action.orbit_zpowers_equiv MulAction.orbitZpowersEquivₓ'. -/
/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimal_period ((•) a) b`. -/
noncomputable def orbitZpowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod ((· • ·) a) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv
#align mul_action.orbit_zpowers_equiv MulAction.orbitZpowersEquiv

/- warning: add_action.orbit_zmultiples_equiv -> AddAction.orbitZmultiplesEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : AddGroup.{u1} α] (a : α) [_inst_6 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_5))] (b : β), Equiv.{succ u2, 1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (AddAction.orbit.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} α _inst_5) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} α _inst_5) α (AddSubgroup.setLike.{u1} α _inst_5)) (AddSubgroup.zmultiples.{u1} α _inst_5 a)) β (SubNegMonoid.toAddMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} α _inst_5) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} α _inst_5) α (AddSubgroup.setLike.{u1} α _inst_5)) (AddSubgroup.zmultiples.{u1} α _inst_5 a)) (AddGroup.toSubNegMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (AddSubgroup.{u1} α _inst_5) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (AddSubgroup.{u1} α _inst_5) α (AddSubgroup.setLike.{u1} α _inst_5)) (AddSubgroup.zmultiples.{u1} α _inst_5 a)) (AddSubgroup.toAddGroup.{u1} α _inst_5 (AddSubgroup.zmultiples.{u1} α _inst_5 a)))) (AddSubgroup.addAction.{u1, u2} α _inst_5 β _inst_6 (AddSubgroup.zmultiples.{u1} α _inst_5 a)) b)) (ZMod (Function.minimalPeriod.{u2} β (VAdd.vadd.{u1, u2} α β (AddAction.toHasVadd.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_5)) _inst_6) a) b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : AddGroup.{u1} α] (a : α) [_inst_6 : AddAction.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_5))] (b : β), Equiv.{succ u2, 1} (Set.Elem.{u2} β (AddAction.orbit.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (AddSubgroup.{u1} α _inst_5) (SetLike.instMembership.{u1, u1} (AddSubgroup.{u1} α _inst_5) α (AddSubgroup.instSetLikeAddSubgroup.{u1} α _inst_5)) x (AddSubgroup.zmultiples.{u1} α _inst_5 a))) β (AddSubmonoid.toAddMonoid.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_5)) (AddSubgroup.toAddSubmonoid.{u1} α _inst_5 (AddSubgroup.zmultiples.{u1} α _inst_5 a))) (AddSubgroup.instAddActionSubtypeMemAddSubgroupInstMembershipInstSetLikeAddSubgroupToAddMonoidToAddMonoidToSubNegAddMonoidToAddSubmonoid.{u1, u2} α _inst_5 β _inst_6 (AddSubgroup.zmultiples.{u1} α _inst_5 a)) b)) (ZMod (Function.minimalPeriod.{u2} β ((fun (x._@.Mathlib.Data.ZMod.Quotient._hyg.1788 : α) (x._@.Mathlib.Data.ZMod.Quotient._hyg.1790 : β) => HVAdd.hVAdd.{u1, u2, u2} α β β (instHVAdd.{u1, u2} α β (AddAction.toVAdd.{u1, u2} α β (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_5)) _inst_6)) x._@.Mathlib.Data.ZMod.Quotient._hyg.1788 x._@.Mathlib.Data.ZMod.Quotient._hyg.1790) a) b))
Case conversion may be inaccurate. Consider using '#align add_action.orbit_zmultiples_equiv AddAction.orbitZmultiplesEquivₓ'. -/
/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def AddAction.orbitZmultiplesEquiv {α β : Type _} [AddGroup α] (a : α) [AddAction α β]
    (b : β) : AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod ((· +ᵥ ·) a) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv
#align add_action.orbit_zmultiples_equiv AddAction.orbitZmultiplesEquiv

attribute [to_additive orbit_zmultiples_equiv] orbit_zpowers_equiv

/- warning: mul_action.orbit_zpowers_equiv_symm_apply -> MulAction.orbitZpowersEquiv_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_action.orbit_zpowers_equiv_symm_apply MulAction.orbitZpowersEquiv_symm_applyₓ'. -/
@[to_additive orbit_zmultiples_equiv_symm_apply]
theorem orbitZpowersEquiv_symm_apply (k : ZMod (minimalPeriod ((· • ·) a) b)) :
    (orbitZpowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl
#align mul_action.orbit_zpowers_equiv_symm_apply MulAction.orbitZpowersEquiv_symm_apply
#align add_action.orbit_zmultiples_equiv_symm_apply AddAction.orbit_zmultiples_equiv_symm_apply

/- warning: mul_action.orbit_zpowers_equiv_symm_apply' -> MulAction.orbitZpowersEquiv_symm_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_action.orbit_zpowers_equiv_symm_apply' MulAction.orbitZpowersEquiv_symm_apply'ₓ'. -/
theorem orbitZpowersEquiv_symm_apply' (k : ℤ) :
    (orbitZpowersEquiv a b).symm k = (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ :=
  by
  rw [orbit_zpowers_equiv_symm_apply, ZMod.coe_int_cast]
  exact Subtype.ext (zpow_smul_mod_minimal_period _ _ k)
#align mul_action.orbit_zpowers_equiv_symm_apply' MulAction.orbitZpowersEquiv_symm_apply'

/- warning: add_action.orbit_zmultiples_equiv_symm_apply' -> AddAction.orbitZmultiplesEquiv_symm_apply' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_action.orbit_zmultiples_equiv_symm_apply' AddAction.orbitZmultiplesEquiv_symm_apply'ₓ'. -/
theorem AddAction.orbitZmultiplesEquiv_symm_apply' {α β : Type _} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZmultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ :=
  by
  rw [AddAction.orbit_zmultiples_equiv_symm_apply, ZMod.coe_int_cast]
  exact Subtype.ext (zsmul_vadd_mod_minimal_period _ _ k)
#align add_action.orbit_zmultiples_equiv_symm_apply' AddAction.orbitZmultiplesEquiv_symm_apply'

attribute [to_additive orbit_zmultiples_equiv_symm_apply'] orbit_zpowers_equiv_symm_apply'

/- warning: mul_action.minimal_period_eq_card -> MulAction.minimalPeriod_eq_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β) [_inst_5 : Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Subgroup.toGroup.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a)))) (Subgroup.mulAction.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b))], Eq.{1} Nat (Function.minimalPeriod.{u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4) a) b) (Fintype.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Subgroup.toGroup.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a)))) (Subgroup.mulAction.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b)) _inst_5)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β) [_inst_5 : Fintype.{u2} (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))) β (Submonoid.toMonoid.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) (Subgroup.toSubmonoid.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b))], Eq.{1} Nat (Function.minimalPeriod.{u2} β ((fun (x._@.Mathlib.Data.ZMod.Quotient._hyg.2180 : α) (x._@.Mathlib.Data.ZMod.Quotient._hyg.2182 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4)) x._@.Mathlib.Data.ZMod.Quotient._hyg.2180 x._@.Mathlib.Data.ZMod.Quotient._hyg.2182) a) b) (Fintype.card.{u2} (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))) β (Submonoid.toMonoid.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) (Subgroup.toSubmonoid.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b)) _inst_5)
Case conversion may be inaccurate. Consider using '#align mul_action.minimal_period_eq_card MulAction.minimalPeriod_eq_cardₓ'. -/
@[to_additive]
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod ((· • ·) a) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbit_zpowers_equiv a b), ZMod.card]
#align mul_action.minimal_period_eq_card MulAction.minimalPeriod_eq_card
#align add_action.minimal_period_eq_card AddAction.minimalPeriod_eq_card

/- warning: mul_action.minimal_period_pos -> MulAction.minimalPeriod_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β) [_inst_5 : Finite.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (MulAction.orbit.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) β (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)) (Subgroup.toGroup.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a)))) (Subgroup.mulAction.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b))], NeZero.{0} Nat Nat.hasZero (Function.minimalPeriod.{u2} β (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4) a) b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] (a : α) [_inst_4 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))] (b : β) [_inst_5 : Finite.{succ u2} (Set.Elem.{u2} β (MulAction.orbit.{u1, u2} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))) β (Submonoid.toMonoid.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) (Subgroup.toSubmonoid.{u1} α _inst_3 (Subgroup.zpowers.{u1} α _inst_3 a))) (Subgroup.instMulActionSubtypeMemSubgroupInstMembershipInstSetLikeSubgroupToMonoidToMonoidToDivInvMonoidToSubmonoid.{u1, u2} α _inst_3 β _inst_4 (Subgroup.zpowers.{u1} α _inst_3 a)) b))], NeZero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (Function.minimalPeriod.{u2} β ((fun (x._@.Mathlib.Data.ZMod.Quotient._hyg.2287 : α) (x._@.Mathlib.Data.ZMod.Quotient._hyg.2289 : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) _inst_4)) x._@.Mathlib.Data.ZMod.Quotient._hyg.2287 x._@.Mathlib.Data.ZMod.Quotient._hyg.2289) a) b)
Case conversion may be inaccurate. Consider using '#align mul_action.minimal_period_pos MulAction.minimalPeriod_posₓ'. -/
@[to_additive]
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod ((· • ·) a) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    haveI : Nonempty (orbit (zpowers a) b) := (orbit_nonempty b).to_subtype
    rw [minimal_period_eq_card]
    exact Fintype.card_ne_zero⟩
#align mul_action.minimal_period_pos MulAction.minimalPeriod_pos
#align add_action.minimal_period_pos AddAction.minimalPeriod_pos

end MulAction

section Group

open Subgroup

variable {α : Type _} [Group α] (a : α)

/- warning: order_eq_card_zpowers' -> order_eq_card_zpowers' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Group.{u1} α] (a : α), Eq.{1} Nat (orderOf.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Group.{u1} α] (a : α), Eq.{1} Nat (orderOf.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) (Nat.card.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))))
Case conversion may be inaccurate. Consider using '#align order_eq_card_zpowers' order_eq_card_zpowers'ₓ'. -/
/-- See also `order_eq_card_zpowers`. -/
@[to_additive add_order_eq_card_zmultiples' "See also `add_order_eq_card_zmultiples`."]
theorem order_eq_card_zpowers' : orderOf a = Nat.card (zpowers a) :=
  by
  have := Nat.card_congr (MulAction.orbitZpowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self, eq_comm] at this
#align order_eq_card_zpowers' order_eq_card_zpowers'
#align add_order_eq_card_zmultiples' add_order_eq_card_zmultiples'

variable {a}

/- warning: is_of_fin_order.finite_zpowers -> IsOfFinOrder.finite_zpowers is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Group.{u1} α] {a : α}, (IsOfFinOrder.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) -> (Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} α _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.setLike.{u1} α _inst_3)) (Subgroup.zpowers.{u1} α _inst_3 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Group.{u1} α] {a : α}, (IsOfFinOrder.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) -> (Finite.{succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subgroup.{u1} α _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} α _inst_3) α (Subgroup.instSetLikeSubgroup.{u1} α _inst_3)) x (Subgroup.zpowers.{u1} α _inst_3 a))))
Case conversion may be inaccurate. Consider using '#align is_of_fin_order.finite_zpowers IsOfFinOrder.finite_zpowersₓ'. -/
@[to_additive IsOfFinAddOrder.finite_zmultiples]
theorem IsOfFinOrder.finite_zpowers (h : IsOfFinOrder a) : Finite <| zpowers a :=
  by
  rw [← orderOf_pos_iff, order_eq_card_zpowers'] at h
  exact Nat.finite_of_card_ne_zero h.ne.symm
#align is_of_fin_order.finite_zpowers IsOfFinOrder.finite_zpowers
#align is_of_fin_add_order.finite_zmultiples IsOfFinAddOrder.finite_zmultiples

end Group

