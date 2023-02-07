/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.units
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Prod
import Mathbin.Data.Fintype.Sum
import Mathbin.Data.Int.Units

/-!
# fintype instances relating to units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

/- warning: units_int.fintype -> UnitsInt.fintype is a dubious translation:
lean 3 declaration is
  Fintype.{0} (Units.{0} Int Int.monoid)
but is expected to have type
  Fintype.{0} (Units.{0} Int Int.instMonoidInt)
Case conversion may be inaccurate. Consider using '#align units_int.fintype UnitsInt.fintypeₓ'. -/
instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩
#align units_int.fintype UnitsInt.fintype

/- warning: units_int.univ -> UnitsInt.univ is a dubious translation:
lean 3 declaration is
  Eq.{1} (Finset.{0} (Units.{0} Int Int.monoid)) (Finset.univ.{0} (Units.{0} Int Int.monoid) UnitsInt.fintype) (Insert.insert.{0, 0} (Units.{0} Int Int.monoid) (Finset.{0} (Units.{0} Int Int.monoid)) (Finset.hasInsert.{0} (Units.{0} Int Int.monoid) (fun (a : Units.{0} Int Int.monoid) (b : Units.{0} Int Int.monoid) => Units.decidableEq.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableEq a b) a b)) (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid))))) (Singleton.singleton.{0, 0} (Units.{0} Int Int.monoid) (Finset.{0} (Units.{0} Int Int.monoid)) (Finset.hasSingleton.{0} (Units.{0} Int Int.monoid)) (Neg.neg.{0} (Units.{0} Int Int.monoid) (Units.hasNeg.{0} Int Int.monoid (NonUnitalNonAssocRing.toHasDistribNeg.{0} Int (NonAssocRing.toNonUnitalNonAssocRing.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid))))))))
but is expected to have type
  Eq.{1} (Finset.{0} (Units.{0} Int Int.instMonoidInt)) (Finset.univ.{0} (Units.{0} Int Int.instMonoidInt) UnitsInt.fintype) (Insert.insert.{0, 0} (Units.{0} Int Int.instMonoidInt) (Finset.{0} (Units.{0} Int Int.instMonoidInt)) (Finset.instInsertFinset.{0} (Units.{0} Int Int.instMonoidInt) (fun (a : Units.{0} Int Int.instMonoidInt) (b : Units.{0} Int Int.instMonoidInt) => Units.instDecidableEqUnits.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.instDecidableEqInt a b) a b)) (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt)))))))) (Singleton.singleton.{0, 0} (Units.{0} Int Int.instMonoidInt) (Finset.{0} (Units.{0} Int Int.instMonoidInt)) (Finset.instSingletonFinset.{0} (Units.{0} Int Int.instMonoidInt)) (Neg.neg.{0} (Units.{0} Int Int.instMonoidInt) (Units.instNegUnits.{0} Int Int.instMonoidInt (NonUnitalNonAssocRing.toHasDistribNeg.{0} Int (NonAssocRing.toNonUnitalNonAssocRing.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt)))))))))))
Case conversion may be inaccurate. Consider using '#align units_int.univ UnitsInt.univₓ'. -/
@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} :=
  rfl
#align units_int.univ UnitsInt.univ

#print Fintype.card_units_int /-
@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 :=
  rfl
#align fintype.card_units_int Fintype.card_units_int
-/

instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

instance [Monoid α] [Finite α] : Finite αˣ :=
  Finite.of_injective _ Units.ext

#print Fintype.card_units /-
theorem Fintype.card_units [GroupWithZero α] [Fintype α] [Fintype αˣ] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  classical
    rw [eq_comm, Nat.sub_eq_iff_eq_add (Fintype.card_pos_iff.2 ⟨(0 : α)⟩),
      Fintype.card_congr (unitsEquivNeZero α)]
    have := Fintype.card_congr (Equiv.sumCompl (· = (0 : α))).symm
    rwa [Fintype.card_sum, add_comm, Fintype.card_subtype_eq] at this
#align fintype.card_units Fintype.card_units
-/

