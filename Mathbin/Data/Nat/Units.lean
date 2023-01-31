/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.units
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Basic
import Mathbin.Algebra.Group.Units

/-! # The units of the natural numbers as a `monoid` and `add_monoid`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


namespace Nat

/- warning: nat.units_eq_one -> Nat.units_eq_one is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Nat Nat.monoid), Eq.{1} (Units.{0} Nat Nat.monoid) u (OfNat.ofNat.{0} (Units.{0} Nat Nat.monoid) 1 (OfNat.mk.{0} (Units.{0} Nat Nat.monoid) 1 (One.one.{0} (Units.{0} Nat Nat.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Nat Nat.monoid) (Units.mulOneClass.{0} Nat Nat.monoid)))))
but is expected to have type
  forall (u : Units.{0} Nat Nat.monoid), Eq.{1} (Units.{0} Nat Nat.monoid) u (OfNat.ofNat.{0} (Units.{0} Nat Nat.monoid) 1 (One.toOfNat1.{0} (Units.{0} Nat Nat.monoid) (InvOneClass.toOne.{0} (Units.{0} Nat Nat.monoid) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Nat Nat.monoid) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Nat Nat.monoid) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Nat Nat.monoid) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Nat Nat.monoid) (Units.instCommGroupUnitsToMonoid.{0} Nat Nat.commMonoid))))))))
Case conversion may be inaccurate. Consider using '#align nat.units_eq_one Nat.units_eq_oneₓ'. -/
theorem units_eq_one (u : ℕˣ) : u = 1 :=
  Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩
#align nat.units_eq_one Nat.units_eq_one

/- warning: nat.add_units_eq_zero -> Nat.addUnits_eq_zero is a dubious translation:
lean 3 declaration is
  forall (u : AddUnits.{0} Nat Nat.addMonoid), Eq.{1} (AddUnits.{0} Nat Nat.addMonoid) u (OfNat.ofNat.{0} (AddUnits.{0} Nat Nat.addMonoid) 0 (OfNat.mk.{0} (AddUnits.{0} Nat Nat.addMonoid) 0 (Zero.zero.{0} (AddUnits.{0} Nat Nat.addMonoid) (AddZeroClass.toHasZero.{0} (AddUnits.{0} Nat Nat.addMonoid) (AddUnits.addZeroClass.{0} Nat Nat.addMonoid)))))
but is expected to have type
  forall (u : AddUnits.{0} Nat Nat.addMonoid), Eq.{1} (AddUnits.{0} Nat Nat.addMonoid) u (OfNat.ofNat.{0} (AddUnits.{0} Nat Nat.addMonoid) 0 (Zero.toOfNat0.{0} (AddUnits.{0} Nat Nat.addMonoid) (NegZeroClass.toZero.{0} (AddUnits.{0} Nat Nat.addMonoid) (SubNegZeroMonoid.toNegZeroClass.{0} (AddUnits.{0} Nat Nat.addMonoid) (SubtractionMonoid.toSubNegZeroMonoid.{0} (AddUnits.{0} Nat Nat.addMonoid) (SubtractionCommMonoid.toSubtractionMonoid.{0} (AddUnits.{0} Nat Nat.addMonoid) (AddCommGroup.toDivisionAddCommMonoid.{0} (AddUnits.{0} Nat Nat.addMonoid) (AddUnits.instAddCommGroupAddUnitsToAddMonoid.{0} Nat Nat.addCommMonoid))))))))
Case conversion may be inaccurate. Consider using '#align nat.add_units_eq_zero Nat.addUnits_eq_zeroₓ'. -/
theorem addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1
#align nat.add_units_eq_zero Nat.addUnits_eq_zero

#print Nat.isUnit_iff /-
@[simp]
protected theorem isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 :=
  Iff.intro
    (fun ⟨u, hu⟩ =>
      match n, u, hu, Nat.units_eq_one u with
      | _, _, rfl, rfl => rfl)
    fun h => h.symm ▸ ⟨1, rfl⟩
#align nat.is_unit_iff Nat.isUnit_iff
-/

#print Nat.unique_units /-
instance unique_units : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one
#align nat.unique_units Nat.unique_units
-/

#print Nat.unique_addUnits /-
instance unique_addUnits : Unique (AddUnits ℕ)
    where
  default := 0
  uniq := Nat.addUnits_eq_zero
#align nat.unique_add_units Nat.unique_addUnits
-/

end Nat

