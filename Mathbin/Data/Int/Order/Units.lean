/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.order.units
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic
import Mathbin.Data.Int.Units
import Mathbin.Algebra.GroupPower.Order

/-!
# Lemmas about units in `ℤ`, which interact with the order structure.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Int

/- warning: int.is_unit_iff_abs_eq -> Int.isUnit_iff_abs_eq is a dubious translation:
lean 3 declaration is
  forall {x : Int}, Iff (IsUnit.{0} Int Int.monoid x) (Eq.{1} Int (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.hasNeg (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (LinearOrder.toLattice.{0} Int Int.linearOrder)))) x) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {x : Int}, Iff (IsUnit.{0} Int Int.instMonoidInt x) (Eq.{1} Int (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.instNegInt (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (DistribLattice.toLattice.{0} Int (instDistribLattice.{0} Int Int.instLinearOrderInt))))) x) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.is_unit_iff_abs_eq Int.isUnit_iff_abs_eqₓ'. -/
theorem isUnit_iff_abs_eq {x : ℤ} : IsUnit x ↔ abs x = 1 := by
  rw [is_unit_iff_nat_abs_eq, abs_eq_nat_abs, ← Int.ofNat_one, coe_nat_inj']
#align int.is_unit_iff_abs_eq Int.isUnit_iff_abs_eq

/- warning: int.is_unit_sq -> Int.isUnit_sq is a dubious translation:
lean 3 declaration is
  forall {a : Int}, (IsUnit.{0} Int Int.monoid a) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {a : Int}, (IsUnit.{0} Int Int.instMonoidInt a) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.is_unit_sq Int.isUnit_sqₓ'. -/
theorem isUnit_sq {a : ℤ} (ha : IsUnit a) : a ^ 2 = 1 := by rw [sq, is_unit_mul_self ha]
#align int.is_unit_sq Int.isUnit_sq

/- warning: int.units_sq -> Int.units_sq is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Eq.{1} (Units.{0} Int Int.monoid) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.monoid) Nat (Units.{0} Int Int.monoid) (instHPow.{0, 0} (Units.{0} Int Int.monoid) Nat (Monoid.Pow.{0} (Units.{0} Int Int.monoid) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.monoid) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.monoid) (Units.group.{0} Int Int.monoid))))) u (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid)))))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Eq.{1} (Units.{0} Int Int.instMonoidInt) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Units.{0} Int Int.instMonoidInt) (instHPow.{0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Monoid.Pow.{0} (Units.{0} Int Int.instMonoidInt) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instGroupUnits.{0} Int Int.instMonoidInt))))) u (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt))))))))
Case conversion may be inaccurate. Consider using '#align int.units_sq Int.units_sqₓ'. -/
@[simp]
theorem units_sq (u : ℤˣ) : u ^ 2 = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, is_unit_sq u.is_unit]
#align int.units_sq Int.units_sq

alias units_sq ← units_pow_two

/- warning: int.units_mul_self -> Int.units_mul_self is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Eq.{1} (Units.{0} Int Int.monoid) (HMul.hMul.{0, 0, 0} (Units.{0} Int Int.monoid) (Units.{0} Int Int.monoid) (Units.{0} Int Int.monoid) (instHMul.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasMul.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid))) u u) (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid)))))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Eq.{1} (Units.{0} Int Int.instMonoidInt) (HMul.hMul.{0, 0, 0} (Units.{0} Int Int.instMonoidInt) (Units.{0} Int Int.instMonoidInt) (Units.{0} Int Int.instMonoidInt) (instHMul.{0} (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt))) u u) (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt))))))))
Case conversion may be inaccurate. Consider using '#align int.units_mul_self Int.units_mul_selfₓ'. -/
@[simp]
theorem units_mul_self (u : ℤˣ) : u * u = 1 := by rw [← sq, units_sq]
#align int.units_mul_self Int.units_mul_self

/- warning: int.units_inv_eq_self -> Int.units_inv_eq_self is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Eq.{1} (Units.{0} Int Int.monoid) (Inv.inv.{0} (Units.{0} Int Int.monoid) (Units.hasInv.{0} Int Int.monoid) u) u
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Eq.{1} (Units.{0} Int Int.instMonoidInt) (Inv.inv.{0} (Units.{0} Int Int.instMonoidInt) (Units.instInvUnits.{0} Int Int.instMonoidInt) u) u
Case conversion may be inaccurate. Consider using '#align int.units_inv_eq_self Int.units_inv_eq_selfₓ'. -/
@[simp]
theorem units_inv_eq_self (u : ℤˣ) : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, units_mul_self]
#align int.units_inv_eq_self Int.units_inv_eq_self

/- warning: int.units_coe_mul_self -> Int.units_coe_mul_self is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) u) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) u)) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Units.val.{0} Int Int.instMonoidInt u) (Units.val.{0} Int Int.instMonoidInt u)) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))
Case conversion may be inaccurate. Consider using '#align int.units_coe_mul_self Int.units_coe_mul_selfₓ'. -/
-- `units.coe_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further
@[simp]
theorem units_coe_mul_self (u : ℤˣ) : (u * u : ℤ) = 1 := by
  rw [← Units.val_mul, units_mul_self, Units.val_one]
#align int.units_coe_mul_self Int.units_coe_mul_self

/- warning: int.neg_one_pow_ne_zero -> Int.neg_one_pow_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Ne.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) n) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))
but is expected to have type
  forall {n : Nat}, Ne.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) n) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))
Case conversion may be inaccurate. Consider using '#align int.neg_one_pow_ne_zero Int.neg_one_pow_ne_zeroₓ'. -/
@[simp]
theorem neg_one_pow_ne_zero {n : ℕ} : (-1 : ℤ) ^ n ≠ 0 :=
  pow_ne_zero _ (abs_pos.mp (by simp))
#align int.neg_one_pow_ne_zero Int.neg_one_pow_ne_zero

/- warning: int.sq_eq_one_of_sq_lt_four -> Int.sq_eq_one_of_sq_lt_four is a dubious translation:
lean 3 declaration is
  forall {x : Int}, (LT.lt.{0} Int Int.hasLt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Int 4 (OfNat.mk.{0} Int 4 (bit0.{0} Int Int.hasAdd (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))))) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {x : Int}, (LT.lt.{0} Int Int.instLTInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Int 4 (instOfNatInt 4))) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.sq_eq_one_of_sq_lt_four Int.sq_eq_one_of_sq_lt_fourₓ'. -/
theorem sq_eq_one_of_sq_lt_four {x : ℤ} (h1 : x ^ 2 < 4) (h2 : x ≠ 0) : x ^ 2 = 1 :=
  sq_eq_one_iff.mpr
    ((abs_eq (zero_le_one' ℤ)).mp
      (le_antisymm (lt_add_one_iff.mp (abs_lt_of_sq_lt_sq h1 zero_le_two))
        (sub_one_lt_iff.mp (abs_pos.mpr h2))))
#align int.sq_eq_one_of_sq_lt_four Int.sq_eq_one_of_sq_lt_four

/- warning: int.sq_eq_one_of_sq_le_three -> Int.sq_eq_one_of_sq_le_three is a dubious translation:
lean 3 declaration is
  forall {x : Int}, (LE.le.{0} Int Int.hasLe (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Int 3 (OfNat.mk.{0} Int 3 (bit1.{0} Int Int.hasOne Int.hasAdd (One.one.{0} Int Int.hasOne))))) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {x : Int}, (LE.le.{0} Int Int.instLEInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Int 3 (instOfNatInt 3))) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.sq_eq_one_of_sq_le_three Int.sq_eq_one_of_sq_le_threeₓ'. -/
theorem sq_eq_one_of_sq_le_three {x : ℤ} (h1 : x ^ 2 ≤ 3) (h2 : x ≠ 0) : x ^ 2 = 1 :=
  sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one 3)) h2
#align int.sq_eq_one_of_sq_le_three Int.sq_eq_one_of_sq_le_three

/- warning: int.units_pow_eq_pow_mod_two -> Int.units_pow_eq_pow_mod_two is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid) (n : Nat), Eq.{1} (Units.{0} Int Int.monoid) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.monoid) Nat (Units.{0} Int Int.monoid) (instHPow.{0, 0} (Units.{0} Int Int.monoid) Nat (Monoid.Pow.{0} (Units.{0} Int Int.monoid) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.monoid) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.monoid) (Units.group.{0} Int Int.monoid))))) u n) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.monoid) Nat (Units.{0} Int Int.monoid) (instHPow.{0, 0} (Units.{0} Int Int.monoid) Nat (Monoid.Pow.{0} (Units.{0} Int Int.monoid) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.monoid) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.monoid) (Units.group.{0} Int Int.monoid))))) u (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt) (n : Nat), Eq.{1} (Units.{0} Int Int.instMonoidInt) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Units.{0} Int Int.instMonoidInt) (instHPow.{0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Monoid.Pow.{0} (Units.{0} Int Int.instMonoidInt) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instGroupUnits.{0} Int Int.instMonoidInt))))) u n) (HPow.hPow.{0, 0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Units.{0} Int Int.instMonoidInt) (instHPow.{0, 0} (Units.{0} Int Int.instMonoidInt) Nat (Monoid.Pow.{0} (Units.{0} Int Int.instMonoidInt) (DivInvMonoid.toMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Group.toDivInvMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instGroupUnits.{0} Int Int.instMonoidInt))))) u (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align int.units_pow_eq_pow_mod_two Int.units_pow_eq_pow_mod_twoₓ'. -/
theorem units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) := by
  conv =>
      lhs
      rw [← Nat.mod_add_div n 2] <;>
    rw [pow_add, pow_mul, units_sq, one_pow, mul_one]
#align int.units_pow_eq_pow_mod_two Int.units_pow_eq_pow_mod_two

end Int

