/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.laurent_series
! leanprover-community/mathlib commit a87d22575d946e1e156fc1edd1e1269600a8a282
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.HahnSeries
import Mathbin.RingTheory.Localization.FractionRing

/-!
# Laurent Series

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/


open HahnSeries

open BigOperators Classical Polynomial

noncomputable section

universe u

#print LaurentSeries /-
/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type _) [Zero R] :=
  HahnSeries ℤ R
#align laurent_series LaurentSeries
-/

variable {R : Type u}

namespace LaurentSeries

section Semiring

variable [Semiring R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

/- warning: laurent_series.coe_power_series clashes with [anonymous] -> [anonymous]
warning: laurent_series.coe_power_series -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : Semiring.{u} R] (x : PowerSeries.{u} R), Eq.{max 1 (succ u)} (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) ((fun (a : Sort.{max 1 (succ u)}) (b : Sort.{max 1 (succ u)}) [self : HasLiftT.{max 1 (succ u), max 1 (succ u)} a b] => self.0) (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HasLiftT.mk.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (CoeTCₓ.coe.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (coeBase.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (LaurentSeries.hasCoe.{u} R _inst_1)))) x) (coeFn.{succ u, succ u} (RingHom.{u, u} (PowerSeries.{u} R) (HahnSeries.{0, u} Int R (OrderedCancelAddCommMonoid.toPartialOrder.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1)) (HahnSeries.nonAssocSemiring.{0, u} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (Semiring.toNonAssocSemiring.{u} R _inst_1))) (fun (_x : RingHom.{u, u} (PowerSeries.{u} R) (HahnSeries.{0, u} Int R (OrderedCancelAddCommMonoid.toPartialOrder.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1)) (HahnSeries.nonAssocSemiring.{0, u} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (Semiring.toNonAssocSemiring.{u} R _inst_1))) => (PowerSeries.{u} R) -> (HahnSeries.{0, u} Int R (OrderedCancelAddCommMonoid.toPartialOrder.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1)))))) (RingHom.hasCoeToFun.{u, u} (PowerSeries.{u} R) (HahnSeries.{0, u} Int R (OrderedCancelAddCommMonoid.toPartialOrder.{0} Int (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1)) (HahnSeries.nonAssocSemiring.{0, u} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (Semiring.toNonAssocSemiring.{u} R _inst_1))) (HahnSeries.ofPowerSeries.{0, u} Int R _inst_1 (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) x)
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align laurent_series.coe_power_series [anonymous]ₓ'. -/
theorem [anonymous] (x : PowerSeries R) : (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl
#align laurent_series.coe_power_series [anonymous]

/- warning: laurent_series.coeff_coe_power_series -> LaurentSeries.coeff_coe_powerSeries is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align laurent_series.coeff_coe_power_series LaurentSeries.coeff_coe_powerSeriesₓ'. -/
@[simp]
theorem coeff_coe_powerSeries (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [coe_power_series, of_power_series_apply_coeff]
#align laurent_series.coeff_coe_power_series LaurentSeries.coeff_coe_powerSeries

/- warning: laurent_series.power_series_part -> LaurentSeries.powerSeriesPart is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) -> (PowerSeries.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) -> (PowerSeries.{u1} R)
Case conversion may be inaccurate. Consider using '#align laurent_series.power_series_part LaurentSeries.powerSeriesPartₓ'. -/
/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def powerSeriesPart (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)
#align laurent_series.power_series_part LaurentSeries.powerSeriesPart

/- warning: laurent_series.power_series_part_coeff -> LaurentSeries.powerSeriesPart_coeff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (n : Nat), Eq.{succ u1} R (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (PowerSeries.{u1} R) R (PowerSeries.addCommMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.module.{u1, u1} R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Semiring.toModule.{u1} R _inst_1)) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (PowerSeries.{u1} R) R (PowerSeries.addCommMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.module.{u1, u1} R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Semiring.toModule.{u1} R _inst_1)) => (PowerSeries.{u1} R) -> R) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R (PowerSeries.{u1} R) R _inst_1 _inst_1 (PowerSeries.addCommMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.module.{u1, u1} R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Semiring.toModule.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.coeff.{u1} R _inst_1 n) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 x)) (HahnSeries.coeff.{0, u1} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (HahnSeries.order.{0, u1} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) Int.hasZero x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (n : Nat), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : PowerSeries.{u1} R) => R) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 x)) (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (PowerSeries.{u1} R) R (PowerSeries.instAddCommMonoidPowerSeries.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.instModulePowerSeriesInstAddCommMonoidPowerSeries.{u1, u1} R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Semiring.toModule.{u1} R _inst_1)) (PowerSeries.{u1} R) (fun (_x : PowerSeries.{u1} R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : PowerSeries.{u1} R) => R) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R (PowerSeries.{u1} R) R _inst_1 _inst_1 (PowerSeries.instAddCommMonoidPowerSeries.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.instModulePowerSeriesInstAddCommMonoidPowerSeries.{u1, u1} R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Semiring.toModule.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (PowerSeries.coeff.{u1} R _inst_1 n) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 x)) (HahnSeries.coeff.{0, u1} Int R (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) x (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (HahnSeries.order.{0, u1} Int R (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (CommMonoidWithZero.toZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) x) (Nat.cast.{0} Int instNatCastInt n)))
Case conversion may be inaccurate. Consider using '#align laurent_series.power_series_part_coeff LaurentSeries.powerSeriesPart_coeffₓ'. -/
@[simp]
theorem powerSeriesPart_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.powerSeriesPart = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _
#align laurent_series.power_series_part_coeff LaurentSeries.powerSeriesPart_coeff

/- warning: laurent_series.power_series_part_zero -> LaurentSeries.powerSeriesPart_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Eq.{succ u1} (PowerSeries.{u1} R) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 (OfNat.ofNat.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) 0 (OfNat.mk.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) 0 (Zero.zero.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (HahnSeries.hasZero.{0, u1} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))) (OfNat.ofNat.{u1} (PowerSeries.{u1} R) 0 (OfNat.mk.{u1} (PowerSeries.{u1} R) 0 (Zero.zero.{u1} (PowerSeries.{u1} R) (MulZeroClass.toHasZero.{u1} (PowerSeries.{u1} R) (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} (PowerSeries.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (PowerSeries.{u1} R) (Semiring.toNonAssocSemiring.{u1} (PowerSeries.{u1} R) (PowerSeries.semiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Eq.{succ u1} (PowerSeries.{u1} R) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 (OfNat.ofNat.{u1} (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) 0 (Zero.toOfNat0.{u1} (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HahnSeries.instZeroHahnSeries.{0, u1} Int R (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} (PowerSeries.{u1} R) 0 (Zero.toOfNat0.{u1} (PowerSeries.{u1} R) (PowerSeries.instZeroPowerSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zeroₓ'. -/
@[simp]
theorem powerSeriesPart_zero : powerSeriesPart (0 : LaurentSeries R) = 0 := by ext; simp
#align laurent_series.power_series_part_zero LaurentSeries.powerSeriesPart_zero

/- warning: laurent_series.power_series_part_eq_zero -> LaurentSeries.powerSeriesPart_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))), Iff (Eq.{succ u1} (PowerSeries.{u1} R) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 x) (OfNat.ofNat.{u1} (PowerSeries.{u1} R) 0 (OfNat.mk.{u1} (PowerSeries.{u1} R) 0 (Zero.zero.{u1} (PowerSeries.{u1} R) (MulZeroClass.toHasZero.{u1} (PowerSeries.{u1} R) (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} (PowerSeries.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (PowerSeries.{u1} R) (Semiring.toNonAssocSemiring.{u1} (PowerSeries.{u1} R) (PowerSeries.semiring.{u1} R _inst_1))))))))) (Eq.{succ u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x (OfNat.ofNat.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) 0 (OfNat.mk.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) 0 (Zero.zero.{u1} (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (HahnSeries.hasZero.{0, u1} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))), Iff (Eq.{succ u1} (PowerSeries.{u1} R) (LaurentSeries.powerSeriesPart.{u1} R _inst_1 x) (OfNat.ofNat.{u1} (PowerSeries.{u1} R) 0 (Zero.toOfNat0.{u1} (PowerSeries.{u1} R) (PowerSeries.instZeroPowerSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))) (Eq.{succ u1} (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) x (OfNat.ofNat.{u1} (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) 0 (Zero.toOfNat0.{u1} (LaurentSeries.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HahnSeries.instZeroHahnSeries.{0, u1} Int R (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zeroₓ'. -/
@[simp]
theorem powerSeriesPart_eq_zero (x : LaurentSeries R) : x.powerSeriesPart = 0 ↔ x = 0 :=
  by
  constructor
  · contrapose!
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
    simp [coeff_order_ne_zero h]
  · rintro rfl
    simp
#align laurent_series.power_series_part_eq_zero LaurentSeries.powerSeriesPart_eq_zero

/- warning: laurent_series.single_order_mul_power_series_part -> LaurentSeries.single_order_mul_powerSeriesPart is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPartₓ'. -/
@[simp]
theorem single_order_mul_powerSeriesPart (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.powerSeriesPart = x :=
  by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul]
  by_cases h : x.order ≤ n
  ·
    rw [Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series,
      power_series_part_coeff, ← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right]
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
    · contrapose! h
      simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      exact Int.zero_le_ofNat _
#align laurent_series.single_order_mul_power_series_part LaurentSeries.single_order_mul_powerSeriesPart

/- warning: laurent_series.of_power_series_power_series_part -> LaurentSeries.ofPowerSeries_powerSeriesPart is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align laurent_series.of_power_series_power_series_part LaurentSeries.ofPowerSeries_powerSeriesPartₓ'. -/
theorem ofPowerSeries_powerSeriesPart (x : LaurentSeries R) :
    ofPowerSeries ℤ R x.powerSeriesPart = single (-x.order) 1 * x :=
  by
  refine' Eq.trans _ (congr rfl x.single_order_mul_power_series_part)
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul,
    coe_power_series]
#align laurent_series.of_power_series_power_series_part LaurentSeries.ofPowerSeries_powerSeriesPart

end Semiring

instance [CommSemiring R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

/- warning: laurent_series.coe_algebra_map -> LaurentSeries.coe_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align laurent_series.coe_algebra_map LaurentSeries.coe_algebraMapₓ'. -/
@[simp]
theorem coe_algebraMap [CommSemiring R] :
    ⇑(algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl
#align laurent_series.coe_algebra_map LaurentSeries.coe_algebraMap

/- warning: laurent_series.of_power_series_localization -> LaurentSeries.of_powerSeries_localization is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R], IsLocalization.{u1, u1} (PowerSeries.{u1} R) (PowerSeries.commSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Submonoid.powers.{u1} (PowerSeries.{u1} R) (Ring.toMonoid.{u1} (PowerSeries.{u1} R) (PowerSeries.ring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PowerSeries.X.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (LaurentSeries.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HahnSeries.commSemiring.{0, u1} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (CommRing.toCommSemiring.{u1} R _inst_1)) (LaurentSeries.algebra.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R], IsLocalization.{u1, u1} (PowerSeries.{u1} R) (PowerSeries.instCommSemiringPowerSeries.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Submonoid.powers.{u1} (PowerSeries.{u1} R) (MonoidWithZero.toMonoid.{u1} (PowerSeries.{u1} R) (Semiring.toMonoidWithZero.{u1} (PowerSeries.{u1} R) (PowerSeries.instSemiringPowerSeries.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (PowerSeries.X.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (LaurentSeries.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (HahnSeries.instCommSemiringHahnSeriesToPartialOrderToZeroToCommMonoidWithZero.{0, u1} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Int (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Int (LinearOrderedCommRing.toLinearOrderedCommSemiring.{0} Int Int.linearOrderedCommRing)))) (CommRing.toCommSemiring.{u1} R _inst_1)) (LaurentSeries.instAlgebraPowerSeriesLaurentSeriesToZeroToCommMonoidWithZeroInstCommSemiringPowerSeriesInstSemiringHahnSeriesToPartialOrderToZeroToMonoidWithZeroIntToOrderedCancelAddCommMonoidToStrictOrderedSemiringToLinearOrderedSemiringToLinearOrderedCommSemiringLinearOrderedCommRingToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localizationₓ'. -/
/-- The localization map from power series to Laurent series. -/
@[simps]
instance of_powerSeries_localization [CommRing R] :
    IsLocalization (Submonoid.powers (PowerSeries.X : PowerSeries R)) (LaurentSeries R)
    where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_one, add_right_neg]
      rfl
    · simp only [single_mul_single, mul_one, add_left_neg]
      rfl
    · simp
  surj := by
    intro z
    by_cases h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.X ^ Int.natAbs z.order * power_series_part z, 1⟩, _⟩
      simp only [RingHom.map_one, mul_one, RingHom.map_mul, coe_algebra_map, of_power_series_X_pow,
        Submonoid.coe_one]
      rw [Int.natAbs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part]
    · refine' ⟨⟨power_series_part z, PowerSeries.X ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [coe_algebra_map, of_power_series_power_series_part]
      rw [mul_comm _ z]
      refine' congr rfl _
      rw [Subtype.coe_mk, of_power_series_X_pow, Int.ofNat_natAbs_of_nonpos]
      exact le_of_not_ge h
  eq_iff_exists := by
    intro x y
    rw [coe_algebra_map, of_power_series_injective.eq_iff]
    constructor
    · rintro rfl
      exact ⟨1, rfl⟩
    · rintro ⟨⟨_, n, rfl⟩, hc⟩
      rw [← sub_eq_zero, ← mul_sub, PowerSeries.ext_iff] at hc
      rw [← sub_eq_zero, PowerSeries.ext_iff]
      intro m
      have h := hc (m + n)
      rwa [LinearMap.map_zero, Subtype.coe_mk, PowerSeries.X_pow_eq, PowerSeries.monomial,
        add_comm m, PowerSeries.coeff, Finsupp.single_add, MvPowerSeries.coeff_add_monomial_mul,
        one_mul] at h
#align laurent_series.of_power_series_localization LaurentSeries.of_powerSeries_localization

instance {K : Type u} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.X : PowerSeries K)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero) fun f hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ HahnSeries.ofPowerSeries_injective hf

end LaurentSeries

namespace PowerSeries

open LaurentSeries

variable {R' : Type _} [Semiring R] [Ring R'] (f g : PowerSeries R) (f' g' : PowerSeries R')

/- warning: power_series.coe_zero -> PowerSeries.coe_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_zero PowerSeries.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : PowerSeries R) : LaurentSeries R) = 0 :=
  (ofPowerSeries ℤ R).map_zero
#align power_series.coe_zero PowerSeries.coe_zero

/- warning: power_series.coe_one -> PowerSeries.coe_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_one PowerSeries.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ((1 : PowerSeries R) : LaurentSeries R) = 1 :=
  (ofPowerSeries ℤ R).map_one
#align power_series.coe_one PowerSeries.coe_one

/- warning: power_series.coe_add -> PowerSeries.coe_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_add PowerSeries.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add : ((f + g : PowerSeries R) : LaurentSeries R) = f + g :=
  (ofPowerSeries ℤ R).map_add _ _
#align power_series.coe_add PowerSeries.coe_add

/- warning: power_series.coe_sub -> PowerSeries.coe_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_sub PowerSeries.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub : ((f' - g' : PowerSeries R') : LaurentSeries R') = f' - g' :=
  (ofPowerSeries ℤ R').map_sub _ _
#align power_series.coe_sub PowerSeries.coe_sub

/- warning: power_series.coe_neg -> PowerSeries.coe_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_neg PowerSeries.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg : ((-f' : PowerSeries R') : LaurentSeries R') = -f' :=
  (ofPowerSeries ℤ R').map_neg _
#align power_series.coe_neg PowerSeries.coe_neg

/- warning: power_series.coe_mul -> PowerSeries.coe_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_mul PowerSeries.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul : ((f * g : PowerSeries R) : LaurentSeries R) = f * g :=
  (ofPowerSeries ℤ R).map_mul _ _
#align power_series.coe_mul PowerSeries.coe_mul

/- warning: power_series.coeff_coe -> PowerSeries.coeff_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coeff_coe PowerSeries.coeff_coeₓ'. -/
theorem coeff_coe (i : ℤ) :
    ((f : PowerSeries R) : LaurentSeries R).coeff i =
      if i < 0 then 0 else PowerSeries.coeff R i.natAbs f :=
  by
  cases i
  ·
    rw [Int.natAbs_ofNat_core, Int.ofNat_eq_coe, coeff_coe_power_series,
      if_neg (Int.coe_nat_nonneg _).not_lt]
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_image_support,
      if_pos (Int.negSucc_lt_zero _)]
    simp only [not_exists, RelEmbedding.coe_mk, Set.mem_image, not_and, Function.Embedding.coeFn_mk,
      Ne.def, to_power_series_symm_apply_coeff, mem_support, Int.coe_nat_eq, imp_true_iff,
      not_false_iff]
#align power_series.coeff_coe PowerSeries.coeff_coe

/- warning: power_series.coe_C -> PowerSeries.coe_C is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_C PowerSeries.coe_Cₓ'. -/
@[simp, norm_cast]
theorem coe_C (r : R) : ((C R r : PowerSeries R) : LaurentSeries R) = HahnSeries.C r :=
  ofPowerSeries_C _
#align power_series.coe_C PowerSeries.coe_C

/- warning: power_series.coe_X -> PowerSeries.coe_X is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_X PowerSeries.coe_Xₓ'. -/
@[simp]
theorem coe_X : ((X : PowerSeries R) : LaurentSeries R) = single 1 1 :=
  ofPowerSeries_X
#align power_series.coe_X PowerSeries.coe_X

/- warning: power_series.coe_smul -> PowerSeries.coe_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_smul PowerSeries.coe_smulₓ'. -/
@[simp, norm_cast]
theorem coe_smul {S : Type _} [Semiring S] [Module R S] (r : R) (x : PowerSeries S) :
    ((r • x : PowerSeries S) : LaurentSeries S) = r • x := by ext;
  simp [coeff_coe, coeff_smul, smul_ite]
#align power_series.coe_smul PowerSeries.coe_smul

/- warning: power_series.coe_bit0 clashes with [anonymous] -> [anonymous]
warning: power_series.coe_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : Semiring.{u} R] (f : PowerSeries.{u} R), Eq.{max 1 (succ u)} (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) ((fun (a : Sort.{max 1 (succ u)}) (b : Sort.{max 1 (succ u)}) [self : HasLiftT.{max 1 (succ u), max 1 (succ u)} a b] => self.0) (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HasLiftT.mk.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (CoeTCₓ.coe.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (coeBase.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (LaurentSeries.hasCoe.{u} R _inst_1)))) (bit0.{u} (PowerSeries.{u} R) (Distrib.toHasAdd.{u} (PowerSeries.{u} R) (NonUnitalNonAssocSemiring.toDistrib.{u} (PowerSeries.{u} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} (PowerSeries.{u} R) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1))))) f)) (bit0.{u} (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HahnSeries.hasAdd.{0, u} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (AddMonoidWithOne.toAddMonoid.{u} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u} R (NonAssocSemiring.toAddCommMonoidWithOne.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) ((fun (a : Sort.{max 1 (succ u)}) (b : Sort.{max 1 (succ u)}) [self : HasLiftT.{max 1 (succ u), max 1 (succ u)} a b] => self.0) (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HasLiftT.mk.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (CoeTCₓ.coe.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (coeBase.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (LaurentSeries.hasCoe.{u} R _inst_1)))) f))
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align power_series.coe_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] : ((bit0 f : PowerSeries R) : LaurentSeries R) = bit0 f :=
  (ofPowerSeries ℤ R).map_bit0 _
#align power_series.coe_bit0 [anonymous]

/- warning: power_series.coe_bit1 clashes with [anonymous] -> [anonymous]
warning: power_series.coe_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u}} [_inst_1 : Semiring.{u} R] (f : PowerSeries.{u} R), Eq.{max 1 (succ u)} (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) ((fun (a : Sort.{max 1 (succ u)}) (b : Sort.{max 1 (succ u)}) [self : HasLiftT.{max 1 (succ u), max 1 (succ u)} a b] => self.0) (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HasLiftT.mk.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (CoeTCₓ.coe.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (coeBase.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (LaurentSeries.hasCoe.{u} R _inst_1)))) (bit1.{u} (PowerSeries.{u} R) (AddMonoidWithOne.toOne.{u} (PowerSeries.{u} R) (AddCommMonoidWithOne.toAddMonoidWithOne.{u} (PowerSeries.{u} R) (NonAssocSemiring.toAddCommMonoidWithOne.{u} (PowerSeries.{u} R) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1))))) (Distrib.toHasAdd.{u} (PowerSeries.{u} R) (NonUnitalNonAssocSemiring.toDistrib.{u} (PowerSeries.{u} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} (PowerSeries.{u} R) (Semiring.toNonAssocSemiring.{u} (PowerSeries.{u} R) (PowerSeries.semiring.{u} R _inst_1))))) f)) (bit1.{u} (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HahnSeries.hasOne.{0, u} Int R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Int (StrictOrderedRing.toStrictOrderedSemiring.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1)))) (AddMonoidWithOne.toOne.{u} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u} R (NonAssocSemiring.toAddCommMonoidWithOne.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HahnSeries.hasAdd.{0, u} Int R (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (AddMonoidWithOne.toAddMonoid.{u} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u} R (NonAssocSemiring.toAddCommMonoidWithOne.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) ((fun (a : Sort.{max 1 (succ u)}) (b : Sort.{max 1 (succ u)}) [self : HasLiftT.{max 1 (succ u), max 1 (succ u)} a b] => self.0) (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (HasLiftT.mk.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (CoeTCₓ.coe.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (coeBase.{max 1 (succ u), max 1 (succ u)} (PowerSeries.{u} R) (LaurentSeries.{u} R (MulZeroClass.toHasZero.{u} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u} R (Semiring.toNonAssocSemiring.{u} R _inst_1))))) (LaurentSeries.hasCoe.{u} R _inst_1)))) f))
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align power_series.coe_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] : ((bit1 f : PowerSeries R) : LaurentSeries R) = bit1 f :=
  (ofPowerSeries ℤ R).map_bit1 _
#align power_series.coe_bit1 [anonymous]

/- warning: power_series.coe_pow -> PowerSeries.coe_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align power_series.coe_pow PowerSeries.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (n : ℕ) : ((f ^ n : PowerSeries R) : LaurentSeries R) = f ^ n :=
  (ofPowerSeries ℤ R).map_pow _ _
#align power_series.coe_pow PowerSeries.coe_pow

end PowerSeries

