/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module analysis.normed_space.int
! leanprover-community/mathlib commit 5cc2dfdd3e92f340411acea4427d701dc7ed26f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Field.Basic

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `nnreal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/


open BigOperators

namespace Int

/- warning: int.nnnorm_coe_units -> Int.nnnorm_coe_units is a dubious translation:
lean 3 declaration is
  forall (e : Units.{0} Int Int.monoid), Eq.{1} NNReal (NNNorm.nnnorm.{0} Int (SeminormedAddGroup.toNNNorm.{0} Int (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Int (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Int (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Int (NormedRing.toNonUnitalNormedRing.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) e)) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  forall (e : Units.{0} Int Int.instMonoidInt), Eq.{1} NNReal (NNNorm.nnnorm.{0} Int (SeminormedAddGroup.toNNNorm.{0} Int (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Int (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Int (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Int (NormedRing.toNonUnitalNormedRing.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)))))) (Units.val.{0} Int Int.instMonoidInt e)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))
Case conversion may be inaccurate. Consider using '#align int.nnnorm_coe_units Int.nnnorm_coe_unitsₓ'. -/
theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := Int.units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]
#align int.nnnorm_coe_units Int.nnnorm_coe_units

/- warning: int.norm_coe_units -> Int.norm_coe_units is a dubious translation:
lean 3 declaration is
  forall (e : Units.{0} Int Int.monoid), Eq.{1} Real (Norm.norm.{0} Int (NormedRing.toHasNorm.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) e)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (e : Units.{0} Int Int.instMonoidInt), Eq.{1} Real (Norm.norm.{0} Int (NormedRing.toNorm.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)) (Units.val.{0} Int Int.instMonoidInt e)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align int.norm_coe_units Int.norm_coe_unitsₓ'. -/
theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, Int.nnnorm_coe_units, NNReal.coe_one]
#align int.norm_coe_units Int.norm_coe_units

#print Int.nnnorm_coe_nat /-
@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnnorm_coe_nat _
#align int.nnnorm_coe_nat Int.nnnorm_coe_nat
-/

/- warning: int.to_nat_add_to_nat_neg_eq_nnnorm -> Int.toNat_add_toNat_neg_eq_nnnorm is a dubious translation:
lean 3 declaration is
  forall (n : Int), Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Int.toNat n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Int.toNat (Neg.neg.{0} Int Int.hasNeg n)))) (NNNorm.nnnorm.{0} Int (SeminormedAddGroup.toNNNorm.{0} Int (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Int (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Int (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Int (NormedRing.toNonUnitalNormedRing.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)))))) n)
but is expected to have type
  forall (n : Int), Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (Int.toNat n)) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (Int.toNat (Neg.neg.{0} Int Int.instNegInt n)))) (NNNorm.nnnorm.{0} Int (SeminormedAddGroup.toNNNorm.{0} Int (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Int (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Int (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Int (NormedRing.toNonUnitalNormedRing.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)))))) n)
Case conversion may be inaccurate. Consider using '#align int.to_nat_add_to_nat_neg_eq_nnnorm Int.toNat_add_toNat_neg_eq_nnnormₓ'. -/
@[simp]
theorem toNat_add_toNat_neg_eq_nnnorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, to_nat_add_to_nat_neg_eq_nat_abs, NNReal.coe_natAbs]
#align int.to_nat_add_to_nat_neg_eq_nnnorm Int.toNat_add_toNat_neg_eq_nnnorm

/- warning: int.to_nat_add_to_nat_neg_eq_norm -> Int.toNat_add_toNat_neg_eq_norm is a dubious translation:
lean 3 declaration is
  forall (n : Int), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Int.toNat n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Int.toNat (Neg.neg.{0} Int Int.hasNeg n)))) (Norm.norm.{0} Int (NormedRing.toHasNorm.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)) n)
but is expected to have type
  forall (n : Int), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast (Int.toNat n)) (Nat.cast.{0} Real Real.natCast (Int.toNat (Neg.neg.{0} Int Int.instNegInt n)))) (Norm.norm.{0} Int (NormedRing.toNorm.{0} Int (NormedCommRing.toNormedRing.{0} Int Int.normedCommRing)) n)
Case conversion may be inaccurate. Consider using '#align int.to_nat_add_to_nat_neg_eq_norm Int.toNat_add_toNat_neg_eq_normₓ'. -/
@[simp]
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_nat_cast, NNReal.coe_add] using
    congr_arg (coe : _ → ℝ) (to_nat_add_to_nat_neg_eq_nnnorm n)
#align int.to_nat_add_to_nat_neg_eq_norm Int.toNat_add_toNat_neg_eq_norm

end Int

