/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä

! This file was ported from Lean 3 source module analysis.normed_space.is_R_or_C
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.IsROrC.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.Pointwise

/-!
# Normed spaces over R or C

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is about results on normed spaces over the fields `ℝ` and `ℂ`.

## Main definitions

None.

## Main theorems

* `continuous_linear_map.op_norm_bound_of_ball_bound`: A bound on the norms of values of a linear
  map in a ball yields a bound on the operator norm.

## Notes

This file exists mainly to avoid importing `is_R_or_C` in the main normed space theory files.
-/


open Metric

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedAddCommGroup E]

/- warning: is_R_or_C.norm_coe_norm -> IsROrC.norm_coe_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] {z : E}, Eq.{1} Real (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) z))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) z)
but is expected to have type
  forall {𝕜 : Type.{u2}} [_inst_1 : IsROrC.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] {z : E}, Eq.{1} Real (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (IsROrC.ofReal.{u2} 𝕜 _inst_1 (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) z))) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) z)
Case conversion may be inaccurate. Consider using '#align is_R_or_C.norm_coe_norm IsROrC.norm_coe_normₓ'. -/
theorem IsROrC.norm_coe_norm {z : E} : ‖(‖z‖ : 𝕜)‖ = ‖z‖ := by simp
#align is_R_or_C.norm_coe_norm IsROrC.norm_coe_norm

variable [NormedSpace 𝕜 E]

/- warning: norm_smul_inv_norm -> norm_smul_inv_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))))) (Inv.inv.{u1} 𝕜 (DivInvMonoid.toHasInv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x))) x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))))) (Inv.inv.{u1} 𝕜 (Field.toInv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x))) x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align norm_smul_inv_norm norm_smul_inv_normₓ'. -/
/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to unit length. -/
@[simp]
theorem norm_smul_inv_norm {x : E} (hx : x ≠ 0) : ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 :=
  by
  have : ‖x‖ ≠ 0 := by simp [hx]
  field_simp [norm_smul]
#align norm_smul_inv_norm norm_smul_inv_norm

/- warning: norm_smul_inv_norm' -> norm_smul_inv_norm' is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall {x : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) r) (Inv.inv.{u1} 𝕜 (DivInvMonoid.toHasInv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x)))) x)) r))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall {x : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (IsROrC.ofReal.{u1} 𝕜 _inst_1 r) (Inv.inv.{u1} 𝕜 (Field.toInv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x)))) x)) r))
Case conversion may be inaccurate. Consider using '#align norm_smul_inv_norm' norm_smul_inv_norm'ₓ'. -/
/-- Lemma to normalize a vector in a normed space `E` over either `ℂ` or `ℝ` to length `r`. -/
theorem norm_smul_inv_norm' {r : ℝ} (r_nonneg : 0 ≤ r) {x : E} (hx : x ≠ 0) :
    ‖(r * ‖x‖⁻¹ : 𝕜) • x‖ = r := by
  have : ‖x‖ ≠ 0 := by simp [hx]
  field_simp [norm_smul, r_nonneg, is_R_or_C_simps]
#align norm_smul_inv_norm' norm_smul_inv_norm'

/- warning: linear_map.bound_of_sphere_bound -> LinearMap.bound_of_sphere_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.bound_of_sphere_bound LinearMap.bound_of_sphere_boundₓ'. -/
theorem LinearMap.bound_of_sphere_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ sphere (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ :=
  by
  by_cases z_zero : z = 0
  · rw [z_zero]
    simp only [LinearMap.map_zero, norm_zero, MulZeroClass.mul_zero]
  set z₁ := (r * ‖z‖⁻¹ : 𝕜) • z with hz₁
  have norm_f_z₁ : ‖f z₁‖ ≤ c := by
    apply h
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm' r_pos.le z_zero
  have r_ne_zero : (r : 𝕜) ≠ 0 := is_R_or_C.of_real_ne_zero.mpr r_pos.ne'
  have eq : f z = ‖z‖ / r * f z₁ :=
    by
    rw [hz₁, LinearMap.map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, div_mul_cancel _ r_ne_zero, mul_inv_cancel, one_mul]
    simp only [z_zero, IsROrC.ofReal_eq_zero, norm_eq_zero, Ne.def, not_false_iff]
  rw [Eq, norm_mul, norm_div, IsROrC.norm_coe_norm, IsROrC.norm_of_nonneg r_pos.le,
    div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm]
  apply div_le_div _ _ r_pos rfl.ge
  · exact mul_nonneg ((norm_nonneg _).trans norm_f_z₁) (norm_nonneg z)
  apply mul_le_mul norm_f_z₁ rfl.le (norm_nonneg z) ((norm_nonneg _).trans norm_f_z₁)
#align linear_map.bound_of_sphere_bound LinearMap.bound_of_sphere_bound

/- warning: linear_map.bound_of_ball_bound' -> LinearMap.bound_of_ball_bound' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.bound_of_ball_bound' LinearMap.bound_of_ball_bound'ₓ'. -/
/-- `linear_map.bound_of_ball_bound` is a version of this over arbitrary nontrivially normed fields.
It produces a less precise bound so we keep both versions. -/
theorem LinearMap.bound_of_ball_bound' {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] 𝕜)
    (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) (z : E) : ‖f z‖ ≤ c / r * ‖z‖ :=
  f.bound_of_sphere_bound r_pos c (fun z hz => h z hz.le) z
#align linear_map.bound_of_ball_bound' LinearMap.bound_of_ball_bound'

/- warning: continuous_linear_map.op_norm_bound_of_ball_bound -> ContinuousLinearMap.op_norm_bound_of_ball_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.op_norm_bound_of_ball_bound ContinuousLinearMap.op_norm_bound_of_ball_boundₓ'. -/
theorem ContinuousLinearMap.op_norm_bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ)
    (f : E →L[𝕜] 𝕜) (h : ∀ z ∈ closedBall (0 : E) r, ‖f z‖ ≤ c) : ‖f‖ ≤ c / r :=
  by
  apply ContinuousLinearMap.op_norm_le_bound
  · apply div_nonneg _ r_pos.le
    exact
      (norm_nonneg _).trans
        (h 0 (by simp only [norm_zero, mem_closed_ball, dist_zero_left, r_pos.le]))
  apply LinearMap.bound_of_ball_bound' r_pos
  exact fun z hz => h z hz
#align continuous_linear_map.op_norm_bound_of_ball_bound ContinuousLinearMap.op_norm_bound_of_ball_bound

variable (𝕜)

include 𝕜

/- warning: normed_space.sphere_nonempty_is_R_or_C -> NormedSpace.sphere_nonempty_isROrC is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : IsROrC.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_4 : Nontrivial.{u2} E] {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Nonempty.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Metric.sphere.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))) r)))
but is expected to have type
  forall (𝕜 : Type.{u2}) [_inst_1 : IsROrC.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)] [_inst_4 : Nontrivial.{u1} E] {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Nonempty.{succ u1} (Set.Elem.{u1} E (Metric.sphere.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))) r)))
Case conversion may be inaccurate. Consider using '#align normed_space.sphere_nonempty_is_R_or_C NormedSpace.sphere_nonempty_isROrCₓ'. -/
theorem NormedSpace.sphere_nonempty_isROrC [Nontrivial E] {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (sphere (0 : E) r) :=
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  (normed_space.sphere_nonempty.mpr hr).coeSort
#align normed_space.sphere_nonempty_is_R_or_C NormedSpace.sphere_nonempty_isROrC

