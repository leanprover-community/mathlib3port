/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury G. Kudryashov, Dylan MacKenzie, Patrick Massot

! This file was ported from Lean 3 source module analysis.specific_limits.normed
! leanprover-community/mathlib commit 7d34004e19699895c13c86b78ae62bbaea0bc893
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# A collection of specific limit computations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
as well as such computations in `ℝ` when the natural proof passes through a fact about normed
spaces.

-/


noncomputable section

open Classical Set Function Filter Finset Metric Asymptotics

open Classical Topology Nat BigOperators uniformity NNReal ENNReal

variable {α : Type _} {β : Type _} {ι : Type _}

/- warning: tendsto_norm_at_top_at_top -> tendsto_norm_atTop_atTop is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real (Norm.norm.{0} Real Real.hasNorm) (Filter.atTop.{0} Real Real.preorder) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real (Norm.norm.{0} Real Real.norm) (Filter.atTop.{0} Real Real.instPreorderReal) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align tendsto_norm_at_top_at_top tendsto_norm_atTop_atTopₓ'. -/
theorem tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop :=
  tendsto_abs_atTop_atTop
#align tendsto_norm_at_top_at_top tendsto_norm_atTop_atTop

/- warning: summable_of_absolute_convergence_real -> summable_of_absolute_convergence_real is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Exists.{1} Real (fun (r : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
but is expected to have type
  forall {f : Nat -> Real}, (Exists.{1} Real (fun (r : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) r))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f)
Case conversion may be inaccurate. Consider using '#align summable_of_absolute_convergence_real summable_of_absolute_convergence_realₓ'. -/
theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n => ∑ i in range n, |f i|) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ =>
    by
    refine' summable_of_summable_norm ⟨r, (hasSum_iff_tendsto_nat_of_nonneg _ _).2 _⟩
    exact fun i => norm_nonneg _
    simpa only using hr
#align summable_of_absolute_convergence_real summable_of_absolute_convergence_real

/-! ### Powers -/


/- warning: tendsto_norm_zero' -> tendsto_norm_zero' is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} 𝕜], Filter.Tendsto.{u1, 0} 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedAddCommGroup.toHasNorm.{u1} 𝕜 _inst_1)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} 𝕜 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} 𝕜 _inst_1)))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (SubNegMonoid.toAddMonoid.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 _inst_1))))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.booleanAlgebra.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.hasSingleton.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (SubNegMonoid.toAddMonoid.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 _inst_1)))))))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} 𝕜], Filter.Tendsto.{u1, 0} 𝕜 Real (Norm.norm.{u1} 𝕜 (NormedAddCommGroup.toNorm.{u1} 𝕜 _inst_1)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} 𝕜 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} 𝕜 _inst_1)))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (NegZeroClass.toZero.{u1} 𝕜 (SubNegZeroMonoid.toNegZeroClass.{u1} 𝕜 (SubtractionMonoid.toSubNegZeroMonoid.{u1} 𝕜 (SubtractionCommMonoid.toSubtractionMonoid.{u1} 𝕜 (AddCommGroup.toDivisionAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 _inst_1)))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.instBooleanAlgebraSet.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.instSingletonSet.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (NegZeroClass.toZero.{u1} 𝕜 (SubNegZeroMonoid.toNegZeroClass.{u1} 𝕜 (SubtractionMonoid.toSubNegZeroMonoid.{u1} 𝕜 (SubtractionCommMonoid.toSubtractionMonoid.{u1} 𝕜 (AddCommGroup.toDivisionAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 _inst_1))))))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_norm_zero' tendsto_norm_zero'ₓ'. -/
theorem tendsto_norm_zero' {𝕜 : Type _} [NormedAddCommGroup 𝕜] :
    Tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf <| tendsto_principal_principal.2 fun x hx => norm_pos_iff.2 hx
#align tendsto_norm_zero' tendsto_norm_zero'

namespace NormedField

/- warning: normed_field.tendsto_norm_inverse_nhds_within_0_at_top -> NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜], Filter.Tendsto.{u1, 0} 𝕜 Real (fun (x : 𝕜) => Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) (Inv.inv.{u1} 𝕜 (DivInvMonoid.toHasInv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1)))) x)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.booleanAlgebra.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.hasSingleton.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))))))) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜], Filter.Tendsto.{u1, 0} 𝕜 Real (fun (x : 𝕜) => Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_1) (Inv.inv.{u1} 𝕜 (Field.toInv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)) x)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.instBooleanAlgebraSet.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.instSingletonSet.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))))) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align normed_field.tendsto_norm_inverse_nhds_within_0_at_top NormedField.tendsto_norm_inverse_nhdsWithin_0_atTopₓ'. -/
theorem tendsto_norm_inverse_nhdsWithin_0_atTop {𝕜 : Type _} [NormedField 𝕜] :
    Tendsto (fun x : 𝕜 => ‖x⁻¹‖) (𝓝[≠] 0) atTop :=
  (tendsto_inv_zero_atTop.comp tendsto_norm_zero').congr fun x => (norm_inv x).symm
#align normed_field.tendsto_norm_inverse_nhds_within_0_at_top NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop

/- warning: normed_field.tendsto_norm_zpow_nhds_within_0_at_top -> NormedField.tendsto_norm_zpow_nhdsWithin_0_atTop is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] {m : Int}, (LT.lt.{0} Int Int.hasLt m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Filter.Tendsto.{u1, 0} 𝕜 Real (fun (x : 𝕜) => Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) (HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1))))) x m)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.booleanAlgebra.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.hasSingleton.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))))))) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] {m : Int}, (LT.lt.{0} Int Int.instLTInt m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Filter.Tendsto.{u1, 0} 𝕜 Real (fun (x : 𝕜) => Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_1) (HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1))))) x m)) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.instBooleanAlgebraSet.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.instSingletonSet.{u1} 𝕜) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))))) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align normed_field.tendsto_norm_zpow_nhds_within_0_at_top NormedField.tendsto_norm_zpow_nhdsWithin_0_atTopₓ'. -/
theorem tendsto_norm_zpow_nhdsWithin_0_atTop {𝕜 : Type _} [NormedField 𝕜] {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : 𝕜 => ‖x ^ m‖) (𝓝[≠] 0) atTop :=
  by
  rcases neg_surjective m with ⟨m, rfl⟩
  rw [neg_lt_zero] at hm; lift m to ℕ using hm.le; rw [Int.coe_nat_pos] at hm
  simp only [norm_pow, zpow_neg, zpow_ofNat, ← inv_pow]
  exact (tendsto_pow_at_top hm.ne').comp NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop
#align normed_field.tendsto_norm_zpow_nhds_within_0_at_top NormedField.tendsto_norm_zpow_nhdsWithin_0_atTop

/- warning: normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded -> NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded NormedField.tendsto_zero_smul_of_tendsto_zero_of_boundedₓ'. -/
/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
theorem tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type _} [NormedField 𝕜]
    [NormedAddCommGroup 𝔸] [NormedSpace 𝕜 𝔸] {l : Filter ι} {ε : ι → 𝕜} {f : ι → 𝔸}
    (hε : Tendsto ε l (𝓝 0)) (hf : Filter.IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← is_o_one_iff 𝕜] at hε⊢
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))
#align normed_field.tendsto_zero_smul_of_tendsto_zero_of_bounded NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded

/- warning: normed_field.continuous_at_zpow -> NormedField.continuousAt_zpow is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {m : Int} {x : 𝕜}, Iff (ContinuousAt.{u1, u1} 𝕜 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) x m) x) (Or (Ne.{succ u1} 𝕜 x (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {m : Int} {x : 𝕜}, Iff (ContinuousAt.{u1, u1} 𝕜 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) x m) x) (Or (Ne.{succ u1} 𝕜 x (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m))
Case conversion may be inaccurate. Consider using '#align normed_field.continuous_at_zpow NormedField.continuousAt_zpowₓ'. -/
@[simp]
theorem continuousAt_zpow {𝕜 : Type _} [NontriviallyNormedField 𝕜] {m : ℤ} {x : 𝕜} :
    ContinuousAt (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  by
  refine' ⟨_, continuousAt_zpow₀ _ _⟩
  contrapose!; rintro ⟨rfl, hm⟩ hc
  exact
    not_tendsto_atTop_of_tendsto_nhds (hc.tendsto.mono_left nhdsWithin_le_nhds).norm
      (tendsto_norm_zpow_nhds_within_0_at_top hm)
#align normed_field.continuous_at_zpow NormedField.continuousAt_zpow

/- warning: normed_field.continuous_at_inv -> NormedField.continuousAt_inv is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {x : 𝕜}, Iff (ContinuousAt.{u1, u1} 𝕜 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Inv.inv.{u1} 𝕜 (DivInvMonoid.toHasInv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) x) (Ne.{succ u1} 𝕜 x (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {x : 𝕜}, Iff (ContinuousAt.{u1, u1} 𝕜 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Inv.inv.{u1} 𝕜 (Field.toInv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) x) (Ne.{succ u1} 𝕜 x (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align normed_field.continuous_at_inv NormedField.continuousAt_invₓ'. -/
@[simp]
theorem continuousAt_inv {𝕜 : Type _} [NontriviallyNormedField 𝕜] {x : 𝕜} :
    ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa [(zero_lt_one' ℤ).not_le] using @continuousAt_zpow _ _ (-1) x
#align normed_field.continuous_at_inv NormedField.continuousAt_inv

end NormedField

/- warning: is_o_pow_pow_of_lt_left -> isLittleO_pow_pow_of_lt_left is a dubious translation:
lean 3 declaration is
  forall {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r₁) -> (LT.lt.{0} Real Real.hasLt r₁ r₂) -> (Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₂ n))
but is expected to have type
  forall {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r₁) -> (LT.lt.{0} Real Real.instLTReal r₁ r₂) -> (Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₂ n))
Case conversion may be inaccurate. Consider using '#align is_o_pow_pow_of_lt_left isLittleO_pow_pow_of_lt_leftₓ'. -/
theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ => r₁ ^ n) =o[atTop] fun n => r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (isLittleO_of_tendsto fun n hn => False.elim <| H.ne' <| pow_eq_zero hn) <|
    (tendsto_pow_atTop_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr
      fun n => div_pow _ _ _
#align is_o_pow_pow_of_lt_left isLittleO_pow_pow_of_lt_left

/- warning: is_O_pow_pow_of_le_left -> isBigO_pow_pow_of_le_left is a dubious translation:
lean 3 declaration is
  forall {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r₁) -> (LE.le.{0} Real Real.hasLe r₁ r₂) -> (Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₂ n))
but is expected to have type
  forall {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r₁) -> (LE.le.{0} Real Real.instLEReal r₁ r₂) -> (Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₂ n))
Case conversion may be inaccurate. Consider using '#align is_O_pow_pow_of_le_left isBigO_pow_pow_of_le_leftₓ'. -/
theorem isBigO_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ => r₁ ^ n) =O[atTop] fun n => r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h => h ▸ isBigO_refl _ _) fun h =>
    (isLittleO_pow_pow_of_lt_left h₁ h).IsBigO
#align is_O_pow_pow_of_le_left isBigO_pow_pow_of_le_left

/- warning: is_o_pow_pow_of_abs_lt_left -> isLittleO_pow_pow_of_abs_lt_left is a dubious translation:
lean 3 declaration is
  forall {r₁ : Real} {r₂ : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r₁) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r₂)) -> (Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₂ n))
but is expected to have type
  forall {r₁ : Real} {r₂ : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r₁) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r₂)) -> (Asymptotics.IsLittleO.{0, 0, 0} Nat Real Real Real.norm Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₁ n) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₂ n))
Case conversion may be inaccurate. Consider using '#align is_o_pow_pow_of_abs_lt_left isLittleO_pow_pow_of_abs_lt_leftₓ'. -/
theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
    (fun n : ℕ => r₁ ^ n) =o[atTop] fun n => r₂ ^ n :=
  by
  refine' (is_o.of_norm_left _).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)
#align is_o_pow_pow_of_abs_lt_left isLittleO_pow_pow_of_abs_lt_left

/- warning: tfae_exists_lt_is_o_pow -> TFAE_exists_lt_isLittleO_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align tfae_exists_lt_is_o_pow TFAE_exists_lt_isLittleO_powₓ'. -/
/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem TFAE_exists_lt_isLittleO_pow (f : ℕ → ℝ) (R : ℝ) :
    TFAE
      [∃ a ∈ Ioo (-R) R, f =o[atTop] pow a, ∃ a ∈ Ioo 0 R, f =o[atTop] pow a,
        ∃ a ∈ Ioo (-R) R, f =O[atTop] pow a, ∃ a ∈ Ioo 0 R, f =O[atTop] pow a,
        ∃ a < R, ∃ (C : _)(h₀ : 0 < C ∨ 0 < R), ∀ n, |f n| ≤ C * a ^ n,
        ∃ a ∈ Ioo 0 R, ∃ C > 0, ∀ n, |f n| ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in atTop, |f n| ≤ a ^ n,
        ∃ a ∈ Ioo 0 R, ∀ᶠ n in atTop, |f n| ≤ a ^ n] :=
  by
  have A : Ico 0 R ⊆ Ioo (-R) R := fun x hx =>
    ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsBigO⟩
  tfae_have 2 → 1
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  tfae_have 3 → 2
  · rintro ⟨a, ha, H⟩
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact
      ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
        H.trans_is_o (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 → 4
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsBigO⟩
  tfae_have 4 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  · rintro ⟨a, ha, H⟩
    rcases bound_of_is_O_nat_at_top H with ⟨C, hC₀, hC⟩
    refine' ⟨a, ha, C, hC₀, fun n => _⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 → 5
  exact fun ⟨a, ha, C, H₀, H⟩ => ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  · rintro ⟨a, ha, C, h₀, H⟩
    rcases sign_cases_of_C_mul_pow_nonneg fun n => (abs_nonneg _).trans (H n) with
      (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or_iff] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩
    exact
      ⟨a, A ⟨ha₀, ha⟩,
        is_O_of_le' _ fun n => (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  · rintro ⟨a, ha, H⟩
    refine' ⟨a, ha, (H.def zero_lt_one).mono fun n hn => _⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7
  exact fun ⟨a, ha, H⟩ => ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  · rintro ⟨a, ha, H⟩
    have : 0 ≤ a := nonneg_of_eventually_pow_nonneg (H.mono fun n => (abs_nonneg _).trans)
    refine' ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩
    simpa only [Real.norm_eq_abs, one_mul, abs_pow, abs_of_nonneg this]
  tfae_finish
#align tfae_exists_lt_is_o_pow TFAE_exists_lt_isLittleO_pow

/- warning: is_o_pow_const_const_pow_of_one_lt -> isLittleO_pow_const_const_pow_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) n) k) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) n) k) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))
Case conversion may be inaccurate. Consider using '#align is_o_pow_const_const_pow_of_one_lt isLittleO_pow_const_const_pow_of_one_ltₓ'. -/
/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type _} [NormedRing R] (k : ℕ) {r : ℝ}
    (hr : 1 < r) : (fun n => n ^ k : ℕ → R) =o[atTop] fun n => r ^ n :=
  by
  have : tendsto (fun x : ℝ => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).And self_mem_nhdsWithin).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices : (fun n => n ^ k : ℕ → R) =O[at_top] fun n : ℕ => (r' ^ k) ^ n
  exact this.trans_is_o (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices : ∀ n : ℕ, ‖(n : R)‖ ≤ (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖
  exact (is_O_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine' n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  simpa [div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1
#align is_o_pow_const_const_pow_of_one_lt isLittleO_pow_const_const_pow_of_one_lt

/- warning: is_o_coe_const_pow_of_one_lt -> isLittleO_coe_const_pow_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))
Case conversion may be inaccurate. Consider using '#align is_o_coe_const_pow_of_one_lt isLittleO_coe_const_pow_of_one_ltₓ'. -/
/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem isLittleO_coe_const_pow_of_one_lt {R : Type _} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    (coe : ℕ → R) =o[atTop] fun n => r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr
#align is_o_coe_const_pow_of_one_lt isLittleO_coe_const_pow_of_one_lt

/- warning: is_o_pow_const_mul_const_pow_const_pow_of_norm_lt -> isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r₁ : R} {r₂ : Real}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) r₁) r₂) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) r₁ n)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r₂ n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r₁ : R} {r₂ : Real}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) r₁) r₂) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) r₁ n)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r₂ n))
Case conversion may be inaccurate. Consider using '#align is_o_pow_const_mul_const_pow_const_pow_of_norm_lt isLittleO_pow_const_mul_const_pow_const_pow_of_norm_ltₓ'. -/
/-- If `‖r₁‖ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type _} [NormedRing R] (k : ℕ)
    {r₁ : R} {r₂ : ℝ} (h : ‖r₁‖ < r₂) :
    (fun n => n ^ k * r₁ ^ n : ℕ → R) =o[atTop] fun n => r₂ ^ n :=
  by
  by_cases h0 : r₁ = 0
  · refine' (is_o_zero _ _).congr' (mem_at_top_sets.2 <| ⟨1, fun n hn => _⟩) eventually_eq.rfl
    simp [zero_pow (zero_lt_one.trans_le hn), h0]
  rw [← Ne.def, ← norm_pos_iff] at h0
  have A : (fun n => n ^ k : ℕ → R) =o[at_top] fun n => (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n => r₁ ^ n) =O[at_top] fun n => ‖r₁‖ ^ n by
    simpa [div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this
  exact is_O.of_bound 1 (by simpa using eventually_norm_pow_le r₁)
#align is_o_pow_const_mul_const_pow_const_pow_of_norm_lt isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt

/- warning: tendsto_pow_const_div_const_pow_of_one_lt -> tendsto_pow_const_div_const_pow_of_one_lt is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (k : Nat) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Nat.cast.{0} Real Real.natCast n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_const_div_const_pow_of_one_lt tendsto_pow_const_div_const_pow_of_one_ltₓ'. -/
theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n => n ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero
#align tendsto_pow_const_div_const_pow_of_one_lt tendsto_pow_const_div_const_pow_of_one_lt

/- warning: tendsto_pow_const_mul_const_pow_of_abs_lt_one -> tendsto_pow_const_mul_const_pow_of_abs_lt_one is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (k : Nat) {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Nat.cast.{0} Real Real.natCast n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_const_mul_const_pow_of_abs_lt_one tendsto_pow_const_mul_const_pow_of_abs_lt_oneₓ'. -/
/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  by
  by_cases h0 : r = 0
  ·
    exact
      tendsto_const_nhds.congr'
        (mem_at_top_sets.2 ⟨1, fun n hn => by simp [zero_lt_one.trans_le hn, h0]⟩)
  have hr' : 1 < (|r|)⁻¹ := one_lt_inv (abs_pos.2 h0) hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'
#align tendsto_pow_const_mul_const_pow_of_abs_lt_one tendsto_pow_const_mul_const_pow_of_abs_lt_one

/- warning: tendsto_pow_const_mul_const_pow_of_lt_one -> tendsto_pow_const_mul_const_pow_of_lt_one is a dubious translation:
lean 3 declaration is
  forall (k : Nat) {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (k : Nat) {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Nat.cast.{0} Real Real.natCast n) k) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_const_mul_const_pow_of_lt_one tendsto_pow_const_mul_const_pow_of_lt_oneₓ'. -/
/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)
#align tendsto_pow_const_mul_const_pow_of_lt_one tendsto_pow_const_mul_const_pow_of_lt_one

/- warning: tendsto_self_mul_const_pow_of_abs_lt_one -> tendsto_self_mul_const_pow_of_abs_lt_one is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_self_mul_const_pow_of_abs_lt_one tendsto_self_mul_const_pow_of_abs_lt_oneₓ'. -/
/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr
#align tendsto_self_mul_const_pow_of_abs_lt_one tendsto_self_mul_const_pow_of_abs_lt_one

/- warning: tendsto_self_mul_const_pow_of_lt_one -> tendsto_self_mul_const_pow_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_self_mul_const_pow_of_lt_one tendsto_self_mul_const_pow_of_lt_oneₓ'. -/
/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r
#align tendsto_self_mul_const_pow_of_lt_one tendsto_self_mul_const_pow_of_lt_one

/- warning: tendsto_pow_at_top_nhds_0_of_norm_lt_1 -> tendsto_pow_atTop_nhds_0_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] {x : R}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, u1} Nat R (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] {x : R}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, u1} Nat R (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_at_top_nhds_0_of_norm_lt_1 tendsto_pow_atTop_nhds_0_of_norm_lt_1ₓ'. -/
/-- In a normed ring, the powers of an element x with `‖x‖ < 1` tend to zero. -/
theorem tendsto_pow_atTop_nhds_0_of_norm_lt_1 {R : Type _} [NormedRing R] {x : R} (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_0_of_lt_1 (norm_nonneg _) h
#align tendsto_pow_at_top_nhds_0_of_norm_lt_1 tendsto_pow_atTop_nhds_0_of_norm_lt_1

/- warning: tendsto_pow_at_top_nhds_0_of_abs_lt_1 -> tendsto_pow_atTop_nhds_0_of_abs_lt_1 is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_at_top_nhds_0_of_abs_lt_1 tendsto_pow_atTop_nhds_0_of_abs_lt_1ₓ'. -/
theorem tendsto_pow_atTop_nhds_0_of_abs_lt_1 {r : ℝ} (h : |r| < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_0_of_norm_lt_1 h
#align tendsto_pow_at_top_nhds_0_of_abs_lt_1 tendsto_pow_atTop_nhds_0_of_abs_lt_1

/-! ### Geometric series-/


section Geometric

variable {K : Type _} [NormedField K] {ξ : K}

/- warning: has_sum_geometric_of_norm_lt_1 -> hasSum_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} K (NormedField.toHasNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (HasSum.{u1, 0} K Nat (AddCommGroup.toAddCommMonoid.{u1} K (NormedAddCommGroup.toAddCommGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSemiNormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (Ring.toMonoid.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) ξ n) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (NormedDivisionRing.toDivisionRing.{u1} K (NormedField.toNormedDivisionRing.{u1} K _inst_1)))) (HSub.hSub.{u1, u1, u1} K K K (instHSub.{u1} K (SubNegMonoid.toHasSub.{u1} K (AddGroup.toSubNegMonoid.{u1} K (NormedAddGroup.toAddGroup.{u1} K (NormedAddCommGroup.toNormedAddGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))))) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))))))) ξ)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} K (NormedField.toNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (HasSum.{u1, 0} K Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSeminormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1)))))))) ξ n) (Inv.inv.{u1} K (Field.toInv.{u1} K (NormedField.toField.{u1} K _inst_1)) (HSub.hSub.{u1, u1, u1} K K K (instHSub.{u1} K (Ring.toSub.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1))))))) ξ)))
Case conversion may be inaccurate. Consider using '#align has_sum_geometric_of_norm_lt_1 hasSum_geometric_of_norm_lt_1ₓ'. -/
theorem hasSum_geometric_of_norm_lt_1 (h : ‖ξ‖ < 1) : HasSum (fun n : ℕ => ξ ^ n) (1 - ξ)⁻¹ :=
  by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
  · simp [norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h]
#align has_sum_geometric_of_norm_lt_1 hasSum_geometric_of_norm_lt_1

/- warning: summable_geometric_of_norm_lt_1 -> summable_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} K (NormedField.toHasNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Summable.{u1, 0} K Nat (AddCommGroup.toAddCommMonoid.{u1} K (NormedAddCommGroup.toAddCommGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSemiNormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (Ring.toMonoid.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) ξ n))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} K (NormedField.toNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Summable.{u1, 0} K Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSeminormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1)))))))) ξ n))
Case conversion may be inaccurate. Consider using '#align summable_geometric_of_norm_lt_1 summable_geometric_of_norm_lt_1ₓ'. -/
theorem summable_geometric_of_norm_lt_1 (h : ‖ξ‖ < 1) : Summable fun n : ℕ => ξ ^ n :=
  ⟨_, hasSum_geometric_of_norm_lt_1 h⟩
#align summable_geometric_of_norm_lt_1 summable_geometric_of_norm_lt_1

/- warning: tsum_geometric_of_norm_lt_1 -> tsum_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} K (NormedField.toHasNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{succ u1} K (tsum.{u1, 0} K (AddCommGroup.toAddCommMonoid.{u1} K (NormedAddCommGroup.toAddCommGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSemiNormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) Nat (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (Ring.toMonoid.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) ξ n)) (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (NormedDivisionRing.toDivisionRing.{u1} K (NormedField.toNormedDivisionRing.{u1} K _inst_1)))) (HSub.hSub.{u1, u1, u1} K K K (instHSub.{u1} K (SubNegMonoid.toHasSub.{u1} K (AddGroup.toSubNegMonoid.{u1} K (NormedAddGroup.toAddGroup.{u1} K (NormedAddCommGroup.toNormedAddGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))))) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))))))) ξ)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} K (NormedField.toNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{succ u1} K (tsum.{u1, 0} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSeminormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) Nat (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1)))))))) ξ n)) (Inv.inv.{u1} K (Field.toInv.{u1} K (NormedField.toField.{u1} K _inst_1)) (HSub.hSub.{u1, u1, u1} K K K (instHSub.{u1} K (Ring.toSub.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1))))))) ξ)))
Case conversion may be inaccurate. Consider using '#align tsum_geometric_of_norm_lt_1 tsum_geometric_of_norm_lt_1ₓ'. -/
theorem tsum_geometric_of_norm_lt_1 (h : ‖ξ‖ < 1) : (∑' n : ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
  (hasSum_geometric_of_norm_lt_1 h).tsum_eq
#align tsum_geometric_of_norm_lt_1 tsum_geometric_of_norm_lt_1

/- warning: has_sum_geometric_of_abs_lt_1 -> hasSum_geometric_of_abs_lt_1 is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (HasSum.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n) (Inv.inv.{0} Real Real.hasInv (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r)))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (HasSum.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n) (Inv.inv.{0} Real Real.instInvReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r)))
Case conversion may be inaccurate. Consider using '#align has_sum_geometric_of_abs_lt_1 hasSum_geometric_of_abs_lt_1ₓ'. -/
theorem hasSum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) :
    HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_1 h
#align has_sum_geometric_of_abs_lt_1 hasSum_geometric_of_abs_lt_1

/- warning: summable_geometric_of_abs_lt_1 -> summable_geometric_of_abs_lt_1 is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))
Case conversion may be inaccurate. Consider using '#align summable_geometric_of_abs_lt_1 summable_geometric_of_abs_lt_1ₓ'. -/
theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ => r ^ n :=
  summable_geometric_of_norm_lt_1 h
#align summable_geometric_of_abs_lt_1 summable_geometric_of_abs_lt_1

/- warning: tsum_geometric_of_abs_lt_1 -> tsum_geometric_of_abs_lt_1 is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (tsum.{0, 0} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (Inv.inv.{0} Real Real.hasInv (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r)))
but is expected to have type
  forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (tsum.{0, 0} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Nat (fun (n : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (Inv.inv.{0} Real Real.instInvReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r)))
Case conversion may be inaccurate. Consider using '#align tsum_geometric_of_abs_lt_1 tsum_geometric_of_abs_lt_1ₓ'. -/
theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_1 h
#align tsum_geometric_of_abs_lt_1 tsum_geometric_of_abs_lt_1

/- warning: summable_geometric_iff_norm_lt_1 -> summable_geometric_iff_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, Iff (Summable.{u1, 0} K Nat (AddCommGroup.toAddCommMonoid.{u1} K (NormedAddCommGroup.toAddCommGroup.{u1} K (NonUnitalNormedRing.toNormedAddCommGroup.{u1} K (NormedRing.toNonUnitalNormedRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSemiNormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (Ring.toMonoid.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) ξ n)) (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} K (NormedField.toHasNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : NormedField.{u1} K] {ξ : K}, Iff (Summable.{u1, 0} K Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (NormedRing.toRing.{u1} K (NormedCommRing.toNormedRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedRing.toPseudoMetricSpace.{u1} K (SeminormedCommRing.toSeminormedRing.{u1} K (NormedCommRing.toSeminormedCommRing.{u1} K (NormedField.toNormedCommRing.{u1} K _inst_1)))))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} K Nat K (instHPow.{u1, 0} K Nat (Monoid.Pow.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K (NormedField.toField.{u1} K _inst_1)))))))) ξ n)) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} K (NormedField.toNorm.{u1} K _inst_1) ξ) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align summable_geometric_iff_norm_lt_1 summable_geometric_iff_norm_lt_1ₓ'. -/
/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_1 : (Summable fun n : ℕ => ξ ^ n) ↔ ‖ξ‖ < 1 :=
  by
  refine' ⟨fun h => _, summable_geometric_of_norm_lt_1⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow _ zero_le_one hk
#align summable_geometric_iff_norm_lt_1 summable_geometric_iff_norm_lt_1

end Geometric

section MulGeometric

/- warning: summable_norm_pow_mul_geometric_of_norm_lt_1 -> summable_norm_pow_mul_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r : R}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) r n))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] (k : Nat) {r : R}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) r n))))
Case conversion may be inaccurate. Consider using '#align summable_norm_pow_mul_geometric_of_norm_lt_1 summable_norm_pow_mul_geometric_of_norm_lt_1ₓ'. -/
theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] (k : ℕ) {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ => ‖(n ^ k * r ^ n : R)‖ :=
  by
  rcases exists_between hr with ⟨r', hrr', h⟩
  exact
    summable_of_isBigO_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').IsBigO.norm_left
#align summable_norm_pow_mul_geometric_of_norm_lt_1 summable_norm_pow_mul_geometric_of_norm_lt_1

/- warning: summable_pow_mul_geometric_of_norm_lt_1 -> summable_pow_mul_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (k : Nat) {r : R}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Summable.{u1, 0} R Nat (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) r n)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (k : Nat) {r : R}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Summable.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) n) k) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) r n)))
Case conversion may be inaccurate. Consider using '#align summable_pow_mul_geometric_of_norm_lt_1 summable_pow_mul_geometric_of_norm_lt_1ₓ'. -/
theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] [CompleteSpace R]
    (k : ℕ) {r : R} (hr : ‖r‖ < 1) : Summable (fun n => n ^ k * r ^ n : ℕ → R) :=
  summable_of_summable_norm <| summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr
#align summable_pow_mul_geometric_of_norm_lt_1 summable_pow_mul_geometric_of_norm_lt_1

/- warning: has_sum_coe_mul_geometric_of_norm_lt_1 -> hasSum_coe_mul_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))] {r : 𝕜}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (HasSum.{u1, 0} 𝕜 Nat (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))) n) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) r n)) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1))))) r (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))) r) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))] {r : 𝕜}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_1) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (HasSum.{u1, 0} 𝕜 Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (fun (n : Nat) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (Semiring.toNatCast.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))) n) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))) r n)) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))) r (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (Semiring.toOne.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) r) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align has_sum_coe_mul_geometric_of_norm_lt_1 hasSum_coe_mul_geometric_of_norm_lt_1ₓ'. -/
/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem hasSum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜}
    (hr : ‖r‖ < 1) : HasSum (fun n => n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) :=
  by
  have A : Summable (fun n => n * r ^ n : ℕ → 𝕜) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr
  have B : HasSum (pow r : ℕ → 𝕜) (1 - r)⁻¹ := hasSum_geometric_of_norm_lt_1 hr
  refine' A.has_sum_iff.2 _
  have hr' : r ≠ 1 := by
    rintro rfl
    simpa [lt_irrefl] using hr
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n
  calc
    s = (1 - r) * s / (1 - r) := (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm
    _ = (s - r * s) / (1 - r) := by rw [sub_mul, one_mul]
    _ = (((0 : ℕ) * r ^ 0 + ∑' n : ℕ, (n + 1 : ℕ) * r ^ (n + 1)) - r * s) / (1 - r) := by
      rw [← tsum_eq_zero_add A]
    _ = ((r * ∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) := by
      simp [pow_succ, mul_left_comm _ r, tsum_mul_left]
    _ = r / (1 - r) ^ 2 := by
      simp [add_mul, tsum_add A B.summable, mul_add, B.tsum_eq, ← div_eq_mul_inv, sq, div_div]
    
#align has_sum_coe_mul_geometric_of_norm_lt_1 hasSum_coe_mul_geometric_of_norm_lt_1

/- warning: tsum_coe_mul_geometric_of_norm_lt_1 -> tsum_coe_mul_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))] {r : 𝕜}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{succ u1} 𝕜 (tsum.{u1, 0} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) Nat (fun (n : Nat) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))) n) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) r n))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1))))) r (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))))))) r) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))] {r : 𝕜}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_1) r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{succ u1} 𝕜 (tsum.{u1, 0} 𝕜 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) Nat (fun (n : Nat) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (Semiring.toNatCast.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))) n) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))) r n))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))) r (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (Semiring.toOne.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) r) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align tsum_coe_mul_geometric_of_norm_lt_1 tsum_coe_mul_geometric_of_norm_lt_1ₓ'. -/
/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜}
    (hr : ‖r‖ < 1) : (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq
#align tsum_coe_mul_geometric_of_norm_lt_1 tsum_coe_mul_geometric_of_norm_lt_1

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : ℝ} {f : ℕ → α}

/- warning: seminormed_add_comm_group.cauchy_seq_of_le_geometric -> SeminormedAddCommGroup.cauchySeq_of_le_geometric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall {u : Nat -> α}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (SeminormedAddGroup.toAddGroup.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α _inst_1))))) (u n) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall {u : Nat -> α}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (SeminormedAddGroup.toAddGroup.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α _inst_1))))) (u n) (u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) u))
Case conversion may be inaccurate. Consider using '#align seminormed_add_comm_group.cauchy_seq_of_le_geometric SeminormedAddCommGroup.cauchySeq_of_le_geometricₓ'. -/
theorem SeminormedAddCommGroup.cauchySeq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1) {u : ℕ → α}
    (h : ∀ n, ‖u n - u (n + 1)‖ ≤ C * r ^ n) : CauchySeq u :=
  cauchySeq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)
#align seminormed_add_comm_group.cauchy_seq_of_le_geometric SeminormedAddCommGroup.cauchySeq_of_le_geometric

/- warning: dist_partial_sum_le_of_le_geometric -> dist_partial_sum_le_of_le_geometric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => f i))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => f i))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)))
Case conversion may be inaccurate. Consider using '#align dist_partial_sum_le_of_le_geometric dist_partial_sum_le_of_le_geometricₓ'. -/
theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) ≤ C * r ^ n :=
  by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel']
  exact hf n
#align dist_partial_sum_le_of_le_geometric dist_partial_sum_le_of_le_geometric

/- warning: cauchy_seq_finset_of_geometric_bound -> cauchySeq_finset_of_geometric_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (CauchySeq.{u1, 0} α (Finset.{0} Nat) (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} (Finset.{0} Nat) (Finset.lattice.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b))) (fun (s : Finset.{0} Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) s (fun (x : Nat) => f x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (CauchySeq.{u1, 0} α (Finset.{0} Nat) (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} (Finset.{0} Nat) (Finset.instLatticeFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b))) (fun (s : Finset.{0} Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) s (fun (x : Nat) => f x)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_finset_of_geometric_bound cauchySeq_finset_of_geometric_boundₓ'. -/
/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ => ∑ x in s, f x :=
  cauchySeq_finset_of_norm_bounded _
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).Summable hf
#align cauchy_seq_finset_of_geometric_bound cauchySeq_finset_of_geometric_bound

/- warning: norm_sub_le_of_geometric_bound_of_has_sum -> norm_sub_le_of_geometric_bound_of_hasSum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (forall {a : α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f a) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (SeminormedAddGroup.toAddGroup.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α _inst_1))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (x : Nat) => f x)) a)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {r : Real} {C : Real} {f : Nat -> α}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (forall {a : α}, (HasSum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f a) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (SeminormedAddGroup.toAddGroup.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α _inst_1))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (x : Nat) => f x)) a)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r))))
Case conversion may be inaccurate. Consider using '#align norm_sub_le_of_geometric_bound_of_has_sum norm_sub_le_of_geometric_bound_of_hasSumₓ'. -/
/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) {a : α}
    (ha : HasSum f a) (n : ℕ) : ‖(∑ x in Finset.range n, f x) - a‖ ≤ C * r ^ n / (1 - r) :=
  by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat
#align norm_sub_le_of_geometric_bound_of_has_sum norm_sub_le_of_geometric_bound_of_hasSum

#print dist_partial_sum /-
@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) :
    dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ‖u n‖ := by
  simp [dist_eq_norm, sum_range_succ]
#align dist_partial_sum dist_partial_sum
-/

#print dist_partial_sum' /-
@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) :
    dist (∑ k in range n, u k) (∑ k in range (n + 1), u k) = ‖u n‖ := by
  simp [dist_eq_norm', sum_range_succ]
#align dist_partial_sum' dist_partial_sum'
-/

/- warning: cauchy_series_of_le_geometric -> cauchy_series_of_le_geometric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (k : Nat) => u k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (k : Nat) => u k)))
Case conversion may be inaccurate. Consider using '#align cauchy_series_of_le_geometric cauchy_series_of_le_geometricₓ'. -/
theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range n, u k :=
  cauchySeq_of_le_geometric r C hr (by simp [h])
#align cauchy_series_of_le_geometric cauchy_series_of_le_geometric

/- warning: normed_add_comm_group.cauchy_series_of_le_geometric' -> NormedAddCommGroup.cauchy_series_of_le_geometric' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => u k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => u k)))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.cauchy_series_of_le_geometric' NormedAddCommGroup.cauchy_series_of_le_geometric'ₓ'. -/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_atTop_nat 1
#align normed_add_comm_group.cauchy_series_of_le_geometric' NormedAddCommGroup.cauchy_series_of_le_geometric'

/- warning: normed_add_comm_group.cauchy_series_of_le_geometric'' -> NormedAddCommGroup.cauchy_series_of_le_geometric'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {N : Nat} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n N) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => u k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {C : Real} {u : Nat -> α} {N : Nat} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (forall (n : Nat), (GE.ge.{0} Nat instLENat n N) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (u n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)))) -> (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => u k)))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.cauchy_series_of_le_geometric'' NormedAddCommGroup.cauchy_series_of_le_geometric''ₓ'. -/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (h : ∀ n ≥ N, ‖u n‖ ≤ C * r ^ n) :
    CauchySeq fun n => ∑ k in range (n + 1), u k :=
  by
  set v : ℕ → α := fun n => if n < N then 0 else u n
  have hC : 0 ≤ C :=
    (zero_le_mul_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : ∀ n ≥ N, u n = v n := by
    intro n hn
    simp [v, hn, if_neg (not_lt.mpr hn)]
  refine'
    cauchySeq_sum_of_eventually_eq this (NormedAddCommGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
  intro n
  dsimp [v]
  split_ifs with H H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
  · push_neg  at H
    exact h _ H
#align normed_add_comm_group.cauchy_series_of_le_geometric'' NormedAddCommGroup.cauchy_series_of_le_geometric''

end SummableLeGeometric

section NormedRingGeometric

variable {R : Type _} [NormedRing R] [CompleteSpace R]

open NormedSpace

/- warning: normed_ring.summable_geometric_of_norm_lt_1 -> NormedRing.summable_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Summable.{u1, 0} R Nat (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Summable.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x n))
Case conversion may be inaccurate. Consider using '#align normed_ring.summable_geometric_of_norm_lt_1 NormedRing.summable_geometric_of_norm_lt_1ₓ'. -/
/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem NormedRing.summable_geometric_of_norm_lt_1 (x : R) (h : ‖x‖ < 1) :
    Summable fun n : ℕ => x ^ n :=
  by
  have h1 : Summable fun n : ℕ => ‖x‖ ^ n := summable_geometric_of_lt_1 (norm_nonneg _) h
  refine' summable_of_norm_bounded_eventually _ h1 _
  rw [Nat.cofinite_eq_atTop]
  exact eventually_norm_pow_le x
#align normed_ring.summable_geometric_of_norm_lt_1 NormedRing.summable_geometric_of_norm_lt_1

/- warning: normed_ring.tsum_geometric_of_norm_lt_1 -> NormedRing.tsum_geometric_of_norm_lt_1 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) (tsum.{u1, 0} R (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x n))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Inv.inv.{0} Real Real.hasInv (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (tsum.{u1, 0} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (n : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x n))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Inv.inv.{0} Real Real.instInvReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x)))))
Case conversion may be inaccurate. Consider using '#align normed_ring.tsum_geometric_of_norm_lt_1 NormedRing.tsum_geometric_of_norm_lt_1ₓ'. -/
/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `‖1‖ = 1`. -/
theorem NormedRing.tsum_geometric_of_norm_lt_1 (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ :=
  by
  rw [tsum_eq_zero_add (NormedRing.summable_geometric_of_norm_lt_1 x h)]
  simp only [pow_zero]
  refine' le_trans (norm_add_le _ _) _
  have : ‖∑' b : ℕ, (fun n => x ^ (n + 1)) b‖ ≤ (1 - ‖x‖)⁻¹ - 1 :=
    by
    refine' tsum_of_norm_bounded _ fun b => norm_pow_le' _ (Nat.succ_pos b)
    convert(hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_1 (norm_nonneg x) h)
    simp
  linarith
#align normed_ring.tsum_geometric_of_norm_lt_1 NormedRing.tsum_geometric_of_norm_lt_1

/- warning: geom_series_mul_neg -> geom_series_mul_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (tsum.{u1, 0} R (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x i)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) x)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (tsum.{u1, 0} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x i)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align geom_series_mul_neg geom_series_mul_negₓ'. -/
theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 :=
  by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_right (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_0_of_norm_lt_1 h)
  convert← this
  ext n
  rw [← geom_sum_mul_neg, Finset.sum_mul]
#align geom_series_mul_neg geom_series_mul_neg

/- warning: mul_neg_geom_series -> mul_neg_geom_series is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) x) (tsum.{u1, 0} R (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x i))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x) (tsum.{u1, 0} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) Nat (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x i))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_neg_geom_series mul_neg_geom_seriesₓ'. -/
theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : ((1 - x) * ∑' i : ℕ, x ^ i) = 1 :=
  by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_left (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_0_of_norm_lt_1 h)
  convert← this
  ext n
  rw [← mul_neg_geom_sum, Finset.mul_sum]
#align mul_neg_geom_series mul_neg_geom_series

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/


/- warning: summable_of_ratio_norm_eventually_le -> summable_of_ratio_norm_eventually_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))] {f : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))] {f : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_ratio_norm_eventually_le summable_of_ratio_norm_eventually_leₓ'. -/
theorem summable_of_ratio_norm_eventually_le {α : Type _} [SeminormedAddCommGroup α]
    [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr₁ : r < 1)
    (h : ∀ᶠ n in atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f :=
  by
  by_cases hr₀ : 0 ≤ r
  · rw [eventually_at_top] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine'
      summable_of_norm_bounded (fun n => ‖f N‖ * r ^ n)
        (Summable.mul_left _ <| summable_geometric_of_lt_1 hr₀ hr₁) fun n => _
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine' le_geom hr₀ n fun i _ => _
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
  · push_neg  at hr₀
    refine' summable_of_norm_bounded_eventually 0 summable_zero _
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [h]with _ hn
    by_contra' h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn <| mul_neg_of_neg_of_pos hr₀ h)
#align summable_of_ratio_norm_eventually_le summable_of_ratio_norm_eventually_le

/- warning: summable_of_ratio_test_tendsto_lt_one -> summable_of_ratio_test_tendsto_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))] {f : Nat -> α} {l : Real}, (LT.lt.{0} Real Real.hasLt l (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => Ne.{succ u1} α (f n) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α _inst_1)))))))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))] {f : Nat -> α} {l : Real}, (LT.lt.{0} Real Real.instLTReal l (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => Ne.{succ u1} α (f n) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1))))))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α _inst_1) (f n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_ratio_test_tendsto_lt_one summable_of_ratio_test_tendsto_lt_oneₓ'. -/
theorem summable_of_ratio_test_tendsto_lt_one {α : Type _} [NormedAddCommGroup α] [CompleteSpace α]
    {f : ℕ → α} {l : ℝ} (hl₁ : l < 1) (hf : ∀ᶠ n in atTop, f n ≠ 0)
    (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable f :=
  by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine' summable_of_ratio_norm_eventually_le hr₁ _
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf]with _ _ h₁
  rwa [← div_le_iff (norm_pos_iff.mpr h₁)]
#align summable_of_ratio_test_tendsto_lt_one summable_of_ratio_test_tendsto_lt_one

/- warning: not_summable_of_ratio_norm_eventually_ge -> not_summable_of_ratio_norm_eventually_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {f : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) r) -> (Filter.Frequently.{0} Nat (fun (n : Nat) => Ne.{1} Real (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n))) (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) -> (Not (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {f : Nat -> α} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) r) -> (Filter.Frequently.{0} Nat (fun (n : Nat) => Ne.{1} Real (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n))) (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) -> (Not (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f))
Case conversion may be inaccurate. Consider using '#align not_summable_of_ratio_norm_eventually_ge not_summable_of_ratio_norm_eventually_geₓ'. -/
theorem not_summable_of_ratio_norm_eventually_ge {α : Type _} [SeminormedAddCommGroup α] {f : ℕ → α}
    {r : ℝ} (hr : 1 < r) (hf : ∃ᶠ n in atTop, ‖f n‖ ≠ 0)
    (h : ∀ᶠ n in atTop, r * ‖f n‖ ≤ ‖f (n + 1)‖) : ¬Summable f :=
  by
  rw [eventually_at_top] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_at_top] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine'
    mt Summable.tendsto_atTop_zero fun h' =>
      not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') _
  convert tendsto_atTop_of_geom_le _ hr _
  · refine' lt_of_le_of_ne (norm_nonneg _) _
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_app, zero_add] at h''
    exact hN h''.symm
  · intro i
    dsimp only [comp_app]
    convert hN₀ (i + N) (hNN₀.trans (N.le_add_left i)) using 3
    ac_rfl
#align not_summable_of_ratio_norm_eventually_ge not_summable_of_ratio_norm_eventually_ge

/- warning: not_summable_of_ratio_test_tendsto_gt_one -> not_summable_of_ratio_test_tendsto_gt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {f : Nat -> α} {l : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) l) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (f n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Not (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] {f : Nat -> α} {l : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) l) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (f n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Not (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (SeminormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α _inst_1))) f))
Case conversion may be inaccurate. Consider using '#align not_summable_of_ratio_test_tendsto_gt_one not_summable_of_ratio_test_tendsto_gt_oneₓ'. -/
theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type _} [SeminormedAddCommGroup α]
    {f : ℕ → α} {l : ℝ} (hl : 1 < l) (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f :=
  by
  have key : ∀ᶠ n in at_top, ‖f n‖ ≠ 0 :=
    by
    filter_upwards [eventually_ge_of_tendsto_gt hl h]with _ hn hc
    rw [hc, div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine' not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key]with _ _ h₁
  rwa [← le_div_iff (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]
#align not_summable_of_ratio_test_tendsto_gt_one not_summable_of_ratio_test_tendsto_gt_one

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/- warning: monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded -> Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {b : Real} {f : Nat -> Real} {z : Nat -> E}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E (NormedAddCommGroup.toHasNorm.{u1} E _inst_1) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => z i))) b) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => SMul.smul.{0, u1} Real E (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2))))) (f i) (z i))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {b : Real} {f : Nat -> Real} {z : Nat -> E}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_1) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => z i))) b) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HSMul.hSMul.{0, u1, u1} Real E E (instHSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)))))) (f i) (z i))))
Case conversion may be inaccurate. Consider using '#align monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Monotone.cauchySeq_series_mul_of_tendsto_zero_of_boundedₓ'. -/
/-- **Dirichlet's Test** for monotone sequences. -/
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hgb : ∀ n, ‖∑ i in range n, z i‖ ≤ b) :
    CauchySeq fun n => ∑ i in range (n + 1), f i • z i :=
  by
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply
    (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
          ⟨b, eventually_map.mpr <| eventually_of_forall fun n => hgb <| n + 1⟩).CauchySeq.add
  refine' (cauchySeq_range_of_norm_bounded _ _ (fun n => _ : ∀ n, _ ≤ b * |f (n + 1) - f n|)).neg
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply real.uniform_continuous_const_mul.comp_cauchy_seq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (tendsto.cauchy_seq hf0).AddConst
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
#align monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded

/- warning: antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded -> Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {b : Real} {f : Nat -> Real} {z : Nat -> E}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} E (NormedAddCommGroup.toHasNorm.{u1} E _inst_1) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => z i))) b) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => SMul.smul.{0, u1} Real E (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2))))) (f i) (z i))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {b : Real} {f : Nat -> Real} {z : Nat -> E}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_1) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => z i))) b) -> (CauchySeq.{u1, 0} E Nat (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HSMul.hSMul.{0, u1, u1} Real E E (instHSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)))))) (f i) (z i))))
Case conversion may be inaccurate. Consider using '#align antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Antitone.cauchySeq_series_mul_of_tendsto_zero_of_boundedₓ'. -/
/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hzb : ∀ n, ‖∑ i in range n, z i‖ ≤ b) :
    CauchySeq fun n => ∑ i in range (n + 1), f i • z i :=
  by
  have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg <| hfa hab
  have hf0' : tendsto (fun n => -f n) at_top (𝓝 0) :=
    by
    convert hf0.neg
    norm_num
  convert(hfa'.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  funext
  simp
#align antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded

/- warning: norm_sum_neg_one_pow_le -> norm_sum_neg_one_pow_le is a dubious translation:
lean 3 declaration is
  forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{0} Real Real.hasNorm (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) i))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{0} Real Real.norm (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) i))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align norm_sum_neg_one_pow_le norm_sum_neg_one_pow_leₓ'. -/
theorem norm_sum_neg_one_pow_le (n : ℕ) : ‖∑ i in range n, (-1 : ℝ) ^ i‖ ≤ 1 :=
  by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num
#align norm_sum_neg_one_pow_le norm_sum_neg_one_pow_le

/- warning: monotone.cauchy_seq_alternating_series_of_tendsto_zero -> Monotone.cauchySeq_alternating_series_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) i) (f i))))
but is expected to have type
  forall {f : Nat -> Real}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) i) (f i))))
Case conversion may be inaccurate. Consider using '#align monotone.cauchy_seq_alternating_series_of_tendsto_zero Monotone.cauchySeq_alternating_series_of_tendsto_zeroₓ'. -/
/-- The **alternating series test** for monotone sequences.
See also `tendsto_alternating_series_of_monotone_tendsto_zero`. -/
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range (n + 1), (-1) ^ i * f i :=
  by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align monotone.cauchy_seq_alternating_series_of_tendsto_zero Monotone.cauchySeq_alternating_series_of_tendsto_zero

/- warning: monotone.tendsto_alternating_series_of_tendsto_zero -> Monotone.tendsto_alternating_series_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Exists.{1} Real (fun (l : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) i) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)))
but is expected to have type
  forall {f : Nat -> Real}, (Monotone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Exists.{1} Real (fun (l : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) i) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)))
Case conversion may be inaccurate. Consider using '#align monotone.tendsto_alternating_series_of_tendsto_zero Monotone.tendsto_alternating_series_of_tendsto_zeroₓ'. -/
/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0
#align monotone.tendsto_alternating_series_of_tendsto_zero Monotone.tendsto_alternating_series_of_tendsto_zero

/- warning: antitone.cauchy_seq_alternating_series_of_tendsto_zero -> Antitone.cauchySeq_alternating_series_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) i) (f i))))
but is expected to have type
  forall {f : Nat -> Real}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (CauchySeq.{0, 0} Real Nat (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) i) (f i))))
Case conversion may be inaccurate. Consider using '#align antitone.cauchy_seq_alternating_series_of_tendsto_zero Antitone.cauchySeq_alternating_series_of_tendsto_zeroₓ'. -/
/-- The **alternating series test** for antitone sequences.
See also `tendsto_alternating_series_of_antitone_tendsto_zero`. -/
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range (n + 1), (-1) ^ i * f i :=
  by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
#align antitone.cauchy_seq_alternating_series_of_tendsto_zero Antitone.cauchySeq_alternating_series_of_tendsto_zero

/- warning: antitone.tendsto_alternating_series_of_tendsto_zero -> Antitone.tendsto_alternating_series_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Real.preorder f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Exists.{1} Real (fun (l : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) i) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)))
but is expected to have type
  forall {f : Nat -> Real}, (Antitone.{0, 0} Nat Real (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Real.instPreorderReal f) -> (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Exists.{1} Real (fun (l : Real) => Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) i) (f i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)))
Case conversion may be inaccurate. Consider using '#align antitone.tendsto_alternating_series_of_tendsto_zero Antitone.tendsto_alternating_series_of_tendsto_zeroₓ'. -/
/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0
#align antitone.tendsto_alternating_series_of_tendsto_zero Antitone.tendsto_alternating_series_of_tendsto_zero

end

/-!
### Factorial
-/


/- warning: real.summable_pow_div_factorial -> Real.summable_pow_div_factorial is a dubious translation:
lean 3 declaration is
  forall (x : Real), Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n)))
but is expected to have type
  forall (x : Real), Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n)))
Case conversion may be inaccurate. Consider using '#align real.summable_pow_div_factorial Real.summable_pow_div_factorialₓ'. -/
/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_div_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n => x ^ n / n ! : ℕ → ℝ) :=
  by
  -- We start with trivial extimates
  have A : (0 : ℝ) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices : ∀ n ≥ ⌊‖x‖⌋₊, ‖x ^ (n + 1) / (n + 1)!‖ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / ↑n !‖
  exact summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨⌊‖x‖⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ‖x ^ (n + 1) / (n + 1)!‖ = ‖x‖ / (n + 1) * ‖x ^ n / n !‖ := by
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, ← div_mul_div_comm, norm_mul, norm_div,
        Real.norm_coe_nat, Nat.cast_succ]
    _ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / n !‖ := by
      mono* with 0 ≤ ‖x ^ n / n !‖, 0 ≤ ‖x‖ <;> apply norm_nonneg
    
#align real.summable_pow_div_factorial Real.summable_pow_div_factorial

/- warning: real.tendsto_pow_div_factorial_at_top -> Real.tendsto_pow_div_factorial_atTop is a dubious translation:
lean 3 declaration is
  forall (x : Real), Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.factorial n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (x : Real), Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Nat.cast.{0} Real Real.natCast (Nat.factorial n))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_pow_div_factorial_at_top Real.tendsto_pow_div_factorial_atTopₓ'. -/
theorem Real.tendsto_pow_div_factorial_atTop (x : ℝ) :
    Tendsto (fun n => x ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_atTop_zero
#align real.tendsto_pow_div_factorial_at_top Real.tendsto_pow_div_factorial_atTop

