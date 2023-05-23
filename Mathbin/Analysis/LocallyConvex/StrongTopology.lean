/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.locally_convex.strong_topology
! leanprover-community/mathlib commit 47b12e7f2502f14001f891ca87fbae2b4acaed3f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.StrongTopology
import Mathbin.Topology.Algebra.Module.LocallyConvex

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Todo

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/


open Topology UniformConvergence

variable {R 𝕜₁ 𝕜₂ E F : Type _}

namespace ContinuousLinearMap

variable [AddCommGroup E] [TopologicalSpace E] [AddCommGroup F] [TopologicalSpace F]
  [TopologicalAddGroup F]

section General

variable (R)

variable [OrderedSemiring R]

variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}

variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

/- warning: continuous_linear_map.strong_topology.locally_convex_space -> ContinuousLinearMap.strongTopology.locallyConvexSpace is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {𝕜₁ : Type.{u2}} {𝕜₂ : Type.{u3}} {E : Type.{u4}} {F : Type.{u5}} [_inst_1 : AddCommGroup.{u4} E] [_inst_2 : TopologicalSpace.{u4} E] [_inst_3 : AddCommGroup.{u5} F] [_inst_4 : TopologicalSpace.{u5} F] [_inst_5 : TopologicalAddGroup.{u5} F _inst_4 (AddCommGroup.toAddGroup.{u5} F _inst_3)] [_inst_6 : OrderedSemiring.{u1} R] [_inst_7 : NormedField.{u2} 𝕜₁] [_inst_8 : NormedField.{u3} 𝕜₂] [_inst_9 : Module.{u2, u4} 𝕜₁ E (Ring.toSemiring.{u2} 𝕜₁ (NormedRing.toRing.{u2} 𝕜₁ (NormedCommRing.toNormedRing.{u2} 𝕜₁ (NormedField.toNormedCommRing.{u2} 𝕜₁ _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} E _inst_1)] [_inst_10 : Module.{u3, u5} 𝕜₂ F (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))) (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)] {σ : RingHom.{u2, u3} 𝕜₁ 𝕜₂ (NonAssocRing.toNonAssocSemiring.{u2} 𝕜₁ (Ring.toNonAssocRing.{u2} 𝕜₁ (NormedRing.toRing.{u2} 𝕜₁ (NormedCommRing.toNormedRing.{u2} 𝕜₁ (NormedField.toNormedCommRing.{u2} 𝕜₁ _inst_7))))) (NonAssocRing.toNonAssocSemiring.{u3} 𝕜₂ (Ring.toNonAssocRing.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))))} [_inst_11 : Module.{u1, u5} R F (OrderedSemiring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)] [_inst_12 : ContinuousConstSMul.{u1, u5} R F _inst_4 (SMulZeroClass.toHasSmul.{u1, u5} R F (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (SMulWithZero.toSmulZeroClass.{u1, u5} R F (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (OrderedSemiring.toSemiring.{u1} R _inst_6))))) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (MulActionWithZero.toSMulWithZero.{u1, u5} R F (Semiring.toMonoidWithZero.{u1} R (OrderedSemiring.toSemiring.{u1} R _inst_6)) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (Module.toMulActionWithZero.{u1, u5} R F (OrderedSemiring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_11))))] [_inst_13 : LocallyConvexSpace.{u1, u5} R F _inst_6 (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_11 _inst_4] [_inst_14 : SMulCommClass.{u3, u1, u5} 𝕜₂ R F (SMulZeroClass.toHasSmul.{u3, u5} 𝕜₂ F (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (SMulWithZero.toSmulZeroClass.{u3, u5} 𝕜₂ F (MulZeroClass.toHasZero.{u3} 𝕜₂ (MulZeroOneClass.toMulZeroClass.{u3} 𝕜₂ (MonoidWithZero.toMulZeroOneClass.{u3} 𝕜₂ (Semiring.toMonoidWithZero.{u3} 𝕜₂ (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))))))) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (MulActionWithZero.toSMulWithZero.{u3, u5} 𝕜₂ F (Semiring.toMonoidWithZero.{u3} 𝕜₂ (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8))))) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (Module.toMulActionWithZero.{u3, u5} 𝕜₂ F (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))) (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_10)))) (SMulZeroClass.toHasSmul.{u1, u5} R F (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (SMulWithZero.toSmulZeroClass.{u1, u5} R F (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (OrderedSemiring.toSemiring.{u1} R _inst_6))))) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (MulActionWithZero.toSMulWithZero.{u1, u5} R F (Semiring.toMonoidWithZero.{u1} R (OrderedSemiring.toSemiring.{u1} R _inst_6)) (AddZeroClass.toHasZero.{u5} F (AddMonoid.toAddZeroClass.{u5} F (AddCommMonoid.toAddMonoid.{u5} F (AddCommGroup.toAddCommMonoid.{u5} F _inst_3)))) (Module.toMulActionWithZero.{u1, u5} R F (OrderedSemiring.toSemiring.{u1} R _inst_6) (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_11))))] (𝔖 : Set.{u4} (Set.{u4} E)), (Set.Nonempty.{u4} (Set.{u4} E) 𝔖) -> (DirectedOn.{u4} (Set.{u4} E) (HasSubset.Subset.{u4} (Set.{u4} E) (Set.hasSubset.{u4} E)) 𝔖) -> (LocallyConvexSpace.{u1, max u4 u5} R (ContinuousLinearMap.{u2, u3, u4, u5} 𝕜₁ 𝕜₂ (Ring.toSemiring.{u2} 𝕜₁ (NormedRing.toRing.{u2} 𝕜₁ (NormedCommRing.toNormedRing.{u2} 𝕜₁ (NormedField.toNormedCommRing.{u2} 𝕜₁ _inst_7)))) (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))) σ E _inst_2 (AddCommGroup.toAddCommMonoid.{u4} E _inst_1) F _inst_4 (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_9 _inst_10) _inst_6 (ContinuousLinearMap.addCommMonoid.{u2, u3, u4, u5} 𝕜₁ 𝕜₂ (Ring.toSemiring.{u2} 𝕜₁ (NormedRing.toRing.{u2} 𝕜₁ (NormedCommRing.toNormedRing.{u2} 𝕜₁ (NormedField.toNormedCommRing.{u2} 𝕜₁ _inst_7)))) (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))) σ E _inst_2 (AddCommGroup.toAddCommMonoid.{u4} E _inst_1) F _inst_4 (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_9 _inst_10 (TopologicalAddGroup.to_continuousAdd.{u5} F _inst_4 (AddCommGroup.toAddGroup.{u5} F _inst_3) _inst_5)) (ContinuousLinearMap.module.{u2, u3, u1, u4, u5} 𝕜₁ 𝕜₂ R (Ring.toSemiring.{u2} 𝕜₁ (NormedRing.toRing.{u2} 𝕜₁ (NormedCommRing.toNormedRing.{u2} 𝕜₁ (NormedField.toNormedCommRing.{u2} 𝕜₁ _inst_7)))) (Ring.toSemiring.{u3} 𝕜₂ (NormedRing.toRing.{u3} 𝕜₂ (NormedCommRing.toNormedRing.{u3} 𝕜₂ (NormedField.toNormedCommRing.{u3} 𝕜₂ _inst_8)))) (OrderedSemiring.toSemiring.{u1} R _inst_6) E _inst_2 (AddCommGroup.toAddCommMonoid.{u4} E _inst_1) _inst_9 F _inst_4 (AddCommGroup.toAddCommMonoid.{u5} F _inst_3) _inst_10 _inst_11 _inst_14 _inst_12 σ (TopologicalAddGroup.to_continuousAdd.{u5} F _inst_4 (AddCommGroup.toAddGroup.{u5} F _inst_3) _inst_5)) (ContinuousLinearMap.strongTopology.{u2, u3, u4, u5} 𝕜₁ 𝕜₂ _inst_7 _inst_8 σ E F _inst_1 _inst_9 _inst_3 _inst_10 _inst_2 _inst_4 _inst_5 𝔖))
but is expected to have type
  forall (R : Type.{u4}) {𝕜₁ : Type.{u2}} {𝕜₂ : Type.{u1}} {E : Type.{u5}} {F : Type.{u3}} [_inst_1 : AddCommGroup.{u5} E] [_inst_2 : TopologicalSpace.{u5} E] [_inst_3 : AddCommGroup.{u3} F] [_inst_4 : TopologicalSpace.{u3} F] [_inst_5 : TopologicalAddGroup.{u3} F _inst_4 (AddCommGroup.toAddGroup.{u3} F _inst_3)] [_inst_6 : OrderedSemiring.{u4} R] [_inst_7 : NormedField.{u2} 𝕜₁] [_inst_8 : NormedField.{u1} 𝕜₂] [_inst_9 : Module.{u2, u5} 𝕜₁ E (DivisionSemiring.toSemiring.{u2} 𝕜₁ (Semifield.toDivisionSemiring.{u2} 𝕜₁ (Field.toSemifield.{u2} 𝕜₁ (NormedField.toField.{u2} 𝕜₁ _inst_7)))) (AddCommGroup.toAddCommMonoid.{u5} E _inst_1)] [_inst_10 : Module.{u1, u3} 𝕜₂ F (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3)] {σ : RingHom.{u2, u1} 𝕜₁ 𝕜₂ (Semiring.toNonAssocSemiring.{u2} 𝕜₁ (DivisionSemiring.toSemiring.{u2} 𝕜₁ (Semifield.toDivisionSemiring.{u2} 𝕜₁ (Field.toSemifield.{u2} 𝕜₁ (NormedField.toField.{u2} 𝕜₁ _inst_7))))) (Semiring.toNonAssocSemiring.{u1} 𝕜₂ (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))))} [_inst_11 : Module.{u4, u3} R F (OrderedSemiring.toSemiring.{u4} R _inst_6) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3)] [_inst_12 : ContinuousConstSMul.{u4, u3} R F _inst_4 (SMulZeroClass.toSMul.{u4, u3} R F (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (SMulWithZero.toSMulZeroClass.{u4, u3} R F (MonoidWithZero.toZero.{u4} R (Semiring.toMonoidWithZero.{u4} R (OrderedSemiring.toSemiring.{u4} R _inst_6))) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (MulActionWithZero.toSMulWithZero.{u4, u3} R F (Semiring.toMonoidWithZero.{u4} R (OrderedSemiring.toSemiring.{u4} R _inst_6)) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (Module.toMulActionWithZero.{u4, u3} R F (OrderedSemiring.toSemiring.{u4} R _inst_6) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_11))))] [_inst_13 : LocallyConvexSpace.{u4, u3} R F _inst_6 (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_11 _inst_4] [_inst_14 : SMulCommClass.{u1, u4, u3} 𝕜₂ R F (SMulZeroClass.toSMul.{u1, u3} 𝕜₂ F (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (SMulWithZero.toSMulZeroClass.{u1, u3} 𝕜₂ F (CommMonoidWithZero.toZero.{u1} 𝕜₂ (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜₂ (Semifield.toCommGroupWithZero.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8))))) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜₂ F (Semiring.toMonoidWithZero.{u1} 𝕜₂ (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8))))) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (Module.toMulActionWithZero.{u1, u3} 𝕜₂ F (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_10)))) (SMulZeroClass.toSMul.{u4, u3} R F (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (SMulWithZero.toSMulZeroClass.{u4, u3} R F (MonoidWithZero.toZero.{u4} R (Semiring.toMonoidWithZero.{u4} R (OrderedSemiring.toSemiring.{u4} R _inst_6))) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (MulActionWithZero.toSMulWithZero.{u4, u3} R F (Semiring.toMonoidWithZero.{u4} R (OrderedSemiring.toSemiring.{u4} R _inst_6)) (NegZeroClass.toZero.{u3} F (SubNegZeroMonoid.toNegZeroClass.{u3} F (SubtractionMonoid.toSubNegZeroMonoid.{u3} F (SubtractionCommMonoid.toSubtractionMonoid.{u3} F (AddCommGroup.toDivisionAddCommMonoid.{u3} F _inst_3))))) (Module.toMulActionWithZero.{u4, u3} R F (OrderedSemiring.toSemiring.{u4} R _inst_6) (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_11))))] (𝔖 : Set.{u5} (Set.{u5} E)), (Set.Nonempty.{u5} (Set.{u5} E) 𝔖) -> (DirectedOn.{u5} (Set.{u5} E) (fun (x._@.Mathlib.Analysis.LocallyConvex.StrongTopology._hyg.275 : Set.{u5} E) (x._@.Mathlib.Analysis.LocallyConvex.StrongTopology._hyg.277 : Set.{u5} E) => HasSubset.Subset.{u5} (Set.{u5} E) (Set.instHasSubsetSet.{u5} E) x._@.Mathlib.Analysis.LocallyConvex.StrongTopology._hyg.275 x._@.Mathlib.Analysis.LocallyConvex.StrongTopology._hyg.277) 𝔖) -> (LocallyConvexSpace.{u4, max u3 u5} R (ContinuousLinearMap.{u2, u1, u5, u3} 𝕜₁ 𝕜₂ (DivisionSemiring.toSemiring.{u2} 𝕜₁ (Semifield.toDivisionSemiring.{u2} 𝕜₁ (Field.toSemifield.{u2} 𝕜₁ (NormedField.toField.{u2} 𝕜₁ _inst_7)))) (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))) σ E _inst_2 (AddCommGroup.toAddCommMonoid.{u5} E _inst_1) F _inst_4 (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_9 _inst_10) _inst_6 (ContinuousLinearMap.addCommMonoid.{u2, u1, u5, u3} 𝕜₁ 𝕜₂ (DivisionSemiring.toSemiring.{u2} 𝕜₁ (Semifield.toDivisionSemiring.{u2} 𝕜₁ (Field.toSemifield.{u2} 𝕜₁ (NormedField.toField.{u2} 𝕜₁ _inst_7)))) (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))) σ E _inst_2 (AddCommGroup.toAddCommMonoid.{u5} E _inst_1) F _inst_4 (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_9 _inst_10 (TopologicalAddGroup.toContinuousAdd.{u3} F _inst_4 (AddCommGroup.toAddGroup.{u3} F _inst_3) _inst_5)) (ContinuousLinearMap.module.{u2, u1, u4, u5, u3} 𝕜₁ 𝕜₂ R (DivisionSemiring.toSemiring.{u2} 𝕜₁ (Semifield.toDivisionSemiring.{u2} 𝕜₁ (Field.toSemifield.{u2} 𝕜₁ (NormedField.toField.{u2} 𝕜₁ _inst_7)))) (DivisionSemiring.toSemiring.{u1} 𝕜₂ (Semifield.toDivisionSemiring.{u1} 𝕜₂ (Field.toSemifield.{u1} 𝕜₂ (NormedField.toField.{u1} 𝕜₂ _inst_8)))) (OrderedSemiring.toSemiring.{u4} R _inst_6) E _inst_2 (AddCommGroup.toAddCommMonoid.{u5} E _inst_1) _inst_9 F _inst_4 (AddCommGroup.toAddCommMonoid.{u3} F _inst_3) _inst_10 _inst_11 _inst_14 _inst_12 σ (TopologicalAddGroup.toContinuousAdd.{u3} F _inst_4 (AddCommGroup.toAddGroup.{u3} F _inst_3) _inst_5)) (ContinuousLinearMap.strongTopology.{u2, u1, u5, u3} 𝕜₁ 𝕜₂ _inst_7 _inst_8 σ E F _inst_1 _inst_9 _inst_3 _inst_10 _inst_2 _inst_4 _inst_5 𝔖))
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.strong_topology.locally_convex_space ContinuousLinearMap.strongTopology.locallyConvexSpaceₓ'. -/
theorem strongTopology.locallyConvexSpace (𝔖 : Set (Set E)) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    @LocallyConvexSpace R (E →SL[σ] F) _ _ _ (strongTopology σ F 𝔖) :=
  by
  letI : TopologicalSpace (E →SL[σ] F) := strong_topology σ F 𝔖
  haveI : TopologicalAddGroup (E →SL[σ] F) := strong_topology.topological_add_group _ _ _
  refine'
    LocallyConvexSpace.ofBasisZero _ _ _ _
      (strong_topology.has_basis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
        (LocallyConvexSpace.convex_basis_zero R F))
      _
  rintro ⟨S, V⟩ ⟨hS, hVmem, hVconvex⟩ f hf g hg a b ha hb hab x hx
  exact hVconvex (hf x hx) (hg x hx) ha hb hab
#align continuous_linear_map.strong_topology.locally_convex_space ContinuousLinearMap.strongTopology.locallyConvexSpace

end General

section BoundedSets

variable [OrderedSemiring R]

variable [NormedField 𝕜₁] [NormedField 𝕜₂] [Module 𝕜₁ E] [Module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}

variable [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

instance : LocallyConvexSpace R (E →SL[σ] F) :=
  strongTopology.locallyConvexSpace R _ ⟨∅, Bornology.isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)

end BoundedSets

end ContinuousLinearMap

