/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.instances.real_vector_space
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Instances.Rat

/-!
# Continuous additive maps are `ℝ`-linear

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/


variable {E : Type _} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {F : Type _} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] [T2Space F]

/- warning: map_real_smul -> map_real_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align map_real_smul map_real_smulₓ'. -/
/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
theorem map_real_smul {G} [AddMonoidHomClass G E F] (f : G) (hf : Continuous f) (c : ℝ) (x : E) :
    f (c • x) = c • f x :=
  suffices (fun c : ℝ => f (c • x)) = fun c : ℝ => c • f x from congr_fun this c
  Rat.denseEmbedding_coe_real.dense.equalizer (hf.comp <| continuous_id.smul continuous_const)
    (continuous_id.smul continuous_const) (funext fun r => map_rat_cast_smul f ℝ ℝ r x)
#align map_real_smul map_real_smul

namespace AddMonoidHom

/- warning: add_monoid_hom.to_real_linear_map -> AddMonoidHom.toRealLinearMap is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_3 : TopologicalSpace.{u1} E] [_inst_4 : ContinuousSMul.{0, u1} Real E (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real Real.semiring)))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real Real.semiring) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_3] {F : Type.{u2}} [_inst_5 : AddCommGroup.{u2} F] [_inst_6 : Module.{0, u2} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u2} F _inst_5)] [_inst_7 : TopologicalSpace.{u2} F] [_inst_8 : ContinuousSMul.{0, u2} Real F (SMulZeroClass.toHasSmul.{0, u2} Real F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_5)))) (SMulWithZero.toSmulZeroClass.{0, u2} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real Real.semiring)))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_5)))) (MulActionWithZero.toSMulWithZero.{0, u2} Real F (Semiring.toMonoidWithZero.{0} Real Real.semiring) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_5)))) (Module.toMulActionWithZero.{0, u2} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u2} F _inst_5) _inst_6)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_7] [_inst_9 : T2Space.{u2} F _inst_7] (f : AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))), (Continuous.{u1, u2} E F _inst_3 _inst_7 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) (fun (_x : AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) => E -> F) (AddMonoidHom.hasCoeToFun.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) f)) -> (ContinuousLinearMap.{0, 0, u1, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E _inst_3 (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) F _inst_7 (AddCommGroup.toAddCommMonoid.{u2} F _inst_5) _inst_2 _inst_6)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] [_inst_2 : Module.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1)] [_inst_3 : TopologicalSpace.{u1} E] [_inst_4 : ContinuousSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E _inst_1))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) _inst_2)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_3] {F : Type.{u2}} [_inst_5 : AddCommGroup.{u2} F] [_inst_6 : Module.{0, u2} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u2} F _inst_5)] [_inst_7 : TopologicalSpace.{u2} F] [_inst_8 : ContinuousSMul.{0, u2} Real F (SMulZeroClass.toSMul.{0, u2} Real F (NegZeroClass.toZero.{u2} F (SubNegZeroMonoid.toNegZeroClass.{u2} F (SubtractionMonoid.toSubNegZeroMonoid.{u2} F (SubtractionCommMonoid.toSubtractionMonoid.{u2} F (AddCommGroup.toDivisionAddCommMonoid.{u2} F _inst_5))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real F Real.instZeroReal (NegZeroClass.toZero.{u2} F (SubNegZeroMonoid.toNegZeroClass.{u2} F (SubtractionMonoid.toSubNegZeroMonoid.{u2} F (SubtractionCommMonoid.toSubtractionMonoid.{u2} F (AddCommGroup.toDivisionAddCommMonoid.{u2} F _inst_5))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} F (SubNegZeroMonoid.toNegZeroClass.{u2} F (SubtractionMonoid.toSubNegZeroMonoid.{u2} F (SubtractionCommMonoid.toSubtractionMonoid.{u2} F (AddCommGroup.toDivisionAddCommMonoid.{u2} F _inst_5))))) (Module.toMulActionWithZero.{0, u2} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u2} F _inst_5) _inst_6)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) _inst_7] [_inst_9 : T2Space.{u2} F _inst_7] (f : AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))), (Continuous.{u1, u2} E F _inst_3 _inst_7 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) E (fun (_x : E) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : E) => F) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) E F (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))) E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5)))) (AddMonoidHom.addMonoidHomClass.{u1, u2} E F (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_5))))))) f)) -> (ContinuousLinearMap.{0, 0, u1, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E _inst_3 (AddCommGroup.toAddCommMonoid.{u1} E _inst_1) F _inst_7 (AddCommGroup.toAddCommMonoid.{u2} F _inst_5) _inst_2 _inst_6)
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.to_real_linear_map AddMonoidHom.toRealLinearMapₓ'. -/
/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def toRealLinearMap (f : E →+ F) (hf : Continuous f) : E →L[ℝ] F :=
  ⟨{  toFun := f
      map_add' := f.map_add
      map_smul' := map_real_smul f hf }, hf⟩
#align add_monoid_hom.to_real_linear_map AddMonoidHom.toRealLinearMap

/- warning: add_monoid_hom.coe_to_real_linear_map -> AddMonoidHom.coe_toRealLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.coe_to_real_linear_map AddMonoidHom.coe_toRealLinearMapₓ'. -/
@[simp]
theorem coe_toRealLinearMap (f : E →+ F) (hf : Continuous f) : ⇑(f.toRealLinearMap hf) = f :=
  rfl
#align add_monoid_hom.coe_to_real_linear_map AddMonoidHom.coe_toRealLinearMap

end AddMonoidHom

/- warning: add_equiv.to_real_linear_equiv -> AddEquiv.toRealLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align add_equiv.to_real_linear_equiv AddEquiv.toRealLinearEquivₓ'. -/
/-- Reinterpret a continuous additive equivalence between two real vector spaces
as a continuous real-linear map. -/
def AddEquiv.toRealLinearEquiv (e : E ≃+ F) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    E ≃L[ℝ] F :=
  { e, e.toAddMonoidHom.toRealLinearMap h₁ with }
#align add_equiv.to_real_linear_equiv AddEquiv.toRealLinearEquiv

#print Real.isScalarTower /-
/-- A topological group carries at most one structure of a topological `ℝ`-module, so for any
topological `ℝ`-algebra `A` (e.g. `A = ℂ`) and any topological group that is both a topological
`ℝ`-module and a topological `A`-module, these structures agree. -/
instance (priority := 900) Real.isScalarTower [T2Space E] {A : Type _} [TopologicalSpace A] [Ring A]
    [Algebra ℝ A] [Module A E] [ContinuousSMul ℝ A] [ContinuousSMul A E] : IsScalarTower ℝ A E :=
  ⟨fun r x y => map_real_smul ((smulAddHom A E).flip y) (continuous_id.smul continuous_const) r x⟩
#align real.is_scalar_tower Real.isScalarTower
-/

