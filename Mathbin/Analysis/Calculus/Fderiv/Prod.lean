/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.prod
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Linear
import Mathbin.Analysis.Calculus.Fderiv.Comp

/-!
# Derivative of the cartesian product of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
cartesian products of functions, and functions into Pi-types.
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open Topology Classical NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type _} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter E}

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


section Prod

variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

/- warning: has_strict_fderiv_at.prod -> HasStrictFDerivAt.prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.prod HasStrictFDerivAt.prodₓ'. -/
protected theorem HasStrictFDerivAt.prod (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.prodLeft hf₂
#align has_strict_fderiv_at.prod HasStrictFDerivAt.prod

/- warning: has_fderiv_at_filter.prod -> HasFDerivAtFilter.prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.prod HasFDerivAtFilter.prodₓ'. -/
theorem HasFDerivAtFilter.prod (hf₁ : HasFDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x L :=
  hf₁.prodLeft hf₂
#align has_fderiv_at_filter.prod HasFDerivAtFilter.prod

/- warning: has_fderiv_within_at.prod -> HasFDerivWithinAt.prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.prod HasFDerivWithinAt.prodₓ'. -/
theorem HasFDerivWithinAt.prod (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') s x :=
  hf₁.Prod hf₂
#align has_fderiv_within_at.prod HasFDerivWithinAt.prod

/- warning: has_fderiv_at.prod -> HasFDerivAt.prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.prod HasFDerivAt.prodₓ'. -/
theorem HasFDerivAt.prod (hf₁ : HasFDerivAt f₁ f₁' x) (hf₂ : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.Prod hf₂
#align has_fderiv_at.prod HasFDerivAt.prod

/- warning: has_fderiv_at_prod_mk_left -> hasFDerivAt_prod_mk_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] (e₀ : E) (f₀ : F), HasFDerivAt.{u1, u2, max u2 u3} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (fun (e : E) => Prod.mk.{u2, u3} E F e f₀) (ContinuousLinearMap.inl.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) e₀
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] (e₀ : E) (f₀ : F), HasFDerivAt.{u3, u2, max u1 u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) (fun (e : E) => Prod.mk.{u2, u1} E F e f₀) (ContinuousLinearMap.inl.{u3, u2, u1} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)) e₀
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_prod_mk_left hasFDerivAt_prod_mk_leftₓ'. -/
theorem hasFDerivAt_prod_mk_left (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFDerivAt_id e₀).Prod (hasFDerivAt_const f₀ e₀)
#align has_fderiv_at_prod_mk_left hasFDerivAt_prod_mk_left

/- warning: has_fderiv_at_prod_mk_right -> hasFDerivAt_prod_mk_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] (e₀ : E) (f₀ : F), HasFDerivAt.{u1, u3, max u2 u3} 𝕜 _inst_1 F _inst_4 _inst_5 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) (fun (f : F) => Prod.mk.{u2, u3} E F e₀ f) (ContinuousLinearMap.inr.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) f₀
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] (e₀ : E) (f₀ : F), HasFDerivAt.{u3, u2, max u2 u1} 𝕜 _inst_1 F _inst_4 _inst_5 (Prod.{u1, u2} E F) (Prod.normedAddCommGroup.{u1, u2} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5) (fun (f : F) => Prod.mk.{u1, u2} E F e₀ f) (ContinuousLinearMap.inr.{u3, u1, u2} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_4)) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5)) f₀
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_prod_mk_right hasFDerivAt_prod_mk_rightₓ'. -/
theorem hasFDerivAt_prod_mk_right (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFDerivAt_const e₀ f₀).Prod (hasFDerivAt_id f₀)
#align has_fderiv_at_prod_mk_right hasFDerivAt_prod_mk_right

/- warning: differentiable_within_at.prod -> DifferentiableWithinAt.prod is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₁ : E -> F} {x : E} {s : Set.{u2} E} {f₂ : E -> G}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ s x) -> (DifferentiableWithinAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ s x) -> (DifferentiableWithinAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u3, u4} F G (f₁ x) (f₂ x)) s x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₁ : E -> F} {x : E} {s : Set.{u3} E} {f₂ : E -> G}, (DifferentiableWithinAt.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ s x) -> (DifferentiableWithinAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ s x) -> (DifferentiableWithinAt.{u4, u3, max u1 u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u2, u1} F G (f₁ x) (f₂ x)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.prod DifferentiableWithinAt.prodₓ'. -/
theorem DifferentiableWithinAt.prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.HasFDerivWithinAt.Prod hf₂.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.prod DifferentiableWithinAt.prod

/- warning: differentiable_at.prod -> DifferentiableAt.prod is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₁ : E -> F} {x : E} {f₂ : E -> G}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ x) -> (DifferentiableAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ x) -> (DifferentiableAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u3, u4} F G (f₁ x) (f₂ x)) x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₁ : E -> F} {x : E} {f₂ : E -> G}, (DifferentiableAt.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ x) -> (DifferentiableAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ x) -> (DifferentiableAt.{u4, u3, max u1 u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u2, u1} F G (f₁ x) (f₂ x)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.prod DifferentiableAt.prodₓ'. -/
@[simp]
theorem DifferentiableAt.prod (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.HasFDerivAt.Prod hf₂.HasFDerivAt).DifferentiableAt
#align differentiable_at.prod DifferentiableAt.prod

/- warning: differentiable_on.prod -> DifferentiableOn.prod is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₁ : E -> F} {s : Set.{u2} E} {f₂ : E -> G}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ s) -> (DifferentiableOn.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ s) -> (DifferentiableOn.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u3, u4} F G (f₁ x) (f₂ x)) s)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₁ : E -> F} {s : Set.{u3} E} {f₂ : E -> G}, (DifferentiableOn.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁ s) -> (DifferentiableOn.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂ s) -> (DifferentiableOn.{u4, u3, max u1 u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u2, u1} F G (f₁ x) (f₂ x)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.prod DifferentiableOn.prodₓ'. -/
theorem DifferentiableOn.prod (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx =>
  DifferentiableWithinAt.prod (hf₁ x hx) (hf₂ x hx)
#align differentiable_on.prod DifferentiableOn.prod

/- warning: differentiable.prod -> Differentiable.prod is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₁ : E -> F} {f₂ : E -> G}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁) -> (Differentiable.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂) -> (Differentiable.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u3, u4} F G (f₁ x) (f₂ x)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₁ : E -> F} {f₂ : E -> G}, (Differentiable.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f₁) -> (Differentiable.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 f₂) -> (Differentiable.{u4, u3, max u1 u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) (fun (x : E) => Prod.mk.{u2, u1} F G (f₁ x) (f₂ x)))
Case conversion may be inaccurate. Consider using '#align differentiable.prod Differentiable.prodₓ'. -/
@[simp]
theorem Differentiable.prod (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x => DifferentiableAt.prod (hf₁ x) (hf₂ x)
#align differentiable.prod Differentiable.prod

/- warning: differentiable_at.fderiv_prod -> DifferentiableAt.fderiv_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.fderiv_prod DifferentiableAt.fderiv_prodₓ'. -/
theorem DifferentiableAt.fderiv_prod (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).Prod (fderiv 𝕜 f₂ x) :=
  (hf₁.HasFDerivAt.Prod hf₂.HasFDerivAt).fderiv
#align differentiable_at.fderiv_prod DifferentiableAt.fderiv_prod

/- warning: differentiable_at.fderiv_within_prod -> DifferentiableAt.fderivWithin_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.fderiv_within_prod DifferentiableAt.fderivWithin_prodₓ'. -/
theorem DifferentiableAt.fderivWithin_prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).Prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.HasFDerivWithinAt.Prod hf₂.HasFDerivWithinAt).fderivWithin hxs
#align differentiable_at.fderiv_within_prod DifferentiableAt.fderivWithin_prod

end Prod

section Fst

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

/- warning: has_strict_fderiv_at_fst -> hasStrictFDerivAt_fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, HasStrictFDerivAt.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u3} E F) (ContinuousLinearMap.fst.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {p : Prod.{u2, u1} E F}, HasStrictFDerivAt.{u3, max u2 u1, u2} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u1} E F) (ContinuousLinearMap.fst.{u3, u2, u1} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)) p
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at_fst hasStrictFDerivAt_fstₓ'. -/
theorem hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).HasStrictFDerivAt
#align has_strict_fderiv_at_fst hasStrictFDerivAt_fst

/- warning: has_strict_fderiv_at.fst -> HasStrictFDerivAt.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.fst HasStrictFDerivAt.fstₓ'. -/
protected theorem HasStrictFDerivAt.fst (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_fst.comp x h
#align has_strict_fderiv_at.fst HasStrictFDerivAt.fst

#print hasFDerivAtFilter_fst /-
theorem hasFDerivAtFilter_fst {L : Filter (E × F)} :
    HasFDerivAtFilter (@Prod.fst E F) (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).HasFDerivAtFilter
#align has_fderiv_at_filter_fst hasFDerivAtFilter_fst
-/

/- warning: has_fderiv_at_filter.fst -> HasFDerivAtFilter.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.fst HasFDerivAtFilter.fstₓ'. -/
protected theorem HasFDerivAtFilter.fst (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  hasFDerivAtFilter_fst.comp x h tendsto_map
#align has_fderiv_at_filter.fst HasFDerivAtFilter.fst

/- warning: has_fderiv_at_fst -> hasFDerivAt_fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, HasFDerivAt.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u3} E F) (ContinuousLinearMap.fst.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {p : Prod.{u2, u1} E F}, HasFDerivAt.{u3, max u2 u1, u2} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u1} E F) (ContinuousLinearMap.fst.{u3, u2, u1} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)) p
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_fst hasFDerivAt_fstₓ'. -/
theorem hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst
#align has_fderiv_at_fst hasFDerivAt_fst

/- warning: has_fderiv_at.fst -> HasFDerivAt.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.fst HasFDerivAt.fstₓ'. -/
protected theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst
#align has_fderiv_at.fst HasFDerivAt.fst

#print hasFDerivWithinAt_fst /-
theorem hasFDerivWithinAt_fst {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFDerivAtFilter_fst
#align has_fderiv_within_at_fst hasFDerivWithinAt_fst
-/

/- warning: has_fderiv_within_at.fst -> HasFDerivWithinAt.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.fst HasFDerivWithinAt.fstₓ'. -/
protected theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst
#align has_fderiv_within_at.fst HasFDerivWithinAt.fst

/- warning: differentiable_at_fst -> differentiableAt_fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, DifferentiableAt.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u3} E F) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {p : Prod.{u1, u2} E F}, DifferentiableAt.{u3, max u2 u1, u1} 𝕜 _inst_1 (Prod.{u1, u2} E F) (Prod.normedAddCommGroup.{u1, u2} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u1, u2} E F) p
Case conversion may be inaccurate. Consider using '#align differentiable_at_fst differentiableAt_fstₓ'. -/
theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFDerivAt_fst.DifferentiableAt
#align differentiable_at_fst differentiableAt_fst

/- warning: differentiable_at.fst -> DifferentiableAt.fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {x : E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u3, u4} F G (f₂ x)) x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {x : E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ x) -> (DifferentiableAt.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u2, u1} F G (f₂ x)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.fst DifferentiableAt.fstₓ'. -/
@[simp]
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h
#align differentiable_at.fst DifferentiableAt.fst

/- warning: differentiable_fst -> differentiable_fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], Differentiable.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u3} E F)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)], Differentiable.{u3, max u2 u1, u2} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u1} E F)
Case conversion may be inaccurate. Consider using '#align differentiable_fst differentiable_fstₓ'. -/
theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun x =>
  differentiableAt_fst
#align differentiable_fst differentiable_fst

/- warning: differentiable.fst -> Differentiable.fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₂ : E -> (Prod.{u3, u4} F G)}, (Differentiable.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u3, u4} F G (f₂ x)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₂ : E -> (Prod.{u2, u1} F G)}, (Differentiable.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂) -> (Differentiable.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u2, u1} F G (f₂ x)))
Case conversion may be inaccurate. Consider using '#align differentiable.fst Differentiable.fstₓ'. -/
@[simp]
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h
#align differentiable.fst Differentiable.fst

#print differentiableWithinAt_fst /-
theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.DifferentiableWithinAt
#align differentiable_within_at_fst differentiableWithinAt_fst
-/

/- warning: differentiable_within_at.fst -> DifferentiableWithinAt.fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {x : E} {s : Set.{u2} E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableWithinAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u3, u4} F G (f₂ x)) s x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {x : E} {s : Set.{u3} E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableWithinAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ s x) -> (DifferentiableWithinAt.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u2, u1} F G (f₂ x)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.fst DifferentiableWithinAt.fstₓ'. -/
protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiableWithinAt x h
#align differentiable_within_at.fst DifferentiableWithinAt.fst

#print differentiableOn_fst /-
theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.DifferentiableOn
#align differentiable_on_fst differentiableOn_fst
-/

/- warning: differentiable_on.fst -> DifferentiableOn.fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {s : Set.{u2} E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableOn.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u3, u4} F G (f₂ x)) s)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {s : Set.{u3} E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableOn.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ s) -> (DifferentiableOn.{u4, u3, u2} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => Prod.fst.{u2, u1} F G (f₂ x)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.fst DifferentiableOn.fstₓ'. -/
protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiableOn h
#align differentiable_on.fst DifferentiableOn.fst

/- warning: fderiv_fst -> fderiv_fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, Eq.{max (succ (max u2 u3)) (succ u2)} (ContinuousLinearMap.{u1, u1, max u2 u3, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u2, u3} E F) (UniformSpace.toTopologicalSpace.{max u2 u3} (Prod.{u2, u3} E F) (PseudoMetricSpace.toUniformSpace.{max u2 u3} (Prod.{u2, u3} E F) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u3} (Prod.{u2, u3} E F) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4))))) (AddCommGroup.toAddCommMonoid.{max u2 u3} (Prod.{u2, u3} E F) (NormedAddCommGroup.toAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, max u2 u3} 𝕜 (Prod.{u2, u3} E F) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4)) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)) (fderiv.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u2, u3} E F) p) (ContinuousLinearMap.fst.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {p : Prod.{u3, u2} E F}, Eq.{max (succ u3) (succ u2)} (ContinuousLinearMap.{u1, u1, max u2 u3, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u3, u2} E F) (UniformSpace.toTopologicalSpace.{max u2 u3} (Prod.{u3, u2} E F) (PseudoMetricSpace.toUniformSpace.{max u2 u3} (Prod.{u3, u2} E F) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u3} (Prod.{u3, u2} E F) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4))))) (AddCommGroup.toAddCommMonoid.{max u2 u3} (Prod.{u3, u2} E F) (NormedAddCommGroup.toAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) (NormedSpace.toModule.{u1, max u2 u3} 𝕜 (Prod.{u3, u2} E F) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4)) (Prod.normedSpace.{u1, u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3)) (fderiv.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5) E _inst_2 _inst_3 (Prod.fst.{u3, u2} E F) p) (ContinuousLinearMap.fst.{u1, u3, u2} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5))
Case conversion may be inaccurate. Consider using '#align fderiv_fst fderiv_fstₓ'. -/
theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFDerivAt_fst.fderiv
#align fderiv_fst fderiv_fst

/- warning: fderiv.fst -> fderiv.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv.fst fderiv.fstₓ'. -/
theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFDerivAt.fst.fderiv
#align fderiv.fst fderiv.fst

/- warning: fderiv_within_fst -> fderivWithin_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_fst fderivWithin_fstₓ'. -/
theorem fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFDerivWithinAt_fst.fderivWithin hs
#align fderiv_within_fst fderivWithin_fst

/- warning: fderiv_within.fst -> fderivWithin.fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within.fst fderivWithin.fstₓ'. -/
theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFDerivWithinAt.fst.fderivWithin hs
#align fderiv_within.fst fderivWithin.fst

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

/- warning: has_strict_fderiv_at_snd -> hasStrictFDerivAt_snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, HasStrictFDerivAt.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u3} E F) (ContinuousLinearMap.snd.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {p : Prod.{u2, u1} E F}, HasStrictFDerivAt.{u3, max u2 u1, u1} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u1} E F) (ContinuousLinearMap.snd.{u3, u2, u1} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)) p
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at_snd hasStrictFDerivAt_sndₓ'. -/
theorem hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).HasStrictFDerivAt
#align has_strict_fderiv_at_snd hasStrictFDerivAt_snd

/- warning: has_strict_fderiv_at.snd -> HasStrictFDerivAt.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.snd HasStrictFDerivAt.sndₓ'. -/
protected theorem HasStrictFDerivAt.snd (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_snd.comp x h
#align has_strict_fderiv_at.snd HasStrictFDerivAt.snd

#print hasFDerivAtFilter_snd /-
theorem hasFDerivAtFilter_snd {L : Filter (E × F)} :
    HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).HasFDerivAtFilter
#align has_fderiv_at_filter_snd hasFDerivAtFilter_snd
-/

/- warning: has_fderiv_at_filter.snd -> HasFDerivAtFilter.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.snd HasFDerivAtFilter.sndₓ'. -/
protected theorem HasFDerivAtFilter.snd (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  hasFDerivAtFilter_snd.comp x h tendsto_map
#align has_fderiv_at_filter.snd HasFDerivAtFilter.snd

/- warning: has_fderiv_at_snd -> hasFDerivAt_snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, HasFDerivAt.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u3} E F) (ContinuousLinearMap.snd.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {p : Prod.{u2, u1} E F}, HasFDerivAt.{u3, max u2 u1, u1} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u1} E F) (ContinuousLinearMap.snd.{u3, u2, u1} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)) p
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_snd hasFDerivAt_sndₓ'. -/
theorem hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd
#align has_fderiv_at_snd hasFDerivAt_snd

/- warning: has_fderiv_at.snd -> HasFDerivAt.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.snd HasFDerivAt.sndₓ'. -/
protected theorem HasFDerivAt.snd (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd
#align has_fderiv_at.snd HasFDerivAt.snd

#print hasFDerivWithinAt_snd /-
theorem hasFDerivWithinAt_snd {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFDerivAtFilter_snd
#align has_fderiv_within_at_snd hasFDerivWithinAt_snd
-/

/- warning: has_fderiv_within_at.snd -> HasFDerivWithinAt.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.snd HasFDerivWithinAt.sndₓ'. -/
protected theorem HasFDerivWithinAt.snd (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd
#align has_fderiv_within_at.snd HasFDerivWithinAt.snd

/- warning: differentiable_at_snd -> differentiableAt_snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, DifferentiableAt.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u3} E F) p
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {p : Prod.{u1, u2} E F}, DifferentiableAt.{u3, max u2 u1, u2} 𝕜 _inst_1 (Prod.{u1, u2} E F) (Prod.normedAddCommGroup.{u1, u2} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u1, u2} E F) p
Case conversion may be inaccurate. Consider using '#align differentiable_at_snd differentiableAt_sndₓ'. -/
theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFDerivAt_snd.DifferentiableAt
#align differentiable_at_snd differentiableAt_snd

/- warning: differentiable_at.snd -> DifferentiableAt.snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {x : E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ x) -> (DifferentiableAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u3, u4} F G (f₂ x)) x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {x : E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ x) -> (DifferentiableAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u2, u1} F G (f₂ x)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.snd DifferentiableAt.sndₓ'. -/
@[simp]
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h
#align differentiable_at.snd DifferentiableAt.snd

/- warning: differentiable_snd -> differentiable_snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], Differentiable.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u3} E F)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)], Differentiable.{u3, max u2 u1, u1} 𝕜 _inst_1 (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u1} E F)
Case conversion may be inaccurate. Consider using '#align differentiable_snd differentiable_sndₓ'. -/
theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun x =>
  differentiableAt_snd
#align differentiable_snd differentiable_snd

/- warning: differentiable.snd -> Differentiable.snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f₂ : E -> (Prod.{u3, u4} F G)}, (Differentiable.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂) -> (Differentiable.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u3, u4} F G (f₂ x)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f₂ : E -> (Prod.{u2, u1} F G)}, (Differentiable.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂) -> (Differentiable.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u2, u1} F G (f₂ x)))
Case conversion may be inaccurate. Consider using '#align differentiable.snd Differentiable.sndₓ'. -/
@[simp]
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h
#align differentiable.snd Differentiable.snd

#print differentiableWithinAt_snd /-
theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.DifferentiableWithinAt
#align differentiable_within_at_snd differentiableWithinAt_snd
-/

/- warning: differentiable_within_at.snd -> DifferentiableWithinAt.snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {x : E} {s : Set.{u2} E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableWithinAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ s x) -> (DifferentiableWithinAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u3, u4} F G (f₂ x)) s x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {x : E} {s : Set.{u3} E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableWithinAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ s x) -> (DifferentiableWithinAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u2, u1} F G (f₂ x)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.snd DifferentiableWithinAt.sndₓ'. -/
protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h
#align differentiable_within_at.snd DifferentiableWithinAt.snd

#print differentiableOn_snd /-
theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.DifferentiableOn
#align differentiable_on_snd differentiableOn_snd
-/

/- warning: differentiable_on.snd -> DifferentiableOn.snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {s : Set.{u2} E} {f₂ : E -> (Prod.{u3, u4} F G)}, (DifferentiableOn.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u3, u4} F G) (Prod.normedAddCommGroup.{u3, u4} F G _inst_4 _inst_6) (Prod.normedSpace.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7) f₂ s) -> (DifferentiableOn.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u3, u4} F G (f₂ x)) s)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {s : Set.{u3} E} {f₂ : E -> (Prod.{u2, u1} F G)}, (DifferentiableOn.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Prod.{u2, u1} F G) (Prod.normedAddCommGroup.{u2, u1} F G _inst_4 _inst_6) (Prod.normedSpace.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5 G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6) _inst_7) f₂ s) -> (DifferentiableOn.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => Prod.snd.{u2, u1} F G (f₂ x)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.snd DifferentiableOn.sndₓ'. -/
protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h
#align differentiable_on.snd DifferentiableOn.snd

/- warning: fderiv_snd -> fderiv_snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {p : Prod.{u2, u3} E F}, Eq.{max (succ (max u2 u3)) (succ u3)} (ContinuousLinearMap.{u1, u1, max u2 u3, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u2, u3} E F) (UniformSpace.toTopologicalSpace.{max u2 u3} (Prod.{u2, u3} E F) (PseudoMetricSpace.toUniformSpace.{max u2 u3} (Prod.{u2, u3} E F) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u3} (Prod.{u2, u3} E F) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4))))) (AddCommGroup.toAddCommMonoid.{max u2 u3} (Prod.{u2, u3} E F) (NormedAddCommGroup.toAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, max u2 u3} 𝕜 (Prod.{u2, u3} E F) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4)) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (fderiv.{u1, max u2 u3, u3} 𝕜 _inst_1 (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u2, u3} E F) p) (ContinuousLinearMap.snd.{u1, u2, u3} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {p : Prod.{u3, u2} E F}, Eq.{max (succ u3) (succ u2)} (ContinuousLinearMap.{u1, u1, max u2 u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u3, u2} E F) (UniformSpace.toTopologicalSpace.{max u2 u3} (Prod.{u3, u2} E F) (PseudoMetricSpace.toUniformSpace.{max u2 u3} (Prod.{u3, u2} E F) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u3} (Prod.{u3, u2} E F) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4))))) (AddCommGroup.toAddCommMonoid.{max u2 u3} (Prod.{u3, u2} E F) (NormedAddCommGroup.toAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_4)) (NormedSpace.toModule.{u1, max u2 u3} 𝕜 (Prod.{u3, u2} E F) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u2 u3} (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4)) (Prod.normedSpace.{u1, u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5)) (fderiv.{u1, max u2 u3, u2} 𝕜 _inst_1 (Prod.{u3, u2} E F) (Prod.normedAddCommGroup.{u3, u2} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5) F _inst_4 _inst_5 (Prod.snd.{u3, u2} E F) p) (ContinuousLinearMap.snd.{u1, u3, u2} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_4)) (NormedSpace.toModule.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4) _inst_5))
Case conversion may be inaccurate. Consider using '#align fderiv_snd fderiv_sndₓ'. -/
theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFDerivAt_snd.fderiv
#align fderiv_snd fderiv_snd

/- warning: fderiv.snd -> fderiv.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv.snd fderiv.sndₓ'. -/
theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFDerivAt.snd.fderiv
#align fderiv.snd fderiv.snd

/- warning: fderiv_within_snd -> fderivWithin_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_snd fderivWithin_sndₓ'. -/
theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFDerivWithinAt_snd.fderivWithin hs
#align fderiv_within_snd fderivWithin_snd

/- warning: fderiv_within.snd -> fderivWithin.snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within.snd fderivWithin.sndₓ'. -/
theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFDerivWithinAt.snd.fderivWithin hs
#align fderiv_within.snd fderivWithin.snd

end Snd

section Prod_map

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

/- warning: has_strict_fderiv_at.prod_map -> HasStrictFDerivAt.prodMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.prod_map HasStrictFDerivAt.prodMapₓ'. -/
protected theorem HasStrictFDerivAt.prodMap (hf : HasStrictFDerivAt f f' p.1)
    (hf₂ : HasStrictFDerivAt f₂ f₂' p.2) : HasStrictFDerivAt (Prod.map f f₂) (f'.Prod_map f₂') p :=
  (hf.comp p hasStrictFDerivAt_fst).Prod (hf₂.comp p hasStrictFDerivAt_snd)
#align has_strict_fderiv_at.prod_map HasStrictFDerivAt.prodMap

/- warning: has_fderiv_at.prod_map -> HasFDerivAt.prodMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.prod_map HasFDerivAt.prodMapₓ'. -/
protected theorem HasFDerivAt.prodMap (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2) :
    HasFDerivAt (Prod.map f f₂) (f'.Prod_map f₂') p :=
  (hf.comp p hasFDerivAt_fst).Prod (hf₂.comp p hasFDerivAt_snd)
#align has_fderiv_at.prod_map HasFDerivAt.prodMap

/- warning: differentiable_at.prod_map -> DifferentiableAt.prod_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.prod_map DifferentiableAt.prod_mapₓ'. -/
@[simp]
protected theorem DifferentiableAt.prod_map (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).Prod (hf₂.comp p differentiableAt_snd)
#align differentiable_at.prod_map DifferentiableAt.prod_map

end Prod_map

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has_*fderiv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `λ x i, φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `λ x, Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type _} [Fintype ι] {F' : ι → Type _} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

/- warning: has_strict_fderiv_at_pi' -> hasStrictFDerivAt_pi' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at_pi' hasStrictFDerivAt_pi'ₓ'. -/
@[simp]
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  by
  simp only [HasStrictFDerivAt, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_strict_fderiv_at_pi' hasStrictFDerivAt_pi'

/- warning: has_strict_fderiv_at_pi -> hasStrictFDerivAt_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at_pi hasStrictFDerivAt_piₓ'. -/
@[simp]
theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'
#align has_strict_fderiv_at_pi hasStrictFDerivAt_pi

/- warning: has_fderiv_at_filter_pi' -> hasFDerivAtFilter_pi' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter_pi' hasFDerivAtFilter_pi'ₓ'. -/
@[simp]
theorem hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' x L ↔ ∀ i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L :=
  by
  simp only [HasFDerivAtFilter, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_fderiv_at_filter_pi' hasFDerivAtFilter_pi'

/- warning: has_fderiv_at_filter_pi -> hasFDerivAtFilter_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter_pi hasFDerivAtFilter_piₓ'. -/
theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔
      ∀ i, HasFDerivAtFilter (φ i) (φ' i) x L :=
  hasFDerivAtFilter_pi'
#align has_fderiv_at_filter_pi hasFDerivAtFilter_pi

/- warning: has_fderiv_at_pi' -> hasFDerivAt_pi' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_pi' hasFDerivAt_pi'ₓ'. -/
@[simp]
theorem hasFDerivAt_pi' :
    HasFDerivAt Φ Φ' x ↔ ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'
#align has_fderiv_at_pi' hasFDerivAt_pi'

/- warning: has_fderiv_at_pi -> hasFDerivAt_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_pi hasFDerivAt_piₓ'. -/
theorem hasFDerivAt_pi :
    HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFDerivAt (φ i) (φ' i) x :=
  hasFDerivAtFilter_pi
#align has_fderiv_at_pi hasFDerivAt_pi

/- warning: has_fderiv_within_at_pi' -> hasFDerivWithinAt_pi' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at_pi' hasFDerivWithinAt_pi'ₓ'. -/
@[simp]
theorem hasFDerivWithinAt_pi' :
    HasFDerivWithinAt Φ Φ' s x ↔ ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFDerivAtFilter_pi'
#align has_fderiv_within_at_pi' hasFDerivWithinAt_pi'

/- warning: has_fderiv_within_at_pi -> hasFDerivWithinAt_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at_pi hasFDerivWithinAt_piₓ'. -/
theorem hasFDerivWithinAt_pi :
    HasFDerivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFDerivWithinAt (φ i) (φ' i) s x :=
  hasFDerivAtFilter_pi
#align has_fderiv_within_at_pi hasFDerivWithinAt_pi

/- warning: differentiable_within_at_pi -> differentiableWithinAt_pi is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {s : Set.{u2} E} {ι : Type.{u3}} [_inst_10 : Fintype.{u3} ι] {F' : ι -> Type.{u4}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u4} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u1, u4} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableWithinAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u1, u3, u4} 𝕜 ι (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u4} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ s x) (forall (i : ι), DifferentiableWithinAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) s x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {x : E} {s : Set.{u3} E} {ι : Type.{u2}} [_inst_10 : Fintype.{u2} ι] {F' : ι -> Type.{u1}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u1} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u4, u1} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableWithinAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u2, u1} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u4, u2, u1} 𝕜 ι (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u1} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ s x) (forall (i : ι), DifferentiableWithinAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_pi differentiableWithinAt_piₓ'. -/
@[simp]
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.HasFDerivWithinAt i).DifferentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).HasFDerivWithinAt).DifferentiableWithinAt⟩
#align differentiable_within_at_pi differentiableWithinAt_pi

/- warning: differentiable_at_pi -> differentiableAt_pi is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {x : E} {ι : Type.{u3}} [_inst_10 : Fintype.{u3} ι] {F' : ι -> Type.{u4}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u4} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u1, u4} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableAt.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u1, u3, u4} 𝕜 ι (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u4} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ x) (forall (i : ι), DifferentiableAt.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) x)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {x : E} {ι : Type.{u2}} [_inst_10 : Fintype.{u2} ι] {F' : ι -> Type.{u1}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u1} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u4, u1} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableAt.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u2, u1} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u4, u2, u1} 𝕜 ι (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u1} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ x) (forall (i : ι), DifferentiableAt.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_pi differentiableAt_piₓ'. -/
@[simp]
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFDerivAt_pi'.1 h.HasFDerivAt i).DifferentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).HasFDerivAt).DifferentiableAt⟩
#align differentiable_at_pi differentiableAt_pi

/- warning: differentiable_on_pi -> differentiableOn_pi is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {s : Set.{u2} E} {ι : Type.{u3}} [_inst_10 : Fintype.{u3} ι] {F' : ι -> Type.{u4}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u4} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u1, u4} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableOn.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u1, u3, u4} 𝕜 ι (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u4} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ s) (forall (i : ι), DifferentiableOn.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) s)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {s : Set.{u3} E} {ι : Type.{u2}} [_inst_10 : Fintype.{u2} ι] {F' : ι -> Type.{u1}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u1} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u4, u1} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (DifferentiableOn.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u2, u1} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u4, u2, u1} 𝕜 ι (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u1} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ s) (forall (i : ι), DifferentiableOn.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_pi differentiableOn_piₓ'. -/
theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩
#align differentiable_on_pi differentiableOn_pi

/- warning: differentiable_pi -> differentiable_pi is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {ι : Type.{u3}} [_inst_10 : Fintype.{u3} ι] {F' : ι -> Type.{u4}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u4} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u1, u4} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (Differentiable.{u1, u2, max u3 u4} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u3, u4} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u1, u3, u4} 𝕜 ι (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u4} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ) (forall (i : ι), Differentiable.{u1, u2, u4} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {ι : Type.{u2}} [_inst_10 : Fintype.{u2} ι] {F' : ι -> Type.{u1}} [_inst_11 : forall (i : ι), NormedAddCommGroup.{u1} (F' i)] [_inst_12 : forall (i : ι), NormedSpace.{u4, u1} 𝕜 (F' i) (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (F' i) (_inst_11 i))] {Φ : E -> (forall (i : ι), F' i)}, Iff (Differentiable.{u4, u3, max u2 u1} 𝕜 _inst_1 E _inst_2 _inst_3 (forall (i : ι), F' i) (Pi.normedAddCommGroup.{u2, u1} ι (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => _inst_11 i)) (Pi.normedSpace.{u4, u2, u1} 𝕜 ι (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (fun (i : ι) => F' i) _inst_10 (fun (i : ι) => NormedAddCommGroup.toSeminormedAddCommGroup.{u1} ((fun (i : ι) => F' i) i) ((fun (i : ι) => _inst_11 i) i)) (fun (i : ι) => _inst_12 i)) Φ) (forall (i : ι), Differentiable.{u4, u3, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (F' i) (_inst_11 i) (_inst_12 i) (fun (x : E) => Φ x i))
Case conversion may be inaccurate. Consider using '#align differentiable_pi differentiable_piₓ'. -/
theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩
#align differentiable_pi differentiable_pi

/- warning: fderiv_within_pi -> fderivWithin_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_pi fderivWithin_piₓ'. -/
-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFDerivWithinAt_pi.2 fun i => (h i).HasFDerivWithinAt).fderivWithin hs
#align fderiv_within_pi fderivWithin_pi

/- warning: fderiv_pi -> fderiv_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_pi fderiv_piₓ'. -/
theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFDerivAt_pi.2 fun i => (h i).HasFDerivAt).fderiv
#align fderiv_pi fderiv_pi

end Pi

end CartesianProduct

end

