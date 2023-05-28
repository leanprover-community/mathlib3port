/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.add
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Linear
import Mathbin.Analysis.Calculus.Fderiv.Comp

/-!
# Additive operations on derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
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

section ConstSmul

variable {R : Type _} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/


/- warning: has_strict_fderiv_at.const_smul -> HasStrictFDerivAt.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.const_smul HasStrictFDerivAt.const_smulₓ'. -/
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).HasStrictFDerivAt.comp x h
#align has_strict_fderiv_at.const_smul HasStrictFDerivAt.const_smul

/- warning: has_fderiv_at_filter.const_smul -> HasFDerivAtFilter.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.const_smul HasFDerivAtFilter.const_smulₓ'. -/
theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' x L) (c : R) :
    HasFDerivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).HasFDerivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.const_smul HasFDerivAtFilter.const_smul

/- warning: has_fderiv_within_at.const_smul -> HasFDerivWithinAt.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.const_smul HasFDerivWithinAt.const_smulₓ'. -/
theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c
#align has_fderiv_within_at.const_smul HasFDerivWithinAt.const_smul

/- warning: has_fderiv_at.const_smul -> HasFDerivAt.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.const_smul HasFDerivAt.const_smulₓ'. -/
theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c
#align has_fderiv_at.const_smul HasFDerivAt.const_smul

/- warning: differentiable_within_at.const_smul -> DifferentiableWithinAt.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.const_smul DifferentiableWithinAt.const_smulₓ'. -/
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.HasFDerivWithinAt.const_smul c).DifferentiableWithinAt
#align differentiable_within_at.const_smul DifferentiableWithinAt.const_smul

/- warning: differentiable_at.const_smul -> DifferentiableAt.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_at.const_smul DifferentiableAt.const_smulₓ'. -/
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.HasFDerivAt.const_smul c).DifferentiableAt
#align differentiable_at.const_smul DifferentiableAt.const_smul

/- warning: differentiable_on.const_smul -> DifferentiableOn.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable_on.const_smul DifferentiableOn.const_smulₓ'. -/
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c
#align differentiable_on.const_smul DifferentiableOn.const_smul

/- warning: differentiable.const_smul -> Differentiable.const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align differentiable.const_smul Differentiable.const_smulₓ'. -/
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c
#align differentiable.const_smul Differentiable.const_smul

/- warning: fderiv_within_const_smul -> fderivWithin_const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_const_smul fderivWithin_const_smulₓ'. -/
theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.HasFDerivWithinAt.const_smul c).fderivWithin hxs
#align fderiv_within_const_smul fderivWithin_const_smul

/- warning: fderiv_const_smul -> fderiv_const_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_const_smul fderiv_const_smulₓ'. -/
theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.HasFDerivAt.const_smul c).fderiv
#align fderiv_const_smul fderiv_const_smul

end ConstSmul

section Add

/-! ### Derivative of the sum of two functions -/


/- warning: has_strict_fderiv_at.add -> HasStrictFDerivAt.add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.add HasStrictFDerivAt.addₓ'. -/
theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun y => f y + g y) (f' + g') x :=
  (hf.add hg).congr_left fun y =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_strict_fderiv_at.add HasStrictFDerivAt.add

/- warning: has_fderiv_at_filter.add -> HasFDerivAtFilter.add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.add HasFDerivAtFilter.addₓ'. -/
theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' x L) (hg : HasFDerivAtFilter g g' x L) :
    HasFDerivAtFilter (fun y => f y + g y) (f' + g') x L :=
  (hf.add hg).congr_left fun _ =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_fderiv_at_filter.add HasFDerivAtFilter.add

/- warning: has_fderiv_within_at.add -> HasFDerivWithinAt.add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.add HasFDerivWithinAt.addₓ'. -/
theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg
#align has_fderiv_within_at.add HasFDerivWithinAt.add

/- warning: has_fderiv_at.add -> HasFDerivAt.add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.add HasFDerivAt.addₓ'. -/
theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
#align has_fderiv_at.add HasFDerivAt.add

/- warning: differentiable_within_at.add -> DifferentiableWithinAt.add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) (g y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) (g y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.add DifferentiableWithinAt.addₓ'. -/
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.HasFDerivWithinAt.add hg.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.add DifferentiableWithinAt.add

/- warning: differentiable_at.add -> DifferentiableAt.add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) (g y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) (g y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.add DifferentiableAt.addₓ'. -/
@[simp]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.HasFDerivAt.add hg.HasFDerivAt).DifferentiableAt
#align differentiable_at.add DifferentiableAt.add

/- warning: differentiable_on.add -> DifferentiableOn.add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) (g y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) (g y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.add DifferentiableOn.addₓ'. -/
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)
#align differentiable_on.add DifferentiableOn.add

/- warning: differentiable.add -> Differentiable.add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) (g y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) (g y)))
Case conversion may be inaccurate. Consider using '#align differentiable.add Differentiable.addₓ'. -/
@[simp]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)
#align differentiable.add Differentiable.add

/- warning: fderiv_within_add -> fderivWithin_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_add fderivWithin_addₓ'. -/
theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.HasFDerivWithinAt.add hg.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_add fderivWithin_add

/- warning: fderiv_add -> fderiv_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_add fderiv_addₓ'. -/
theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.HasFDerivAt.add hg.HasFDerivAt).fderiv
#align fderiv_add fderiv_add

/- warning: has_strict_fderiv_at.add_const -> HasStrictFDerivAt.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) f' x)
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.add_const HasStrictFDerivAt.add_constₓ'. -/
theorem HasStrictFDerivAt.add_const (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun y => f y + c) f' x :=
  add_zero f' ▸ hf.add (hasStrictFDerivAt_const _ _)
#align has_strict_fderiv_at.add_const HasStrictFDerivAt.add_const

/- warning: has_fderiv_at_filter.add_const -> HasFDerivAtFilter.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) f' x L)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) f' x L)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.add_const HasFDerivAtFilter.add_constₓ'. -/
theorem HasFDerivAtFilter.add_const (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasFDerivAtFilter_const _ _ _)
#align has_fderiv_at_filter.add_const HasFDerivAtFilter.add_const

/- warning: has_fderiv_within_at.add_const -> HasFDerivWithinAt.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) f' s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) f' s x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.add_const HasFDerivWithinAt.add_constₓ'. -/
theorem HasFDerivWithinAt.add_const (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun y => f y + c) f' s x :=
  hf.AddConst c
#align has_fderiv_within_at.add_const HasFDerivWithinAt.add_const

/- warning: has_fderiv_at.add_const -> HasFDerivAt.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f x) c) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f x) c) f' x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.add_const HasFDerivAt.add_constₓ'. -/
theorem HasFDerivAt.add_const (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => f x + c) f' x :=
  hf.AddConst c
#align has_fderiv_at.add_const HasFDerivAt.add_const

/- warning: differentiable_within_at.add_const -> DifferentiableWithinAt.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.add_const DifferentiableWithinAt.add_constₓ'. -/
theorem DifferentiableWithinAt.add_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x :=
  (hf.HasFDerivWithinAt.AddConst c).DifferentiableWithinAt
#align differentiable_within_at.add_const DifferentiableWithinAt.add_const

/- warning: differentiable_within_at_add_const_iff -> differentiableWithinAt_add_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) s x) (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) s x) (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_add_const_iff differentiableWithinAt_add_const_iffₓ'. -/
@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_within_at_add_const_iff differentiableWithinAt_add_const_iff

/- warning: differentiable_at.add_const -> DifferentiableAt.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.add_const DifferentiableAt.add_constₓ'. -/
theorem DifferentiableAt.add_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x :=
  (hf.HasFDerivAt.AddConst c).DifferentiableAt
#align differentiable_at.add_const DifferentiableAt.add_const

/- warning: differentiable_at_add_const_iff -> differentiableAt_add_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) x) (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) x) (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_add_const_iff differentiableAt_add_const_iffₓ'. -/
@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_at_add_const_iff differentiableAt_add_const_iff

/- warning: differentiable_on.add_const -> DifferentiableOn.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.add_const DifferentiableOn.add_constₓ'. -/
theorem DifferentiableOn.add_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s := fun x hx => (hf x hx).AddConst c
#align differentiable_on.add_const DifferentiableOn.add_const

/- warning: differentiable_on_add_const_iff -> differentiableOn_add_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c) s) (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c) s) (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_add_const_iff differentiableOn_add_const_iffₓ'. -/
@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_on_add_const_iff differentiableOn_add_const_iff

/- warning: differentiable.add_const -> Differentiable.add_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c))
Case conversion may be inaccurate. Consider using '#align differentiable.add_const Differentiable.add_constₓ'. -/
theorem Differentiable.add_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y + c := fun x => (hf x).AddConst c
#align differentiable.add_const Differentiable.add_const

/- warning: differentiable_add_const_iff -> differentiable_add_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f y) c)) (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f y) c)) (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align differentiable_add_const_iff differentiable_add_const_iffₓ'. -/
@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_add_const_iff differentiable_add_const_iff

/- warning: fderiv_within_add_const -> fderivWithin_add_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_add_const fderivWithin_add_constₓ'. -/
theorem fderivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x :=
  if hf : DifferentiableWithinAt 𝕜 f s x then (hf.HasFDerivWithinAt.AddConst c).fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt]
    simpa
#align fderiv_within_add_const fderivWithin_add_const

/- warning: fderiv_add_const -> fderiv_add_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_add_const fderiv_add_constₓ'. -/
theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const uniqueDiffWithinAt_univ]
#align fderiv_add_const fderiv_add_const

/- warning: has_strict_fderiv_at.const_add -> HasStrictFDerivAt.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) f' x)
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.const_add HasStrictFDerivAt.const_addₓ'. -/
theorem HasStrictFDerivAt.const_add (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun y => c + f y) f' x :=
  zero_add f' ▸ (hasStrictFDerivAt_const _ _).add hf
#align has_strict_fderiv_at.const_add HasStrictFDerivAt.const_add

/- warning: has_fderiv_at_filter.const_add -> HasFDerivAtFilter.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) f' x L)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) f' x L)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.const_add HasFDerivAtFilter.const_addₓ'. -/
theorem HasFDerivAtFilter.const_add (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasFDerivAtFilter_const _ _ _).add hf
#align has_fderiv_at_filter.const_add HasFDerivAtFilter.const_add

/- warning: has_fderiv_within_at.const_add -> HasFDerivWithinAt.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) f' s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) f' s x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.const_add HasFDerivWithinAt.const_addₓ'. -/
theorem HasFDerivWithinAt.const_add (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c
#align has_fderiv_within_at.const_add HasFDerivWithinAt.const_add

/- warning: has_fderiv_at.const_add -> HasFDerivAt.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f x)) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f x)) f' x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.const_add HasFDerivAt.const_addₓ'. -/
theorem HasFDerivAt.const_add (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c + f x) f' x :=
  hf.const_add c
#align has_fderiv_at.const_add HasFDerivAt.const_add

/- warning: differentiable_within_at.const_add -> DifferentiableWithinAt.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.const_add DifferentiableWithinAt.const_addₓ'. -/
theorem DifferentiableWithinAt.const_add (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x :=
  (hf.HasFDerivWithinAt.const_add c).DifferentiableWithinAt
#align differentiable_within_at.const_add DifferentiableWithinAt.const_add

/- warning: differentiable_within_at_const_add_iff -> differentiableWithinAt_const_add_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) s x) (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) s x) (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_const_add_iff differentiableWithinAt_const_add_iffₓ'. -/
@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_within_at_const_add_iff differentiableWithinAt_const_add_iff

/- warning: differentiable_at.const_add -> DifferentiableAt.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.const_add DifferentiableAt.const_addₓ'. -/
theorem DifferentiableAt.const_add (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x :=
  (hf.HasFDerivAt.const_add c).DifferentiableAt
#align differentiable_at.const_add DifferentiableAt.const_add

/- warning: differentiable_at_const_add_iff -> differentiableAt_const_add_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) x) (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) x) (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_const_add_iff differentiableAt_const_add_iffₓ'. -/
@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_at_const_add_iff differentiableAt_const_add_iff

/- warning: differentiable_on.const_add -> DifferentiableOn.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.const_add DifferentiableOn.const_addₓ'. -/
theorem DifferentiableOn.const_add (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s := fun x hx => (hf x hx).const_add c
#align differentiable_on.const_add DifferentiableOn.const_add

/- warning: differentiable_on_const_add_iff -> differentiableOn_const_add_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)) s) (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)) s) (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_const_add_iff differentiableOn_const_add_iffₓ'. -/
@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_on_const_add_iff differentiableOn_const_add_iff

/- warning: differentiable.const_add -> Differentiable.const_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y)))
Case conversion may be inaccurate. Consider using '#align differentiable.const_add Differentiable.const_addₓ'. -/
theorem Differentiable.const_add (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c + f y := fun x => (hf x).const_add c
#align differentiable.const_add Differentiable.const_add

/- warning: differentiable_const_add_iff -> differentiable_const_add_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) c (f y))) (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) c (f y))) (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align differentiable_const_add_iff differentiable_const_add_iffₓ'. -/
@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_const_add_iff differentiable_const_add_iff

/- warning: fderiv_within_const_add -> fderivWithin_const_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_const_add fderivWithin_const_addₓ'. -/
theorem fderivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const hxs c
#align fderiv_within_const_add fderivWithin_const_add

/- warning: fderiv_const_add -> fderiv_const_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_const_add fderiv_const_addₓ'. -/
theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]
#align fderiv_const_add fderiv_const_add

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

/- warning: has_strict_fderiv_at.sum -> HasStrictFDerivAt.sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.sum HasStrictFDerivAt.sumₓ'. -/
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  by
  dsimp [HasStrictFDerivAt] at *
  convert is_o.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]
#align has_strict_fderiv_at.sum HasStrictFDerivAt.sum

/- warning: has_fderiv_at_filter.sum -> HasFDerivAtFilter.sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.sum HasFDerivAtFilter.sumₓ'. -/
theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) x L) :
    HasFDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L :=
  by
  dsimp [HasFDerivAtFilter] at *
  convert is_o.sum h
  simp [ContinuousLinearMap.sum_apply]
#align has_fderiv_at_filter.sum HasFDerivAtFilter.sum

/- warning: has_fderiv_within_at.sum -> HasFDerivWithinAt.sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.sum HasFDerivWithinAt.sumₓ'. -/
theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasFDerivAtFilter.sum h
#align has_fderiv_within_at.sum HasFDerivWithinAt.sum

/- warning: has_fderiv_at.sum -> HasFDerivAt.sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.sum HasFDerivAt.sumₓ'. -/
theorem HasFDerivAt.sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasFDerivAtFilter.sum h
#align has_fderiv_at.sum HasFDerivAt.sum

/- warning: differentiable_within_at.sum -> DifferentiableWithinAt.sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {x : E} {s : Set.{u2} E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i u) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) s x)) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u3, u4} F ι (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) u (fun (i : ι) => A i y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {x : E} {s : Set.{u2} E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i u) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) s x)) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u1, u4} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) u (fun (i : ι) => A i y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.sum DifferentiableWithinAt.sumₓ'. -/
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i in u, A i y) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.sum fun i hi => (h i hi).HasFDerivWithinAt
#align differentiable_within_at.sum DifferentiableWithinAt.sum

/- warning: differentiable_at.sum -> DifferentiableAt.sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {x : E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i u) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) x)) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u3, u4} F ι (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) u (fun (i : ι) => A i y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {x : E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i u) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) x)) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u1, u4} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) u (fun (i : ι) => A i y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.sum DifferentiableAt.sumₓ'. -/
@[simp]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.sum fun i hi => (h i hi).HasFDerivAt
#align differentiable_at.sum DifferentiableAt.sum

/- warning: differentiable_on.sum -> DifferentiableOn.sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {s : Set.{u2} E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i u) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) s)) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u3, u4} F ι (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) u (fun (i : ι) => A i y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {s : Set.{u2} E} {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i u) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i) s)) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u1, u4} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) u (fun (i : ι) => A i y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.sum DifferentiableOn.sumₓ'. -/
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx
#align differentiable_on.sum DifferentiableOn.sum

/- warning: differentiable.sum -> Differentiable.sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.Mem.{u4, u4} ι (Finset.{u4} ι) (Finset.hasMem.{u4} ι) i u) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i))) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u3, u4} F ι (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) u (fun (i : ι) => A i y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {ι : Type.{u4}} {u : Finset.{u4} ι} {A : ι -> E -> F}, (forall (i : ι), (Membership.mem.{u4, u4} ι (Finset.{u4} ι) (Finset.instMembershipFinset.{u4} ι) i u) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (A i))) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Finset.sum.{u1, u4} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) u (fun (i : ι) => A i y)))
Case conversion may be inaccurate. Consider using '#align differentiable.sum Differentiable.sumₓ'. -/
@[simp]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i in u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x
#align differentiable.sum Differentiable.sum

/- warning: fderiv_within_sum -> fderivWithin_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_sum fderivWithin_sumₓ'. -/
theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i in u, A i y) s x = ∑ i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_sum fderivWithin_sum

/- warning: fderiv_sum -> fderiv_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_sum fderiv_sumₓ'. -/
theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i in u, A i y) x = ∑ i in u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).HasFDerivAt).fderiv
#align fderiv_sum fderiv_sum

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


/- warning: has_strict_fderiv_at.neg -> HasStrictFDerivAt.neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.neg HasStrictFDerivAt.negₓ'. -/
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).HasStrictFDerivAt.comp x h
#align has_strict_fderiv_at.neg HasStrictFDerivAt.neg

/- warning: has_fderiv_at_filter.neg -> HasFDerivAtFilter.neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.neg HasFDerivAtFilter.negₓ'. -/
theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).HasFDerivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.neg HasFDerivAtFilter.neg

/- warning: has_fderiv_within_at.neg -> HasFDerivWithinAt.neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.neg HasFDerivWithinAt.negₓ'. -/
theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => -f x) (-f') s x :=
  h.neg
#align has_fderiv_within_at.neg HasFDerivWithinAt.neg

/- warning: has_fderiv_at.neg -> HasFDerivAt.neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.neg HasFDerivAt.negₓ'. -/
theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (fun x => -f x) (-f') x :=
  h.neg
#align has_fderiv_at.neg HasFDerivAt.neg

/- warning: differentiable_within_at.neg -> DifferentiableWithinAt.neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.neg DifferentiableWithinAt.negₓ'. -/
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.HasFDerivWithinAt.neg.DifferentiableWithinAt
#align differentiable_within_at.neg DifferentiableWithinAt.neg

/- warning: differentiable_within_at_neg_iff -> differentiableWithinAt_neg_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, Iff (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) s x) (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, Iff (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) s x) (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_neg_iff differentiableWithinAt_neg_iffₓ'. -/
@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_within_at_neg_iff differentiableWithinAt_neg_iff

/- warning: differentiable_at.neg -> DifferentiableAt.neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.neg DifferentiableAt.negₓ'. -/
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.HasFDerivAt.neg.DifferentiableAt
#align differentiable_at.neg DifferentiableAt.neg

/- warning: differentiable_at_neg_iff -> differentiableAt_neg_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, Iff (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) x) (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, Iff (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) x) (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_neg_iff differentiableAt_neg_iffₓ'. -/
@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_at_neg_iff differentiableAt_neg_iff

/- warning: differentiable_on.neg -> DifferentiableOn.neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.neg DifferentiableOn.negₓ'. -/
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg
#align differentiable_on.neg DifferentiableOn.neg

/- warning: differentiable_on_neg_iff -> differentiableOn_neg_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, Iff (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)) s) (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, Iff (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)) s) (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_neg_iff differentiableOn_neg_iffₓ'. -/
@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_on_neg_iff differentiableOn_neg_iff

/- warning: differentiable.neg -> Differentiable.neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y)))
Case conversion may be inaccurate. Consider using '#align differentiable.neg Differentiable.negₓ'. -/
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg
#align differentiable.neg Differentiable.neg

/- warning: differentiable_neg_iff -> differentiable_neg_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, Iff (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f y))) (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, Iff (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f y))) (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align differentiable_neg_iff differentiable_neg_iffₓ'. -/
@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_neg_iff differentiable_neg_iff

/- warning: fderiv_within_neg -> fderivWithin_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_neg fderivWithin_negₓ'. -/
theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then h.HasFDerivWithinAt.neg.fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa
#align fderiv_within_neg fderivWithin_neg

/- warning: fderiv_neg -> fderiv_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_neg fderiv_negₓ'. -/
@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_neg uniqueDiffWithinAt_univ]
#align fderiv_neg fderiv_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


/- warning: has_strict_fderiv_at.sub -> HasStrictFDerivAt.sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.sub HasStrictFDerivAt.subₓ'. -/
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_strict_fderiv_at.sub HasStrictFDerivAt.sub

/- warning: has_fderiv_at_filter.sub -> HasFDerivAtFilter.sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.sub HasFDerivAtFilter.subₓ'. -/
theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' x L) (hg : HasFDerivAtFilter g g' x L) :
    HasFDerivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_fderiv_at_filter.sub HasFDerivAtFilter.sub

/- warning: has_fderiv_within_at.sub -> HasFDerivWithinAt.sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.sub HasFDerivWithinAt.subₓ'. -/
theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg
#align has_fderiv_within_at.sub HasFDerivWithinAt.sub

/- warning: has_fderiv_at.sub -> HasFDerivAt.sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.sub HasFDerivAt.subₓ'. -/
theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg
#align has_fderiv_at.sub HasFDerivAt.sub

/- warning: differentiable_within_at.sub -> DifferentiableWithinAt.sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s x) -> (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) (g y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s x) -> (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) (g y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.sub DifferentiableWithinAt.subₓ'. -/
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.HasFDerivWithinAt.sub hg.HasFDerivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.sub DifferentiableWithinAt.sub

/- warning: differentiable_at.sub -> DifferentiableAt.sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g x) -> (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) (g y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g x) -> (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) (g y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.sub DifferentiableAt.subₓ'. -/
@[simp]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.HasFDerivAt.sub hg.HasFDerivAt).DifferentiableAt
#align differentiable_at.sub DifferentiableAt.sub

/- warning: differentiable_on.sub -> DifferentiableOn.sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s) -> (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) (g y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g s) -> (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) (g y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.sub DifferentiableOn.subₓ'. -/
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)
#align differentiable_on.sub DifferentiableOn.sub

/- warning: differentiable.sub -> Differentiable.sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) (g y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) (g y)))
Case conversion may be inaccurate. Consider using '#align differentiable.sub Differentiable.subₓ'. -/
@[simp]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)
#align differentiable.sub Differentiable.sub

/- warning: fderiv_within_sub -> fderivWithin_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_sub fderivWithin_subₓ'. -/
theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.HasFDerivWithinAt.sub hg.HasFDerivWithinAt).fderivWithin hxs
#align fderiv_within_sub fderivWithin_sub

/- warning: fderiv_sub -> fderiv_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_sub fderiv_subₓ'. -/
theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.HasFDerivAt.sub hg.HasFDerivAt).fderiv
#align fderiv_sub fderiv_sub

/- warning: has_strict_fderiv_at.sub_const -> HasStrictFDerivAt.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f x) c) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasStrictFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f x) c) f' x)
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.sub_const HasStrictFDerivAt.sub_constₓ'. -/
theorem HasStrictFDerivAt.sub_const (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => f x - c) f' x := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_strict_fderiv_at.sub_const HasStrictFDerivAt.sub_const

/- warning: has_fderiv_at_filter.sub_const -> HasFDerivAtFilter.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f x) c) f' x L)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {L : Filter.{u2} E}, (HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x L) -> (forall (c : F), HasFDerivAtFilter.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f x) c) f' x L)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.sub_const HasFDerivAtFilter.sub_constₓ'. -/
theorem HasFDerivAtFilter.sub_const (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_fderiv_at_filter.sub_const HasFDerivAtFilter.sub_const

/- warning: has_fderiv_within_at.sub_const -> HasFDerivWithinAt.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f x) c) f' s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E} {s : Set.{u2} E}, (HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' s x) -> (forall (c : F), HasFDerivWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f x) c) f' s x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.sub_const HasFDerivWithinAt.sub_constₓ'. -/
theorem HasFDerivWithinAt.sub_const (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c
#align has_fderiv_within_at.sub_const HasFDerivWithinAt.sub_const

/- warning: has_fderiv_at.sub_const -> HasFDerivAt.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u1, u1, u2, u3} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f x) c) f' x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {f' : ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5)} {x : E}, (HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f f' x) -> (forall (c : F), HasFDerivAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f x) c) f' x)
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.sub_const HasFDerivAt.sub_constₓ'. -/
theorem HasFDerivAt.sub_const (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => f x - c) f' x :=
  hf.sub_const c
#align has_fderiv_at.sub_const HasFDerivAt.sub_const

/- warning: differentiable_within_at.sub_const -> DifferentiableWithinAt.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.sub_const DifferentiableWithinAt.sub_constₓ'. -/
theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.HasFDerivWithinAt.sub_const c).DifferentiableWithinAt
#align differentiable_within_at.sub_const DifferentiableWithinAt.sub_const

/- warning: differentiable_within_at_sub_const_iff -> differentiableWithinAt_sub_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) s x) (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) s x) (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_sub_const_iff differentiableWithinAt_sub_const_iffₓ'. -/
@[simp]
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]
#align differentiable_within_at_sub_const_iff differentiableWithinAt_sub_const_iff

/- warning: differentiable_at.sub_const -> DifferentiableAt.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.sub_const DifferentiableAt.sub_constₓ'. -/
theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.HasFDerivAt.sub_const c).DifferentiableAt
#align differentiable_at.sub_const DifferentiableAt.sub_const

/- warning: differentiable_at_sub_const_iff -> differentiableAt_sub_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) x) (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) x) (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_sub_const_iff differentiableAt_sub_const_iffₓ'. -/
@[simp]
theorem differentiableAt_sub_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_add_const_iff]
#align differentiable_at_sub_const_iff differentiableAt_sub_const_iff

/- warning: differentiable_on.sub_const -> DifferentiableOn.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.sub_const DifferentiableOn.sub_constₓ'. -/
theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c
#align differentiable_on.sub_const DifferentiableOn.sub_const

/- warning: differentiable_on_sub_const_iff -> differentiableOn_sub_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c) s) (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c) s) (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_sub_const_iff differentiableOn_sub_const_iffₓ'. -/
@[simp]
theorem differentiableOn_sub_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_add_const_iff]
#align differentiable_on_sub_const_iff differentiableOn_sub_const_iff

/- warning: differentiable.sub_const -> Differentiable.sub_const is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c))
Case conversion may be inaccurate. Consider using '#align differentiable.sub_const Differentiable.sub_constₓ'. -/
theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c
#align differentiable.sub_const Differentiable.sub_const

/- warning: differentiable_sub_const_iff -> differentiable_sub_const_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f y) c)) (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f y) c)) (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align differentiable_sub_const_iff differentiable_sub_const_iffₓ'. -/
@[simp]
theorem differentiable_sub_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y - c) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_add_const_iff]
#align differentiable_sub_const_iff differentiable_sub_const_iff

/- warning: fderiv_within_sub_const -> fderivWithin_sub_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_sub_const fderivWithin_sub_constₓ'. -/
theorem fderivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const hxs]
#align fderiv_within_sub_const fderivWithin_sub_const

/- warning: fderiv_sub_const -> fderiv_sub_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_sub_const fderiv_sub_constₓ'. -/
theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]
#align fderiv_sub_const fderiv_sub_const

/- warning: has_strict_fderiv_at.const_sub -> HasStrictFDerivAt.const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.const_sub HasStrictFDerivAt.const_subₓ'. -/
theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_strict_fderiv_at.const_sub HasStrictFDerivAt.const_sub

/- warning: has_fderiv_at_filter.const_sub -> HasFDerivAtFilter.const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter.const_sub HasFDerivAtFilter.const_subₓ'. -/
theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' x L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_fderiv_at_filter.const_sub HasFDerivAtFilter.const_sub

/- warning: has_fderiv_within_at.const_sub -> HasFDerivWithinAt.const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.const_sub HasFDerivWithinAt.const_subₓ'. -/
theorem HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c
#align has_fderiv_within_at.const_sub HasFDerivWithinAt.const_sub

/- warning: has_fderiv_at.const_sub -> HasFDerivAt.const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.const_sub HasFDerivAt.const_subₓ'. -/
theorem HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c
#align has_fderiv_at.const_sub HasFDerivAt.const_sub

/- warning: differentiable_within_at.const_sub -> DifferentiableWithinAt.const_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E}, (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x) -> (forall (c : F), DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at.const_sub DifferentiableWithinAt.const_subₓ'. -/
theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.HasFDerivWithinAt.const_sub c).DifferentiableWithinAt
#align differentiable_within_at.const_sub DifferentiableWithinAt.const_sub

/- warning: differentiable_within_at_const_sub_iff -> differentiableWithinAt_const_sub_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) s x) (DifferentiableWithinAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} {s : Set.{u2} E} (c : F), Iff (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) s x) (DifferentiableWithinAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s x)
Case conversion may be inaccurate. Consider using '#align differentiable_within_at_const_sub_iff differentiableWithinAt_const_sub_iffₓ'. -/
@[simp]
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]
#align differentiable_within_at_const_sub_iff differentiableWithinAt_const_sub_iff

/- warning: differentiable_at.const_sub -> DifferentiableAt.const_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E}, (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x) -> (forall (c : F), DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) x)
Case conversion may be inaccurate. Consider using '#align differentiable_at.const_sub DifferentiableAt.const_subₓ'. -/
theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.HasFDerivAt.const_sub c).DifferentiableAt
#align differentiable_at.const_sub DifferentiableAt.const_sub

/- warning: differentiable_at_const_sub_iff -> differentiableAt_const_sub_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) x) (DifferentiableAt.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {x : E} (c : F), Iff (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) x) (DifferentiableAt.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align differentiable_at_const_sub_iff differentiableAt_const_sub_iffₓ'. -/
@[simp]
theorem differentiableAt_const_sub_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x ↔ DifferentiableAt 𝕜 f x := by simp [sub_eq_add_neg]
#align differentiable_at_const_sub_iff differentiableAt_const_sub_iff

/- warning: differentiable_on.const_sub -> DifferentiableOn.const_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E}, (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s) -> (forall (c : F), DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) s)
Case conversion may be inaccurate. Consider using '#align differentiable_on.const_sub DifferentiableOn.const_subₓ'. -/
theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c
#align differentiable_on.const_sub DifferentiableOn.const_sub

/- warning: differentiable_on_const_sub_iff -> differentiableOn_const_sub_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)) s) (DifferentiableOn.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {s : Set.{u2} E} (c : F), Iff (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)) s) (DifferentiableOn.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f s)
Case conversion may be inaccurate. Consider using '#align differentiable_on_const_sub_iff differentiableOn_const_sub_iffₓ'. -/
@[simp]
theorem differentiableOn_const_sub_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s ↔ DifferentiableOn 𝕜 f s := by simp [sub_eq_add_neg]
#align differentiable_on_const_sub_iff differentiableOn_const_sub_iff

/- warning: differentiable.const_sub -> Differentiable.const_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (c : F), Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y)))
Case conversion may be inaccurate. Consider using '#align differentiable.const_sub Differentiable.const_subₓ'. -/
theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c
#align differentiable.const_sub Differentiable.const_sub

/- warning: differentiable_const_sub_iff -> differentiable_const_sub_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) c (f y))) (Differentiable.{u1, u2, u3} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (c : F), Iff (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (y : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) c (f y))) (Differentiable.{u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align differentiable_const_sub_iff differentiable_const_sub_iffₓ'. -/
@[simp]
theorem differentiable_const_sub_iff (c : F) :
    (Differentiable 𝕜 fun y => c - f y) ↔ Differentiable 𝕜 f := by simp [sub_eq_add_neg]
#align differentiable_const_sub_iff differentiable_const_sub_iff

/- warning: fderiv_within_const_sub -> fderivWithin_const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_within_const_sub fderivWithin_const_subₓ'. -/
theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_neg, hxs]
#align fderiv_within_const_sub fderivWithin_const_sub

/- warning: fderiv_const_sub -> fderiv_const_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fderiv_const_sub fderiv_const_subₓ'. -/
theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]
#align fderiv_const_sub fderiv_const_sub

end Sub

end

