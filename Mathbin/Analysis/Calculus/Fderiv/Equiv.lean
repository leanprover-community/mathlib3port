/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.equiv
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Linear
import Mathbin.Analysis.Calculus.Fderiv.Comp

/-!
# The derivative of a linear equivalence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous linear equivalences.
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

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable (iso : E ≃L[𝕜] F)

/- warning: continuous_linear_equiv.has_strict_fderiv_at -> ContinuousLinearEquiv.hasStrictFDerivAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.has_strict_fderiv_at ContinuousLinearEquiv.hasStrictFDerivAtₓ'. -/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.HasStrictFDerivAt
#align continuous_linear_equiv.has_strict_fderiv_at ContinuousLinearEquiv.hasStrictFDerivAt

/- warning: continuous_linear_equiv.has_fderiv_within_at -> ContinuousLinearEquiv.hasFDerivWithinAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.has_fderiv_within_at ContinuousLinearEquiv.hasFDerivWithinAtₓ'. -/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  iso.toContinuousLinearMap.HasFDerivWithinAt
#align continuous_linear_equiv.has_fderiv_within_at ContinuousLinearEquiv.hasFDerivWithinAt

/- warning: continuous_linear_equiv.has_fderiv_at -> ContinuousLinearEquiv.hasFDerivAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.has_fderiv_at ContinuousLinearEquiv.hasFDerivAtₓ'. -/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.HasFDerivAtFilter
#align continuous_linear_equiv.has_fderiv_at ContinuousLinearEquiv.hasFDerivAt

/- warning: continuous_linear_equiv.differentiable_at -> ContinuousLinearEquiv.differentiableAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.differentiable_at ContinuousLinearEquiv.differentiableAtₓ'. -/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.HasFDerivAt.DifferentiableAt
#align continuous_linear_equiv.differentiable_at ContinuousLinearEquiv.differentiableAt

/- warning: continuous_linear_equiv.differentiable_within_at -> ContinuousLinearEquiv.differentiableWithinAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.differentiable_within_at ContinuousLinearEquiv.differentiableWithinAtₓ'. -/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.DifferentiableAt.DifferentiableWithinAt
#align continuous_linear_equiv.differentiable_within_at ContinuousLinearEquiv.differentiableWithinAt

/- warning: continuous_linear_equiv.fderiv -> ContinuousLinearEquiv.fderiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.fderiv ContinuousLinearEquiv.fderivₓ'. -/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.HasFDerivAt.fderiv
#align continuous_linear_equiv.fderiv ContinuousLinearEquiv.fderiv

/- warning: continuous_linear_equiv.fderiv_within -> ContinuousLinearEquiv.fderivWithin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.fderiv_within ContinuousLinearEquiv.fderivWithinₓ'. -/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.toContinuousLinearMap.fderivWithin hxs
#align continuous_linear_equiv.fderiv_within ContinuousLinearEquiv.fderivWithin

/- warning: continuous_linear_equiv.differentiable -> ContinuousLinearEquiv.differentiable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.differentiable ContinuousLinearEquiv.differentiableₓ'. -/
protected theorem differentiable : Differentiable 𝕜 iso := fun x => iso.DifferentiableAt
#align continuous_linear_equiv.differentiable ContinuousLinearEquiv.differentiable

/- warning: continuous_linear_equiv.differentiable_on -> ContinuousLinearEquiv.differentiableOn is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.differentiable_on ContinuousLinearEquiv.differentiableOnₓ'. -/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.Differentiable.DifferentiableOn
#align continuous_linear_equiv.differentiable_on ContinuousLinearEquiv.differentiableOn

/- warning: continuous_linear_equiv.comp_differentiable_within_at_iff -> ContinuousLinearEquiv.comp_differentiableWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_differentiable_within_at_iff ContinuousLinearEquiv.comp_differentiableWithinAt_iffₓ'. -/
theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by
  refine'
    ⟨fun H => _, fun H => iso.differentiable.differentiable_at.comp_differentiable_within_at x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiable_at.comp_differentiable_within_at x H
  rwa [← Function.comp.assoc iso.symm iso f, iso.symm_comp_self] at this
#align continuous_linear_equiv.comp_differentiable_within_at_iff ContinuousLinearEquiv.comp_differentiableWithinAt_iff

/- warning: continuous_linear_equiv.comp_differentiable_at_iff -> ContinuousLinearEquiv.comp_differentiableAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_differentiable_at_iff ContinuousLinearEquiv.comp_differentiableAt_iffₓ'. -/
theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← differentiableWithinAt_univ,
    iso.comp_differentiable_within_at_iff]
#align continuous_linear_equiv.comp_differentiable_at_iff ContinuousLinearEquiv.comp_differentiableAt_iff

/- warning: continuous_linear_equiv.comp_differentiable_on_iff -> ContinuousLinearEquiv.comp_differentiableOn_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_differentiable_on_iff ContinuousLinearEquiv.comp_differentiableOn_iffₓ'. -/
theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  by
  rw [DifferentiableOn, DifferentiableOn]
  simp only [iso.comp_differentiable_within_at_iff]
#align continuous_linear_equiv.comp_differentiable_on_iff ContinuousLinearEquiv.comp_differentiableOn_iff

/- warning: continuous_linear_equiv.comp_differentiable_iff -> ContinuousLinearEquiv.comp_differentiable_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_differentiable_iff ContinuousLinearEquiv.comp_differentiable_iffₓ'. -/
theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  by
  rw [← differentiableOn_univ, ← differentiableOn_univ]
  exact iso.comp_differentiable_on_iff
#align continuous_linear_equiv.comp_differentiable_iff ContinuousLinearEquiv.comp_differentiable_iff

/- warning: continuous_linear_equiv.comp_has_fderiv_within_at_iff -> ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_has_fderiv_within_at_iff ContinuousLinearEquiv.comp_hasFDerivWithinAt_iffₓ'. -/
theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x :=
  by
  refine' ⟨fun H => _, fun H => iso.has_fderiv_at.comp_has_fderiv_within_at x H⟩
  have A : f = iso.symm ∘ iso ∘ f := by rw [← Function.comp.assoc, iso.symm_comp_self]; rfl
  have B : f' = (iso.symm : F →L[𝕜] E).comp ((iso : E →L[𝕜] F).comp f') := by
    rw [← ContinuousLinearMap.comp_assoc, iso.coe_symm_comp_coe, ContinuousLinearMap.id_comp]
  rw [A, B]
  exact iso.symm.has_fderiv_at.comp_has_fderiv_within_at x H
#align continuous_linear_equiv.comp_has_fderiv_within_at_iff ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff

/- warning: continuous_linear_equiv.comp_has_strict_fderiv_at_iff -> ContinuousLinearEquiv.comp_hasStrictFDerivAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_has_strict_fderiv_at_iff ContinuousLinearEquiv.comp_hasStrictFDerivAt_iffₓ'. -/
theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x :=
  by
  refine' ⟨fun H => _, fun H => iso.has_strict_fderiv_at.comp x H⟩
  convert iso.symm.has_strict_fderiv_at.comp x H <;> ext z <;> apply (iso.symm_apply_apply _).symm
#align continuous_linear_equiv.comp_has_strict_fderiv_at_iff ContinuousLinearEquiv.comp_hasStrictFDerivAt_iff

/- warning: continuous_linear_equiv.comp_has_fderiv_at_iff -> ContinuousLinearEquiv.comp_hasFDerivAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_has_fderiv_at_iff ContinuousLinearEquiv.comp_hasFDerivAt_iffₓ'. -/
theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_has_fderiv_within_at_iff]
#align continuous_linear_equiv.comp_has_fderiv_at_iff ContinuousLinearEquiv.comp_hasFDerivAt_iff

/- warning: continuous_linear_equiv.comp_has_fderiv_within_at_iff' -> ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_has_fderiv_within_at_iff' ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff'ₓ'. -/
theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  by
  rw [← iso.comp_has_fderiv_within_at_iff, ← ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm,
    ContinuousLinearMap.id_comp]
#align continuous_linear_equiv.comp_has_fderiv_within_at_iff' ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff'

/- warning: continuous_linear_equiv.comp_has_fderiv_at_iff' -> ContinuousLinearEquiv.comp_hasFDerivAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_has_fderiv_at_iff' ContinuousLinearEquiv.comp_hasFDerivAt_iff'ₓ'. -/
theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_has_fderiv_within_at_iff']
#align continuous_linear_equiv.comp_has_fderiv_at_iff' ContinuousLinearEquiv.comp_hasFDerivAt_iff'

/- warning: continuous_linear_equiv.comp_fderiv_within -> ContinuousLinearEquiv.comp_fderivWithin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_fderiv_within ContinuousLinearEquiv.comp_fderivWithinₓ'. -/
theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv.comp_fderivWithin x iso.differentiable_at h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiable_within_at_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.comp_zero]
#align continuous_linear_equiv.comp_fderiv_within ContinuousLinearEquiv.comp_fderivWithin

/- warning: continuous_linear_equiv.comp_fderiv -> ContinuousLinearEquiv.comp_fderiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_fderiv ContinuousLinearEquiv.comp_fderivₓ'. -/
theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  by
  rw [← fderivWithin_univ, ← fderivWithin_univ]
  exact iso.comp_fderiv_within uniqueDiffWithinAt_univ
#align continuous_linear_equiv.comp_fderiv ContinuousLinearEquiv.comp_fderiv

/- warning: continuous_linear_equiv.comp_right_differentiable_within_at_iff -> ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_differentiable_within_at_iff ContinuousLinearEquiv.comp_right_differentiableWithinAt_iffₓ'. -/
theorem comp_right_differentiableWithinAt_iff {f : F → G} {s : Set F} {x : E} :
    DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWithinAt 𝕜 f s (iso x) :=
  by
  refine' ⟨fun H => _, fun H => H.comp x iso.differentiable_within_at (maps_to_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) :=
    by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiable_within_at
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp.assoc, iso.self_comp_symm] at this
#align continuous_linear_equiv.comp_right_differentiable_within_at_iff ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff

/- warning: continuous_linear_equiv.comp_right_differentiable_at_iff -> ContinuousLinearEquiv.comp_right_differentiableAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_differentiable_at_iff ContinuousLinearEquiv.comp_right_differentiableAt_iffₓ'. -/
theorem comp_right_differentiableAt_iff {f : F → G} {x : E} :
    DifferentiableAt 𝕜 (f ∘ iso) x ↔ DifferentiableAt 𝕜 f (iso x) := by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiable_within_at_iff,
    preimage_univ]
#align continuous_linear_equiv.comp_right_differentiable_at_iff ContinuousLinearEquiv.comp_right_differentiableAt_iff

/- warning: continuous_linear_equiv.comp_right_differentiable_on_iff -> ContinuousLinearEquiv.comp_right_differentiableOn_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_differentiable_on_iff ContinuousLinearEquiv.comp_right_differentiableOn_iffₓ'. -/
theorem comp_right_differentiableOn_iff {f : F → G} {s : Set F} :
    DifferentiableOn 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ DifferentiableOn 𝕜 f s :=
  by
  refine' ⟨fun H y hy => _, fun H y hy => iso.comp_right_differentiable_within_at_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y, ← comp_right_differentiable_within_at_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy
#align continuous_linear_equiv.comp_right_differentiable_on_iff ContinuousLinearEquiv.comp_right_differentiableOn_iff

/- warning: continuous_linear_equiv.comp_right_differentiable_iff -> ContinuousLinearEquiv.comp_right_differentiable_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_differentiable_iff ContinuousLinearEquiv.comp_right_differentiable_iffₓ'. -/
theorem comp_right_differentiable_iff {f : F → G} :
    Differentiable 𝕜 (f ∘ iso) ↔ Differentiable 𝕜 f := by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiable_on_iff, preimage_univ]
#align continuous_linear_equiv.comp_right_differentiable_iff ContinuousLinearEquiv.comp_right_differentiable_iff

/- warning: continuous_linear_equiv.comp_right_has_fderiv_within_at_iff -> ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_has_fderiv_within_at_iff ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iffₓ'. -/
theorem comp_right_hasFDerivWithinAt_iff {f : F → G} {s : Set F} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f f' s (iso x) :=
  by
  refine' ⟨fun H => _, fun H => H.comp x iso.has_fderiv_within_at (maps_to_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by rw [Function.comp.assoc, iso.self_comp_symm]; rfl
  have B : f' = (f'.comp (iso : E →L[𝕜] F)).comp (iso.symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm, ContinuousLinearMap.comp_id]
  rw [A, B]
  apply H.comp (iso x) iso.symm.has_fderiv_within_at
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy
#align continuous_linear_equiv.comp_right_has_fderiv_within_at_iff ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff

/- warning: continuous_linear_equiv.comp_right_has_fderiv_at_iff -> ContinuousLinearEquiv.comp_right_hasFDerivAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_has_fderiv_at_iff ContinuousLinearEquiv.comp_right_hasFDerivAt_iffₓ'. -/
theorem comp_right_hasFDerivAt_iff {f : F → G} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) x ↔ HasFDerivAt f f' (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_has_fderiv_within_at_iff, preimage_univ]
#align continuous_linear_equiv.comp_right_has_fderiv_at_iff ContinuousLinearEquiv.comp_right_hasFDerivAt_iff

/- warning: continuous_linear_equiv.comp_right_has_fderiv_within_at_iff' -> ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_has_fderiv_within_at_iff' ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff'ₓ'. -/
theorem comp_right_hasFDerivWithinAt_iff' {f : F → G} {s : Set F} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f (f'.comp (iso.symm : F →L[𝕜] E)) s (iso x) :=
  by
  rw [← iso.comp_right_has_fderiv_within_at_iff, ContinuousLinearMap.comp_assoc,
    iso.coe_symm_comp_coe, ContinuousLinearMap.comp_id]
#align continuous_linear_equiv.comp_right_has_fderiv_within_at_iff' ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff'

/- warning: continuous_linear_equiv.comp_right_has_fderiv_at_iff' -> ContinuousLinearEquiv.comp_right_hasFDerivAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_has_fderiv_at_iff' ContinuousLinearEquiv.comp_right_hasFDerivAt_iff'ₓ'. -/
theorem comp_right_hasFDerivAt_iff' {f : F → G} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) f' x ↔ HasFDerivAt f (f'.comp (iso.symm : F →L[𝕜] E)) (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_has_fderiv_within_at_iff', preimage_univ]
#align continuous_linear_equiv.comp_right_has_fderiv_at_iff' ContinuousLinearEquiv.comp_right_hasFDerivAt_iff'

/- warning: continuous_linear_equiv.comp_right_fderiv_within -> ContinuousLinearEquiv.comp_right_fderivWithin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_fderiv_within ContinuousLinearEquiv.comp_right_fderivWithinₓ'. -/
theorem comp_right_fderivWithin {f : F → G} {s : Set F} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) :
    fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x = (fderivWithin 𝕜 f s (iso x)).comp (iso : E →L[𝕜] F) :=
  by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_has_fderiv_within_at_iff.2 h.has_fderiv_within_at).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by intro h';
      exact h (iso.comp_right_differentiable_within_at_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.zero_comp]
#align continuous_linear_equiv.comp_right_fderiv_within ContinuousLinearEquiv.comp_right_fderivWithin

/- warning: continuous_linear_equiv.comp_right_fderiv -> ContinuousLinearEquiv.comp_right_fderiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.comp_right_fderiv ContinuousLinearEquiv.comp_right_fderivₓ'. -/
theorem comp_right_fderiv {f : F → G} {x : E} :
    fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F) :=
  by
  rw [← fderivWithin_univ, ← fderivWithin_univ, ← iso.comp_right_fderiv_within, preimage_univ]
  exact uniqueDiffWithinAt_univ
#align continuous_linear_equiv.comp_right_fderiv ContinuousLinearEquiv.comp_right_fderiv

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable (iso : E ≃ₗᵢ[𝕜] F)

/- warning: linear_isometry_equiv.has_strict_fderiv_at -> LinearIsometryEquiv.hasStrictFDerivAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.has_strict_fderiv_at LinearIsometryEquiv.hasStrictFDerivAtₓ'. -/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasStrictFDerivAt
#align linear_isometry_equiv.has_strict_fderiv_at LinearIsometryEquiv.hasStrictFDerivAt

/- warning: linear_isometry_equiv.has_fderiv_within_at -> LinearIsometryEquiv.hasFDerivWithinAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.has_fderiv_within_at LinearIsometryEquiv.hasFDerivWithinAtₓ'. -/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).HasFDerivWithinAt
#align linear_isometry_equiv.has_fderiv_within_at LinearIsometryEquiv.hasFDerivWithinAt

/- warning: linear_isometry_equiv.has_fderiv_at -> LinearIsometryEquiv.hasFDerivAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.has_fderiv_at LinearIsometryEquiv.hasFDerivAtₓ'. -/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasFDerivAt
#align linear_isometry_equiv.has_fderiv_at LinearIsometryEquiv.hasFDerivAt

/- warning: linear_isometry_equiv.differentiable_at -> LinearIsometryEquiv.differentiableAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.differentiable_at LinearIsometryEquiv.differentiableAtₓ'. -/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.HasFDerivAt.DifferentiableAt
#align linear_isometry_equiv.differentiable_at LinearIsometryEquiv.differentiableAt

/- warning: linear_isometry_equiv.differentiable_within_at -> LinearIsometryEquiv.differentiableWithinAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.differentiable_within_at LinearIsometryEquiv.differentiableWithinAtₓ'. -/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.DifferentiableAt.DifferentiableWithinAt
#align linear_isometry_equiv.differentiable_within_at LinearIsometryEquiv.differentiableWithinAt

/- warning: linear_isometry_equiv.fderiv -> LinearIsometryEquiv.fderiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.fderiv LinearIsometryEquiv.fderivₓ'. -/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.HasFDerivAt.fderiv
#align linear_isometry_equiv.fderiv LinearIsometryEquiv.fderiv

/- warning: linear_isometry_equiv.fderiv_within -> LinearIsometryEquiv.fderivWithin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.fderiv_within LinearIsometryEquiv.fderivWithinₓ'. -/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs
#align linear_isometry_equiv.fderiv_within LinearIsometryEquiv.fderivWithin

/- warning: linear_isometry_equiv.differentiable -> LinearIsometryEquiv.differentiable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.differentiable LinearIsometryEquiv.differentiableₓ'. -/
protected theorem differentiable : Differentiable 𝕜 iso := fun x => iso.DifferentiableAt
#align linear_isometry_equiv.differentiable LinearIsometryEquiv.differentiable

/- warning: linear_isometry_equiv.differentiable_on -> LinearIsometryEquiv.differentiableOn is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.differentiable_on LinearIsometryEquiv.differentiableOnₓ'. -/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.Differentiable.DifferentiableOn
#align linear_isometry_equiv.differentiable_on LinearIsometryEquiv.differentiableOn

/- warning: linear_isometry_equiv.comp_differentiable_within_at_iff -> LinearIsometryEquiv.comp_differentiableWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_differentiable_within_at_iff LinearIsometryEquiv.comp_differentiableWithinAt_iffₓ'. -/
theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff
#align linear_isometry_equiv.comp_differentiable_within_at_iff LinearIsometryEquiv.comp_differentiableWithinAt_iff

/- warning: linear_isometry_equiv.comp_differentiable_at_iff -> LinearIsometryEquiv.comp_differentiableAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_differentiable_at_iff LinearIsometryEquiv.comp_differentiableAt_iffₓ'. -/
theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiableAt_iff
#align linear_isometry_equiv.comp_differentiable_at_iff LinearIsometryEquiv.comp_differentiableAt_iff

/- warning: linear_isometry_equiv.comp_differentiable_on_iff -> LinearIsometryEquiv.comp_differentiableOn_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_differentiable_on_iff LinearIsometryEquiv.comp_differentiableOn_iffₓ'. -/
theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiableOn_iff
#align linear_isometry_equiv.comp_differentiable_on_iff LinearIsometryEquiv.comp_differentiableOn_iff

/- warning: linear_isometry_equiv.comp_differentiable_iff -> LinearIsometryEquiv.comp_differentiable_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_differentiable_iff LinearIsometryEquiv.comp_differentiable_iffₓ'. -/
theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff
#align linear_isometry_equiv.comp_differentiable_iff LinearIsometryEquiv.comp_differentiable_iff

/- warning: linear_isometry_equiv.comp_has_fderiv_within_at_iff -> LinearIsometryEquiv.comp_hasFDerivWithinAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_has_fderiv_within_at_iff LinearIsometryEquiv.comp_hasFDerivWithinAt_iffₓ'. -/
theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff
#align linear_isometry_equiv.comp_has_fderiv_within_at_iff LinearIsometryEquiv.comp_hasFDerivWithinAt_iff

/- warning: linear_isometry_equiv.comp_has_strict_fderiv_at_iff -> LinearIsometryEquiv.comp_hasStrictFDerivAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_has_strict_fderiv_at_iff LinearIsometryEquiv.comp_hasStrictFDerivAt_iffₓ'. -/
theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff
#align linear_isometry_equiv.comp_has_strict_fderiv_at_iff LinearIsometryEquiv.comp_hasStrictFDerivAt_iff

/- warning: linear_isometry_equiv.comp_has_fderiv_at_iff -> LinearIsometryEquiv.comp_hasFDerivAt_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_has_fderiv_at_iff LinearIsometryEquiv.comp_hasFDerivAt_iffₓ'. -/
theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff
#align linear_isometry_equiv.comp_has_fderiv_at_iff LinearIsometryEquiv.comp_hasFDerivAt_iff

/- warning: linear_isometry_equiv.comp_has_fderiv_within_at_iff' -> LinearIsometryEquiv.comp_hasFDerivWithinAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_has_fderiv_within_at_iff' LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'ₓ'. -/
theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'
#align linear_isometry_equiv.comp_has_fderiv_within_at_iff' LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'

/- warning: linear_isometry_equiv.comp_has_fderiv_at_iff' -> LinearIsometryEquiv.comp_hasFDerivAt_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_has_fderiv_at_iff' LinearIsometryEquiv.comp_hasFDerivAt_iff'ₓ'. -/
theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'
#align linear_isometry_equiv.comp_has_fderiv_at_iff' LinearIsometryEquiv.comp_hasFDerivAt_iff'

/- warning: linear_isometry_equiv.comp_fderiv_within -> LinearIsometryEquiv.comp_fderivWithin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_fderiv_within LinearIsometryEquiv.comp_fderivWithinₓ'. -/
theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderivWithin hxs
#align linear_isometry_equiv.comp_fderiv_within LinearIsometryEquiv.comp_fderivWithin

/- warning: linear_isometry_equiv.comp_fderiv -> LinearIsometryEquiv.comp_fderiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.comp_fderiv LinearIsometryEquiv.comp_fderivₓ'. -/
theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv
#align linear_isometry_equiv.comp_fderiv LinearIsometryEquiv.comp_fderiv

end LinearIsometryEquiv

/- warning: has_strict_fderiv_at.of_local_left_inverse -> HasStrictFDerivAt.of_local_left_inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_strict_fderiv_at.of_local_left_inverse HasStrictFDerivAt.of_local_left_inverseₓ'. -/
/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) a :=
  by
  replace hg := hg.prod_map' hg
  replace hfg := hfg.prod_mk_nhds hfg
  have :
    (fun p : F × F => g p.1 - g p.2 - f'.symm (p.1 - p.2)) =O[𝓝 (a, a)] fun p : F × F =>
      f' (g p.1 - g p.2) - (p.1 - p.2) :=
    by
    refine' ((f'.symm : F →L[𝕜] E).isBigO_comp _ _).congr (fun x => _) fun _ => rfl
    simp
  refine' this.trans_is_o _; clear this
  refine'
    ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) (eventually_of_forall fun _ => rfl)).trans_isBigO
      _
  · rintro p ⟨hp1, hp2⟩
    simp [hp1, hp2]
  · refine'
      (hf.is_O_sub_rev.comp_tendsto hg).congr' (eventually_of_forall fun _ => rfl) (hfg.mono _)
    rintro p ⟨hp1, hp2⟩
    simp only [(· ∘ ·), hp1, hp2]
#align has_strict_fderiv_at.of_local_left_inverse HasStrictFDerivAt.of_local_left_inverse

/- warning: has_fderiv_at.of_local_left_inverse -> HasFDerivAt.of_local_left_inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.of_local_left_inverse HasFDerivAt.of_local_left_inverseₓ'. -/
/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFDerivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasFDerivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFDerivAt g (f'.symm : F →L[𝕜] E) a :=
  by
  have : (fun x : F => g x - g a - f'.symm (x - a)) =O[𝓝 a] fun x : F => f' (g x - g a) - (x - a) :=
    by
    refine' ((f'.symm : F →L[𝕜] E).isBigO_comp _ _).congr (fun x => _) fun _ => rfl
    simp
  refine' this.trans_is_o _; clear this
  refine'
    ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) (eventually_of_forall fun _ => rfl)).trans_isBigO
      _
  · rintro p hp
    simp [hp, hfg.self_of_nhds]
  · refine'
      ((hf.is_O_sub_rev f'.antilipschitz).comp_tendsto hg).congr'
        (eventually_of_forall fun _ => rfl) (hfg.mono _)
    rintro p hp
    simp only [(· ∘ ·), hp, hfg.self_of_nhds]
#align has_fderiv_at.of_local_left_inverse HasFDerivAt.of_local_left_inverse

/- warning: local_homeomorph.has_strict_fderiv_at_symm -> LocalHomeomorph.hasStrictFDerivAt_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align local_homeomorph.has_strict_fderiv_at_symm LocalHomeomorph.hasStrictFDerivAt_symmₓ'. -/
/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasStrictFDerivAt_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.target) (htff' : HasStrictFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasStrictFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) (f.eventually_right_inverse ha)
#align local_homeomorph.has_strict_fderiv_at_symm LocalHomeomorph.hasStrictFDerivAt_symm

/- warning: local_homeomorph.has_fderiv_at_symm -> LocalHomeomorph.hasFDerivAt_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align local_homeomorph.has_fderiv_at_symm LocalHomeomorph.hasFDerivAt_symmₓ'. -/
/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasFDerivAt_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.target) (htff' : HasFDerivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasFDerivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) (f.eventually_right_inverse ha)
#align local_homeomorph.has_fderiv_at_symm LocalHomeomorph.hasFDerivAt_symm

/- warning: has_fderiv_within_at.eventually_ne -> HasFDerivWithinAt.eventually_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.eventually_ne HasFDerivWithinAt.eventually_neₓ'. -/
theorem HasFDerivWithinAt.eventually_ne (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ f x :=
  by
  rw [nhdsWithin, diff_eq, ← inf_principal, ← inf_assoc, eventually_inf_principal]
  have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
    is_O_iff.2 <| hf'.imp fun C hC => eventually_of_forall fun z => hC _
  have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.trans_is_O A
  simpa [not_imp_not, sub_eq_zero] using (A.trans this.is_O_symm).eq_zero_imp
#align has_fderiv_within_at.eventually_ne HasFDerivWithinAt.eventually_ne

/- warning: has_fderiv_at.eventually_ne -> HasFDerivAt.eventually_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.eventually_ne HasFDerivAt.eventually_neₓ'. -/
theorem HasFDerivAt.eventually_ne (h : HasFDerivAt f f' x) (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  simpa only [compl_eq_univ_diff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'
#align has_fderiv_at.eventually_ne HasFDerivAt.eventually_ne

end

section

/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f : E → F} {f' : E →L[ℝ] F} {x : E}

/- warning: has_fderiv_at_filter_real_equiv -> has_fderiv_at_filter_real_equiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at_filter_real_equiv has_fderiv_at_filter_real_equivₓ'. -/
theorem has_fderiv_at_filter_real_equiv {L : Filter E} :
    Tendsto (fun x' : E => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
      Tendsto (fun x' : E => ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) :=
  by
  symm
  rw [tendsto_iff_norm_tendsto_zero]; refine' tendsto_congr fun x' => _
  have : ‖x' - x‖⁻¹ ≥ 0 := inv_nonneg.mpr (norm_nonneg _)
  simp [norm_smul, abs_of_nonneg this]
#align has_fderiv_at_filter_real_equiv has_fderiv_at_filter_real_equiv

/- warning: has_fderiv_at.lim_real -> HasFDerivAt.lim_real is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_at.lim_real HasFDerivAt.lim_realₓ'. -/
theorem HasFDerivAt.lim_real (hf : HasFDerivAt f f' x) (v : E) :
    Tendsto (fun c : ℝ => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v)) :=
  by
  apply hf.lim v
  rw [tendsto_at_top_at_top]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩
#align has_fderiv_at.lim_real HasFDerivAt.lim_real

end

section TangentCone

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F}

/- warning: has_fderiv_within_at.maps_to_tangent_cone -> HasFDerivWithinAt.mapsTo_tangent_cone is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.maps_to_tangent_cone HasFDerivWithinAt.mapsTo_tangent_coneₓ'. -/
/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
theorem HasFDerivWithinAt.mapsTo_tangent_cone {x : E} (h : HasFDerivWithinAt f f' s x) :
    MapsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x)) :=
  by
  rintro v ⟨c, d, dtop, clim, cdlim⟩
  refine'
    ⟨c, fun n => f (x + d n) - f x, mem_of_superset dtop _, clim, h.lim at_top dtop clim cdlim⟩
  simp (config := { contextual := true }) [-mem_image, mem_image_of_mem]
#align has_fderiv_within_at.maps_to_tangent_cone HasFDerivWithinAt.mapsTo_tangent_cone

/- warning: has_fderiv_within_at.unique_diff_within_at -> HasFDerivWithinAt.uniqueDiffWithinAt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.unique_diff_within_at HasFDerivWithinAt.uniqueDiffWithinAtₓ'. -/
/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt {x : E} (h : HasFDerivWithinAt f f' s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  by
  refine' ⟨h'.dense_of_maps_to f'.continuous hs.1 _, h.continuous_within_at.mem_closure_image hs.2⟩
  show
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) ≤
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'
  rw [Submodule.span_le]
  exact h.maps_to_tangent_cone.mono (subset.refl _) Submodule.subset_span
#align has_fderiv_within_at.unique_diff_within_at HasFDerivWithinAt.uniqueDiffWithinAt

/- warning: unique_diff_on.image -> UniqueDiffOn.image is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align unique_diff_on.image UniqueDiffOn.imageₓ'. -/
theorem UniqueDiffOn.image {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueDiffOn 𝕜 (f '' s) :=
  ball_image_iff.2 fun x hx => (hf' x hx).UniqueDiffWithinAt (hs x hx) (hd x hx)
#align unique_diff_on.image UniqueDiffOn.image

/- warning: has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv -> HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquivₓ'. -/
theorem HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv {x : E} (e' : E ≃L[𝕜] F)
    (h : HasFDerivWithinAt f (e' : E →L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.UniqueDiffWithinAt hs e'.Surjective.DenseRange
#align has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv

/- warning: continuous_linear_equiv.unique_diff_on_image -> ContinuousLinearEquiv.uniqueDiffOn_image is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.unique_diff_on_image ContinuousLinearEquiv.uniqueDiffOn_imageₓ'. -/
theorem ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun x _ => e.HasFDerivWithinAt) fun x hx => e.Surjective.DenseRange
#align continuous_linear_equiv.unique_diff_on_image ContinuousLinearEquiv.uniqueDiffOn_image

/- warning: continuous_linear_equiv.unique_diff_on_image_iff -> ContinuousLinearEquiv.uniqueDiffOn_image_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.unique_diff_on_image_iff ContinuousLinearEquiv.uniqueDiffOn_image_iffₓ'. -/
@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) :
    UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩
#align continuous_linear_equiv.unique_diff_on_image_iff ContinuousLinearEquiv.uniqueDiffOn_image_iff

/- warning: continuous_linear_equiv.unique_diff_on_preimage_iff -> ContinuousLinearEquiv.uniqueDiffOn_preimage_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.unique_diff_on_preimage_iff ContinuousLinearEquiv.uniqueDiffOn_preimage_iffₓ'. -/
@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) :
    UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s := by
  rw [← e.image_symm_eq_preimage, e.symm.unique_diff_on_image_iff]
#align continuous_linear_equiv.unique_diff_on_preimage_iff ContinuousLinearEquiv.uniqueDiffOn_preimage_iff

end TangentCone

