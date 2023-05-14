/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.prod
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Linear
import Mathbin.Analysis.Calculus.Fderiv.Comp

/-!
# Derivative of the cartesian product of functions

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

protected theorem HasStrictFderivAt.prod (hf₁ : HasStrictFderivAt f₁ f₁' x)
    (hf₂ : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.prodLeft hf₂
#align has_strict_fderiv_at.prod HasStrictFderivAt.prod

theorem HasFderivAtFilter.prod (hf₁ : HasFderivAtFilter f₁ f₁' x L)
    (hf₂ : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x L :=
  hf₁.prodLeft hf₂
#align has_fderiv_at_filter.prod HasFderivAtFilter.prod

theorem HasFderivWithinAt.prod (hf₁ : HasFderivWithinAt f₁ f₁' s x)
    (hf₂ : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') s x :=
  hf₁.Prod hf₂
#align has_fderiv_within_at.prod HasFderivWithinAt.prod

theorem HasFderivAt.prod (hf₁ : HasFderivAt f₁ f₁' x) (hf₂ : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.Prod hf₂
#align has_fderiv_at.prod HasFderivAt.prod

theorem hasFderivAt_prod_mk_left (e₀ : E) (f₀ : F) :
    HasFderivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFderivAt_id e₀).Prod (hasFderivAt_const f₀ e₀)
#align has_fderiv_at_prod_mk_left hasFderivAt_prod_mk_left

theorem hasFderivAt_prod_mk_right (e₀ : E) (f₀ : F) :
    HasFderivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFderivAt_const e₀ f₀).Prod (hasFderivAt_id f₀)
#align has_fderiv_at_prod_mk_right hasFderivAt_prod_mk_right

theorem DifferentiableWithinAt.prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.HasFderivWithinAt.Prod hf₂.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.prod DifferentiableWithinAt.prod

@[simp]
theorem DifferentiableAt.prod (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.HasFderivAt.Prod hf₂.HasFderivAt).DifferentiableAt
#align differentiable_at.prod DifferentiableAt.prod

theorem DifferentiableOn.prod (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx =>
  DifferentiableWithinAt.prod (hf₁ x hx) (hf₂ x hx)
#align differentiable_on.prod DifferentiableOn.prod

@[simp]
theorem Differentiable.prod (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x => DifferentiableAt.prod (hf₁ x) (hf₂ x)
#align differentiable.prod Differentiable.prod

theorem DifferentiableAt.fderiv_prod (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).Prod (fderiv 𝕜 f₂ x) :=
  (hf₁.HasFderivAt.Prod hf₂.HasFderivAt).fderiv
#align differentiable_at.fderiv_prod DifferentiableAt.fderiv_prod

theorem DifferentiableAt.fderivWithin_prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).Prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.HasFderivWithinAt.Prod hf₂.HasFderivWithinAt).fderivWithin hxs
#align differentiable_at.fderiv_within_prod DifferentiableAt.fderivWithin_prod

end Prod

section Fst

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

theorem hasStrictFderivAt_fst : HasStrictFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).HasStrictFderivAt
#align has_strict_fderiv_at_fst hasStrictFderivAt_fst

protected theorem HasStrictFderivAt.fst (h : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFderivAt_fst.comp x h
#align has_strict_fderiv_at.fst HasStrictFderivAt.fst

theorem hasFderivAtFilter_fst {L : Filter (E × F)} :
    HasFderivAtFilter (@Prod.fst E F) (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).HasFderivAtFilter
#align has_fderiv_at_filter_fst hasFderivAtFilter_fst

protected theorem HasFderivAtFilter.fst (h : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  hasFderivAtFilter_fst.comp x h tendsto_map
#align has_fderiv_at_filter.fst HasFderivAtFilter.fst

theorem hasFderivAt_fst : HasFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFderivAtFilter_fst
#align has_fderiv_at_fst hasFderivAt_fst

protected theorem HasFderivAt.fst (h : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst
#align has_fderiv_at.fst HasFderivAt.fst

theorem hasFderivWithinAt_fst {s : Set (E × F)} :
    HasFderivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFderivAtFilter_fst
#align has_fderiv_within_at_fst hasFderivWithinAt_fst

protected theorem HasFderivWithinAt.fst (h : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst
#align has_fderiv_within_at.fst HasFderivWithinAt.fst

theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFderivAt_fst.DifferentiableAt
#align differentiable_at_fst differentiableAt_fst

@[simp]
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h
#align differentiable_at.fst DifferentiableAt.fst

theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun x =>
  differentiableAt_fst
#align differentiable_fst differentiable_fst

@[simp]
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h
#align differentiable.fst Differentiable.fst

theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.DifferentiableWithinAt
#align differentiable_within_at_fst differentiableWithinAt_fst

protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiableWithinAt x h
#align differentiable_within_at.fst DifferentiableWithinAt.fst

theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.DifferentiableOn
#align differentiable_on_fst differentiableOn_fst

protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiableOn h
#align differentiable_on.fst DifferentiableOn.fst

theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFderivAt_fst.fderiv
#align fderiv_fst fderiv_fst

theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFderivAt.fst.fderiv
#align fderiv.fst fderiv.fst

theorem fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFderivWithinAt_fst.fderivWithin hs
#align fderiv_within_fst fderivWithin_fst

theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFderivWithinAt.fst.fderivWithin hs
#align fderiv_within.fst fderivWithin.fst

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

theorem hasStrictFderivAt_snd : HasStrictFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).HasStrictFderivAt
#align has_strict_fderiv_at_snd hasStrictFderivAt_snd

protected theorem HasStrictFderivAt.snd (h : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  hasStrictFderivAt_snd.comp x h
#align has_strict_fderiv_at.snd HasStrictFderivAt.snd

theorem hasFderivAtFilter_snd {L : Filter (E × F)} :
    HasFderivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).HasFderivAtFilter
#align has_fderiv_at_filter_snd hasFderivAtFilter_snd

protected theorem HasFderivAtFilter.snd (h : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  hasFderivAtFilter_snd.comp x h tendsto_map
#align has_fderiv_at_filter.snd HasFderivAtFilter.snd

theorem hasFderivAt_snd : HasFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFderivAtFilter_snd
#align has_fderiv_at_snd hasFderivAt_snd

protected theorem HasFderivAt.snd (h : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd
#align has_fderiv_at.snd HasFderivAt.snd

theorem hasFderivWithinAt_snd {s : Set (E × F)} :
    HasFderivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFderivAtFilter_snd
#align has_fderiv_within_at_snd hasFderivWithinAt_snd

protected theorem HasFderivWithinAt.snd (h : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd
#align has_fderiv_within_at.snd HasFderivWithinAt.snd

theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFderivAt_snd.DifferentiableAt
#align differentiable_at_snd differentiableAt_snd

@[simp]
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h
#align differentiable_at.snd DifferentiableAt.snd

theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun x =>
  differentiableAt_snd
#align differentiable_snd differentiable_snd

@[simp]
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h
#align differentiable.snd Differentiable.snd

theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.DifferentiableWithinAt
#align differentiable_within_at_snd differentiableWithinAt_snd

protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h
#align differentiable_within_at.snd DifferentiableWithinAt.snd

theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.DifferentiableOn
#align differentiable_on_snd differentiableOn_snd

protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h
#align differentiable_on.snd DifferentiableOn.snd

theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFderivAt_snd.fderiv
#align fderiv_snd fderiv_snd

theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFderivAt.snd.fderiv
#align fderiv.snd fderiv.snd

theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFderivWithinAt_snd.fderivWithin hs
#align fderiv_within_snd fderivWithin_snd

theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFderivWithinAt.snd.fderivWithin hs
#align fderiv_within.snd fderivWithin.snd

end Snd

section Prod_map

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

protected theorem HasStrictFderivAt.prodMap (hf : HasStrictFderivAt f f' p.1)
    (hf₂ : HasStrictFderivAt f₂ f₂' p.2) : HasStrictFderivAt (Prod.map f f₂) (f'.Prod_map f₂') p :=
  (hf.comp p hasStrictFderivAt_fst).Prod (hf₂.comp p hasStrictFderivAt_snd)
#align has_strict_fderiv_at.prod_map HasStrictFderivAt.prodMap

protected theorem HasFderivAt.prodMap (hf : HasFderivAt f f' p.1) (hf₂ : HasFderivAt f₂ f₂' p.2) :
    HasFderivAt (Prod.map f f₂) (f'.Prod_map f₂') p :=
  (hf.comp p hasFderivAt_fst).Prod (hf₂.comp p hasFderivAt_snd)
#align has_fderiv_at.prod_map HasFderivAt.prodMap

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

@[simp]
theorem hasStrictFderivAt_pi' :
    HasStrictFderivAt Φ Φ' x ↔ ∀ i, HasStrictFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  by
  simp only [HasStrictFderivAt, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_strict_fderiv_at_pi' hasStrictFderivAt_pi'

@[simp]
theorem hasStrictFderivAt_pi :
    HasStrictFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFderivAt (φ i) (φ' i) x :=
  hasStrictFderivAt_pi'
#align has_strict_fderiv_at_pi hasStrictFderivAt_pi

@[simp]
theorem hasFderivAtFilter_pi' :
    HasFderivAtFilter Φ Φ' x L ↔ ∀ i, HasFderivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L :=
  by
  simp only [HasFderivAtFilter, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_fderiv_at_filter_pi' hasFderivAtFilter_pi'

theorem hasFderivAtFilter_pi :
    HasFderivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔
      ∀ i, HasFderivAtFilter (φ i) (φ' i) x L :=
  hasFderivAtFilter_pi'
#align has_fderiv_at_filter_pi hasFderivAtFilter_pi

@[simp]
theorem hasFderivAt_pi' :
    HasFderivAt Φ Φ' x ↔ ∀ i, HasFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFderivAtFilter_pi'
#align has_fderiv_at_pi' hasFderivAt_pi'

theorem hasFderivAt_pi :
    HasFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFderivAt (φ i) (φ' i) x :=
  hasFderivAtFilter_pi
#align has_fderiv_at_pi hasFderivAt_pi

@[simp]
theorem hasFderivWithinAt_pi' :
    HasFderivWithinAt Φ Φ' s x ↔ ∀ i, HasFderivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFderivAtFilter_pi'
#align has_fderiv_within_at_pi' hasFderivWithinAt_pi'

theorem hasFderivWithinAt_pi :
    HasFderivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFderivWithinAt (φ i) (φ' i) s x :=
  hasFderivAtFilter_pi
#align has_fderiv_within_at_pi hasFderivWithinAt_pi

@[simp]
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFderivWithinAt_pi'.1 h.HasFderivWithinAt i).DifferentiableWithinAt, fun h =>
    (hasFderivWithinAt_pi.2 fun i => (h i).HasFderivWithinAt).DifferentiableWithinAt⟩
#align differentiable_within_at_pi differentiableWithinAt_pi

@[simp]
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFderivAt_pi'.1 h.HasFderivAt i).DifferentiableAt, fun h =>
    (hasFderivAt_pi.2 fun i => (h i).HasFderivAt).DifferentiableAt⟩
#align differentiable_at_pi differentiableAt_pi

theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩
#align differentiable_on_pi differentiableOn_pi

theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩
#align differentiable_pi differentiable_pi

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFderivWithinAt_pi.2 fun i => (h i).HasFderivWithinAt).fderivWithin hs
#align fderiv_within_pi fderivWithin_pi

theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFderivAt_pi.2 fun i => (h i).HasFderivAt).fderiv
#align fderiv_pi fderiv_pi

end Pi

end CartesianProduct

end

