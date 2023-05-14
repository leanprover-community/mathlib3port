/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv.add
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Linear
import Mathbin.Analysis.Calculus.Fderiv.Comp

/-!
# Additive operations on derivatives

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


theorem HasStrictFderivAt.const_smul (h : HasStrictFderivAt f f' x) (c : R) :
    HasStrictFderivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).HasStrictFderivAt.comp x h
#align has_strict_fderiv_at.const_smul HasStrictFderivAt.const_smul

theorem HasFderivAtFilter.const_smul (h : HasFderivAtFilter f f' x L) (c : R) :
    HasFderivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).HasFderivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.const_smul HasFderivAtFilter.const_smul

theorem HasFderivWithinAt.const_smul (h : HasFderivWithinAt f f' s x) (c : R) :
    HasFderivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c
#align has_fderiv_within_at.const_smul HasFderivWithinAt.const_smul

theorem HasFderivAt.const_smul (h : HasFderivAt f f' x) (c : R) :
    HasFderivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c
#align has_fderiv_at.const_smul HasFderivAt.const_smul

theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.HasFderivWithinAt.const_smul c).DifferentiableWithinAt
#align differentiable_within_at.const_smul DifferentiableWithinAt.const_smul

theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.HasFderivAt.const_smul c).DifferentiableAt
#align differentiable_at.const_smul DifferentiableAt.const_smul

theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c
#align differentiable_on.const_smul DifferentiableOn.const_smul

theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c
#align differentiable.const_smul Differentiable.const_smul

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.HasFderivWithinAt.const_smul c).fderivWithin hxs
#align fderiv_within_const_smul fderivWithin_const_smul

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.HasFderivAt.const_smul c).fderiv
#align fderiv_const_smul fderiv_const_smul

end ConstSmul

section Add

/-! ### Derivative of the sum of two functions -/


theorem HasStrictFderivAt.add (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun y => f y + g y) (f' + g') x :=
  (hf.add hg).congr_left fun y =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_strict_fderiv_at.add HasStrictFderivAt.add

theorem HasFderivAtFilter.add (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
    HasFderivAtFilter (fun y => f y + g y) (f' + g') x L :=
  (hf.add hg).congr_left fun _ =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_fderiv_at_filter.add HasFderivAtFilter.add

theorem HasFderivWithinAt.add (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg
#align has_fderiv_within_at.add HasFderivWithinAt.add

theorem HasFderivAt.add (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
#align has_fderiv_at.add HasFderivAt.add

theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.HasFderivWithinAt.add hg.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.add DifferentiableWithinAt.add

@[simp]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.HasFderivAt.add hg.HasFderivAt).DifferentiableAt
#align differentiable_at.add DifferentiableAt.add

theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)
#align differentiable_on.add DifferentiableOn.add

@[simp]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)
#align differentiable.add Differentiable.add

theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.HasFderivWithinAt.add hg.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_add fderivWithin_add

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.HasFderivAt.add hg.HasFderivAt).fderiv
#align fderiv_add fderiv_add

theorem HasStrictFderivAt.add_const (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun y => f y + c) f' x :=
  add_zero f' ▸ hf.add (hasStrictFderivAt_const _ _)
#align has_strict_fderiv_at.add_const HasStrictFderivAt.add_const

theorem HasFderivAtFilter.add_const (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasFderivAtFilter_const _ _ _)
#align has_fderiv_at_filter.add_const HasFderivAtFilter.add_const

theorem HasFderivWithinAt.add_const (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun y => f y + c) f' s x :=
  hf.AddConst c
#align has_fderiv_within_at.add_const HasFderivWithinAt.add_const

theorem HasFderivAt.add_const (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => f x + c) f' x :=
  hf.AddConst c
#align has_fderiv_at.add_const HasFderivAt.add_const

theorem DifferentiableWithinAt.add_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x :=
  (hf.HasFderivWithinAt.AddConst c).DifferentiableWithinAt
#align differentiable_within_at.add_const DifferentiableWithinAt.add_const

@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_within_at_add_const_iff differentiableWithinAt_add_const_iff

theorem DifferentiableAt.add_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x :=
  (hf.HasFderivAt.AddConst c).DifferentiableAt
#align differentiable_at.add_const DifferentiableAt.add_const

@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_at_add_const_iff differentiableAt_add_const_iff

theorem DifferentiableOn.add_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s := fun x hx => (hf x hx).AddConst c
#align differentiable_on.add_const DifferentiableOn.add_const

@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_on_add_const_iff differentiableOn_add_const_iff

theorem Differentiable.add_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y + c := fun x => (hf x).AddConst c
#align differentiable.add_const Differentiable.add_const

@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_add_const_iff differentiable_add_const_iff

theorem fderivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x :=
  if hf : DifferentiableWithinAt 𝕜 f s x then (hf.HasFderivWithinAt.AddConst c).fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt]
    simpa
#align fderiv_within_add_const fderivWithin_add_const

theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const uniqueDiffWithinAt_univ]
#align fderiv_add_const fderiv_add_const

theorem HasStrictFderivAt.const_add (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun y => c + f y) f' x :=
  zero_add f' ▸ (hasStrictFderivAt_const _ _).add hf
#align has_strict_fderiv_at.const_add HasStrictFderivAt.const_add

theorem HasFderivAtFilter.const_add (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasFderivAtFilter_const _ _ _).add hf
#align has_fderiv_at_filter.const_add HasFderivAtFilter.const_add

theorem HasFderivWithinAt.const_add (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c
#align has_fderiv_within_at.const_add HasFderivWithinAt.const_add

theorem HasFderivAt.const_add (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => c + f x) f' x :=
  hf.const_add c
#align has_fderiv_at.const_add HasFderivAt.const_add

theorem DifferentiableWithinAt.const_add (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x :=
  (hf.HasFderivWithinAt.const_add c).DifferentiableWithinAt
#align differentiable_within_at.const_add DifferentiableWithinAt.const_add

@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_within_at_const_add_iff differentiableWithinAt_const_add_iff

theorem DifferentiableAt.const_add (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x :=
  (hf.HasFderivAt.const_add c).DifferentiableAt
#align differentiable_at.const_add DifferentiableAt.const_add

@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_at_const_add_iff differentiableAt_const_add_iff

theorem DifferentiableOn.const_add (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s := fun x hx => (hf x hx).const_add c
#align differentiable_on.const_add DifferentiableOn.const_add

@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_on_const_add_iff differentiableOn_const_add_iff

theorem Differentiable.const_add (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c + f y := fun x => (hf x).const_add c
#align differentiable.const_add Differentiable.const_add

@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_const_add_iff differentiable_const_add_iff

theorem fderivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const hxs c
#align fderiv_within_const_add fderivWithin_const_add

theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]
#align fderiv_const_add fderiv_const_add

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

theorem HasStrictFderivAt.sum (h : ∀ i ∈ u, HasStrictFderivAt (A i) (A' i) x) :
    HasStrictFderivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  by
  dsimp [HasStrictFderivAt] at *
  convert is_o.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]
#align has_strict_fderiv_at.sum HasStrictFderivAt.sum

theorem HasFderivAtFilter.sum (h : ∀ i ∈ u, HasFderivAtFilter (A i) (A' i) x L) :
    HasFderivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L :=
  by
  dsimp [HasFderivAtFilter] at *
  convert is_o.sum h
  simp [ContinuousLinearMap.sum_apply]
#align has_fderiv_at_filter.sum HasFderivAtFilter.sum

theorem HasFderivWithinAt.sum (h : ∀ i ∈ u, HasFderivWithinAt (A i) (A' i) s x) :
    HasFderivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasFderivAtFilter.sum h
#align has_fderiv_within_at.sum HasFderivWithinAt.sum

theorem HasFderivAt.sum (h : ∀ i ∈ u, HasFderivAt (A i) (A' i) x) :
    HasFderivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasFderivAtFilter.sum h
#align has_fderiv_at.sum HasFderivAt.sum

theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i in u, A i y) s x :=
  HasFderivWithinAt.differentiableWithinAt <|
    HasFderivWithinAt.sum fun i hi => (h i hi).HasFderivWithinAt
#align differentiable_within_at.sum DifferentiableWithinAt.sum

@[simp]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x :=
  HasFderivAt.differentiableAt <| HasFderivAt.sum fun i hi => (h i hi).HasFderivAt
#align differentiable_at.sum DifferentiableAt.sum

theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx
#align differentiable_on.sum DifferentiableOn.sum

@[simp]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i in u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x
#align differentiable.sum Differentiable.sum

theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i in u, A i y) s x = ∑ i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFderivWithinAt.sum fun i hi => (h i hi).HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_sum fderivWithin_sum

theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i in u, A i y) x = ∑ i in u, fderiv 𝕜 (A i) x :=
  (HasFderivAt.sum fun i hi => (h i hi).HasFderivAt).fderiv
#align fderiv_sum fderiv_sum

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


theorem HasStrictFderivAt.neg (h : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).HasStrictFderivAt.comp x h
#align has_strict_fderiv_at.neg HasStrictFderivAt.neg

theorem HasFderivAtFilter.neg (h : HasFderivAtFilter f f' x L) :
    HasFderivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).HasFderivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.neg HasFderivAtFilter.neg

theorem HasFderivWithinAt.neg (h : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => -f x) (-f') s x :=
  h.neg
#align has_fderiv_within_at.neg HasFderivWithinAt.neg

theorem HasFderivAt.neg (h : HasFderivAt f f' x) : HasFderivAt (fun x => -f x) (-f') x :=
  h.neg
#align has_fderiv_at.neg HasFderivAt.neg

theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.HasFderivWithinAt.neg.DifferentiableWithinAt
#align differentiable_within_at.neg DifferentiableWithinAt.neg

@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_within_at_neg_iff differentiableWithinAt_neg_iff

theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.HasFderivAt.neg.DifferentiableAt
#align differentiable_at.neg DifferentiableAt.neg

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_at_neg_iff differentiableAt_neg_iff

theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg
#align differentiable_on.neg DifferentiableOn.neg

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_on_neg_iff differentiableOn_neg_iff

theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg
#align differentiable.neg Differentiable.neg

@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_neg_iff differentiable_neg_iff

theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then h.HasFderivWithinAt.neg.fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa
#align fderiv_within_neg fderivWithin_neg

@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_neg uniqueDiffWithinAt_univ]
#align fderiv_neg fderiv_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


theorem HasStrictFderivAt.sub (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_strict_fderiv_at.sub HasStrictFderivAt.sub

theorem HasFderivAtFilter.sub (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
    HasFderivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_fderiv_at_filter.sub HasFderivAtFilter.sub

theorem HasFderivWithinAt.sub (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg
#align has_fderiv_within_at.sub HasFderivWithinAt.sub

theorem HasFderivAt.sub (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg
#align has_fderiv_at.sub HasFderivAt.sub

theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.HasFderivWithinAt.sub hg.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.sub DifferentiableWithinAt.sub

@[simp]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.HasFderivAt.sub hg.HasFderivAt).DifferentiableAt
#align differentiable_at.sub DifferentiableAt.sub

theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)
#align differentiable_on.sub DifferentiableOn.sub

@[simp]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)
#align differentiable.sub Differentiable.sub

theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.HasFderivWithinAt.sub hg.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_sub fderivWithin_sub

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.HasFderivAt.sub hg.HasFderivAt).fderiv
#align fderiv_sub fderiv_sub

theorem HasStrictFderivAt.sub_const (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun x => f x - c) f' x := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_strict_fderiv_at.sub_const HasStrictFderivAt.sub_const

theorem HasFderivAtFilter.sub_const (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_fderiv_at_filter.sub_const HasFderivAtFilter.sub_const

theorem HasFderivWithinAt.sub_const (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c
#align has_fderiv_within_at.sub_const HasFderivWithinAt.sub_const

theorem HasFderivAt.sub_const (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => f x - c) f' x :=
  hf.sub_const c
#align has_fderiv_at.sub_const HasFderivAt.sub_const

theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.HasFderivWithinAt.sub_const c).DifferentiableWithinAt
#align differentiable_within_at.sub_const DifferentiableWithinAt.sub_const

@[simp]
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]
#align differentiable_within_at_sub_const_iff differentiableWithinAt_sub_const_iff

theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.HasFderivAt.sub_const c).DifferentiableAt
#align differentiable_at.sub_const DifferentiableAt.sub_const

@[simp]
theorem differentiableAt_sub_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_add_const_iff]
#align differentiable_at_sub_const_iff differentiableAt_sub_const_iff

theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c
#align differentiable_on.sub_const DifferentiableOn.sub_const

@[simp]
theorem differentiableOn_sub_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_add_const_iff]
#align differentiable_on_sub_const_iff differentiableOn_sub_const_iff

theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c
#align differentiable.sub_const Differentiable.sub_const

@[simp]
theorem differentiable_sub_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y - c) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_add_const_iff]
#align differentiable_sub_const_iff differentiable_sub_const_iff

theorem fderivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const hxs]
#align fderiv_within_sub_const fderivWithin_sub_const

theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]
#align fderiv_sub_const fderiv_sub_const

theorem HasStrictFderivAt.const_sub (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_strict_fderiv_at.const_sub HasStrictFderivAt.const_sub

theorem HasFderivAtFilter.const_sub (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_fderiv_at_filter.const_sub HasFderivAtFilter.const_sub

theorem HasFderivWithinAt.const_sub (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c
#align has_fderiv_within_at.const_sub HasFderivWithinAt.const_sub

theorem HasFderivAt.const_sub (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c
#align has_fderiv_at.const_sub HasFderivAt.const_sub

theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.HasFderivWithinAt.const_sub c).DifferentiableWithinAt
#align differentiable_within_at.const_sub DifferentiableWithinAt.const_sub

@[simp]
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]
#align differentiable_within_at_const_sub_iff differentiableWithinAt_const_sub_iff

theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.HasFderivAt.const_sub c).DifferentiableAt
#align differentiable_at.const_sub DifferentiableAt.const_sub

@[simp]
theorem differentiableAt_const_sub_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x ↔ DifferentiableAt 𝕜 f x := by simp [sub_eq_add_neg]
#align differentiable_at_const_sub_iff differentiableAt_const_sub_iff

theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c
#align differentiable_on.const_sub DifferentiableOn.const_sub

@[simp]
theorem differentiableOn_const_sub_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s ↔ DifferentiableOn 𝕜 f s := by simp [sub_eq_add_neg]
#align differentiable_on_const_sub_iff differentiableOn_const_sub_iff

theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c
#align differentiable.const_sub Differentiable.const_sub

@[simp]
theorem differentiable_const_sub_iff (c : F) :
    (Differentiable 𝕜 fun y => c - f y) ↔ Differentiable 𝕜 f := by simp [sub_eq_add_neg]
#align differentiable_const_sub_iff differentiable_const_sub_iff

theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_neg, hxs]
#align fderiv_within_const_sub fderivWithin_const_sub

theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]
#align fderiv_const_sub fderiv_const_sub

end Sub

end

