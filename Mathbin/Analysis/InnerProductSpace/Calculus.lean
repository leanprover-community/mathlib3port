/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.inner_product_space.calculus
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Calculus in inner product spaces

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]`.

We also prove that functions to a `euclidean_space` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `pi_Lp`.
-/


noncomputable section

open IsROrC Real Filter

open BigOperators Classical Topology

section DerivInner

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

variable [NormedSpace ℝ E]

/-- Derivative of the inner product. -/
def fderivInnerClm (p : E × E) : E × E →L[ℝ] 𝕜 :=
  isBoundedBilinearMapInner.deriv p
#align fderiv_inner_clm fderivInnerClm

@[simp]
theorem fderivInnerClm_apply (p x : E × E) : fderivInnerClm p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ :=
  rfl
#align fderiv_inner_clm_apply fderivInnerClm_apply

theorem contDiff_inner {n} : ContDiff ℝ n fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMapInner.ContDiff
#align cont_diff_inner contDiff_inner

theorem contDiffAt_inner {p : E × E} {n} : ContDiffAt ℝ n (fun p : E × E => ⟪p.1, p.2⟫) p :=
  contDiff_inner.ContDiffAt
#align cont_diff_at_inner contDiffAt_inner

theorem differentiable_inner : Differentiable ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  isBoundedBilinearMapInner.DifferentiableAt
#align differentiable_inner differentiable_inner

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : G → E} {f' g' : G →L[ℝ] E}
  {s : Set G} {x : G} {n : ℕ∞}

include 𝕜

theorem ContDiffWithinAt.inner (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => ⟪f x, g x⟫) s x :=
  contDiffAt_inner.comp_contDiffWithinAt x (hf.Prod hg)
#align cont_diff_within_at.inner ContDiffWithinAt.inner

theorem ContDiffAt.inner (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  hf.inner hg
#align cont_diff_at.inner ContDiffAt.inner

theorem ContDiffOn.inner (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ n (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner (hg x hx)
#align cont_diff_on.inner ContDiffOn.inner

theorem ContDiff.inner (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => ⟪f x, g x⟫ :=
  contDiff_inner.comp (hf.Prod hg)
#align cont_diff.inner ContDiff.inner

theorem HasFderivWithinAt.inner (hf : HasFderivWithinAt f f' s x)
    (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') s x :=
  (isBoundedBilinearMapInner.HasFderivAt (f x, g x)).comp_hasFderivWithinAt x (hf.Prod hg)
#align has_fderiv_within_at.inner HasFderivWithinAt.inner

theorem HasStrictFderivAt.inner (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') x :=
  (isBoundedBilinearMapInner.HasStrictFderivAt (f x, g x)).comp x (hf.Prod hg)
#align has_strict_fderiv_at.inner HasStrictFderivAt.inner

theorem HasFderivAt.inner (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') x :=
  (isBoundedBilinearMapInner.HasFderivAt (f x, g x)).comp x (hf.Prod hg)
#align has_fderiv_at.inner HasFderivAt.inner

theorem HasDerivWithinAt.inner {f g : ℝ → E} {f' g' : E} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x := by
  simpa using (hf.has_fderiv_within_at.inner hg.has_fderiv_within_at).HasDerivWithinAt
#align has_deriv_within_at.inner HasDerivWithinAt.inner

theorem HasDerivAt.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
    HasDerivAt f f' x →
      HasDerivAt g g' x → HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x :=
  by simpa only [← hasDerivWithinAt_univ] using HasDerivWithinAt.inner
#align has_deriv_at.inner HasDerivAt.inner

theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) : DifferentiableWithinAt ℝ (fun x => ⟪f x, g x⟫) s x :=
  ((differentiable_inner _).HasFderivAt.comp_hasFderivWithinAt x
      (hf.Prod hg).HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.inner DifferentiableWithinAt.inner

theorem DifferentiableAt.inner (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x :=
  (differentiable_inner _).comp x (hf.Prod hg)
#align differentiable_at.inner DifferentiableAt.inner

theorem DifferentiableOn.inner (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s) :
    DifferentiableOn ℝ (fun x => ⟪f x, g x⟫) s := fun x hx => (hf x hx).inner (hg x hx)
#align differentiable_on.inner DifferentiableOn.inner

theorem Differentiable.inner (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ fun x => ⟪f x, g x⟫ := fun x => (hf x).inner (hg x)
#align differentiable.inner Differentiable.inner

theorem fderiv_inner_apply (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : G) :
    fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ :=
  by
  rw [(hf.has_fderiv_at.inner hg.has_fderiv_at).fderiv]
  rfl
#align fderiv_inner_apply fderiv_inner_apply

theorem deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
  (hf.HasDerivAt.inner hg.HasDerivAt).deriv
#align deriv_inner_apply deriv_inner_apply

theorem contDiff_norm_sq : ContDiff ℝ n fun x : E => ‖x‖ ^ 2 :=
  by
  simp only [sq, ← inner_self_eq_norm_mul_norm]
  exact (re_clm : 𝕜 →L[ℝ] ℝ).ContDiff.comp (cont_diff_id.inner contDiff_id)
#align cont_diff_norm_sq contDiff_norm_sq

theorem ContDiff.norm_sq (hf : ContDiff ℝ n f) : ContDiff ℝ n fun x => ‖f x‖ ^ 2 :=
  contDiff_norm_sq.comp hf
#align cont_diff.norm_sq ContDiff.norm_sq

theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖ ^ 2) s x :=
  contDiff_norm_sq.ContDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.norm_sq ContDiffWithinAt.norm_sq

theorem ContDiffAt.norm_sq (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y => ‖f y‖ ^ 2) x :=
  hf.normSq
#align cont_diff_at.norm_sq ContDiffAt.norm_sq

theorem contDiffAt_norm {x : E} (hx : x ≠ 0) : ContDiffAt ℝ n norm x :=
  by
  have : ‖id x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_pos_iff.2 hx).ne'
  simpa only [id, sqrt_sq, norm_nonneg] using cont_diff_at_id.norm_sq.sqrt this
#align cont_diff_at_norm contDiffAt_norm

theorem ContDiffAt.norm (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => ‖f y‖) x :=
  (contDiffAt_norm h0).comp x hf
#align cont_diff_at.norm ContDiffAt.norm

theorem ContDiffAt.dist (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (hne : f x ≠ g x) :
    ContDiffAt ℝ n (fun y => dist (f y) (g y)) x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align cont_diff_at.dist ContDiffAt.dist

theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => ‖f y‖) s x :=
  (contDiffAt_norm h0).comp_contDiffWithinAt x hf
#align cont_diff_within_at.norm ContDiffWithinAt.norm

theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (hne : f x ≠ g x) : ContDiffWithinAt ℝ n (fun y => dist (f y) (g y)) s x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align cont_diff_within_at.dist ContDiffWithinAt.dist

theorem ContDiffOn.norm_sq (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun y => ‖f y‖ ^ 2) s :=
  fun x hx => (hf x hx).normSq
#align cont_diff_on.norm_sq ContDiffOn.norm_sq

theorem ContDiffOn.norm (hf : ContDiffOn ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm (h0 x hx)
#align cont_diff_on.norm ContDiffOn.norm

theorem ContDiffOn.dist (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : ContDiffOn ℝ n (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist (hg x hx) (hne x hx)
#align cont_diff_on.dist ContDiffOn.dist

theorem ContDiff.norm (hf : ContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => ‖f y‖ :=
  contDiff_iff_contDiffAt.2 fun x => hf.ContDiffAt.norm (h0 x)
#align cont_diff.norm ContDiff.norm

theorem ContDiff.dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hne : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun y => dist (f y) (g y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.ContDiffAt.dist hg.ContDiffAt (hne x)
#align cont_diff.dist ContDiff.dist

omit 𝕜

theorem hasStrictFderivAt_norm_sq (x : F) :
    HasStrictFderivAt (fun x => ‖x‖ ^ 2) (bit0 (innerSL x : F →L[ℝ] ℝ)) x :=
  by
  simp only [sq, ← inner_self_eq_norm_mul_norm]
  convert (hasStrictFderivAt_id x).inner (hasStrictFderivAt_id x)
  ext y
  simp [bit0, real_inner_comm]
#align has_strict_fderiv_at_norm_sq hasStrictFderivAt_norm_sq

include 𝕜

theorem DifferentiableAt.norm_sq (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => ‖f y‖ ^ 2) x :=
  (contDiffAt_id.normSq.DifferentiableAt le_rfl).comp x hf
#align differentiable_at.norm_sq DifferentiableAt.norm_sq

theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => ‖f y‖) x :=
  ((contDiffAt_norm h0).DifferentiableAt le_rfl).comp x hf
#align differentiable_at.norm DifferentiableAt.norm

theorem DifferentiableAt.dist (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hne : f x ≠ g x) : DifferentiableAt ℝ (fun y => dist (f y) (g y)) x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align differentiable_at.dist DifferentiableAt.dist

theorem Differentiable.norm_sq (hf : Differentiable ℝ f) : Differentiable ℝ fun y => ‖f y‖ ^ 2 :=
  fun x => (hf x).normSq
#align differentiable.norm_sq Differentiable.norm_sq

theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => ‖f y‖ := fun x => (hf x).norm (h0 x)
#align differentiable.norm Differentiable.norm

theorem Differentiable.dist (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hne : ∀ x, f x ≠ g x) : Differentiable ℝ fun y => dist (f y) (g y) := fun x =>
  (hf x).dist (hg x) (hne x)
#align differentiable.dist Differentiable.dist

theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖ ^ 2) s x :=
  (contDiffAt_id.normSq.DifferentiableAt le_rfl).comp_differentiableWithinAt x hf
#align differentiable_within_at.norm_sq DifferentiableWithinAt.norm_sq

theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => ‖f y‖) s x :=
  ((contDiffAt_id.norm h0).DifferentiableAt le_rfl).comp_differentiableWithinAt x hf
#align differentiable_within_at.norm DifferentiableWithinAt.norm

theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (hne : f x ≠ g x) :
    DifferentiableWithinAt ℝ (fun y => dist (f y) (g y)) s x :=
  by
  simp only [dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)
#align differentiable_within_at.dist DifferentiableWithinAt.dist

theorem DifferentiableOn.norm_sq (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun y => ‖f y‖ ^ 2) s := fun x hx => (hf x hx).normSq
#align differentiable_on.norm_sq DifferentiableOn.norm_sq

theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => ‖f y‖) s := fun x hx => (hf x hx).norm (h0 x hx)
#align differentiable_on.norm DifferentiableOn.norm

theorem DifferentiableOn.dist (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (hne : ∀ x ∈ s, f x ≠ g x) : DifferentiableOn ℝ (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist (hg x hx) (hne x hx)
#align differentiable_on.dist DifferentiableOn.dist

end DerivInner

section PiLike

open ContinuousLinearMap

variable {𝕜 ι H : Type _} [IsROrC 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H] [Fintype ι]
  {f : H → EuclideanSpace 𝕜 ι} {f' : H →L[𝕜] EuclideanSpace 𝕜 ι} {t : Set H} {y : H}

theorem differentiableWithinAt_euclidean :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableWithinAt_iff, differentiableWithinAt_pi]
  rfl
#align differentiable_within_at_euclidean differentiableWithinAt_euclidean

theorem differentiableAt_euclidean :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableAt_iff, differentiableAt_pi]
  rfl
#align differentiable_at_euclidean differentiableAt_euclidean

theorem differentiableOn_euclidean :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiableOn_iff, differentiableOn_pi]
  rfl
#align differentiable_on_euclidean differentiableOn_euclidean

theorem differentiable_euclidean : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_differentiable_iff, differentiable_pi]
  rfl
#align differentiable_euclidean differentiable_euclidean

theorem hasStrictFderivAt_euclidean :
    HasStrictFderivAt f f' y ↔
      ∀ i, HasStrictFderivAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_hasStrictFderivAt_iff, hasStrictFderivAt_pi']
  rfl
#align has_strict_fderiv_at_euclidean hasStrictFderivAt_euclidean

theorem hasFderivWithinAt_euclidean :
    HasFderivWithinAt f f' t y ↔
      ∀ i, HasFderivWithinAt (fun x => f x i) (EuclideanSpace.proj i ∘L f') t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_hasFderivWithinAt_iff, hasFderivWithinAt_pi']
  rfl
#align has_fderiv_within_at_euclidean hasFderivWithinAt_euclidean

theorem contDiffWithinAt_euclidean {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f t y ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => f x i) t y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffWithinAt_iff, contDiffWithinAt_pi]
  rfl
#align cont_diff_within_at_euclidean contDiffWithinAt_euclidean

theorem contDiffAt_euclidean {n : ℕ∞} :
    ContDiffAt 𝕜 n f y ↔ ∀ i, ContDiffAt 𝕜 n (fun x => f x i) y :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffAt_iff, contDiffAt_pi]
  rfl
#align cont_diff_at_euclidean contDiffAt_euclidean

theorem contDiffOn_euclidean {n : ℕ∞} :
    ContDiffOn 𝕜 n f t ↔ ∀ i, ContDiffOn 𝕜 n (fun x => f x i) t :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiffOn_iff, contDiffOn_pi]
  rfl
#align cont_diff_on_euclidean contDiffOn_euclidean

theorem contDiff_euclidean {n : ℕ∞} : ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n fun x => f x i :=
  by
  rw [← (EuclideanSpace.equiv ι 𝕜).comp_contDiff_iff, contDiff_pi]
  rfl
#align cont_diff_euclidean contDiff_euclidean

end PiLike

section DiffeomorphUnitBall

open Metric hiding mem_nhds_iffₓ

variable {n : ℕ∞} {E : Type _} [InnerProductSpace ℝ E]

theorem contDiff_homeomorphUnitBall : ContDiff ℝ n fun x : E => (homeomorphUnitBall x : E) :=
  by
  suffices ContDiff ℝ n fun x => (1 + ‖x‖ ^ 2).sqrt⁻¹ by exact this.smul contDiff_id
  have h : ∀ x : E, 0 < 1 + ‖x‖ ^ 2 := fun x => by positivity
  refine' ContDiff.inv _ fun x => real.sqrt_ne_zero'.mpr (h x)
  exact (cont_diff_const.add contDiff_norm_sq).sqrt fun x => (h x).Ne.symm
#align cont_diff_homeomorph_unit_ball contDiff_homeomorphUnitBall

theorem contDiffOn_homeomorphUnitBall_symm {f : E → E}
    (h : ∀ (y) (hy : y ∈ ball (0 : E) 1), f y = homeomorphUnitBall.symm ⟨y, hy⟩) :
    ContDiffOn ℝ n f <| ball 0 1 := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  have hf : f =ᶠ[𝓝 y] fun y => (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹ • (y : E) :=
    by
    rw [eventually_eq_iff_exists_mem]
    refine'
      ⟨ball (0 : E) 1, mem_nhds_iff.mpr ⟨ball (0 : E) 1, Set.Subset.refl _, is_open_ball, hy⟩,
        fun z hz => _⟩
    rw [h z hz]
    rfl
  refine' ContDiffAt.congr_of_eventuallyEq _ hf
  suffices ContDiffAt ℝ n (fun y => (1 - ‖(y : E)‖ ^ 2).sqrt⁻¹) y by exact this.smul contDiffAt_id
  have h : 0 < 1 - ‖(y : E)‖ ^ 2 := by
    rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm_eq_norm, ← sq_lt_sq, one_pow, ← sub_pos] at
      hy
  refine' ContDiffAt.inv _ (real.sqrt_ne_zero'.mpr h)
  refine' ContDiffAt.comp _ (cont_diff_at_sqrt h.ne.symm) _
  exact cont_diff_at_const.sub cont_diff_norm_sq.cont_diff_at
#align cont_diff_on_homeomorph_unit_ball_symm contDiffOn_homeomorphUnitBall_symm

end DiffeomorphUnitBall

