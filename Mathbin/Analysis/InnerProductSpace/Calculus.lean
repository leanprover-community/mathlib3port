/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Derivative of the inner product

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `β`-smooth. In order to state these results, we need a `normed_space β E`
instance. Though we can deduce this structure from `inner_product_space π E`, this instance may be
not definitionally equal to some other βnaturalβ instance. So, we assume `[normed_space β E]`.
-/


noncomputable section

open IsROrC Real Filter

open BigOperators Classical TopologicalSpace

variable {π E F : Type _} [IsROrC π]

variable [InnerProductSpace π E] [InnerProductSpace β F]

-- mathport name: Β«exprβͺ , β«Β»
local notation "βͺ" x ", " y "β«" => @inner π _ _ x y

variable [NormedSpace β E]

/-- Derivative of the inner product. -/
def fderivInnerClm (p : E Γ E) : E Γ E βL[β] π :=
  is_bounded_bilinear_map_inner.deriv p

@[simp]
theorem fderiv_inner_clm_apply (p x : E Γ E) : fderivInnerClm p x = βͺp.1, x.2β« + βͺx.1, p.2β« :=
  rfl

theorem cont_diff_inner {n} : ContDiff β n fun p : E Γ E => βͺp.1, p.2β« :=
  is_bounded_bilinear_map_inner.ContDiff

theorem cont_diff_at_inner {p : E Γ E} {n} : ContDiffAt β n (fun p : E Γ E => βͺp.1, p.2β«) p :=
  cont_diff_inner.ContDiffAt

theorem differentiable_inner : Differentiable β fun p : E Γ E => βͺp.1, p.2β« :=
  is_bounded_bilinear_map_inner.DifferentiableAt

variable {G : Type _} [NormedGroup G] [NormedSpace β G] {f g : G β E} {f' g' : G βL[β] E} {s : Set G} {x : G}
  {n : WithTop β}

include π

theorem ContDiffWithinAt.inner (hf : ContDiffWithinAt β n f s x) (hg : ContDiffWithinAt β n g s x) :
    ContDiffWithinAt β n (fun x => βͺf x, g xβ«) s x :=
  cont_diff_at_inner.comp_cont_diff_within_at x (hf.Prod hg)

theorem ContDiffAt.inner (hf : ContDiffAt β n f x) (hg : ContDiffAt β n g x) : ContDiffAt β n (fun x => βͺf x, g xβ«) x :=
  hf.inner hg

theorem ContDiffOn.inner (hf : ContDiffOn β n f s) (hg : ContDiffOn β n g s) : ContDiffOn β n (fun x => βͺf x, g xβ«) s :=
  fun x hx => (hf x hx).inner (hg x hx)

theorem ContDiff.inner (hf : ContDiff β n f) (hg : ContDiff β n g) : ContDiff β n fun x => βͺf x, g xβ« :=
  cont_diff_inner.comp (hf.Prod hg)

theorem HasFderivWithinAt.inner (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun t => βͺf t, g tβ«) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') s x :=
  (is_bounded_bilinear_map_inner.HasFderivAt (f x, g x)).comp_has_fderiv_within_at x (hf.Prod hg)

theorem HasStrictFderivAt.inner (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun t => βͺf t, g tβ«) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') x :=
  (is_bounded_bilinear_map_inner.HasStrictFderivAt (f x, g x)).comp x (hf.Prod hg)

theorem HasFderivAt.inner (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun t => βͺf t, g tβ«) ((fderivInnerClm (f x, g x)).comp <| f'.Prod g') x :=
  (is_bounded_bilinear_map_inner.HasFderivAt (f x, g x)).comp x (hf.Prod hg)

theorem HasDerivWithinAt.inner {f g : β β E} {f' g' : E} {s : Set β} {x : β} (hf : HasDerivWithinAt f f' s x)
    (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun t => βͺf t, g tβ«) (βͺf x, g'β« + βͺf', g xβ«) s x := by
  simpa using (hf.has_fderiv_within_at.inner hg.has_fderiv_within_at).HasDerivWithinAt

theorem HasDerivAt.inner {f g : β β E} {f' g' : E} {x : β} :
    HasDerivAt f f' x β HasDerivAt g g' x β HasDerivAt (fun t => βͺf t, g tβ«) (βͺf x, g'β« + βͺf', g xβ«) x := by
  simpa only [has_deriv_within_at_univ] using HasDerivWithinAt.inner

theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt β f s x) (hg : DifferentiableWithinAt β g s x) :
    DifferentiableWithinAt β (fun x => βͺf x, g xβ«) s x :=
  ((differentiable_inner _).HasFderivAt.comp_has_fderiv_within_at x
      (hf.Prod hg).HasFderivWithinAt).DifferentiableWithinAt

theorem DifferentiableAt.inner (hf : DifferentiableAt β f x) (hg : DifferentiableAt β g x) :
    DifferentiableAt β (fun x => βͺf x, g xβ«) x :=
  (differentiable_inner _).comp x (hf.Prod hg)

theorem DifferentiableOn.inner (hf : DifferentiableOn β f s) (hg : DifferentiableOn β g s) :
    DifferentiableOn β (fun x => βͺf x, g xβ«) s := fun x hx => (hf x hx).inner (hg x hx)

theorem Differentiable.inner (hf : Differentiable β f) (hg : Differentiable β g) :
    Differentiable β fun x => βͺf x, g xβ« := fun x => (hf x).inner (hg x)

theorem fderiv_inner_apply (hf : DifferentiableAt β f x) (hg : DifferentiableAt β g x) (y : G) :
    fderiv β (fun t => βͺf t, g tβ«) x y = βͺf x, fderiv β g x yβ« + βͺfderiv β f x y, g xβ« := by
  rw [(hf.has_fderiv_at.inner hg.has_fderiv_at).fderiv]
  rfl

theorem deriv_inner_apply {f g : β β E} {x : β} (hf : DifferentiableAt β f x) (hg : DifferentiableAt β g x) :
    deriv (fun t => βͺf t, g tβ«) x = βͺf x, deriv g xβ« + βͺderiv f x, g xβ« :=
  (hf.HasDerivAt.inner hg.HasDerivAt).deriv

theorem cont_diff_norm_sq : ContDiff β n fun x : E => β₯xβ₯ ^ 2 := by
  simp only [β sq, inner_self_eq_norm_mul_norm]
  exact (re_clm : π βL[β] β).ContDiff.comp (cont_diff_id.inner cont_diff_id)

theorem ContDiff.norm_sq (hf : ContDiff β n f) : ContDiff β n fun x => β₯f xβ₯ ^ 2 :=
  cont_diff_norm_sq.comp hf

theorem ContDiffWithinAt.norm_sq (hf : ContDiffWithinAt β n f s x) : ContDiffWithinAt β n (fun y => β₯f yβ₯ ^ 2) s x :=
  cont_diff_norm_sq.ContDiffAt.comp_cont_diff_within_at x hf

theorem ContDiffAt.norm_sq (hf : ContDiffAt β n f x) : ContDiffAt β n (fun y => β₯f yβ₯ ^ 2) x :=
  hf.normSq

theorem cont_diff_at_norm {x : E} (hx : x β  0) : ContDiffAt β n norm x := by
  have : β₯id xβ₯ ^ 2 β  0 := pow_ne_zero _ (norm_pos_iff.2 hx).ne'
  simpa only [β id, β sqrt_sq, β norm_nonneg] using cont_diff_at_id.norm_sq.sqrt this

theorem ContDiffAt.norm (hf : ContDiffAt β n f x) (h0 : f x β  0) : ContDiffAt β n (fun y => β₯f yβ₯) x :=
  (cont_diff_at_norm h0).comp x hf

theorem ContDiffAt.dist (hf : ContDiffAt β n f x) (hg : ContDiffAt β n g x) (hne : f x β  g x) :
    ContDiffAt β n (fun y => dist (f y) (g y)) x := by
  simp only [β dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem ContDiffWithinAt.norm (hf : ContDiffWithinAt β n f s x) (h0 : f x β  0) :
    ContDiffWithinAt β n (fun y => β₯f yβ₯) s x :=
  (cont_diff_at_norm h0).comp_cont_diff_within_at x hf

theorem ContDiffWithinAt.dist (hf : ContDiffWithinAt β n f s x) (hg : ContDiffWithinAt β n g s x) (hne : f x β  g x) :
    ContDiffWithinAt β n (fun y => dist (f y) (g y)) s x := by
  simp only [β dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem ContDiffOn.norm_sq (hf : ContDiffOn β n f s) : ContDiffOn β n (fun y => β₯f yβ₯ ^ 2) s := fun x hx =>
  (hf x hx).normSq

theorem ContDiffOn.norm (hf : ContDiffOn β n f s) (h0 : β, β x β s, β, f x β  0) : ContDiffOn β n (fun y => β₯f yβ₯) s :=
  fun x hx => (hf x hx).norm (h0 x hx)

theorem ContDiffOn.dist (hf : ContDiffOn β n f s) (hg : ContDiffOn β n g s) (hne : β, β x β s, β, f x β  g x) :
    ContDiffOn β n (fun y => dist (f y) (g y)) s := fun x hx => (hf x hx).dist (hg x hx) (hne x hx)

theorem ContDiff.norm (hf : ContDiff β n f) (h0 : β x, f x β  0) : ContDiff β n fun y => β₯f yβ₯ :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.norm (h0 x)

theorem ContDiff.dist (hf : ContDiff β n f) (hg : ContDiff β n g) (hne : β x, f x β  g x) :
    ContDiff β n fun y => dist (f y) (g y) :=
  cont_diff_iff_cont_diff_at.2 fun x => hf.ContDiffAt.dist hg.ContDiffAt (hne x)

omit π

theorem has_strict_fderiv_at_norm_sq (x : F) : HasStrictFderivAt (fun x => β₯xβ₯ ^ 2) (bit0 (innerSL x)) x := by
  simp only [β sq, inner_self_eq_norm_mul_norm]
  convert (has_strict_fderiv_at_id x).inner (has_strict_fderiv_at_id x)
  ext y
  simp [β bit0, β real_inner_comm]

include π

theorem DifferentiableAt.norm_sq (hf : DifferentiableAt β f x) : DifferentiableAt β (fun y => β₯f yβ₯ ^ 2) x :=
  (cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp x hf

theorem DifferentiableAt.norm (hf : DifferentiableAt β f x) (h0 : f x β  0) : DifferentiableAt β (fun y => β₯f yβ₯) x :=
  ((cont_diff_at_norm h0).DifferentiableAt le_rfl).comp x hf

theorem DifferentiableAt.dist (hf : DifferentiableAt β f x) (hg : DifferentiableAt β g x) (hne : f x β  g x) :
    DifferentiableAt β (fun y => dist (f y) (g y)) x := by
  simp only [β dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem Differentiable.norm_sq (hf : Differentiable β f) : Differentiable β fun y => β₯f yβ₯ ^ 2 := fun x => (hf x).normSq

theorem Differentiable.norm (hf : Differentiable β f) (h0 : β x, f x β  0) : Differentiable β fun y => β₯f yβ₯ := fun x =>
  (hf x).norm (h0 x)

theorem Differentiable.dist (hf : Differentiable β f) (hg : Differentiable β g) (hne : β x, f x β  g x) :
    Differentiable β fun y => dist (f y) (g y) := fun x => (hf x).dist (hg x) (hne x)

theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt β f s x) :
    DifferentiableWithinAt β (fun y => β₯f yβ₯ ^ 2) s x :=
  (cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp_differentiable_within_at x hf

theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt β f s x) (h0 : f x β  0) :
    DifferentiableWithinAt β (fun y => β₯f yβ₯) s x :=
  ((cont_diff_at_id.norm h0).DifferentiableAt le_rfl).comp_differentiable_within_at x hf

theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt β f s x) (hg : DifferentiableWithinAt β g s x)
    (hne : f x β  g x) : DifferentiableWithinAt β (fun y => dist (f y) (g y)) s x := by
  simp only [β dist_eq_norm]
  exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem DifferentiableOn.norm_sq (hf : DifferentiableOn β f s) : DifferentiableOn β (fun y => β₯f yβ₯ ^ 2) s :=
  fun x hx => (hf x hx).normSq

theorem DifferentiableOn.norm (hf : DifferentiableOn β f s) (h0 : β, β x β s, β, f x β  0) :
    DifferentiableOn β (fun y => β₯f yβ₯) s := fun x hx => (hf x hx).norm (h0 x hx)

theorem DifferentiableOn.dist (hf : DifferentiableOn β f s) (hg : DifferentiableOn β g s)
    (hne : β, β x β s, β, f x β  g x) : DifferentiableOn β (fun y => dist (f y) (g y)) s := fun x hx =>
  (hf x hx).dist (hg x hx) (hne x hx)

