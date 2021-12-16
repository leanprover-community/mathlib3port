import Mathbin.Analysis.InnerProductSpace.Basic 
import Mathbin.Analysis.SpecialFunctions.Sqrt

/-!
# Derivative of the inner product

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]`.
-/


noncomputable section 

open IsROrC Real Filter

open_locale BigOperators Classical TopologicalSpace

variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

variable [NormedSpace ℝ E]

/-- Derivative of the inner product. -/
def fderivInnerClm (p : E × E) : E × E →L[ℝ] 𝕜 :=
  is_bounded_bilinear_map_inner.deriv p

@[simp]
theorem fderiv_inner_clm_apply (p x : E × E) : fderivInnerClm p x = ⟪p.1, x.2⟫+⟪x.1, p.2⟫ :=
  rfl

theorem times_cont_diff_inner {n} : TimesContDiff ℝ n fun p : E × E => ⟪p.1, p.2⟫ :=
  is_bounded_bilinear_map_inner.TimesContDiff

theorem times_cont_diff_at_inner {p : E × E} {n} : TimesContDiffAt ℝ n (fun p : E × E => ⟪p.1, p.2⟫) p :=
  times_cont_diff_inner.TimesContDiffAt

theorem differentiable_inner : Differentiable ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  is_bounded_bilinear_map_inner.DifferentiableAt

variable {G : Type _} [NormedGroup G] [NormedSpace ℝ G] {f g : G → E} {f' g' : G →L[ℝ] E} {s : Set G} {x : G}
  {n : WithTop ℕ}

include 𝕜

theorem TimesContDiffWithinAt.inner (hf : TimesContDiffWithinAt ℝ n f s x) (hg : TimesContDiffWithinAt ℝ n g s x) :
  TimesContDiffWithinAt ℝ n (fun x => ⟪f x, g x⟫) s x :=
  times_cont_diff_at_inner.comp_times_cont_diff_within_at x (hf.prod hg)

theorem TimesContDiffAt.inner (hf : TimesContDiffAt ℝ n f x) (hg : TimesContDiffAt ℝ n g x) :
  TimesContDiffAt ℝ n (fun x => ⟪f x, g x⟫) x :=
  hf.inner hg

theorem TimesContDiffOn.inner (hf : TimesContDiffOn ℝ n f s) (hg : TimesContDiffOn ℝ n g s) :
  TimesContDiffOn ℝ n (fun x => ⟪f x, g x⟫) s :=
  fun x hx => (hf x hx).inner (hg x hx)

theorem TimesContDiff.inner (hf : TimesContDiff ℝ n f) (hg : TimesContDiff ℝ n g) :
  TimesContDiff ℝ n fun x => ⟪f x, g x⟫ :=
  times_cont_diff_inner.comp (hf.prod hg)

theorem HasFderivWithinAt.inner (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
  HasFderivWithinAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp$ f'.prod g') s x :=
  (is_bounded_bilinear_map_inner.HasFderivAt (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

theorem HasStrictFderivAt.inner (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
  HasStrictFderivAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp$ f'.prod g') x :=
  (is_bounded_bilinear_map_inner.HasStrictFderivAt (f x, g x)).comp x (hf.prod hg)

theorem HasFderivAt.inner (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
  HasFderivAt (fun t => ⟪f t, g t⟫) ((fderivInnerClm (f x, g x)).comp$ f'.prod g') x :=
  (is_bounded_bilinear_map_inner.HasFderivAt (f x, g x)).comp x (hf.prod hg)

theorem HasDerivWithinAt.inner {f g : ℝ → E} {f' g' : E} {s : Set ℝ} {x : ℝ} (hf : HasDerivWithinAt f f' s x)
  (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫+⟪f', g x⟫) s x :=
  by 
    simpa using (hf.has_fderiv_within_at.inner hg.has_fderiv_within_at).HasDerivWithinAt

theorem HasDerivAt.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
  HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫+⟪f', g x⟫) x :=
  by 
    simpa only [←has_deriv_within_at_univ] using HasDerivWithinAt.inner

theorem DifferentiableWithinAt.inner (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
  DifferentiableWithinAt ℝ (fun x => ⟪f x, g x⟫) s x :=
  ((differentiable_inner _).HasFderivAt.comp_has_fderiv_within_at x
      (hf.prod hg).HasFderivWithinAt).DifferentiableWithinAt

theorem DifferentiableAt.inner (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  DifferentiableAt ℝ (fun x => ⟪f x, g x⟫) x :=
  (differentiable_inner _).comp x (hf.prod hg)

theorem DifferentiableOn.inner (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s) :
  DifferentiableOn ℝ (fun x => ⟪f x, g x⟫) s :=
  fun x hx => (hf x hx).inner (hg x hx)

theorem Differentiable.inner (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
  Differentiable ℝ fun x => ⟪f x, g x⟫ :=
  fun x => (hf x).inner (hg x)

theorem fderiv_inner_apply (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (y : G) :
  fderiv ℝ (fun t => ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫+⟪fderiv ℝ f x y, g x⟫ :=
  by 
    rw [(hf.has_fderiv_at.inner hg.has_fderiv_at).fderiv]
    rfl

theorem deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
  deriv (fun t => ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫+⟪deriv f x, g x⟫ :=
  (hf.has_deriv_at.inner hg.has_deriv_at).deriv

theorem times_cont_diff_norm_sq : TimesContDiff ℝ n fun x : E => ∥x∥^2 :=
  by 
    simp only [sq, ←inner_self_eq_norm_mul_norm]
    exact (re_clm : 𝕜 →L[ℝ] ℝ).TimesContDiff.comp (times_cont_diff_id.inner times_cont_diff_id)

theorem TimesContDiff.norm_sq (hf : TimesContDiff ℝ n f) : TimesContDiff ℝ n fun x => ∥f x∥^2 :=
  times_cont_diff_norm_sq.comp hf

theorem TimesContDiffWithinAt.norm_sq (hf : TimesContDiffWithinAt ℝ n f s x) :
  TimesContDiffWithinAt ℝ n (fun y => ∥f y∥^2) s x :=
  times_cont_diff_norm_sq.TimesContDiffAt.comp_times_cont_diff_within_at x hf

theorem TimesContDiffAt.norm_sq (hf : TimesContDiffAt ℝ n f x) : TimesContDiffAt ℝ n (fun y => ∥f y∥^2) x :=
  hf.norm_sq

theorem times_cont_diff_at_norm {x : E} (hx : x ≠ 0) : TimesContDiffAt ℝ n norm x :=
  have  : (∥id x∥^2) ≠ 0 := pow_ne_zero _ (norm_pos_iff.2 hx).ne' 
  by 
    simpa only [id, sqrt_sq, norm_nonneg] using times_cont_diff_at_id.norm_sq.sqrt this

theorem TimesContDiffAt.norm (hf : TimesContDiffAt ℝ n f x) (h0 : f x ≠ 0) : TimesContDiffAt ℝ n (fun y => ∥f y∥) x :=
  (times_cont_diff_at_norm h0).comp x hf

theorem TimesContDiffAt.dist (hf : TimesContDiffAt ℝ n f x) (hg : TimesContDiffAt ℝ n g x) (hne : f x ≠ g x) :
  TimesContDiffAt ℝ n (fun y => dist (f y) (g y)) x :=
  by 
    simp only [dist_eq_norm]
    exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem TimesContDiffWithinAt.norm (hf : TimesContDiffWithinAt ℝ n f s x) (h0 : f x ≠ 0) :
  TimesContDiffWithinAt ℝ n (fun y => ∥f y∥) s x :=
  (times_cont_diff_at_norm h0).comp_times_cont_diff_within_at x hf

theorem TimesContDiffWithinAt.dist (hf : TimesContDiffWithinAt ℝ n f s x) (hg : TimesContDiffWithinAt ℝ n g s x)
  (hne : f x ≠ g x) : TimesContDiffWithinAt ℝ n (fun y => dist (f y) (g y)) s x :=
  by 
    simp only [dist_eq_norm]
    exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem TimesContDiffOn.norm_sq (hf : TimesContDiffOn ℝ n f s) : TimesContDiffOn ℝ n (fun y => ∥f y∥^2) s :=
  fun x hx => (hf x hx).normSq

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem TimesContDiffOn.norm (hf : TimesContDiffOn ℝ n f s) (h0 : ∀ x _ : x ∈ s, f x ≠ 0) :
  TimesContDiffOn ℝ n (fun y => ∥f y∥) s :=
  fun x hx => (hf x hx).norm (h0 x hx)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem TimesContDiffOn.dist (hf : TimesContDiffOn ℝ n f s) (hg : TimesContDiffOn ℝ n g s)
  (hne : ∀ x _ : x ∈ s, f x ≠ g x) : TimesContDiffOn ℝ n (fun y => dist (f y) (g y)) s :=
  fun x hx => (hf x hx).dist (hg x hx) (hne x hx)

theorem TimesContDiff.norm (hf : TimesContDiff ℝ n f) (h0 : ∀ x, f x ≠ 0) : TimesContDiff ℝ n fun y => ∥f y∥ :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => hf.times_cont_diff_at.norm (h0 x)

theorem TimesContDiff.dist (hf : TimesContDiff ℝ n f) (hg : TimesContDiff ℝ n g) (hne : ∀ x, f x ≠ g x) :
  TimesContDiff ℝ n fun y => dist (f y) (g y) :=
  times_cont_diff_iff_times_cont_diff_at.2$ fun x => hf.times_cont_diff_at.dist hg.times_cont_diff_at (hne x)

omit 𝕜

theorem has_strict_fderiv_at_norm_sq (x : F) : HasStrictFderivAt (fun x => ∥x∥^2) (bit0 (innerSL x)) x :=
  by 
    simp only [sq, ←inner_self_eq_norm_mul_norm]
    convert (has_strict_fderiv_at_id x).inner (has_strict_fderiv_at_id x)
    ext y 
    simp [bit0, real_inner_comm]

include 𝕜

theorem DifferentiableAt.norm_sq (hf : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun y => ∥f y∥^2) x :=
  (times_cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp x hf

theorem DifferentiableAt.norm (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) : DifferentiableAt ℝ (fun y => ∥f y∥) x :=
  ((times_cont_diff_at_norm h0).DifferentiableAt le_rfl).comp x hf

theorem DifferentiableAt.dist (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hne : f x ≠ g x) :
  DifferentiableAt ℝ (fun y => dist (f y) (g y)) x :=
  by 
    simp only [dist_eq_norm]
    exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem Differentiable.norm_sq (hf : Differentiable ℝ f) : Differentiable ℝ fun y => ∥f y∥^2 :=
  fun x => (hf x).normSq

theorem Differentiable.norm (hf : Differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) : Differentiable ℝ fun y => ∥f y∥ :=
  fun x => (hf x).norm (h0 x)

theorem Differentiable.dist (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (hne : ∀ x, f x ≠ g x) :
  Differentiable ℝ fun y => dist (f y) (g y) :=
  fun x => (hf x).dist (hg x) (hne x)

theorem DifferentiableWithinAt.norm_sq (hf : DifferentiableWithinAt ℝ f s x) :
  DifferentiableWithinAt ℝ (fun y => ∥f y∥^2) s x :=
  (times_cont_diff_at_id.normSq.DifferentiableAt le_rfl).comp_differentiable_within_at x hf

theorem DifferentiableWithinAt.norm (hf : DifferentiableWithinAt ℝ f s x) (h0 : f x ≠ 0) :
  DifferentiableWithinAt ℝ (fun y => ∥f y∥) s x :=
  ((times_cont_diff_at_id.norm h0).DifferentiableAt le_rfl).comp_differentiable_within_at x hf

theorem DifferentiableWithinAt.dist (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x)
  (hne : f x ≠ g x) : DifferentiableWithinAt ℝ (fun y => dist (f y) (g y)) s x :=
  by 
    simp only [dist_eq_norm]
    exact (hf.sub hg).norm (sub_ne_zero.2 hne)

theorem DifferentiableOn.norm_sq (hf : DifferentiableOn ℝ f s) : DifferentiableOn ℝ (fun y => ∥f y∥^2) s :=
  fun x hx => (hf x hx).normSq

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem DifferentiableOn.norm (hf : DifferentiableOn ℝ f s) (h0 : ∀ x _ : x ∈ s, f x ≠ 0) :
  DifferentiableOn ℝ (fun y => ∥f y∥) s :=
  fun x hx => (hf x hx).norm (h0 x hx)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
theorem DifferentiableOn.dist (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
  (hne : ∀ x _ : x ∈ s, f x ≠ g x) : DifferentiableOn ℝ (fun y => dist (f y) (g y)) s :=
  fun x hx => (hf x hx).dist (hg x hx) (hne x hx)

