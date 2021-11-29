import Mathbin.MeasureTheory.Function.LpSpace

/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `mem_ℒp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `mem_ℒp 1`

In the second part, we establish an API between `integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a `normed_group`
  with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`. In comments, `[f]` is
  also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `has_finite_integral f` means `(∫⁻ a, nnnorm (f a)) < ∞`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/


noncomputable theory

open_locale Classical TopologicalSpace BigOperators Ennreal MeasureTheory Nnreal

open Set Filter TopologicalSpace Ennreal Emetric MeasureTheory

variable{α β γ δ : Type _}{m : MeasurableSpace α}{μ ν : Measureₓ α}

variable[NormedGroup β]

variable[NormedGroup γ]

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/


theorem lintegral_nnnorm_eq_lintegral_edist (f : α → β) : (∫⁻a, nnnorm (f a) ∂μ) = ∫⁻a, edist (f a) 0 ∂μ :=
  by 
    simp only [edist_eq_coe_nnnorm]

theorem lintegral_norm_eq_lintegral_edist (f : α → β) : (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) = ∫⁻a, edist (f a) 0 ∂μ :=
  by 
    simp only [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

theorem lintegral_edist_triangle [second_countable_topology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  {f g h : α → β} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hh : AeMeasurable h μ) :
  (∫⁻a, edist (f a) (g a) ∂μ) ≤ (∫⁻a, edist (f a) (h a) ∂μ)+∫⁻a, edist (g a) (h a) ∂μ :=
  by 
    rw [←lintegral_add' (hf.edist hh) (hg.edist hh)]
    refine' lintegral_mono fun a => _ 
    apply edist_triangle_right

theorem lintegral_nnnorm_zero : (∫⁻a : α, nnnorm (0 : β) ∂μ) = 0 :=
  by 
    simp 

theorem lintegral_nnnorm_add [MeasurableSpace β] [OpensMeasurableSpace β] [MeasurableSpace γ] [OpensMeasurableSpace γ]
  {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
  (∫⁻a, nnnorm (f a)+nnnorm (g a) ∂μ) = (∫⁻a, nnnorm (f a) ∂μ)+∫⁻a, nnnorm (g a) ∂μ :=
  lintegral_add' hf.ennnorm hg.ennnorm

theorem lintegral_nnnorm_neg {f : α → β} : (∫⁻a, nnnorm ((-f) a) ∂μ) = ∫⁻a, nnnorm (f a) ∂μ :=
  by 
    simp only [Pi.neg_apply, nnnorm_neg]

/-! ### The predicate `has_finite_integral` -/


/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def has_finite_integral {m : MeasurableSpace α} (f : α → β)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  (∫⁻a, nnnorm (f a) ∂μ) < ∞

theorem has_finite_integral_iff_norm (f : α → β) : has_finite_integral f μ ↔ (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) < ∞ :=
  by 
    simp only [has_finite_integral, of_real_norm_eq_coe_nnnorm]

theorem has_finite_integral_iff_edist (f : α → β) : has_finite_integral f μ ↔ (∫⁻a, edist (f a) 0 ∂μ) < ∞ :=
  by 
    simp only [has_finite_integral_iff_norm, edist_dist, dist_zero_right]

theorem has_finite_integral_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
  has_finite_integral f μ ↔ (∫⁻a, Ennreal.ofReal (f a) ∂μ) < ∞ :=
  have lintegral_eq : (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) = ∫⁻a, Ennreal.ofReal (f a) ∂μ :=
    by 
      refine' lintegral_congr_ae (h.mono$ fun a h => _)
      rwa [Real.norm_eq_abs, abs_of_nonneg]
  by 
    rw [has_finite_integral_iff_norm, lintegral_eq]

theorem has_finite_integral_iff_of_nnreal {f : α →  ℝ≥0 } :
  has_finite_integral (fun x => (f x : ℝ)) μ ↔ (∫⁻a, f a ∂μ) < ∞ :=
  by 
    simp [has_finite_integral_iff_norm]

theorem has_finite_integral.mono {f : α → β} {g : α → γ} (hg : has_finite_integral g μ) (h : ∀ᵐa ∂μ, ∥f a∥ ≤ ∥g a∥) :
  has_finite_integral f μ :=
  by 
    simp only [has_finite_integral_iff_norm] at *
    calc (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) ≤ ∫⁻a : α, Ennreal.ofReal ∥g a∥ ∂μ :=
      lintegral_mono_ae (h.mono$ fun a h => of_real_le_of_real h)_ < ∞ := hg

theorem has_finite_integral.mono' {f : α → β} {g : α → ℝ} (hg : has_finite_integral g μ) (h : ∀ᵐa ∂μ, ∥f a∥ ≤ g a) :
  has_finite_integral f μ :=
  hg.mono$ h.mono$ fun x hx => le_transₓ hx (le_abs_self _)

theorem has_finite_integral.congr' {f : α → β} {g : α → γ} (hf : has_finite_integral f μ) (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral g μ :=
  hf.mono$ eventually_eq.le$ eventually_eq.symm h

theorem has_finite_integral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) :
  has_finite_integral f μ ↔ has_finite_integral g μ :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr'$ eventually_eq.symm h⟩

theorem has_finite_integral.congr {f g : α → β} (hf : has_finite_integral f μ) (h : f =ᵐ[μ] g) :
  has_finite_integral g μ :=
  hf.congr'$ h.fun_comp norm

theorem has_finite_integral_congr {f g : α → β} (h : f =ᵐ[μ] g) : has_finite_integral f μ ↔ has_finite_integral g μ :=
  has_finite_integral_congr'$ h.fun_comp norm

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_finite_integral_const_iff
{c : β} : «expr ↔ »(has_finite_integral (λ x : α, c) μ, «expr ∨ »(«expr = »(c, 0), «expr < »(μ univ, «expr∞»()))) :=
by simp [] [] [] ["[", expr has_finite_integral, ",", expr lintegral_const, ",", expr lt_top_iff_ne_top, ",", expr or_iff_not_imp_left, "]"] [] []

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_finite_integral_const [is_finite_measure μ] (c : β) : has_finite_integral (λ x : α, c) μ :=
has_finite_integral_const_iff.2 «expr $ »(or.inr, measure_lt_top _ _)

theorem has_finite_integral_of_bounded [is_finite_measure μ] {f : α → β} {C : ℝ} (hC : ∀ᵐa ∂μ, ∥f a∥ ≤ C) :
  has_finite_integral f μ :=
  (has_finite_integral_const C).mono' hC

theorem has_finite_integral.mono_measure {f : α → β} (h : has_finite_integral f ν) (hμ : μ ≤ ν) :
  has_finite_integral f μ :=
  lt_of_le_of_ltₓ (lintegral_mono' hμ (le_reflₓ _)) h

theorem has_finite_integral.add_measure {f : α → β} (hμ : has_finite_integral f μ) (hν : has_finite_integral f ν) :
  has_finite_integral f (μ+ν) :=
  by 
    simp only [has_finite_integral, lintegral_add_measure] at *
    exact add_lt_top.2 ⟨hμ, hν⟩

theorem has_finite_integral.left_of_add_measure {f : α → β} (h : has_finite_integral f (μ+ν)) :
  has_finite_integral f μ :=
  h.mono_measure$ measure.le_add_right$ le_reflₓ _

theorem has_finite_integral.right_of_add_measure {f : α → β} (h : has_finite_integral f (μ+ν)) :
  has_finite_integral f ν :=
  h.mono_measure$ measure.le_add_left$ le_reflₓ _

@[simp]
theorem has_finite_integral_add_measure {f : α → β} :
  has_finite_integral f (μ+ν) ↔ has_finite_integral f μ ∧ has_finite_integral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

theorem has_finite_integral.smul_measure {f : α → β} (h : has_finite_integral f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
  has_finite_integral f (c • μ) :=
  by 
    simp only [has_finite_integral, lintegral_smul_measure] at *
    exact mul_lt_top hc h.ne

@[simp]
theorem has_finite_integral_zero_measure {m : MeasurableSpace α} (f : α → β) : has_finite_integral f (0 : Measureₓ α) :=
  by 
    simp only [has_finite_integral, lintegral_zero_measure, WithTop.zero_lt_top]

variable(α β μ)

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem has_finite_integral_zero : has_finite_integral (λ a : α, (0 : β)) μ :=
by simp [] [] [] ["[", expr has_finite_integral, "]"] [] []

variable{α β μ}

theorem has_finite_integral.neg {f : α → β} (hfi : has_finite_integral f μ) : has_finite_integral (-f) μ :=
  by 
    simpa [has_finite_integral] using hfi

@[simp]
theorem has_finite_integral_neg_iff {f : α → β} : has_finite_integral (-f) μ ↔ has_finite_integral f μ :=
  ⟨fun h => neg_negₓ f ▸ h.neg, has_finite_integral.neg⟩

theorem has_finite_integral.norm {f : α → β} (hfi : has_finite_integral f μ) : has_finite_integral (fun a => ∥f a∥) μ :=
  have eq : (fun a => (nnnorm ∥f a∥ : ℝ≥0∞)) = fun a => (nnnorm (f a) : ℝ≥0∞) :=
    by 
      funext 
      rw [nnnorm_norm]
  by 
    rwa [has_finite_integral, Eq]

theorem has_finite_integral_norm_iff (f : α → β) : has_finite_integral (fun a => ∥f a∥) μ ↔ has_finite_integral f μ :=
  has_finite_integral_congr'$ eventually_of_forall$ fun x => norm_norm (f x)

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_finite_integral_to_real_of_lintegral_ne_top
{f : α → «exprℝ≥0∞»()}
(hf : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»())) : has_finite_integral (λ x, (f x).to_real) μ :=
begin
  have [] [":", expr ∀
   x, «expr = »((«expr∥ ∥₊»((f x).to_real) : «exprℝ≥0∞»()), @coe «exprℝ≥0»() «exprℝ≥0∞»() _ (⟨(f x).to_real, ennreal.to_real_nonneg⟩ : «exprℝ≥0»()))] [],
  { intro [ident x],
    rw [expr real.nnnorm_of_nonneg] [] },
  simp_rw ["[", expr has_finite_integral, ",", expr this, "]"] [],
  refine [expr lt_of_le_of_lt (lintegral_mono (λ x, _)) (lt_top_iff_ne_top.2 hf)],
  by_cases [expr hfx, ":", expr «expr = »(f x, «expr∞»())],
  { simp [] [] [] ["[", expr hfx, "]"] [] [] },
  { lift [expr f x] ["to", expr «exprℝ≥0»()] ["using", expr hfx] ["with", ident fx],
    simp [] [] [] ["[", "<-", expr h, "]"] [] [] }
end

theorem is_finite_measure_with_density_of_real {f : α → ℝ} (hfi : has_finite_integral f μ) :
  is_finite_measure (μ.with_density fun x => Ennreal.ofReal$ f x) :=
  by 
    refine' is_finite_measure_with_density ((lintegral_mono$ fun x => _).trans_lt hfi).Ne 
    exact Real.of_real_le_ennnorm (f x)

section DominatedConvergence

variable{F : ℕ → α → β}{f : α → β}{bound : α → ℝ}

theorem all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐa ∂μ, ∥F n a∥ ≤ bound a) :
  ∀ n, ∀ᵐa ∂μ, Ennreal.ofReal ∥F n a∥ ≤ Ennreal.ofReal (bound a) :=
  fun n => (h n).mono$ fun a h => Ennreal.of_real_le_of_real h

theorem all_ae_tendsto_of_real_norm (h : ∀ᵐa ∂μ, tendsto (fun n => F n a) at_top$ 𝓝$ f a) :
  ∀ᵐa ∂μ, tendsto (fun n => Ennreal.ofReal ∥F n a∥) at_top$ 𝓝$ Ennreal.ofReal ∥f a∥ :=
  h.mono$ fun a h => tendsto_of_real$ tendsto.comp (Continuous.tendsto continuous_norm _) h

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem all_ae_of_real_f_le_bound
(h_bound : ∀ n, «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(F n a), bound a)))
(h_lim : «expr∀ᵐ ∂ , »((a), μ, tendsto (λ
   n, F n a) at_top (expr𝓝() (f a)))) : «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(ennreal.of_real «expr∥ ∥»(f a), ennreal.of_real (bound a))) :=
begin
  have [ident F_le_bound] [] [":=", expr all_ae_of_real_F_le_bound h_bound],
  rw ["<-", expr ae_all_iff] ["at", ident F_le_bound],
  apply [expr F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _)],
  assume [binders (a tendsto_norm F_le_bound)],
  exact [expr le_of_tendsto' tendsto_norm F_le_bound]
end

theorem has_finite_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  (bound_has_finite_integral : has_finite_integral bound μ) (h_bound : ∀ n, ∀ᵐa ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐa ∂μ, tendsto (fun n => F n a) at_top (𝓝 (f a))) : has_finite_integral f μ :=
  by 
    rw [has_finite_integral_iff_norm]
    calc (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) ≤ ∫⁻a, Ennreal.ofReal (bound a) ∂μ :=
      lintegral_mono_ae$ all_ae_of_real_f_le_bound h_bound h_lim _ < ∞ :=
      by 
        rw [←has_finite_integral_iff_of_real]
        ·
          exact bound_has_finite_integral 
        exact (h_bound 0).mono fun a h => le_transₓ (norm_nonneg _) h

theorem tendsto_lintegral_norm_of_dominated_convergence [MeasurableSpace β] [BorelSpace β] [second_countable_topology β]
  {F : ℕ → α → β} {f : α → β} {bound : α → ℝ} (F_measurable : ∀ n, AeMeasurable (F n) μ)
  (bound_has_finite_integral : has_finite_integral bound μ) (h_bound : ∀ n, ∀ᵐa ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐa ∂μ, tendsto (fun n => F n a) at_top (𝓝 (f a))) :
  tendsto (fun n => ∫⁻a, Ennreal.ofReal ∥F n a - f a∥ ∂μ) at_top (𝓝 0) :=
  have f_measurable : AeMeasurable f μ := ae_measurable_of_tendsto_metric_ae F_measurable h_lim 
  let b := fun a => 2*Ennreal.ofReal (bound a)
  have hb : ∀ n, ∀ᵐa ∂μ, Ennreal.ofReal ∥F n a - f a∥ ≤ b a :=
    by 
      intro n 
      filterUpwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim]
      intro a h₁ h₂ 
      calc Ennreal.ofReal ∥F n a - f a∥ ≤ Ennreal.ofReal ∥F n a∥+Ennreal.ofReal ∥f a∥ :=
        by 
          rw [←Ennreal.of_real_add]
          apply of_real_le_of_real
          ·
            apply norm_sub_le
          ·
            exact norm_nonneg _
          ·
            exact norm_nonneg _ _ ≤ Ennreal.ofReal (bound a)+Ennreal.ofReal (bound a) :=
        add_le_add h₁ h₂ _ = b a :=
        by 
          rw [←two_mul]
  have h : ∀ᵐa ∂μ, tendsto (fun n => Ennreal.ofReal ∥F n a - f a∥) at_top (𝓝 0) :=
    by 
      rw [←Ennreal.of_real_zero]
      refine' h_lim.mono fun a h => (continuous_of_real.tendsto _).comp _ 
      rwa [←tendsto_iff_norm_tendsto_zero]
  by 
    suffices h : tendsto (fun n => ∫⁻a, Ennreal.ofReal ∥F n a - f a∥ ∂μ) at_top (𝓝 (∫⁻a : α, 0 ∂μ))
    ·
      rwa [lintegral_zero] at h 
    refine' tendsto_lintegral_of_dominated_convergence' _ _ hb _ _
    ·
      exact fun n => measurable_of_real.comp_ae_measurable ((F_measurable n).sub f_measurable).norm
    ·
      rw [has_finite_integral_iff_of_real] at bound_has_finite_integral
      ·
        calc (∫⁻a, b a ∂μ) = 2*∫⁻a, Ennreal.ofReal (bound a) ∂μ :=
          by 
            rw [lintegral_const_mul']
            exact coe_ne_top _ ≠ ∞ :=
          mul_ne_top coe_ne_top bound_has_finite_integral.ne 
      filterUpwards [h_bound 0] fun a h => le_transₓ (norm_nonneg _) h
    ·
      exact h

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of a `L¹` function -/


theorem has_finite_integral.max_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (fun a => max (f a) 0) μ :=
  hf.mono$
    eventually_of_forall$
      fun x =>
        by 
          simp [Real.norm_eq_abs, abs_le, abs_nonneg, le_abs_self]

theorem has_finite_integral.min_zero {f : α → ℝ} (hf : has_finite_integral f μ) :
  has_finite_integral (fun a => min (f a) 0) μ :=
  hf.mono$
    eventually_of_forall$
      fun x =>
        by 
          simp [Real.norm_eq_abs, abs_le, abs_nonneg, neg_le, neg_le_abs_self, abs_eq_max_neg, le_totalₓ]

end PosPart

section NormedSpace

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 β]

theorem has_finite_integral.smul (c : 𝕜) {f : α → β} : has_finite_integral f μ → has_finite_integral (c • f) μ :=
  by 
    simp only [has_finite_integral]
    intro hfi 
    calc (∫⁻a : α, nnnorm (c • f a) ∂μ) = ∫⁻a : α, nnnorm c*nnnorm (f a) ∂μ :=
      by 
        simp only [nnnorm_smul, Ennreal.coe_mul]_ < ∞ :=
      by 
        rw [lintegral_const_mul']
        exacts[mul_lt_top coe_ne_top hfi.ne, coe_ne_top]

theorem has_finite_integral_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
  has_finite_integral (c • f) μ ↔ has_finite_integral f μ :=
  by 
    split 
    ·
      intro h 
      simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.smul (c⁻¹)
    exact has_finite_integral.smul _

theorem has_finite_integral.const_mul {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (fun x => c*f x) μ :=
  (has_finite_integral.smul c h : _)

theorem has_finite_integral.mul_const {f : α → ℝ} (h : has_finite_integral f μ) (c : ℝ) :
  has_finite_integral (fun x => f x*c) μ :=
  by 
    simpRw [mul_commₓ, h.const_mul _]

end NormedSpace

/-! ### The predicate `integrable` -/


variable[MeasurableSpace β][MeasurableSpace γ][MeasurableSpace δ]

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def integrable {α} {m : MeasurableSpace α} (f : α → β)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  AeMeasurable f μ ∧ has_finite_integral f μ

theorem integrable.ae_measurable {f : α → β} (hf : integrable f μ) : AeMeasurable f μ :=
  hf.1

theorem integrable.has_finite_integral {f : α → β} (hf : integrable f μ) : has_finite_integral f μ :=
  hf.2

theorem integrable.mono {f : α → β} {g : α → γ} (hg : integrable g μ) (hf : AeMeasurable f μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ ≤ ∥g a∥) : integrable f μ :=
  ⟨hf, hg.has_finite_integral.mono h⟩

theorem integrable.mono' {f : α → β} {g : α → ℝ} (hg : integrable g μ) (hf : AeMeasurable f μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ ≤ g a) : integrable f μ :=
  ⟨hf, hg.has_finite_integral.mono' h⟩

theorem integrable.congr' {f : α → β} {g : α → γ} (hf : integrable f μ) (hg : AeMeasurable g μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) : integrable g μ :=
  ⟨hg, hf.has_finite_integral.congr' h⟩

theorem integrable_congr' {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) : integrable f μ ↔ integrable g μ :=
  ⟨fun h2f => h2f.congr' hg h, fun h2g => h2g.congr' hf$ eventually_eq.symm h⟩

theorem integrable.congr {f g : α → β} (hf : integrable f μ) (h : f =ᵐ[μ] g) : integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩

theorem integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) : integrable f μ ↔ integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_const_iff
{c : β} : «expr ↔ »(integrable (λ x : α, c) μ, «expr ∨ »(«expr = »(c, 0), «expr < »(μ univ, «expr∞»()))) :=
begin
  have [] [":", expr ae_measurable (λ x : α, c) μ] [":=", expr measurable_const.ae_measurable],
  rw ["[", expr integrable, ",", expr and_iff_right this, ",", expr has_finite_integral_const_iff, "]"] []
end

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem integrable_const [is_finite_measure μ] (c : β) : integrable (λ x : α, c) μ :=
«expr $ »(integrable_const_iff.2, «expr $ »(or.inr, measure_lt_top _ _))

theorem integrable.mono_measure {f : α → β} (h : integrable f ν) (hμ : μ ≤ ν) : integrable f μ :=
  ⟨h.ae_measurable.mono_measure hμ, h.has_finite_integral.mono_measure hμ⟩

theorem integrable.add_measure {f : α → β} (hμ : integrable f μ) (hν : integrable f ν) : integrable f (μ+ν) :=
  ⟨hμ.ae_measurable.add_measure hν.ae_measurable, hμ.has_finite_integral.add_measure hν.has_finite_integral⟩

theorem integrable.left_of_add_measure {f : α → β} (h : integrable f (μ+ν)) : integrable f μ :=
  h.mono_measure$ measure.le_add_right$ le_reflₓ _

theorem integrable.right_of_add_measure {f : α → β} (h : integrable f (μ+ν)) : integrable f ν :=
  h.mono_measure$ measure.le_add_left$ le_reflₓ _

@[simp]
theorem integrable_add_measure {f : α → β} : integrable f (μ+ν) ↔ integrable f μ ∧ integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

theorem integrable.smul_measure {f : α → β} (h : integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) : integrable f (c • μ) :=
  ⟨h.ae_measurable.smul_measure c, h.has_finite_integral.smul_measure hc⟩

theorem integrable_map_measure [OpensMeasurableSpace β] {f : α → δ} {g : δ → β} (hg : AeMeasurable g (measure.map f μ))
  (hf : Measurable f) : integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
  by 
    simp [integrable, hg, hg.comp_measurable hf, has_finite_integral, lintegral_map' hg.ennnorm hf]

theorem _root_.measurable_embedding.integrable_map_iff {f : α → δ} (hf : MeasurableEmbedding f) {g : δ → β} :
  integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
  by 
    simp only [integrable, hf.ae_measurable_map_iff, has_finite_integral, hf.lintegral_map]

theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → β) : integrable g (measure.map f μ) ↔ integrable (g ∘ f) μ :=
  f.measurable_embedding.integrable_map_iff

theorem measure_preserving.integrable_comp [OpensMeasurableSpace β] {ν : Measureₓ δ} {g : δ → β} {f : α → δ}
  (hf : measure_preserving f μ ν) (hg : AeMeasurable g ν) : integrable (g ∘ f) μ ↔ integrable g ν :=
  by 
    rw [←hf.map_eq] at hg⊢
    exact (integrable_map_measure hg hf.measurable).symm

theorem measure_preserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : measure_preserving f μ ν)
  (h₂ : MeasurableEmbedding f) {g : δ → β} : integrable (g ∘ f) μ ↔ integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top [second_countable_topology β] [OpensMeasurableSpace β] {f g : α → β}
  (hf : integrable f μ) (hg : integrable g μ) : (∫⁻a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_ltₓ
    (lintegral_edist_triangle hf.ae_measurable hg.ae_measurable
      (measurable_const.AeMeasurable : AeMeasurable (fun a => (0 : β)) μ))
    (Ennreal.add_lt_top.2$
      by 
        simpRw [←has_finite_integral_iff_edist]
        exact ⟨hf.has_finite_integral, hg.has_finite_integral⟩)

variable(α β μ)

@[simp]
theorem integrable_zero : integrable (fun _ => (0 : β)) μ :=
  by 
    simp [integrable, measurable_const.ae_measurable]

variable{α β μ}

theorem integrable.add' [OpensMeasurableSpace β] {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) :
  has_finite_integral (f+g) μ :=
  calc (∫⁻a, nnnorm (f a+g a) ∂μ) ≤ ∫⁻a, nnnorm (f a)+nnnorm (g a) ∂μ :=
    lintegral_mono
      fun a =>
        by 
          exactModCast nnnorm_add_le _ _ 
    _ = _ := lintegral_nnnorm_add hf.ae_measurable hg.ae_measurable 
    _ < ∞ := add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩
    

theorem integrable.add [BorelSpace β] [second_countable_topology β] {f g : α → β} (hf : integrable f μ)
  (hg : integrable g μ) : integrable (f+g) μ :=
  ⟨hf.ae_measurable.add hg.ae_measurable, hf.add' hg⟩

theorem integrable_finset_sum {ι} [BorelSpace β] [second_countable_topology β] (s : Finset ι) {f : ι → α → β}
  (hf : ∀ i (_ : i ∈ s), integrable (f i) μ) : integrable (fun a => ∑i in s, f i a) μ :=
  by 
    simp only [←Finset.sum_apply]
    exact Finset.sum_induction f (fun g => integrable g μ) (fun _ _ => integrable.add) (integrable_zero _ _ _) hf

theorem integrable.neg [BorelSpace β] {f : α → β} (hf : integrable f μ) : integrable (-f) μ :=
  ⟨hf.ae_measurable.neg, hf.has_finite_integral.neg⟩

@[simp]
theorem integrable_neg_iff [BorelSpace β] {f : α → β} : integrable (-f) μ ↔ integrable f μ :=
  ⟨fun h => neg_negₓ f ▸ h.neg, integrable.neg⟩

theorem integrable.sub' [OpensMeasurableSpace β] {f g : α → β} (hf : integrable f μ) (hg : integrable g μ) :
  has_finite_integral (f - g) μ :=
  calc (∫⁻a, nnnorm (f a - g a) ∂μ) ≤ ∫⁻a, nnnorm (f a)+nnnorm (-g a) ∂μ :=
    lintegral_mono
      fun a =>
        by 
          simp only [sub_eq_add_neg]
          exactModCast nnnorm_add_le _ _ 
    _ = _ :=
    by 
      simp only [nnnorm_neg]
      exact lintegral_nnnorm_add hf.ae_measurable hg.ae_measurable 
    _ < ∞ := add_lt_top.2 ⟨hf.has_finite_integral, hg.has_finite_integral⟩
    

theorem integrable.sub [BorelSpace β] [second_countable_topology β] {f g : α → β} (hf : integrable f μ)
  (hg : integrable g μ) : integrable (f - g) μ :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem integrable.norm [OpensMeasurableSpace β] {f : α → β} (hf : integrable f μ) : integrable (fun a => ∥f a∥) μ :=
  ⟨hf.ae_measurable.norm, hf.has_finite_integral.norm⟩

theorem integrable_norm_iff [OpensMeasurableSpace β] {f : α → β} (hf : AeMeasurable f μ) :
  integrable (fun a => ∥f a∥) μ ↔ integrable f μ :=
  by 
    simpRw [integrable, and_iff_right hf, and_iff_right hf.norm, has_finite_integral_norm_iff]

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_of_norm_sub_le
[opens_measurable_space β]
{f₀ f₁ : α → β}
{g : α → exprℝ()}
(hf₁_m : ae_measurable f₁ μ)
(hf₀_i : integrable f₀ μ)
(hg_i : integrable g μ)
(h : «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(«expr - »(f₀ a, f₁ a)), g a))) : integrable f₁ μ :=
begin
  have [] [":", expr «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(f₁ a), «expr + »(«expr∥ ∥»(f₀ a), g a)))] [],
  { apply [expr h.mono],
    intros [ident a, ident ha],
    calc
      «expr ≤ »(«expr∥ ∥»(f₁ a), «expr + »(«expr∥ ∥»(f₀ a), «expr∥ ∥»(«expr - »(f₀ a, f₁ a)))) : norm_le_insert _ _
      «expr ≤ »(..., «expr + »(«expr∥ ∥»(f₀ a), g a)) : add_le_add_left ha _ },
  exact [expr integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this]
end

theorem integrable.prod_mk [OpensMeasurableSpace β] [OpensMeasurableSpace γ] {f : α → β} {g : α → γ}
  (hf : integrable f μ) (hg : integrable g μ) : integrable (fun x => (f x, g x)) μ :=
  ⟨hf.ae_measurable.prod_mk hg.ae_measurable,
    (hf.norm.add' hg.norm).mono$
      eventually_of_forall$
        fun x =>
          calc max ∥f x∥ ∥g x∥ ≤ ∥f x∥+∥g x∥ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
            _ ≤ ∥∥f x∥+∥g x∥∥ := le_abs_self _
            ⟩

theorem mem_ℒp_one_iff_integrable {f : α → β} : mem_ℒp f 1 μ ↔ integrable f μ :=
  by 
    simpRw [integrable, has_finite_integral, mem_ℒp, snorm_one_eq_lintegral_nnnorm]

theorem mem_ℒp.integrable [BorelSpace β] {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → β} [is_finite_measure μ]
  (hfq : mem_ℒp f q μ) : integrable f μ :=
  mem_ℒp_one_iff_integrable.mp (hfq.mem_ℒp_of_exponent_le hq1)

theorem lipschitz_with.integrable_comp_iff_of_antilipschitz [CompleteSpace β] [BorelSpace β] [BorelSpace γ] {K K'}
  {f : α → β} {g : β → γ} (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
  integrable (g ∘ f) μ ↔ integrable f μ :=
  by 
    simp [←mem_ℒp_one_iff_integrable, hg.mem_ℒp_comp_iff_of_antilipschitz hg' g0]

theorem integrable.real_to_nnreal {f : α → ℝ} (hf : integrable f μ) : integrable (fun x => ((f x).toNnreal : ℝ)) μ :=
  by 
    refine' ⟨hf.ae_measurable.real_to_nnreal.coe_nnreal_real, _⟩
    rw [has_finite_integral_iff_norm]
    refine' lt_of_le_of_ltₓ _ ((has_finite_integral_iff_norm _).1 hf.has_finite_integral)
    apply lintegral_mono 
    intro x 
    simp [Real.norm_eq_abs, Ennreal.of_real_le_of_real, abs_le, abs_nonneg, le_abs_self]

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_real_to_real_ae_eq
{f : α → «exprℝ≥0∞»()}
(hf : «expr∀ᵐ ∂ , »((x), μ, «expr < »(f x, «expr∞»()))) : «expr =ᵐ[ ] »(λ x, ennreal.of_real (f x).to_real, μ, f) :=
begin
  rw [expr ae_iff] ["at", ident hf],
  rw ["[", expr filter.eventually_eq, ",", expr ae_iff, "]"] [],
  have [] [":", expr «expr = »({x | «expr¬ »(«expr = »(ennreal.of_real (f x).to_real, f x))}, {x | «expr = »(f x, «expr∞»())})] [],
  { ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr ne.def, ",", expr set.mem_set_of_eq, "]"] [] [],
    split; intro [ident hx],
    { by_contra [ident hntop],
      exact [expr hx (ennreal.of_real_to_real hntop)] },
    { rw [expr hx] [],
      simp [] [] [] [] [] [] } },
  rw [expr this] [],
  simpa [] [] [] [] [] ["using", expr hf]
end

theorem integrable_with_density_iff {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐx ∂μ, f x < ∞) {g : α → ℝ}
  (hg : Measurable g) : integrable g (μ.with_density f) ↔ integrable (fun x => g x*(f x).toReal) μ :=
  by 
    simp only [integrable, has_finite_integral, hg.ae_measurable.mul hf.ae_measurable.ennreal_to_real, hg.ae_measurable,
      true_andₓ, coe_mul, NormedField.nnnorm_mul]
    suffices h_int_eq : (∫⁻a, ∥g a∥₊ ∂μ.with_density f) = ∫⁻a, ∥g a∥₊*∥(f a).toReal∥₊ ∂μ
    ·
      rw [h_int_eq]
    rw [lintegral_with_density_eq_lintegral_mul _ hf hg.nnnorm.coe_nnreal_ennreal]
    refine' lintegral_congr_ae _ 
    rw [mul_commₓ]
    refine' Filter.EventuallyEq.mul (ae_eq_refl _) ((of_real_to_real_ae_eq hflt).symm.trans _)
    convert ae_eq_refl _ 
    ext1 x 
    exact Real.ennnorm_eq_of_real Ennreal.to_real_nonneg

theorem mem_ℒ1_to_real_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) (hfi : (∫⁻x, f x ∂μ) ≠ ∞) :
  mem_ℒp (fun x => (f x).toReal) 1 μ :=
  by 
    rw [mem_ℒp, snorm_one_eq_lintegral_nnnorm]
    exact ⟨AeMeasurable.ennreal_to_real hfm, has_finite_integral_to_real_of_lintegral_ne_top hfi⟩

theorem integrable_to_real_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) (hfi : (∫⁻x, f x ∂μ) ≠ ∞) :
  integrable (fun x => (f x).toReal) μ :=
  mem_ℒp_one_iff_integrable.1$ mem_ℒ1_to_real_of_lintegral_ne_top hfm hfi

section PosPart

/-! ### Lemmas used for defining the positive part of a `L¹` function -/


theorem integrable.max_zero {f : α → ℝ} (hf : integrable f μ) : integrable (fun a => max (f a) 0) μ :=
  ⟨hf.ae_measurable.max measurable_const.AeMeasurable, hf.has_finite_integral.max_zero⟩

theorem integrable.min_zero {f : α → ℝ} (hf : integrable f μ) : integrable (fun a => min (f a) 0) μ :=
  ⟨hf.ae_measurable.min measurable_const.AeMeasurable, hf.has_finite_integral.min_zero⟩

end PosPart

section NormedSpace

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 β][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem integrable.smul [BorelSpace β] (c : 𝕜) {f : α → β} (hf : integrable f μ) : integrable (c • f) μ :=
  ⟨hf.ae_measurable.const_smul c, hf.has_finite_integral.smul c⟩

theorem integrable_smul_iff [BorelSpace β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) : integrable (c • f) μ ↔ integrable f μ :=
  and_congr (ae_measurable_const_smul_iff₀ hc) (has_finite_integral_smul_iff hc f)

theorem integrable.const_mul {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (fun x => c*f x) μ :=
  integrable.smul c h

theorem integrable.mul_const {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (fun x => f x*c) μ :=
  by 
    simpRw [mul_commₓ, h.const_mul _]

end NormedSpace

section NormedSpaceOverCompleteField

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜][CompleteSpace 𝕜][MeasurableSpace 𝕜]

variable[BorelSpace 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E][MeasurableSpace E][BorelSpace E]

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_smul_const
{f : α → 𝕜}
{c : E}
(hc : «expr ≠ »(c, 0)) : «expr ↔ »(integrable (λ x, «expr • »(f x, c)) μ, integrable f μ) :=
begin
  simp_rw ["[", expr integrable, ",", expr ae_measurable_smul_const hc, ",", expr and.congr_right_iff, ",", expr has_finite_integral, ",", expr nnnorm_smul, ",", expr ennreal.coe_mul, "]"] [],
  intro [ident hf],
  rw ["[", expr lintegral_mul_const' _ _ ennreal.coe_ne_top, ",", expr ennreal.mul_lt_top_iff, "]"] [],
  have [] [":", expr ∀
   x : «exprℝ≥0∞»(), «expr = »(x, 0) → «expr < »(x, «expr∞»())] [":=", expr by simp [] [] [] [] [] []],
  simp [] [] [] ["[", expr hc, ",", expr or_iff_left_of_imp (this _), "]"] [] []
end

end NormedSpaceOverCompleteField

section IsROrC

variable{𝕜 : Type _}[IsROrC 𝕜]{f : α → 𝕜}

theorem integrable.of_real {f : α → ℝ} (hf : integrable f μ) : integrable (fun x => (f x : 𝕜)) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf⊢
    exact hf.of_real

theorem integrable.re_im_iff :
  integrable (fun x => IsROrC.re (f x)) μ ∧ integrable (fun x => IsROrC.im (f x)) μ ↔ integrable f μ :=
  by 
    simpRw [←mem_ℒp_one_iff_integrable]
    exact mem_ℒp_re_im_iff

theorem integrable.re (hf : integrable f μ) : integrable (fun x => IsROrC.re (f x)) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf⊢
    exact hf.re

theorem integrable.im (hf : integrable f μ) : integrable (fun x => IsROrC.im (f x)) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf⊢
    exact hf.im

end IsROrC

section InnerProduct

variable{𝕜 E :
    Type
      _}[IsROrC
      𝕜][InnerProductSpace 𝕜 E][MeasurableSpace E][OpensMeasurableSpace E][second_countable_topology E]{f : α → E}

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

theorem integrable.const_inner (c : E) (hf : integrable f μ) : integrable (fun x => ⟪c, f x⟫) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf⊢
    exact hf.const_inner c

theorem integrable.inner_const (hf : integrable f μ) (c : E) : integrable (fun x => ⟪f x, c⟫) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf⊢
    exact hf.inner_const c

end InnerProduct

section Trim

variable{H :
    Type
      _}[NormedGroup H][MeasurableSpace H][OpensMeasurableSpace H]{m0 : MeasurableSpace α}{μ' : Measureₓ α}{f : α → H}

theorem integrable.trim (hm : m ≤ m0) (hf_int : integrable f μ') (hf : @Measurable _ _ m _ f) :
  integrable f (μ'.trim hm) :=
  by 
    refine' ⟨Measurable.ae_measurable hf, _⟩
    rw [has_finite_integral, lintegral_trim hm _]
    ·
      exact hf_int.2
    ·
      exact @Measurable.coe_nnreal_ennreal α m _ (@Measurable.nnnorm _ α _ _ _ m _ hf)

theorem integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : integrable f (μ'.trim hm)) : integrable f μ' :=
  by 
    obtain ⟨hf_meas_ae, hf⟩ := hf_int 
    refine' ⟨ae_measurable_of_ae_measurable_trim hm hf_meas_ae, _⟩
    rw [has_finite_integral] at hf⊢
    rwa [lintegral_trim_ae hm _] at hf 
    exact @AeMeasurable.coe_nnreal_ennreal α m _ _ (@AeMeasurable.nnnorm H α _ _ _ m _ _ hf_meas_ae)

end Trim

section SigmaFinite

variable{E : Type _}{m0 : MeasurableSpace α}[NormedGroup E][MeasurableSpace E][OpensMeasurableSpace E]

theorem integrable_of_forall_fin_meas_le' {μ : Measureₓ α} (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (C : ℝ≥0∞)
  (hC : C < ∞) {f : α → E} (hf_meas : AeMeasurable f μ)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻x in s, nnnorm (f x) ∂μ) ≤ C) : integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_le' hm C hf_meas.nnnorm.coe_nnreal_ennreal hf).trans_lt hC⟩

theorem integrable_of_forall_fin_meas_le [sigma_finite μ] (C : ℝ≥0∞) (hC : C < ∞) {f : α → E}
  (hf_meas : AeMeasurable f μ) (hf : ∀ (s : Set α), MeasurableSet s → μ s ≠ ∞ → (∫⁻x in s, nnnorm (f x) ∂μ) ≤ C) :
  integrable f μ :=
  @integrable_of_forall_fin_meas_le' _ _ _ _ _ _ _ _ _
    (by 
      rwa [trim_eq_self])
    C hC _ hf_meas hf

end SigmaFinite

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/


namespace AeEqFun

section 

/-- A class of almost everywhere equal functions is `integrable` if its function representative
is integrable. -/
def integrable (f : α →ₘ[μ] β) : Prop :=
  integrable f μ

theorem integrable_mk {f : α → β} (hf : AeMeasurable f μ) :
  integrable (mk f hf : α →ₘ[μ] β) ↔ MeasureTheory.Integrable f μ :=
  by 
    simp [integrable]
    apply integrable_congr 
    exact coe_fn_mk f hf

theorem integrable_coe_fn {f : α →ₘ[μ] β} : MeasureTheory.Integrable f μ ↔ integrable f :=
  by 
    rw [←integrable_mk, mk_coe_fn]

theorem integrable_zero : integrable (0 : α →ₘ[μ] β) :=
  (integrable_zero α β μ).congr (coe_fn_mk _ _).symm

end 

section 

variable[BorelSpace β]

theorem integrable.neg {f : α →ₘ[μ] β} : integrable f → integrable (-f) :=
  induction_on f$ fun f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section 

variable[second_countable_topology β]

theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : integrable f ↔ f ∈ (α →₁[μ] β) :=
  by 
    rw [←integrable_coe_fn, ←mem_ℒp_one_iff_integrable, Lp.mem_Lp_iff_mem_ℒp]

theorem integrable.add {f g : α →ₘ[μ] β} : integrable f → integrable g → integrable (f+g) :=
  by 
    refine' induction_on₂ f g fun f hf g hg hfi hgi => _ 
    simp only [integrable_mk, mk_add_mk] at hfi hgi⊢
    exact hfi.add hgi

theorem integrable.sub {f g : α →ₘ[μ] β} (hf : integrable f) (hg : integrable g) : integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end 

section NormedSpace

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 β][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : integrable f → integrable (c • f) :=
  induction_on f$ fun f hfm hfi => (integrable_mk _).2$ ((integrable_mk hfm).1 hfi).smul _

end NormedSpace

end 

end AeEqFun

namespace L1

variable[second_countable_topology β][BorelSpace β]

theorem integrable_coe_fn (f : α →₁[μ] β) : integrable f μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable]
    exact Lp.mem_ℒp f

theorem has_finite_integral_coe_fn (f : α →₁[μ] β) : has_finite_integral f μ :=
  (integrable_coe_fn f).HasFiniteIntegral

theorem measurable_coe_fn (f : α →₁[μ] β) : Measurable f :=
  Lp.measurable f

theorem ae_measurable_coe_fn (f : α →₁[μ] β) : AeMeasurable f μ :=
  Lp.ae_measurable f

theorem edist_def (f g : α →₁[μ] β) : edist f g = ∫⁻a, edist (f a) (g a) ∂μ :=
  by 
    simp [Lp.edist_def, snorm, snorm']
    simp [edist_eq_coe_nnnorm_sub]

theorem dist_def (f g : α →₁[μ] β) : dist f g = (∫⁻a, edist (f a) (g a) ∂μ).toReal :=
  by 
    simp [Lp.dist_def, snorm, snorm']
    simp [edist_eq_coe_nnnorm_sub]

theorem norm_def (f : α →₁[μ] β) : ∥f∥ = (∫⁻a, nnnorm (f a) ∂μ).toReal :=
  by 
    simp [Lp.norm_def, snorm, snorm']

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem norm_sub_eq_lintegral (f g : α →₁[μ] β) : ∥f - g∥ = (∫⁻x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ).toReal :=
  by 
    rw [norm_def]
    congr 1
    rw [lintegral_congr_ae]
    filterUpwards [Lp.coe_fn_sub f g]
    intro a ha 
    simp only [ha, Pi.sub_apply]

theorem of_real_norm_eq_lintegral (f : α →₁[μ] β) : Ennreal.ofReal ∥f∥ = ∫⁻x, (nnnorm (f x) : ℝ≥0∞) ∂μ :=
  by 
    rw [norm_def, Ennreal.of_real_to_real]
    exact ne_of_ltₓ (has_finite_integral_coe_fn f)

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem of_real_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
  Ennreal.ofReal ∥f - g∥ = ∫⁻x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ :=
  by 
    simpRw [of_real_norm_eq_lintegral, ←edist_eq_coe_nnnorm]
    apply lintegral_congr_ae 
    filterUpwards [Lp.coe_fn_sub f g]
    intro a ha 
    simp only [ha, Pi.sub_apply]

end L1

namespace Integrable

variable[second_countable_topology β][BorelSpace β]

/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `L1 β 1 μ`. -/
def to_L1 (f : α → β) (hf : integrable f μ) : α →₁[μ] β :=
  (mem_ℒp_one_iff_integrable.2 hf).toLp f

@[simp]
theorem to_L1_coe_fn (f : α →₁[μ] β) (hf : integrable f μ) : hf.to_L1 f = f :=
  by 
    simp [integrable.to_L1]

theorem coe_fn_to_L1 {f : α → β} (hf : integrable f μ) : hf.to_L1 f =ᵐ[μ] f :=
  ae_eq_fun.coe_fn_mk _ _

@[simp]
theorem to_L1_zero (h : integrable (0 : α → β) μ) : h.to_L1 0 = 0 :=
  rfl

@[simp]
theorem to_L1_eq_mk (f : α → β) (hf : integrable f μ) : (hf.to_L1 f : α →ₘ[μ] β) = ae_eq_fun.mk f hf.ae_measurable :=
  rfl

@[simp]
theorem to_L1_eq_to_L1_iff (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 f hf = to_L1 g hg ↔ f =ᵐ[μ] g :=
  mem_ℒp.to_Lp_eq_to_Lp_iff _ _

theorem to_L1_add (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f+g) (hf.add hg) = to_L1 f hf+to_L1 g hg :=
  rfl

theorem to_L1_neg (f : α → β) (hf : integrable f μ) : to_L1 (-f) (integrable.neg hf) = -to_L1 f hf :=
  rfl

theorem to_L1_sub (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  to_L1 (f - g) (hf.sub hg) = to_L1 f hf - to_L1 g hg :=
  rfl

theorem norm_to_L1 (f : α → β) (hf : integrable f μ) : ∥hf.to_L1 f∥ = Ennreal.toReal (∫⁻a, edist (f a) 0 ∂μ) :=
  by 
    simp [to_L1, snorm, snorm']
    simp [edist_eq_coe_nnnorm]

theorem norm_to_L1_eq_lintegral_norm (f : α → β) (hf : integrable f μ) :
  ∥hf.to_L1 f∥ = Ennreal.toReal (∫⁻a, Ennreal.ofReal ∥f a∥ ∂μ) :=
  by 
    rw [norm_to_L1, lintegral_norm_eq_lintegral_edist]

@[simp]
theorem edist_to_L1_to_L1 (f g : α → β) (hf : integrable f μ) (hg : integrable g μ) :
  edist (hf.to_L1 f) (hg.to_L1 g) = ∫⁻a, edist (f a) (g a) ∂μ :=
  by 
    simp [integrable.to_L1, snorm, snorm']
    simp [edist_eq_coe_nnnorm_sub]

@[simp]
theorem edist_to_L1_zero (f : α → β) (hf : integrable f μ) : edist (hf.to_L1 f) 0 = ∫⁻a, edist (f a) 0 ∂μ :=
  by 
    simp [integrable.to_L1, snorm, snorm']
    simp [edist_eq_coe_nnnorm]

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 β][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem to_L1_smul (f : α → β) (hf : integrable f μ) (k : 𝕜) : to_L1 (fun a => k • f a) (hf.smul k) = k • to_L1 f hf :=
  rfl

theorem to_L1_smul' (f : α → β) (hf : integrable f μ) (k : 𝕜) : to_L1 (k • f) (hf.smul k) = k • to_L1 f hf :=
  rfl

end Integrable

end MeasureTheory

open MeasureTheory

theorem integrable_zero_measure {m : MeasurableSpace α} [MeasurableSpace β] {f : α → β} :
  integrable f (0 : Measureₓ α) :=
  by 
    apply (integrable_zero _ _ _).congr 
    change (0 : Measureₓ α) { x | 0 ≠ f x } = 0
    rfl

variable{E :
    Type
      _}[NormedGroup
      E][MeasurableSpace
      E][BorelSpace
      E]{𝕜 : Type _}[NondiscreteNormedField 𝕜][NormedSpace 𝕜 E]{H : Type _}[NormedGroup H][NormedSpace 𝕜 H]

theorem MeasureTheory.Integrable.apply_continuous_linear_map {φ : α → H →L[𝕜] E} (φ_int : integrable φ μ) (v : H) :
  integrable (fun a => φ a v) μ :=
  (φ_int.norm.mul_const ∥v∥).mono' (φ_int.ae_measurable.apply_continuous_linear_map v)
    (eventually_of_forall$ fun a => (φ a).le_op_norm v)

variable[MeasurableSpace H][OpensMeasurableSpace H]

-- error in MeasureTheory.Function.L1Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_linear_map.integrable_comp
{φ : α → H}
(L : «expr →L[ ] »(H, 𝕜, E))
(φ_int : integrable φ μ) : integrable (λ a : α, L (φ a)) μ :=
((integrable.norm φ_int).const_mul «expr∥ ∥»(L)).mono' (L.measurable.comp_ae_measurable φ_int.ae_measurable) «expr $ »(eventually_of_forall, λ
 a, L.le_op_norm (φ a))

