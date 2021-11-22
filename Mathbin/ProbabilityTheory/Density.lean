import Mathbin.MeasureTheory.Decomposition.RadonNikodym 
import Mathbin.MeasureTheory.Measure.Lebesgue

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `measure_theory.has_pdf` : A random variable `X : α → E` is said to `has_pdf` with
  respect to the measure `ℙ` on `α` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`.
* `measure_theory.pdf` : If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.with_density f`.
* `measure_theory.pdf.uniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `measure_theory.pdf.integral_fun_mul_eq_integral` : Law of the unconscious statistician,
  i.e. if a random variable `X : α → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `measure_theory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `measure_theory.pdf.uniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/


noncomputable theory

open_locale Classical MeasureTheory Nnreal Ennreal

namespace MeasureTheory

open TopologicalSpace MeasureTheory.Measure

variable{α E :
    Type
      _}[NormedGroup E][MeasurableSpace E][second_countable_topology E][NormedSpace ℝ E][CompleteSpace E][BorelSpace E]

/-- A random variable `X : α → E` is said to `has_pdf` with respect to the measure `ℙ` on `α` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.with_density f`. -/
class
  has_pdf{m : MeasurableSpace α}(X : α → E)(ℙ : Measureₓ α)(μ : Measureₓ E :=  by 
    runTac 
      volume_tac) :
  Prop where 
  pdf' : Measurable X ∧ ∃ f : E → ℝ≥0∞, Measurable f ∧ map X ℙ = μ.with_density f

@[measurability]
theorem has_pdf.measurable {m : MeasurableSpace α} (X : α → E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac)
  [hX : has_pdf X ℙ μ] : Measurable X :=
  hX.pdf'.1

/-- If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`. -/
def pdf {m : MeasurableSpace α} (X : α → E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac) :=
  if hX : has_pdf X ℙ μ then Classical.some hX.pdf'.2 else 0

theorem pdf_undef {m : MeasurableSpace α} {ℙ : Measureₓ α} {μ : Measureₓ E} {X : α → E} (h : ¬has_pdf X ℙ μ) :
  pdf X ℙ μ = 0 :=
  by 
    simp only [pdf, dif_neg h]

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem has_pdf_of_pdf_ne_zero
{m : measurable_space α}
{ℙ : measure α}
{μ : measure E}
{X : α → E}
(h : «expr ≠ »(pdf X ℙ μ, 0)) : has_pdf X ℙ μ :=
begin
  by_contra [ident hpdf],
  rw ["[", expr pdf, ",", expr dif_neg hpdf, "]"] ["at", ident h],
  exact [expr hpdf (false.rec (has_pdf X ℙ μ) (h rfl))]
end

theorem pdf_eq_zero_of_not_measurable {m : MeasurableSpace α} {ℙ : Measureₓ α} {μ : Measureₓ E} {X : α → E}
  (hX : ¬Measurable X) : pdf X ℙ μ = 0 :=
  pdf_undef fun hpdf => hX hpdf.pdf'.1

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem measurable_of_pdf_ne_zero
{m : measurable_space α}
{ℙ : measure α}
{μ : measure E}
(X : α → E)
(h : «expr ≠ »(pdf X ℙ μ, 0)) : measurable X :=
by { by_contra [ident hX],
  exact [expr h (pdf_eq_zero_of_not_measurable hX)] }

@[measurability]
theorem measurable_pdf {m : MeasurableSpace α} (X : α → E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac) :
  Measurable (pdf X ℙ μ) :=
  by 
    byCases' hX : has_pdf X ℙ μ
    ·
      rw [pdf, dif_pos hX]
      exact (Classical.some_spec hX.pdf'.2).1
    ·
      rw [pdf, dif_neg hX]
      exact measurable_zero

theorem map_eq_with_density_pdf {m : MeasurableSpace α} (X : α → E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac)
  [hX : has_pdf X ℙ μ] : measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
  by 
    rw [pdf, dif_pos hX]
    exact (Classical.some_spec hX.pdf'.2).2

theorem map_eq_set_lintegral_pdf {m : MeasurableSpace α} (X : α → E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac)
  [hX : has_pdf X ℙ μ] {s : Set E} (hs : MeasurableSet s) : measure.map X ℙ s = ∫⁻x in s, pdf X ℙ μ x ∂μ :=
  by 
    rw [←with_density_apply _ hs, map_eq_with_density_pdf X ℙ μ]

namespace Pdf

variable{m : MeasurableSpace α}{ℙ : Measureₓ α}{μ : Measureₓ E}

theorem lintegral_eq_measure_univ {X : α → E} [has_pdf X ℙ μ] : (∫⁻x, pdf X ℙ μ x ∂μ) = ℙ Set.Univ :=
  by 
    rw [←set_lintegral_univ, ←map_eq_set_lintegral_pdf X ℙ μ MeasurableSet.univ,
      measure.map_apply (has_pdf.measurable X ℙ μ) MeasurableSet.univ, Set.preimage_univ]

theorem ae_lt_top [is_finite_measure ℙ] {μ : Measureₓ E} {X : α → E} : ∀ᵐx ∂μ, pdf X ℙ μ x < ∞ :=
  by 
    byCases' hpdf : has_pdf X ℙ μ
    ·
      haveI  := hpdf 
      refine' ae_lt_top (measurable_pdf X ℙ μ) _ 
      rw [lintegral_eq_measure_univ]
      exact (measure_lt_top _ _).Ne
    ·
      rw [pdf, dif_neg hpdf]
      exact Filter.eventually_of_forall fun x => WithTop.zero_lt_top

theorem of_real_to_real_ae_eq [is_finite_measure ℙ] {X : α → E} :
  (fun x => Ennreal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  by 
    byCases' hpdf : has_pdf X ℙ μ
    ·
      exactI of_real_to_real_ae_eq ae_lt_top
    ·
      convert ae_eq_refl _ 
      ext1 x 
      rw [pdf, dif_neg hpdf, Pi.zero_apply, Ennreal.zero_to_real, Ennreal.of_real_zero]

theorem integrable_iff_integrable_mul_pdf [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ] {f : E → ℝ}
  (hf : Measurable f) : integrable (fun x => f (X x)) ℙ ↔ integrable (fun x => f x*(pdf X ℙ μ x).toReal) μ :=
  by 
    rw [←integrable_map_measure hf.ae_measurable (has_pdf.measurable X ℙ μ), map_eq_with_density_pdf X ℙ μ,
      integrable_with_density_iff (measurable_pdf _ _ _) ae_lt_top hf]
    infer_instance

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_fun_mul_eq_integral [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ] {f : E → ℝ} (hf : Measurable f) :
  (∫x, f x*(pdf X ℙ μ x).toReal ∂μ) = ∫x, f (X x) ∂ℙ :=
  by 
    byCases' hpdf : integrable (fun x => f x*(pdf X ℙ μ x).toReal) μ
    ·
      rw [←integral_map (has_pdf.measurable X ℙ μ) hf.ae_measurable, map_eq_with_density_pdf X ℙ μ,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_of_real,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_of_real]
      ·
        congr 2
        ·
          have  :
            ∀ x, Ennreal.ofReal (f x*(pdf X ℙ μ x).toReal) = Ennreal.ofReal (pdf X ℙ μ x).toReal*Ennreal.ofReal (f x)
          ·
            intro x 
            rw [mul_commₓ, Ennreal.of_real_mul Ennreal.to_real_nonneg]
          simpRw [this]
          exact lintegral_congr_ae (Filter.EventuallyEq.mul of_real_to_real_ae_eq (ae_eq_refl _))
        ·
          have  :
            ∀ x, Ennreal.ofReal (-f x*(pdf X ℙ μ x).toReal) = Ennreal.ofReal (pdf X ℙ μ x).toReal*Ennreal.ofReal (-f x)
          ·
            intro x 
            rw [neg_mul_eq_neg_mul, mul_commₓ, Ennreal.of_real_mul Ennreal.to_real_nonneg]
          simpRw [this]
          exact lintegral_congr_ae (Filter.EventuallyEq.mul of_real_to_real_ae_eq (ae_eq_refl _))
      ·
        refine' ⟨hf.ae_measurable, _⟩
        rw [has_finite_integral,
          lintegral_with_density_eq_lintegral_mul _ (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal]
        have  : (fun x => (pdf X ℙ μ*fun x => «expr↑ » ∥f x∥₊) x) =ᵐ[μ] fun x => ∥f x*(pdf X ℙ μ x).toReal∥₊
        ·
          simpRw [←smul_eq_mul, nnnorm_smul, Ennreal.coe_mul]
          rw [smul_eq_mul, mul_commₓ]
          refine' Filter.EventuallyEq.mul (ae_eq_refl _) (ae_eq_trans of_real_to_real_ae_eq.symm _)
          convert ae_eq_refl _ 
          ext1 x 
          exact Real.ennnorm_eq_of_real Ennreal.to_real_nonneg 
        rw [lintegral_congr_ae this]
        exact hpdf.2
    ·
      rw [integral_undef hpdf, integral_undef]
      rwa [←integrable_iff_integrable_mul_pdf hf] at hpdf 
      all_goals 
        infer_instance

theorem map_absolutely_continuous {X : α → E} [has_pdf X ℙ μ] : map X ℙ ≪ μ :=
  by 
    rw [map_eq_with_density_pdf X ℙ μ]
    exact with_density_absolutely_continuous _ _

/-- A random variable that `has_pdf` is quasi-measure preserving. -/
theorem to_quasi_measure_preserving {X : α → E} [has_pdf X ℙ μ] : quasi_measure_preserving X ℙ μ :=
  { Measurable := has_pdf.measurable X ℙ μ, AbsolutelyContinuous := map_absolutely_continuous }

theorem have_lebesgue_decomposition_of_has_pdf {X : α → E} [hX' : has_pdf X ℙ μ] :
  (map X ℙ).HaveLebesgueDecomposition μ :=
  ⟨⟨⟨0, pdf X ℙ μ⟩,
      by 
        simp only [zero_addₓ, measurable_pdf X ℙ μ, true_andₓ, mutually_singular.zero_left,
          map_eq_with_density_pdf X ℙ μ]⟩⟩

theorem has_pdf_iff {X : α → E} : has_pdf X ℙ μ ↔ Measurable X ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  by 
    split 
    ·
      intro hX' 
      exactI ⟨hX'.pdf'.1, have_lebesgue_decomposition_of_has_pdf, map_absolutely_continuous⟩
    ·
      rintro ⟨hX, h_decomp, h⟩
      haveI  := h_decomp 
      refine' ⟨⟨hX, (measure.map X ℙ).rnDeriv μ, measurable_rn_deriv _ _, _⟩⟩
      rwa [with_density_rn_deriv_eq]

theorem has_pdf_iff_of_measurable {X : α → E} (hX : Measurable X) :
  has_pdf X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  by 
    rw [has_pdf_iff]
    simp only [hX, true_andₓ]

section 

variable{F :
    Type
      _}[NormedGroup
      F][MeasurableSpace F][second_countable_topology F][NormedSpace ℝ F][CompleteSpace F][BorelSpace F]{ν : Measureₓ F}

/-- A random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf` if `(map g (map X ℙ)).have_lebesgue_decomposition μ`.

`quasi_measure_preserving_has_pdf'` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasi_measure_preserving_has_pdf {X : α → E} [has_pdf X ℙ μ] {g : E → F} (hg : quasi_measure_preserving g μ ν)
  (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) : has_pdf (g ∘ X) ℙ ν :=
  by 
    rw [has_pdf_iff, ←map_map hg.measurable (has_pdf.measurable X ℙ μ)]
    refine' ⟨hg.measurable.comp (has_pdf.measurable X ℙ μ), hmap, _⟩
    rw [map_eq_with_density_pdf X ℙ μ]
    refine' absolutely_continuous.mk fun s hsm hs => _ 
    rw [map_apply hg.measurable hsm, with_density_apply _ (hg.measurable hsm)]
    have  := hg.absolutely_continuous hs 
    rw [map_apply hg.measurable hsm] at this 
    exact set_lintegral_measure_zero _ _ this

theorem quasi_measure_preserving_has_pdf' [is_finite_measure ℙ] [sigma_finite ν] {X : α → E} [has_pdf X ℙ μ] {g : E → F}
  (hg : quasi_measure_preserving g μ ν) : has_pdf (g ∘ X) ℙ ν :=
  quasi_measure_preserving_has_pdf hg inferInstance

end 

section Real

variable[is_finite_measure ℙ]{X : α → ℝ}

/-- A real-valued random variable `X` `has_pdf X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
theorem real.has_pdf_iff_of_measurable (hX : Measurable X) : has_pdf X ℙ ↔ map X ℙ ≪ volume :=
  by 
    rw [has_pdf_iff_of_measurable hX, and_iff_right_iff_imp]
    exact fun h => inferInstance

theorem real.has_pdf_iff : has_pdf X ℙ ↔ Measurable X ∧ map X ℙ ≪ volume :=
  by 
    byCases' hX : Measurable X
    ·
      rw [real.has_pdf_iff_of_measurable hX, iff_and_self]
      exact fun h => hX 
      infer_instance
    ·
      exact ⟨fun h => False.elim (hX h.pdf'.1), fun h => False.elim (hX h.1)⟩

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_mul_eq_integral [has_pdf X ℙ] : (∫x, x*(pdf X ℙ volume x).toReal) = ∫x, X x ∂ℙ :=
  integral_fun_mul_eq_integral measurable_id

theorem has_finite_integral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ =ᵐ[volume] g) (hgi : (∫⁻x, ∥f x∥₊*g x) ≠ ∞) :
  has_finite_integral fun x => f x*(pdf X ℙ volume x).toReal :=
  by 
    rw [has_finite_integral]
    have  : (fun x => «expr↑ » ∥f x∥₊*g x) =ᵐ[volume] fun x => ∥f x*(pdf X ℙ volume x).toReal∥₊
    ·
      refine'
        ae_eq_trans
          (Filter.EventuallyEq.mul (ae_eq_refl fun x => ∥f x∥₊) (ae_eq_trans hg.symm of_real_to_real_ae_eq.symm)) _ 
      simpRw [←smul_eq_mul, nnnorm_smul, Ennreal.coe_mul, smul_eq_mul]
      refine' Filter.EventuallyEq.mul (ae_eq_refl _) _ 
      convert ae_eq_refl _ 
      ext1 x 
      exact Real.ennnorm_eq_of_real Ennreal.to_real_nonneg 
    rwa [lt_top_iff_ne_top, ←lintegral_congr_ae this]

end Real

section 

/-! **Uniform Distribution** -/


/-- A random variable `X` has uniform distribution if it has a probability density function `f`
with support `s` such that `f = (μ s)⁻¹ 1ₛ` a.e. where `1ₛ` is the indicator function for `s`. -/
def is_uniform {m : MeasurableSpace α} (X : α → E) (support : Set E) (ℙ : Measureₓ α)
  (μ : Measureₓ E :=  by 
    runTac 
      volume_tac) :=
  pdf X ℙ μ =ᵐ[μ] support.indicator (μ support⁻¹ • 1)

namespace IsUniform

theorem has_pdf {m : MeasurableSpace α} {X : α → E} {ℙ : Measureₓ α} {μ : Measureₓ E} {support : Set E}
  (hns : μ support ≠ 0) (hnt : μ support ≠ ⊤) (hu : is_uniform X support ℙ μ) : has_pdf X ℙ μ :=
  has_pdf_of_pdf_ne_zero
    (by 
      intro hpdf 
      rw [is_uniform, hpdf] at hu 
      suffices  : μ (support ∩ Function.Support (μ support⁻¹ • 1)) = 0
      ·
        have heq : Function.Support (μ support⁻¹ • (1 : E → ℝ≥0∞)) = Set.Univ
        ·
          ext x 
          rw [Function.mem_support]
          simp [hnt]
        rw [HEq, Set.inter_univ] at this 
        exact hns this 
      exact Set.indicator_ae_eq_zero hu.symm)

theorem pdf_to_real_ae_eq {m : MeasurableSpace α} {X : α → E} {ℙ : Measureₓ α} {μ : Measureₓ E} {s : Set E}
  (hX : is_uniform X s ℙ μ) :
  (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x => (s.indicator (μ s⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp hX Ennreal.toReal

variable[is_finite_measure ℙ]{X : α → ℝ}

variable{s : Set ℝ}(hms : MeasurableSet s)(hns : volume s ≠ 0)

include hms hns

theorem mul_pdf_integrable (hcs : IsCompact s) (huX : is_uniform X s ℙ) :
  integrable fun x : ℝ => x*(pdf X ℙ volume x).toReal :=
  by 
    byCases' hsupp : volume s = ∞
    ·
      have  : pdf X ℙ =ᵐ[volume] 0
      ·
        refine' ae_eq_trans huX _ 
        simp [hsupp]
      refine' integrable.congr (integrable_zero _ _ _) _ 
      rw
        [(by 
          simp  :
        (fun x => 0 : ℝ → ℝ) = fun x => x*(0 : ℝ≥0∞).toReal)]
      refine' Filter.EventuallyEq.mul (ae_eq_refl _) (Filter.EventuallyEq.fun_comp this.symm Ennreal.toReal)
    refine' ⟨ae_measurable_id'.mul (measurable_pdf X ℙ).AeMeasurable.ennreal_to_real, _⟩
    refine' has_finite_integral_mul huX _ 
    set ind := volume s⁻¹ • (1 : ℝ → ℝ≥0∞) with hind 
    have  : ∀ x, («expr↑ » ∥x∥₊*s.indicator ind x) = s.indicator (fun x => ∥x∥₊*ind x) x :=
      fun x => (s.indicator_mul_right (fun x => «expr↑ » ∥x∥₊) ind).symm 
    simp only [this, lintegral_indicator _ hms, hind, mul_oneₓ, Algebra.id.smul_eq_mul, Pi.one_apply, Pi.smul_apply]
    rw [lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal]
    ·
      refine'
        (Ennreal.mul_lt_top (set_lintegral_lt_top_of_is_compact hsupp hcs continuous_nnnorm).Ne
            (Ennreal.inv_lt_top.2 (pos_iff_ne_zero.mpr hns)).Ne).Ne
    ·
      infer_instance

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (hnt : volume s ≠ ⊤) (huX : is_uniform X s ℙ) : (∫x, X x ∂ℙ) = volume s⁻¹.toReal*∫x in s, x :=
  by 
    haveI  := has_pdf hns hnt huX 
    rw [←integral_mul_eq_integral]
    all_goals 
      try 
        infer_instance 
    rw [integral_congr_ae (Filter.EventuallyEq.mul (ae_eq_refl _) (pdf_to_real_ae_eq huX))]
    have  :
      ∀ x, (x*(s.indicator (volume s⁻¹ • (1 : ℝ → ℝ≥0∞)) x).toReal) = x*s.indicator (volume s⁻¹.toReal • (1 : ℝ → ℝ)) x
    ·
      refine' fun x => congr_argₓ ((·*·) x) _ 
      byCases' hx : x ∈ s
      ·
        simp [Set.indicator_of_mem hx]
      ·
        simp [Set.indicator_of_not_mem hx]
    simpRw [this, ←s.indicator_mul_right fun x => x, integral_indicator hms]
    change (∫x in s, x*volume s⁻¹.toReal • 1 ∂volume) = _ 
    rw [integral_mul_right, mul_commₓ, Algebra.id.smul_eq_mul, mul_oneₓ]

end IsUniform

end 

end Pdf

end MeasureTheory

