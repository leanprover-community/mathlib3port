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

theorem has_pdf_of_pdf_ne_zero {m : MeasurableSpace α} {ℙ : Measureₓ α} {μ : Measureₓ E} {X : α → E}
  (h : pdf X ℙ μ ≠ 0) : has_pdf X ℙ μ :=
  by 
    byContra hpdf 
    rw [pdf, dif_neg hpdf] at h 
    exact hpdf (False.ndrec (has_pdf X ℙ μ) (h rfl))

theorem pdf_eq_zero_of_not_measurable {m : MeasurableSpace α} {ℙ : Measureₓ α} {μ : Measureₓ E} {X : α → E}
  (hX : ¬Measurable X) : pdf X ℙ μ = 0 :=
  pdf_undef fun hpdf => hX hpdf.pdf'.1

theorem measurable_of_pdf_ne_zero {m : MeasurableSpace α} {ℙ : Measureₓ α} {μ : Measureₓ E} (X : α → E)
  (h : pdf X ℙ μ ≠ 0) : Measurable X :=
  by 
    byContra hX 
    exact h (pdf_eq_zero_of_not_measurable hX)

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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_lt_top
[is_finite_measure ℙ]
{μ : measure E}
{X : α → E} : «expr∀ᵐ ∂ , »((x), μ, «expr < »(pdf X ℙ μ x, «expr∞»())) :=
begin
  by_cases [expr hpdf, ":", expr has_pdf X ℙ μ],
  { haveI [] [] [":=", expr hpdf],
    refine [expr ae_lt_top (measurable_pdf X ℙ μ) _],
    rw [expr lintegral_eq_measure_univ] [],
    exact [expr (measure_lt_top _ _).ne] },
  { rw ["[", expr pdf, ",", expr dif_neg hpdf, "]"] [],
    exact [expr filter.eventually_of_forall (λ x, with_top.zero_lt_top)] }
end

theorem of_real_to_real_ae_eq [is_finite_measure ℙ] {X : α → E} :
  (fun x => Ennreal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  by 
    byCases' hpdf : has_pdf X ℙ μ
    ·
      exact of_real_to_real_ae_eq ae_lt_top
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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
theorem integral_fun_mul_eq_integral
[is_finite_measure ℙ]
{X : α → E}
[has_pdf X ℙ μ]
{f : E → exprℝ()}
(hf : measurable f) : «expr = »(«expr∫ , ∂ »((x), «expr * »(f x, (pdf X ℙ μ x).to_real), μ), «expr∫ , ∂ »((x), f (X x), ℙ)) :=
begin
  by_cases [expr hpdf, ":", expr integrable (λ x, «expr * »(f x, (pdf X ℙ μ x).to_real)) μ],
  { rw ["[", "<-", expr integral_map (has_pdf.measurable X ℙ μ) hf.ae_measurable, ",", expr map_eq_with_density_pdf X ℙ μ, ",", expr integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf, ",", expr integral_eq_lintegral_pos_part_sub_lintegral_neg_part, ",", expr lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_of_real, ",", expr lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_of_real, "]"] [],
    { congr' [2] [],
      { have [] [":", expr ∀
         x, «expr = »(ennreal.of_real «expr * »(f x, (pdf X ℙ μ x).to_real), «expr * »(ennreal.of_real (pdf X ℙ μ x).to_real, ennreal.of_real (f x)))] [],
        { intro [ident x],
          rw ["[", expr mul_comm, ",", expr ennreal.of_real_mul ennreal.to_real_nonneg, "]"] [] },
        simp_rw ["[", expr this, "]"] [],
        exact [expr lintegral_congr_ae (filter.eventually_eq.mul of_real_to_real_ae_eq (ae_eq_refl _))] },
      { have [] [":", expr ∀
         x, «expr = »(ennreal.of_real «expr- »(«expr * »(f x, (pdf X ℙ μ x).to_real)), «expr * »(ennreal.of_real (pdf X ℙ μ x).to_real, ennreal.of_real «expr- »(f x)))] [],
        { intro [ident x],
          rw ["[", expr neg_mul_eq_neg_mul, ",", expr mul_comm, ",", expr ennreal.of_real_mul ennreal.to_real_nonneg, "]"] [] },
        simp_rw ["[", expr this, "]"] [],
        exact [expr lintegral_congr_ae (filter.eventually_eq.mul of_real_to_real_ae_eq (ae_eq_refl _))] } },
    { refine [expr ⟨hf.ae_measurable, _⟩],
      rw ["[", expr has_finite_integral, ",", expr lintegral_with_density_eq_lintegral_mul _ (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal, "]"] [],
      have [] [":", expr «expr =ᵐ[ ] »(λ
        x, «expr * »(pdf X ℙ μ, λ
         x, «expr↑ »(«expr∥ ∥₊»(f x))) x, μ, λ x, «expr∥ ∥₊»(«expr * »(f x, (pdf X ℙ μ x).to_real)))] [],
      { simp_rw ["[", "<-", expr smul_eq_mul, ",", expr nnnorm_smul, ",", expr ennreal.coe_mul, "]"] [],
        rw ["[", expr smul_eq_mul, ",", expr mul_comm, "]"] [],
        refine [expr filter.eventually_eq.mul (ae_eq_refl _) (ae_eq_trans of_real_to_real_ae_eq.symm _)],
        convert [] [expr ae_eq_refl _] [],
        ext1 [] [ident x],
        exact [expr real.ennnorm_eq_of_real ennreal.to_real_nonneg] },
      rw [expr lintegral_congr_ae this] [],
      exact [expr hpdf.2] } },
  { rw ["[", expr integral_undef hpdf, ",", expr integral_undef, "]"] [],
    rwa ["<-", expr integrable_iff_integrable_mul_pdf hf] ["at", ident hpdf],
    all_goals { apply_instance } }
end

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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_pdf_iff
{X : α → E} : «expr ↔ »(has_pdf X ℙ μ, «expr ∧ »(measurable X, «expr ∧ »((map X ℙ).have_lebesgue_decomposition μ, «expr ≪ »(map X ℙ, μ)))) :=
begin
  split,
  { intro [ident hX'],
    exactI [expr ⟨hX'.pdf'.1, have_lebesgue_decomposition_of_has_pdf, map_absolutely_continuous⟩] },
  { rintros ["⟨", ident hX, ",", ident h_decomp, ",", ident h, "⟩"],
    haveI [] [] [":=", expr h_decomp],
    refine [expr ⟨⟨hX, (measure.map X ℙ).rn_deriv μ, measurable_rn_deriv _ _, _⟩⟩],
    rwa [expr with_density_rn_deriv_eq] [] }
end

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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf` if `(map g (map X ℙ)).have_lebesgue_decomposition μ`.

`quasi_measure_preserving_has_pdf'` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
theorem quasi_measure_preserving_has_pdf
{X : α → E}
[has_pdf X ℙ μ]
{g : E → F}
(hg : quasi_measure_preserving g μ ν)
(hmap : (map g (map X ℙ)).have_lebesgue_decomposition ν) : has_pdf «expr ∘ »(g, X) ℙ ν :=
begin
  rw ["[", expr has_pdf_iff, ",", "<-", expr map_map hg.measurable (has_pdf.measurable X ℙ μ), "]"] [],
  refine [expr ⟨hg.measurable.comp (has_pdf.measurable X ℙ μ), hmap, _⟩],
  rw ["[", expr map_eq_with_density_pdf X ℙ μ, "]"] [],
  refine [expr absolutely_continuous.mk (λ s hsm hs, _)],
  rw ["[", expr map_apply hg.measurable hsm, ",", expr with_density_apply _ (hg.measurable hsm), "]"] [],
  have [] [] [":=", expr hg.absolutely_continuous hs],
  rw [expr map_apply hg.measurable hsm] ["at", ident this],
  exact [expr set_lintegral_measure_zero _ _ this]
end

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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_finite_integral_mul
{f : exprℝ() → exprℝ()}
{g : exprℝ() → «exprℝ≥0∞»()}
(hg : «expr =ᵐ[ ] »(pdf X ℙ, volume, g))
(hgi : «expr ≠ »(«expr∫⁻ , »((x), «expr * »(«expr∥ ∥₊»(f x), g x)), «expr∞»())) : has_finite_integral (λ
 x, «expr * »(f x, (pdf X ℙ volume x).to_real)) :=
begin
  rw [expr has_finite_integral] [],
  have [] [":", expr «expr =ᵐ[ ] »(λ
    x, «expr * »(«expr↑ »(«expr∥ ∥₊»(f x)), g x), volume, λ
    x, «expr∥ ∥₊»(«expr * »(f x, (pdf X ℙ volume x).to_real)))] [],
  { refine [expr ae_eq_trans (filter.eventually_eq.mul (ae_eq_refl (λ
        x, «expr∥ ∥₊»(f x))) (ae_eq_trans hg.symm of_real_to_real_ae_eq.symm)) _],
    simp_rw ["[", "<-", expr smul_eq_mul, ",", expr nnnorm_smul, ",", expr ennreal.coe_mul, ",", expr smul_eq_mul, "]"] [],
    refine [expr filter.eventually_eq.mul (ae_eq_refl _) _],
    convert [] [expr ae_eq_refl _] [],
    ext1 [] [ident x],
    exact [expr real.ennnorm_eq_of_real ennreal.to_real_nonneg] },
  rwa ["[", expr lt_top_iff_ne_top, ",", "<-", expr lintegral_congr_ae this, "]"] []
end

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

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_pdf
{m : measurable_space α}
{X : α → E}
{ℙ : measure α}
{μ : measure E}
{support : set E}
(hns : «expr ≠ »(μ support, 0))
(hnt : «expr ≠ »(μ support, «expr⊤»()))
(hu : is_uniform X support ℙ μ) : has_pdf X ℙ μ :=
has_pdf_of_pdf_ne_zero (begin
   intro [ident hpdf],
   rw ["[", expr is_uniform, ",", expr hpdf, "]"] ["at", ident hu],
   suffices [] [":", expr «expr = »(μ «expr ∩ »(support, function.support «expr • »(«expr ⁻¹»(μ support), 1)), 0)],
   { have [ident heq] [":", expr «expr = »(function.support «expr • »(«expr ⁻¹»(μ support), (1 : E → «exprℝ≥0∞»())), set.univ)] [],
     { ext [] [ident x] [],
       rw ["[", expr function.mem_support, "]"] [],
       simp [] [] [] ["[", expr hnt, "]"] [] [] },
     rw ["[", expr heq, ",", expr set.inter_univ, "]"] ["at", ident this],
     exact [expr hns this] },
   exact [expr set.indicator_ae_eq_zero hu.symm]
 end)

theorem pdf_to_real_ae_eq {m : MeasurableSpace α} {X : α → E} {ℙ : Measureₓ α} {μ : Measureₓ E} {s : Set E}
  (hX : is_uniform X s ℙ μ) :
  (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x => (s.indicator (μ s⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp hX Ennreal.toReal

variable[is_finite_measure ℙ]{X : α → ℝ}

variable{s : Set ℝ}(hms : MeasurableSet s)(hns : volume s ≠ 0)

include hms hns

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_pdf_integrable
(hcs : is_compact s)
(huX : is_uniform X s ℙ) : integrable (λ x : exprℝ(), «expr * »(x, (pdf X ℙ volume x).to_real)) :=
begin
  by_cases [expr hsupp, ":", expr «expr = »(volume s, «expr∞»())],
  { have [] [":", expr «expr =ᵐ[ ] »(pdf X ℙ, volume, 0)] [],
    { refine [expr ae_eq_trans huX _],
      simp [] [] [] ["[", expr hsupp, "]"] [] [] },
    refine [expr integrable.congr (integrable_zero _ _ _) _],
    rw ["[", expr (by simp [] [] [] [] [] [] : «expr = »((λ
      x, 0 : exprℝ() → exprℝ()), λ x, «expr * »(x, (0 : «exprℝ≥0∞»()).to_real))), "]"] [],
    refine [expr filter.eventually_eq.mul (ae_eq_refl _) (filter.eventually_eq.fun_comp this.symm ennreal.to_real)] },
  refine [expr ⟨ae_measurable_id'.mul (measurable_pdf X ℙ).ae_measurable.ennreal_to_real, _⟩],
  refine [expr has_finite_integral_mul huX _],
  set [] [ident ind] [] [":="] [expr «expr • »(«expr ⁻¹»(volume s), (1 : exprℝ() → «exprℝ≥0∞»()))] ["with", ident hind],
  have [] [":", expr ∀
   x, «expr = »(«expr * »(«expr↑ »(«expr∥ ∥₊»(x)), s.indicator ind x), s.indicator (λ
     x, «expr * »(«expr∥ ∥₊»(x), ind x)) x)] [":=", expr λ
   x, (s.indicator_mul_right (λ x, «expr↑ »(«expr∥ ∥₊»(x))) ind).symm],
  simp [] [] ["only"] ["[", expr this, ",", expr lintegral_indicator _ hms, ",", expr hind, ",", expr mul_one, ",", expr algebra.id.smul_eq_mul, ",", expr pi.one_apply, ",", expr pi.smul_apply, "]"] [] [],
  rw [expr lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal] [],
  { refine [expr (ennreal.mul_lt_top (set_lintegral_lt_top_of_is_compact hsupp hcs continuous_nnnorm).ne (ennreal.inv_lt_top.2 (pos_iff_ne_zero.mpr hns)).ne).ne] },
  { apply_instance }
end

-- error in ProbabilityTheory.Density: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq
(hnt : «expr ≠ »(volume s, «expr⊤»()))
(huX : is_uniform X s ℙ) : «expr = »(«expr∫ , ∂ »((x), X x, ℙ), «expr * »(«expr ⁻¹»(volume s).to_real, «expr∫ in , »((x), s, x))) :=
begin
  haveI [] [] [":=", expr has_pdf hns hnt huX],
  rw ["<-", expr integral_mul_eq_integral] [],
  all_goals { try { apply_instance } },
  rw [expr integral_congr_ae (filter.eventually_eq.mul (ae_eq_refl _) (pdf_to_real_ae_eq huX))] [],
  have [] [":", expr ∀
   x, «expr = »(«expr * »(x, (s.indicator «expr • »(«expr ⁻¹»(volume s), (1 : exprℝ() → «exprℝ≥0∞»())) x).to_real), «expr * »(x, s.indicator «expr • »(«expr ⁻¹»(volume s).to_real, (1 : exprℝ() → exprℝ())) x))] [],
  { refine [expr λ x, congr_arg (((«expr * »)) x) _],
    by_cases [expr hx, ":", expr «expr ∈ »(x, s)],
    { simp [] [] [] ["[", expr set.indicator_of_mem hx, "]"] [] [] },
    { simp [] [] [] ["[", expr set.indicator_of_not_mem hx, "]"] [] [] } },
  simp_rw ["[", expr this, ",", "<-", expr s.indicator_mul_right (λ x, x), ",", expr integral_indicator hms, "]"] [],
  change [expr «expr = »(«expr∫ in , ∂ »((x), s, «expr * »(x, «expr • »(«expr ⁻¹»(volume s).to_real, 1)), volume), _)] [] [],
  rw ["[", expr integral_mul_right, ",", expr mul_comm, ",", expr algebra.id.smul_eq_mul, ",", expr mul_one, "]"] []
end

end IsUniform

end 

end Pdf

end MeasureTheory

