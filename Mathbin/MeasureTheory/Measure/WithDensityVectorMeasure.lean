import Mathbin.MeasureTheory.Measure.VectorMeasure 
import Mathbin.MeasureTheory.Function.AeEqOfIntegral

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable set `s`, `v i = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `measure_theory.measure.with_densityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/


noncomputable theory

open_locale Classical MeasureTheory Nnreal Ennreal

variable{α β : Type _}{m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable{μ ν : Measureₓ α}

variable{E :
    Type
      _}[NormedGroup E][MeasurableSpace E][second_countable_topology E][NormedSpace ℝ E][CompleteSpace E][BorelSpace E]

/-- Given a measure `μ` and an integrable function `f`, `μ.with_densityᵥ f` is
the vector measure which maps the set `s` to `∫ₛ f ∂μ`. -/
def measure.with_densityᵥ {m : MeasurableSpace α} (μ : Measureₓ α) (f : α → E) : vector_measure α E :=
  if hf : integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫x in s, f x ∂μ else 0,
      empty' :=
        by 
          simp ,
      not_measurable' := fun s hs => if_neg hs,
      m_Union' :=
        fun s hs₁ hs₂ =>
          by 
            convert has_sum_integral_Union hs₁ hs₂ hf.integrable_on
            ·
              ext n 
              rw [if_pos (hs₁ n)]
            ·
              rw [if_pos (MeasurableSet.Union hs₁)] }
  else 0

open Measureₓ

include m

variable{f g : α → E}

theorem with_densityᵥ_apply (hf : integrable f μ) {s : Set α} (hs : MeasurableSet s) :
  μ.with_densityᵥ f s = ∫x in s, f x ∂μ :=
  by 
    rw [with_densityᵥ, dif_pos hf]
    exact dif_pos hs

@[simp]
theorem with_densityᵥ_zero : μ.with_densityᵥ (0 : α → E) = 0 :=
  by 
    ext1 s hs 
    erw [with_densityᵥ_apply (integrable_zero α E μ) hs]
    simp 

@[simp]
theorem with_densityᵥ_neg : μ.with_densityᵥ (-f) = -μ.with_densityᵥ f :=
  by 
    byCases' hf : integrable f μ
    ·
      ext1 i hi 
      rw [vector_measure.neg_apply, with_densityᵥ_apply hf hi, ←integral_neg, with_densityᵥ_apply hf.neg hi]
      rfl
    ·
      rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, neg_zero]
      rwa [integrable_neg_iff]

theorem with_densityᵥ_neg' : (μ.with_densityᵥ fun x => -f x) = -μ.with_densityᵥ f :=
  with_densityᵥ_neg

@[simp]
theorem with_densityᵥ_add (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (f+g) = μ.with_densityᵥ f+μ.with_densityᵥ g :=
  by 
    ext1 i hi 
    rw [with_densityᵥ_apply (hf.add hg) hi, vector_measure.add_apply, with_densityᵥ_apply hf hi,
      with_densityᵥ_apply hg hi]
    simpRw [Pi.add_apply]
    rw [integral_add] <;> rw [←integrable_on_univ]
    ·
      exact hf.integrable_on.restrict MeasurableSet.univ
    ·
      exact hg.integrable_on.restrict MeasurableSet.univ

theorem with_densityᵥ_add' (hf : integrable f μ) (hg : integrable g μ) :
  (μ.with_densityᵥ fun x => f x+g x) = μ.with_densityᵥ f+μ.with_densityᵥ g :=
  with_densityᵥ_add hf hg

@[simp]
theorem with_densityᵥ_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ (f - g) = μ.with_densityᵥ f - μ.with_densityᵥ g :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, with_densityᵥ_add hf hg.neg, with_densityᵥ_neg]

theorem with_densityᵥ_sub' (hf : integrable f μ) (hg : integrable g μ) :
  (μ.with_densityᵥ fun x => f x - g x) = μ.with_densityᵥ f - μ.with_densityᵥ g :=
  with_densityᵥ_sub hf hg

@[simp]
theorem with_densityᵥ_smul {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 E] [SmulCommClass ℝ 𝕜 E]
  [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] (f : α → E) (r : 𝕜) : μ.with_densityᵥ (r • f) = r • μ.with_densityᵥ f :=
  by 
    byCases' hf : integrable f μ
    ·
      ext1 i hi 
      rw [with_densityᵥ_apply (hf.smul r) hi, vector_measure.smul_apply, with_densityᵥ_apply hf hi, ←integral_smul r f]
      rfl
    ·
      byCases' hr : r = 0
      ·
        rw [hr, zero_smul, zero_smul, with_densityᵥ_zero]
      ·
        rw [with_densityᵥ, with_densityᵥ, dif_neg hf, dif_neg, smul_zero]
        rwa [integrable_smul_iff hr f]

theorem with_densityᵥ_smul' {𝕜 : Type _} [NondiscreteNormedField 𝕜] [NormedSpace 𝕜 E] [SmulCommClass ℝ 𝕜 E]
  [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] (f : α → E) (r : 𝕜) :
  (μ.with_densityᵥ fun x => r • f x) = r • μ.with_densityᵥ f :=
  with_densityᵥ_smul f r

theorem measure.with_densityᵥ_absolutely_continuous (μ : Measureₓ α) (f : α → ℝ) :
  μ.with_densityᵥ f ≪ᵥ μ.to_ennreal_vector_measure :=
  by 
    byCases' hf : integrable f μ
    ·
      refine' vector_measure.absolutely_continuous.mk fun i hi₁ hi₂ => _ 
      rw [to_ennreal_vector_measure_apply_measurable hi₁] at hi₂ 
      rw [with_densityᵥ_apply hf hi₁, measure.restrict_zero_set hi₂, integral_zero_measure]
    ·
      rw [with_densityᵥ, dif_neg hf]
      exact vector_measure.absolutely_continuous.zero _

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
theorem integrable.ae_eq_of_with_densityᵥ_eq {f g : α → E} (hf : integrable f μ) (hg : integrable g μ)
  (hfg : μ.with_densityᵥ f = μ.with_densityᵥ g) : f =ᵐ[μ] g :=
  by 
    refine' hf.ae_eq_of_forall_set_integral_eq f g hg fun i hi _ => _ 
    rw [←with_densityᵥ_apply hf hi, hfg, with_densityᵥ_apply hg hi]

-- error in MeasureTheory.Measure.WithDensityVectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem with_densityᵥ_eq.congr_ae
{f g : α → E}
(h : «expr =ᵐ[ ] »(f, μ, g)) : «expr = »(μ.with_densityᵥ f, μ.with_densityᵥ g) :=
begin
  by_cases [expr hf, ":", expr integrable f μ],
  { ext [] [ident i, ident hi] [],
    rw ["[", expr with_densityᵥ_apply hf hi, ",", expr with_densityᵥ_apply (hf.congr h) hi, "]"] [],
    exact [expr integral_congr_ae (ae_restrict_of_ae h)] },
  { have [ident hg] [":", expr «expr¬ »(integrable g μ)] [],
    { intro [ident hg],
      exact [expr hf (hg.congr h.symm)] },
    rw ["[", expr with_densityᵥ, ",", expr with_densityᵥ, ",", expr dif_neg hf, ",", expr dif_neg hg, "]"] [] }
end

theorem integrable.with_densityᵥ_eq_iff {f g : α → E} (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_densityᵥ f = μ.with_densityᵥ g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg => hf.ae_eq_of_with_densityᵥ_eq hg hfg, fun h => with_densityᵥ_eq.congr_ae h⟩

section SignedMeasure

-- error in MeasureTheory.Measure.WithDensityVectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem with_densityᵥ_to_real
{f : α → «exprℝ≥0∞»()}
(hfm : ae_measurable f μ)
(hf : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»())) : «expr = »(μ.with_densityᵥ (λ
  x, (f x).to_real), @to_signed_measure α _ (μ.with_density f) (is_finite_measure_with_density hf)) :=
begin
  have [ident hfi] [] [":=", expr integrable_to_real_of_lintegral_ne_top hfm hf],
  ext [] [ident i, ident hi] [],
  rw ["[", expr with_densityᵥ_apply hfi hi, ",", expr to_signed_measure_apply_measurable hi, ",", expr with_density_apply _ hi, ",", expr integral_to_real hfm.restrict, "]"] [],
  refine [expr ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf _)],
  conv_rhs [] [] { rw ["<-", expr set_lintegral_univ] },
  exact [expr lintegral_mono_set (set.subset_univ _)]
end

theorem with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part {f : α → ℝ} (hfi : integrable f μ) :
  μ.with_densityᵥ f =
    @to_signed_measure α _ (μ.with_density fun x => Ennreal.ofReal$ f x)
        (is_finite_measure_with_density_of_real hfi.2) -
      @to_signed_measure α _ (μ.with_density fun x => Ennreal.ofReal$ -f x)
        (is_finite_measure_with_density_of_real hfi.neg.2) :=
  by 
    ext i hi 
    rw [with_densityᵥ_apply hfi hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrable_on,
      vector_measure.sub_apply, to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi,
      with_density_apply _ hi, with_density_apply _ hi]

theorem integrable.with_densityᵥ_trim_eq_integral {m m0 : MeasurableSpace α} {μ : Measureₓ α} (hm : m ≤ m0) {f : α → ℝ}
  (hf : integrable f μ) {i : Set α} (hi : measurable_set[m] i) : (μ.with_densityᵥ f).trim hm i = ∫x in i, f x ∂μ :=
  by 
    rw [vector_measure.trim_measurable_set_eq hm hi, with_densityᵥ_apply hf (hm _ hi)]

theorem integrable.with_densityᵥ_trim_absolutely_continuous {m m0 : MeasurableSpace α} {μ : Measureₓ α} (hm : m ≤ m0)
  (hfi : integrable f μ) : (μ.with_densityᵥ f).trim hm ≪ᵥ (μ.trim hm).toEnnrealVectorMeasure :=
  by 
    refine' vector_measure.absolutely_continuous.mk fun j hj₁ hj₂ => _ 
    rw [measure.to_ennreal_vector_measure_apply_measurable hj₁, trim_measurable_set_eq hm hj₁] at hj₂ 
    rw [vector_measure.trim_measurable_set_eq hm hj₁, with_densityᵥ_apply hfi (hm _ hj₁)]
    simp only [measure.restrict_eq_zero.mpr hj₂, integral_zero_measure]

end SignedMeasure

end MeasureTheory

