import Mathbin.MeasureTheory.Decomposition.Lebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rn_deriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`measure_theory/function/conditional_expectation`).

## Main results

* `measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
  the Radon-Nikodym theorem
* `measure_theory.signed_measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
  the Radon-Nikodym theorem for signed measures

## Tags

Radon-Nikodym theorem
-/


noncomputable theory

open_locale Classical MeasureTheory Nnreal Ennreal

variable{α β : Type _}{m : MeasurableSpace α}

namespace MeasureTheory

namespace Measureₓ

include m

-- error in MeasureTheory.Decomposition.RadonNikodym: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem with_density_rn_deriv_eq
(μ ν : measure α)
[have_lebesgue_decomposition μ ν]
(h : «expr ≪ »(μ, ν)) : «expr = »(ν.with_density (rn_deriv μ ν), μ) :=
begin
  obtain ["⟨", ident hf₁, ",", "⟨", ident E, ",", ident hE₁, ",", ident hE₂, ",", ident hE₃, "⟩", ",", ident hadd, "⟩", ":=", expr have_lebesgue_decomposition_spec μ ν],
  have [] [":", expr «expr = »(singular_part μ ν, 0)] [],
  { refine [expr le_antisymm (λ A hA, _) (measure.zero_le _)],
    suffices [] [":", expr «expr = »(singular_part μ ν set.univ, 0)],
    { rw ["[", expr measure.coe_zero, ",", expr pi.zero_apply, ",", "<-", expr this, "]"] [],
      exact [expr measure_mono (set.subset_univ _)] },
    rw ["[", "<-", expr set.union_compl_self E, ",", expr measure_union (@disjoint_compl_right _ E _) hE₁ hE₁.compl, ",", expr hE₂, ",", expr zero_add, "]"] [],
    have [] [":", expr «expr = »(«expr + »(singular_part μ ν, ν.with_density (rn_deriv μ ν)) «expr ᶜ»(E), μ «expr ᶜ»(E))] [],
    { rw ["<-", expr hadd] [] },
    rw ["[", expr measure.coe_add, ",", expr pi.add_apply, ",", expr h hE₃, "]"] ["at", ident this],
    exact [expr (add_eq_zero_iff.1 this).1] },
  rw ["[", expr this, ",", expr zero_add, "]"] ["at", ident hadd],
  exact [expr hadd.symm]
end

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.with_density (rn_deriv μ ν) = μ`. -/
theorem absolutely_continuous_iff_with_density_rn_deriv_eq {μ ν : Measureₓ α} [have_lebesgue_decomposition μ ν] :
  μ ≪ ν ↔ ν.with_density (rn_deriv μ ν) = μ :=
  ⟨with_density_rn_deriv_eq μ ν, fun h => h ▸ with_density_absolutely_continuous _ _⟩

theorem with_density_rn_deriv_to_real_eq {μ ν : Measureₓ α} [is_finite_measure μ] [have_lebesgue_decomposition μ ν]
  (h : μ ≪ ν) {i : Set α} (hi : MeasurableSet i) : (∫x in i, (μ.rn_deriv ν x).toReal ∂ν) = (μ i).toReal :=
  by 
    rw [integral_to_real, ←with_density_apply _ hi, with_density_rn_deriv_eq μ ν h]
    ·
      measurability
    ·
      refine' ae_lt_top (μ.measurable_rn_deriv ν) (lt_of_le_of_ltₓ (lintegral_mono_set i.subset_univ) _).Ne 
      rw [←with_density_apply _ MeasurableSet.univ, with_density_rn_deriv_eq μ ν h]
      exact measure_lt_top _ _

end Measureₓ

namespace SignedMeasure

include m

open Measureₓ VectorMeasure

theorem with_densityᵥ_rn_deriv_eq (s : signed_measure α) (μ : Measureₓ α) [sigma_finite μ]
  (h : s ≪ᵥ μ.to_ennreal_vector_measure) : μ.with_densityᵥ (s.rn_deriv μ) = s :=
  by 
    rw [absolutely_continuous_ennreal_iff, (_ : μ.to_ennreal_vector_measure.ennreal_to_measure = μ),
      total_variation_absolutely_continuous_iff] at h
    ·
      ext1 i hi 
      rw [with_densityᵥ_apply (integrable_rn_deriv _ _) hi, rn_deriv, integral_sub,
        with_density_rn_deriv_to_real_eq h.1 hi, with_density_rn_deriv_to_real_eq h.2 hi]
      ·
        convRHS => rw [←s.to_signed_measure_to_jordan_decomposition]
        erw [vector_measure.sub_apply]
        rw [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi]
      all_goals 
        rw [←integrable_on_univ]
        refine' integrable_on.restrict _ MeasurableSet.univ 
        refine' ⟨_, has_finite_integral_to_real_of_lintegral_ne_top _⟩
        ·
          measurability
        ·
          rw [set_lintegral_univ]
          exact (lintegral_rn_deriv_lt_top _ _).Ne
    ·
      exact equiv_measure.right_inv μ

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq (s : signed_measure α) (μ : Measureₓ α) [sigma_finite μ] :
  s ≪ᵥ μ.to_ennreal_vector_measure ↔ μ.with_densityᵥ (s.rn_deriv μ) = s :=
  ⟨with_densityᵥ_rn_deriv_eq s μ, fun h => h ▸ with_densityᵥ_absolutely_continuous _ _⟩

end SignedMeasure

end MeasureTheory

