import Mathbin.MeasureTheory.Measure.Complex 
import Mathbin.MeasureTheory.Decomposition.Jordan 
import Mathbin.MeasureTheory.Measure.WithDensityVectorMeasure 
import Mathbin.MeasureTheory.Function.AeEqOfIntegral

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `measure_theory.measure.have_lebesgue_decomposition` : A pair of measures `μ` and `ν` is said
  to `have_lebesgue_decomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f`
* `measure_theory.measure.singular_part` : If a pair of measures `have_lebesgue_decomposition`,
  then `singular_part` chooses the measure from `have_lebesgue_decomposition`, otherwise it
  returns the zero measure.
* `measure_theory.measure.rn_deriv`: If a pair of measures
  `have_lebesgue_decomposition`, then `rn_deriv` chooses the measurable function from
  `have_lebesgue_decomposition`, otherwise it returns the zero function.
* `measure_theory.signed_measure.have_lebesgue_decomposition` : A signed measure `s` and a
  measure `μ` is said to `have_lebesgue_decomposition` if both the positive part and negative
  part of `s` `have_lebesgue_decomposition` with respect to `μ`.
* `measure_theory.signed_measure.singular_part` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `measure_theory.signed_measure.rn_deriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite` :
  the Lebesgue decomposition theorem.
* `measure_theory.measure.eq_singular_part` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singular_part ν`.
* `measure_theory.measure.eq_rn_deriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rn_deriv ν`.
* `measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

# Tags

Lebesgue decomposition theorem
-/


noncomputable theory

open_locale Classical MeasureTheory Nnreal Ennreal

variable{α β : Type _}{m : MeasurableSpace α}{μ ν : MeasureTheory.Measure α}

include m

namespace MeasureTheory

namespace Measureₓ

/-- A pair of measures `μ` and `ν` is said to `have_lebesgue_decomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.with_density f`. -/
class have_lebesgue_decomposition(μ ν : Measureₓ α) : Prop where 
  lebesgue_decomposition : ∃ p : Measureₓ α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⊥ₘ ν ∧ μ = p.1+ν.with_density p.2

/-- If a pair of measures `have_lebesgue_decomposition`, then `singular_part` chooses the
measure from `have_lebesgue_decomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singular_part ν + ν.with_density (μ.rn_deriv ν)`. -/
@[irreducible]
def singular_part (μ ν : Measureₓ α) : Measureₓ α :=
  if h : have_lebesgue_decomposition μ ν then (Classical.some h.lebesgue_decomposition).1 else 0

/-- If a pair of measures `have_lebesgue_decomposition`, then `rn_deriv` chooses the
measurable function from `have_lebesgue_decomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singular_part ν + ν.with_density (μ.rn_deriv ν)`.-/
@[irreducible]
def rn_deriv (μ ν : Measureₓ α) : α → ℝ≥0∞ :=
  if h : have_lebesgue_decomposition μ ν then (Classical.some h.lebesgue_decomposition).2 else 0

theorem have_lebesgue_decomposition_spec (μ ν : Measureₓ α) [h : have_lebesgue_decomposition μ ν] :
  Measurable (μ.rn_deriv ν) ∧ μ.singular_part ν ⊥ₘ ν ∧ μ = μ.singular_part ν+ν.with_density (μ.rn_deriv ν) :=
  by 
    rw [singular_part, rn_deriv, dif_pos h, dif_pos h]
    exact Classical.some_spec h.lebesgue_decomposition

theorem have_lebesgue_decomposition_add (μ ν : Measureₓ α) [have_lebesgue_decomposition μ ν] :
  μ = μ.singular_part ν+ν.with_density (μ.rn_deriv ν) :=
  (have_lebesgue_decomposition_spec μ ν).2.2

instance have_lebesgue_decomposition_smul (μ ν : Measureₓ α) [have_lebesgue_decomposition μ ν] (r :  ℝ≥0 ) :
  (r • μ).HaveLebesgueDecomposition ν :=
  { lebesgue_decomposition :=
      by 
        obtain ⟨hmeas, hsing, hadd⟩ := have_lebesgue_decomposition_spec μ ν 
        refine' ⟨⟨r • μ.singular_part ν, r • μ.rn_deriv ν⟩, _, hsing.smul _, _⟩
        ·
          change Measurable ((r : ℝ≥0∞) • _)
          exact hmeas.const_smul _
        ·
          change _ = ((r : ℝ≥0∞) • _)+ν.with_density ((r : ℝ≥0∞) • _)
          rw [with_density_smul _ hmeas, ←smul_add, ←hadd]
          rfl }

@[measurability]
theorem measurable_rn_deriv (μ ν : Measureₓ α) : Measurable$ μ.rn_deriv ν :=
  by 
    byCases' h : have_lebesgue_decomposition μ ν
    ·
      exact (have_lebesgue_decomposition_spec μ ν).1
    ·
      rw [rn_deriv, dif_neg h]
      exact measurable_zero

theorem mutually_singular_singular_part (μ ν : Measureₓ α) : μ.singular_part ν ⊥ₘ ν :=
  by 
    byCases' h : have_lebesgue_decomposition μ ν
    ·
      exact (have_lebesgue_decomposition_spec μ ν).2.1
    ·
      rw [singular_part, dif_neg h]
      exact mutually_singular.zero_left

theorem singular_part_le (μ ν : Measureₓ α) : μ.singular_part ν ≤ μ :=
  by 
    byCases' hl : have_lebesgue_decomposition μ ν
    ·
      cases' (have_lebesgue_decomposition_spec μ ν).2 with _ h 
      convRHS => rw [h]
      exact measure.le_add_right (le_reflₓ _)
    ·
      rw [singular_part, dif_neg hl]
      exact measure.zero_le μ

theorem with_density_rn_deriv_le (μ ν : Measureₓ α) : ν.with_density (μ.rn_deriv ν) ≤ μ :=
  by 
    byCases' hl : have_lebesgue_decomposition μ ν
    ·
      cases' (have_lebesgue_decomposition_spec μ ν).2 with _ h 
      convRHS => rw [h]
      exact measure.le_add_left (le_reflₓ _)
    ·
      rw [rn_deriv, dif_neg hl, with_density_zero]
      exact measure.zero_le μ

instance  [is_finite_measure μ] : is_finite_measure (μ.singular_part ν) :=
  is_finite_measure_of_le μ$ singular_part_le μ ν

instance  [sigma_finite μ] : sigma_finite (μ.singular_part ν) :=
  sigma_finite_of_le μ$ singular_part_le μ ν

instance  [TopologicalSpace α] [is_locally_finite_measure μ] : is_locally_finite_measure (μ.singular_part ν) :=
  is_locally_finite_measure_of_le$ singular_part_le μ ν

instance  [is_finite_measure μ] : is_finite_measure (ν.with_density$ μ.rn_deriv ν) :=
  is_finite_measure_of_le μ$ with_density_rn_deriv_le μ ν

instance  [sigma_finite μ] : sigma_finite (ν.with_density$ μ.rn_deriv ν) :=
  sigma_finite_of_le μ$ with_density_rn_deriv_le μ ν

instance  [TopologicalSpace α] [is_locally_finite_measure μ] :
  is_locally_finite_measure (ν.with_density$ μ.rn_deriv ν) :=
  is_locally_finite_measure_of_le$ with_density_rn_deriv_le μ ν

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_rn_deriv_lt_top_of_measure_ne_top
{μ : measure α}
(ν : measure α)
{s : set α}
(hs : «expr ≠ »(μ s, «expr∞»())) : «expr < »(«expr∫⁻ in , ∂ »((x), s, μ.rn_deriv ν x, ν), «expr∞»()) :=
begin
  by_cases [expr hl, ":", expr have_lebesgue_decomposition μ ν],
  { haveI [] [] [":=", expr hl],
    obtain ["⟨", "-", ",", "-", ",", ident hadd, "⟩", ":=", expr have_lebesgue_decomposition_spec μ ν],
    suffices [] [":", expr «expr < »(«expr∫⁻ in , ∂ »((x), to_measurable μ s, μ.rn_deriv ν x, ν), «expr∞»())],
    from [expr lt_of_le_of_lt (lintegral_mono_set (subset_to_measurable _ _)) this],
    rw ["[", "<-", expr with_density_apply _ (measurable_set_to_measurable _ _), "]"] [],
    refine [expr lt_of_le_of_lt (le_add_left (le_refl _) : «expr ≤ »(_, «expr + »(μ.singular_part ν (to_measurable μ s), ν.with_density (μ.rn_deriv ν) (to_measurable μ s)))) _],
    rw ["[", "<-", expr measure.add_apply, ",", "<-", expr hadd, ",", expr measure_to_measurable, "]"] [],
    exact [expr hs.lt_top] },
  { erw ["[", expr measure.rn_deriv, ",", expr dif_neg hl, ",", expr lintegral_zero, "]"] [],
    exact [expr with_top.zero_lt_top] }
end

theorem lintegral_rn_deriv_lt_top (μ ν : Measureₓ α) [is_finite_measure μ] : (∫⁻x, μ.rn_deriv ν x ∂ν) < ∞ :=
  by 
    rw [←set_lintegral_univ]
    exact lintegral_rn_deriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).Ne

/-- The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to another
measure `ν` is `ν`-almost everywhere finite. -/
theorem rn_deriv_lt_top (μ ν : Measureₓ α) [sigma_finite μ] : ∀ᵐx ∂ν, μ.rn_deriv ν x < ∞ :=
  by 
    suffices  : ∀ n, ∀ᵐx ∂ν, x ∈ spanning_sets μ n → μ.rn_deriv ν x < ∞
    ·
      filterUpwards [ae_all_iff.2 this]
      intro x hx 
      exact hx _ (mem_spanning_sets_index _ _)
    intro n 
    rw [←ae_restrict_iff' (measurable_spanning_sets _ _)]
    apply ae_lt_top (measurable_rn_deriv _ _)
    refine' (lintegral_rn_deriv_lt_top_of_measure_ne_top _ _).Ne 
    exact (measure_spanning_sets_lt_top _ _).Ne

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singular_part μ`.

This theorem provides the uniqueness of the `singular_part` in the Lebesgue decomposition theorem,
while `measure_theory.measure.eq_rn_deriv` provides the uniqueness of the
`rn_deriv`. -/
theorem eq_singular_part
{s : measure α}
{f : α → «exprℝ≥0∞»()}
(hf : measurable f)
(hs : «expr ⊥ₘ »(s, ν))
(hadd : «expr = »(μ, «expr + »(s, ν.with_density f))) : «expr = »(s, μ.singular_part ν) :=
begin
  haveI [] [":", expr have_lebesgue_decomposition μ ν] [":=", expr ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩],
  obtain ["⟨", ident hmeas, ",", ident hsing, ",", ident hadd', "⟩", ":=", expr have_lebesgue_decomposition_spec μ ν],
  obtain ["⟨", "⟨", ident S, ",", ident hS₁, ",", ident hS₂, ",", ident hS₃, "⟩", ",", "⟨", ident T, ",", ident hT₁, ",", ident hT₂, ",", ident hT₃, "⟩", "⟩", ":=", "⟨", expr hs, ",", expr hsing, "⟩"],
  rw [expr hadd'] ["at", ident hadd],
  have [ident hνinter] [":", expr «expr = »(ν «expr ᶜ»(«expr ∩ »(S, T)), 0)] [],
  { rw [expr set.compl_inter] [],
    refine [expr nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)],
    rw ["[", expr hT₃, ",", expr hS₃, ",", expr add_zero, "]"] [],
    exact [expr le_refl _] },
  have [ident heq] [":", expr «expr = »(s.restrict «expr ᶜ»(«expr ∩ »(S, T)), (μ.singular_part ν).restrict «expr ᶜ»(«expr ∩ »(S, T)))] [],
  { ext1 [] [ident A, ident hA],
    have [ident hf] [":", expr «expr = »(ν.with_density f «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T))), 0)] [],
    { refine [expr with_density_absolutely_continuous ν _ _],
      rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(hνinter, measure_mono (set.inter_subset_right _ _))] },
    have [ident hrn] [":", expr «expr = »(ν.with_density (μ.rn_deriv ν) «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T))), 0)] [],
    { refine [expr with_density_absolutely_continuous ν _ _],
      rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(hνinter, measure_mono (set.inter_subset_right _ _))] },
    rw ["[", expr restrict_apply hA, ",", expr restrict_apply hA, ",", "<-", expr add_zero (s «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T)))), ",", "<-", expr hf, ",", "<-", expr add_apply, ",", "<-", expr hadd, ",", expr add_apply, ",", expr hrn, ",", expr add_zero, "]"] [] },
  have [ident heq'] [":", expr ∀
   A : set α, measurable_set A → «expr = »(s A, s.restrict «expr ᶜ»(«expr ∩ »(S, T)) A)] [],
  { intros [ident A, ident hA],
    have [ident hsinter] [":", expr «expr = »(s «expr ∩ »(A, «expr ∩ »(S, T)), 0)] [],
    { rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(hS₂, measure_mono (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _)))] },
    rw ["[", expr restrict_apply hA, ",", "<-", expr add_zero (s «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T)))), ",", "<-", expr hsinter, ",", "<-", expr measure_union, ",", "<-", expr set.inter_union_distrib_left, ",", expr set.compl_union_self, ",", expr set.inter_univ, "]"] [],
    { exact [expr disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_left)] },
    { measurability [] [] },
    { measurability [] [] } },
  ext1 [] [ident A, ident hA],
  have [ident hμinter] [":", expr «expr = »(μ.singular_part ν «expr ∩ »(A, «expr ∩ »(S, T)), 0)] [],
  { rw ["<-", expr nonpos_iff_eq_zero] [],
    exact [expr «expr ▸ »(hT₂, measure_mono (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_right _ _)))] },
  rw ["[", expr heq' A hA, ",", expr heq, ",", "<-", expr add_zero ((μ.singular_part ν).restrict «expr ᶜ»(«expr ∩ »(S, T)) A), ",", "<-", expr hμinter, ",", expr restrict_apply hA, ",", "<-", expr measure_union, ",", "<-", expr set.inter_union_distrib_left, ",", expr set.compl_union_self, ",", expr set.inter_univ, "]"] [],
  { exact [expr disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_left)] },
  { measurability [] [] },
  { measurability [] [] }
end

theorem singular_part_zero (ν : Measureₓ α) : (0 : Measureₓ α).singularPart ν = 0 :=
  by 
    refine' (eq_singular_part measurable_zero mutually_singular.zero_left _).symm 
    rw [zero_addₓ, with_density_zero]

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singular_part_smul
(μ ν : measure α)
(r : «exprℝ≥0»()) : «expr = »(«expr • »(r, μ).singular_part ν, «expr • »(r, μ.singular_part ν)) :=
begin
  by_cases [expr hr, ":", expr «expr = »(r, 0)],
  { rw ["[", expr hr, ",", expr zero_smul, ",", expr zero_smul, ",", expr singular_part_zero, "]"] [] },
  by_cases [expr hl, ":", expr have_lebesgue_decomposition μ ν],
  { haveI [] [] [":=", expr hl],
    refine [expr (eq_singular_part ((measurable_rn_deriv μ ν).const_smul (r : «exprℝ≥0∞»())) (mutually_singular.smul r (have_lebesgue_decomposition_spec _ _).2.1) _).symm],
    rw ["[", expr with_density_smul _ (measurable_rn_deriv _ _), ",", "<-", expr smul_add, ",", "<-", expr have_lebesgue_decomposition_add μ ν, ",", expr ennreal.smul_def, "]"] [] },
  { rw ["[", expr singular_part, ",", expr singular_part, ",", expr dif_neg hl, ",", expr dif_neg, ",", expr smul_zero, "]"] [],
    refine [expr λ hl', hl _],
    rw ["<-", expr inv_smul_smul₀ hr μ] [],
    exact [expr @measure.have_lebesgue_decomposition_smul _ _ _ _ hl' _] }
end

theorem singular_part_add (μ₁ μ₂ ν : Measureₓ α) [have_lebesgue_decomposition μ₁ ν] [have_lebesgue_decomposition μ₂ ν] :
  (μ₁+μ₂).singularPart ν = μ₁.singular_part ν+μ₂.singular_part ν :=
  by 
    refine'
      (eq_singular_part ((measurable_rn_deriv μ₁ ν).add (measurable_rn_deriv μ₂ ν))
          ((have_lebesgue_decomposition_spec _ _).2.1.add_left (have_lebesgue_decomposition_spec _ _).2.1) _).symm
        
    erw [with_density_add (measurable_rn_deriv μ₁ ν) (measurable_rn_deriv μ₂ ν)]
    convRHS => rw [add_assocₓ, add_commₓ (μ₂.singular_part ν), ←add_assocₓ, ←add_assocₓ]
    rw [←have_lebesgue_decomposition_add μ₁ ν, add_assocₓ, add_commₓ (ν.with_density (μ₂.rn_deriv ν)),
      ←have_lebesgue_decomposition_add μ₂ ν]

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singular_part_with_density
(ν : measure α)
{f : α → «exprℝ≥0∞»()}
(hf : measurable f) : «expr = »((ν.with_density f).singular_part ν, 0) :=
begin
  have [] [":", expr «expr = »(ν.with_density f, «expr + »(0, ν.with_density f))] [],
  by rw [expr zero_add] [],
  exact [expr (eq_singular_part hf mutually_singular.zero_left this).symm]
end

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rn_deriv ν`.

This theorem provides the uniqueness of the `rn_deriv` in the Lebesgue decomposition
theorem, while `measure_theory.measure.eq_singular_part` provides the uniqueness of the
`singular_part`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rn_deriv`. -/
theorem eq_with_density_rn_deriv
{s : measure α}
{f : α → «exprℝ≥0∞»()}
(hf : measurable f)
(hs : «expr ⊥ₘ »(s, ν))
(hadd : «expr = »(μ, «expr + »(s, ν.with_density f))) : «expr = »(ν.with_density f, ν.with_density (μ.rn_deriv ν)) :=
begin
  haveI [] [":", expr have_lebesgue_decomposition μ ν] [":=", expr ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩],
  obtain ["⟨", ident hmeas, ",", ident hsing, ",", ident hadd', "⟩", ":=", expr have_lebesgue_decomposition_spec μ ν],
  obtain ["⟨", "⟨", ident S, ",", ident hS₁, ",", ident hS₂, ",", ident hS₃, "⟩", ",", "⟨", ident T, ",", ident hT₁, ",", ident hT₂, ",", ident hT₃, "⟩", "⟩", ":=", "⟨", expr hs, ",", expr hsing, "⟩"],
  rw [expr hadd'] ["at", ident hadd],
  have [ident hνinter] [":", expr «expr = »(ν «expr ᶜ»(«expr ∩ »(S, T)), 0)] [],
  { rw [expr set.compl_inter] [],
    refine [expr nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)],
    rw ["[", expr hT₃, ",", expr hS₃, ",", expr add_zero, "]"] [],
    exact [expr le_refl _] },
  have [ident heq] [":", expr «expr = »((ν.with_density f).restrict «expr ∩ »(S, T), (ν.with_density (μ.rn_deriv ν)).restrict «expr ∩ »(S, T))] [],
  { ext1 [] [ident A, ident hA],
    have [ident hs] [":", expr «expr = »(s «expr ∩ »(A, «expr ∩ »(S, T)), 0)] [],
    { rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(hS₂, measure_mono (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _)))] },
    have [ident hsing] [":", expr «expr = »(μ.singular_part ν «expr ∩ »(A, «expr ∩ »(S, T)), 0)] [],
    { rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(hT₂, measure_mono (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_right _ _)))] },
    rw ["[", expr restrict_apply hA, ",", expr restrict_apply hA, ",", "<-", expr add_zero (ν.with_density f «expr ∩ »(A, «expr ∩ »(S, T))), ",", "<-", expr hs, ",", "<-", expr add_apply, ",", expr add_comm, ",", "<-", expr hadd, ",", expr add_apply, ",", expr hsing, ",", expr zero_add, "]"] [] },
  have [ident heq'] [":", expr ∀
   A : set α, measurable_set A → «expr = »(ν.with_density f A, (ν.with_density f).restrict «expr ∩ »(S, T) A)] [],
  { intros [ident A, ident hA],
    have [ident hνfinter] [":", expr «expr = »(ν.with_density f «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T))), 0)] [],
    { rw ["<-", expr nonpos_iff_eq_zero] [],
      exact [expr «expr ▸ »(with_density_absolutely_continuous ν f hνinter, measure_mono (set.inter_subset_right _ _))] },
    rw ["[", expr restrict_apply hA, ",", "<-", expr add_zero (ν.with_density f «expr ∩ »(A, «expr ∩ »(S, T))), ",", "<-", expr hνfinter, ",", "<-", expr measure_union, ",", "<-", expr set.inter_union_distrib_left, ",", expr set.union_compl_self, ",", expr set.inter_univ, "]"] [],
    { exact [expr disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_right)] },
    { measurability [] [] },
    { measurability [] [] } },
  ext1 [] [ident A, ident hA],
  have [ident hνrn] [":", expr «expr = »(ν.with_density (μ.rn_deriv ν) «expr ∩ »(A, «expr ᶜ»(«expr ∩ »(S, T))), 0)] [],
  { rw ["<-", expr nonpos_iff_eq_zero] [],
    exact [expr «expr ▸ »(with_density_absolutely_continuous ν (μ.rn_deriv ν) hνinter, measure_mono (set.inter_subset_right _ _))] },
  rw ["[", expr heq' A hA, ",", expr heq, ",", "<-", expr add_zero ((ν.with_density (μ.rn_deriv ν)).restrict «expr ∩ »(S, T) A), ",", "<-", expr hνrn, ",", expr restrict_apply hA, ",", "<-", expr measure_union, ",", "<-", expr set.inter_union_distrib_left, ",", expr set.union_compl_self, ",", expr set.inter_univ, "]"] [],
  { exact [expr disjoint.inter_left' _ (disjoint.inter_right' _ disjoint_compl_right)] },
  { measurability [] [] },
  { measurability [] [] }
end

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rn_deriv ν`.

This theorem provides the uniqueness of the `rn_deriv` in the Lebesgue decomposition
theorem, while `measure_theory.measure.eq_singular_part` provides the uniqueness of the
`singular_part`. Here, the uniqueness is given in terms of the functions, while the uniqueness in
terms of the functions is given in `eq_with_density_rn_deriv`. -/
theorem eq_rn_deriv [sigma_finite ν] {s : Measureₓ α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⊥ₘ ν)
  (hadd : μ = s+ν.with_density f) : f =ᵐ[ν] μ.rn_deriv ν :=
  by 
    refine' ae_eq_of_forall_set_lintegral_eq_of_sigma_finite hf (measurable_rn_deriv μ ν) _ 
    intro a ha h'a 
    calc (∫⁻x : α in a, f x ∂ν) = ν.with_density f a :=
      (with_density_apply f ha).symm _ = ν.with_density (μ.rn_deriv ν) a :=
      by 
        rw [eq_with_density_rn_deriv hf hs hadd]_ = ∫⁻x : α in a, μ.rn_deriv ν x ∂ν :=
      with_density_apply _ ha

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rn_deriv_with_density
(ν : measure α)
[sigma_finite ν]
{f : α → «exprℝ≥0∞»()}
(hf : measurable f) : «expr =ᵐ[ ] »((ν.with_density f).rn_deriv ν, ν, f) :=
begin
  have [] [":", expr «expr = »(ν.with_density f, «expr + »(0, ν.with_density f))] [],
  by rw [expr zero_add] [],
  exact [expr (eq_rn_deriv hf mutually_singular.zero_left this).symm]
end

open VectorMeasure SignedMeasure

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two finite measures `μ` and `ν` are not mutually singular, there exists some `ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem. -/
theorem exists_positive_of_not_mutually_singular
(μ ν : measure α)
[is_finite_measure μ]
[is_finite_measure ν]
(h : «expr¬ »(«expr ⊥ₘ »(μ, ν))) : «expr∃ , »((ε : «exprℝ≥0»()), «expr ∧ »(«expr < »(0, ε), «expr∃ , »((E : set α), «expr ∧ »(measurable_set E, «expr ∧ »(«expr < »(0, ν E), «expr ≤[ ] »(0, E, «expr - »(μ.to_signed_measure, «expr • »(ε, ν).to_signed_measure))))))) :=
begin
  have [] [":", expr ∀
   n : exprℕ(), «expr∃ , »((i : set α), «expr ∧ »(measurable_set i, «expr ∧ »(«expr ≤[ ] »(0, i, «expr - »(μ.to_signed_measure, «expr • »((«expr / »(1, «expr + »(n, 1)) : «exprℝ≥0»()), ν).to_signed_measure)), «expr ≤[ ] »(«expr - »(μ.to_signed_measure, «expr • »((«expr / »(1, «expr + »(n, 1)) : «exprℝ≥0»()), ν).to_signed_measure), «expr ᶜ»(i), 0))))] [],
  { intro [],
    exact [expr exists_compl_positive_negative _] },
  choose [] [ident f] [ident hf₁, ident hf₂, ident hf₃] ["using", expr this],
  set [] [ident A] [] [":="] [expr «expr⋂ , »((n), «expr ᶜ»(f n))] ["with", ident hA₁],
  have [ident hAmeas] [":", expr measurable_set A] [],
  { exact [expr measurable_set.Inter (λ n, (hf₁ n).compl)] },
  have [ident hA₂] [":", expr ∀
   n : exprℕ(), «expr ≤[ ] »(«expr - »(μ.to_signed_measure, «expr • »((«expr / »(1, «expr + »(n, 1)) : «exprℝ≥0»()), ν).to_signed_measure), A, 0)] [],
  { intro [ident n],
    exact [expr restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (set.Inter_subset _ _)] },
  have [ident hA₃] [":", expr ∀
   n : exprℕ(), «expr ≤ »(μ A, «expr * »((«expr / »(1, «expr + »(n, 1)) : «exprℝ≥0»()), ν A))] [],
  { intro [ident n],
    have [] [] [":=", expr nonpos_of_restrict_le_zero _ (hA₂ n)],
    rwa ["[", expr to_signed_measure_sub_apply hAmeas, ",", expr sub_nonpos, ",", expr ennreal.to_real_le_to_real, "]"] ["at", ident this],
    exacts ["[", expr ne_of_lt (measure_lt_top _ _), ",", expr ne_of_lt (measure_lt_top _ _), "]"] },
  have [ident hμ] [":", expr «expr = »(μ A, 0)] [],
  { lift [expr μ A] ["to", expr «exprℝ≥0»()] ["using", expr ne_of_lt (measure_lt_top _ _)] ["with", ident μA],
    lift [expr ν A] ["to", expr «exprℝ≥0»()] ["using", expr ne_of_lt (measure_lt_top _ _)] ["with", ident νA],
    rw [expr ennreal.coe_eq_zero] [],
    by_cases [expr hb, ":", expr «expr < »(0, νA)],
    { suffices [] [":", expr ∀ b, «expr < »(0, b) → «expr ≤ »(μA, b)],
      { by_contra [],
        have [ident h'] [] [":=", expr this «expr / »(μA, 2) (nnreal.half_pos (zero_lt_iff.2 h))],
        rw ["<-", expr @not_not «expr ≤ »(μA, «expr / »(μA, 2))] ["at", ident h'],
        exact [expr h' (not_le.2 (nnreal.half_lt_self h))] },
      intros [ident c, ident hc],
      have [] [":", expr «expr∃ , »((n : exprℕ()), «expr < »(«expr / »(1, («expr + »(n, 1) : exprℝ())), «expr * »(c, «expr ⁻¹»(νA))))] [],
      refine [expr exists_nat_one_div_lt _],
      { refine [expr mul_pos hc _],
        rw [expr _root_.inv_pos] [],
        exact [expr hb] },
      rcases [expr this, "with", "⟨", ident n, ",", ident hn, "⟩"],
      have [ident hb₁] [":", expr «expr < »((0 : exprℝ()), «expr ⁻¹»(νA))] [],
      { rw [expr _root_.inv_pos] [],
        exact [expr hb] },
      have [ident h'] [":", expr «expr < »(«expr * »(«expr / »(1, «expr + »(«expr↑ »(n), 1)), νA), c)] [],
      { rw ["[", "<-", expr nnreal.coe_lt_coe, ",", "<-", expr mul_lt_mul_right hb₁, ",", expr nnreal.coe_mul, ",", expr mul_assoc, ",", "<-", expr nnreal.coe_inv, ",", "<-", expr nnreal.coe_mul, ",", expr _root_.mul_inv_cancel, ",", "<-", expr nnreal.coe_mul, ",", expr mul_one, ",", expr nnreal.coe_inv, "]"] [],
        { convert [] [expr hn] [],
          simp [] [] [] [] [] [] },
        { exact [expr ne.symm (ne_of_lt hb)] } },
      refine [expr le_trans _ (le_of_lt h')],
      rw ["[", "<-", expr ennreal.coe_le_coe, ",", expr ennreal.coe_mul, "]"] [],
      exact [expr hA₃ n] },
    { rw ["[", expr not_lt, ",", expr le_zero_iff, "]"] ["at", ident hb],
      specialize [expr hA₃ 0],
      simp [] [] [] ["[", expr hb, ",", expr le_zero_iff, "]"] [] ["at", ident hA₃],
      assumption } },
  rw [expr mutually_singular] ["at", ident h],
  push_neg ["at", ident h],
  have [] [] [":=", expr h _ hAmeas hμ],
  simp_rw ["[", expr hA₁, ",", expr set.compl_Inter, ",", expr compl_compl, "]"] ["at", ident this],
  obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr exists_measure_pos_of_not_measure_Union_null this],
  exact [expr ⟨«expr / »(1, «expr + »(n, 1)), by simp [] [] [] [] [] [], f n, hf₁ n, hn, hf₂ n⟩]
end

namespace LebesgueDecomposition

/-- Given two measures `μ` and `ν`, `measurable_le μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
def measurable_le (μ ν : Measureₓ α) : Set (α → ℝ≥0∞) :=
  { f | Measurable f ∧ ∀ A : Set α hA : MeasurableSet A, (∫⁻x in A, f x ∂μ) ≤ ν A }

theorem zero_mem_measurable_le : (0 : α → ℝ≥0∞) ∈ measurable_le μ ν :=
  ⟨measurable_zero,
    fun A hA =>
      by 
        simp ⟩

theorem max_measurable_le (f g : α → ℝ≥0∞) (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) (A : Set α)
  (hA : MeasurableSet A) :
  (∫⁻a in A, max (f a) (g a) ∂μ) ≤ (∫⁻a in A ∩ { a | f a ≤ g a }, g a ∂μ)+∫⁻a in A ∩ { a | g a < f a }, f a ∂μ :=
  by 
    rw [←lintegral_indicator _ hA, ←lintegral_indicator f, ←lintegral_indicator g, ←lintegral_add]
    ·
      refine' lintegral_mono fun a => _ 
      byCases' haA : a ∈ A
      ·
        byCases' f a ≤ g a
        ·
          simp only 
          rw [Set.indicator_of_mem haA, Set.indicator_of_mem, Set.indicator_of_not_mem, add_zeroₓ]
          simp only [le_reflₓ, max_le_iff, and_trueₓ, h]
          ·
            rintro ⟨_, hc⟩
            exact False.elim ((not_ltₓ.2 h) hc)
          ·
            exact ⟨haA, h⟩
        ·
          simp only 
          rw [Set.indicator_of_mem haA, Set.indicator_of_mem _ f, Set.indicator_of_not_mem, zero_addₓ]
          simp only [true_andₓ, le_reflₓ, max_le_iff, le_of_ltₓ (not_leₓ.1 h)]
          ·
            rintro ⟨_, hc⟩
            exact False.elim (h hc)
          ·
            exact ⟨haA, not_leₓ.1 h⟩
      ·
        simp [Set.indicator_of_not_mem haA]
    ·
      exact Measurable.indicator hg.1 (hA.inter (measurable_set_le hf.1 hg.1))
    ·
      exact Measurable.indicator hf.1 (hA.inter (measurable_set_lt hg.1 hf.1))
    ·
      exact hA.inter (measurable_set_le hf.1 hg.1)
    ·
      exact hA.inter (measurable_set_lt hg.1 hf.1)

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sup_mem_measurable_le
{f g : α → «exprℝ≥0∞»()}
(hf : «expr ∈ »(f, measurable_le μ ν))
(hg : «expr ∈ »(g, measurable_le μ ν)) : «expr ∈ »(λ a, «expr ⊔ »(f a, g a), measurable_le μ ν) :=
begin
  simp_rw [expr ennreal.sup_eq_max] [],
  refine [expr ⟨measurable.max hf.1 hg.1, λ A hA, _⟩],
  have [ident h₁] [] [":=", expr hA.inter (measurable_set_le hf.1 hg.1)],
  have [ident h₂] [] [":=", expr hA.inter (measurable_set_lt hg.1 hf.1)],
  refine [expr le_trans (max_measurable_le f g hf hg A hA) _],
  refine [expr le_trans (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)) _],
  { rw ["[", "<-", expr measure_union _ h₁ h₂, "]"] [],
    { refine [expr le_of_eq _],
      congr,
      convert [] [expr set.inter_union_compl A _] [],
      ext [] [ident a] [],
      simpa [] [] [] [] [] [] },
    rintro [ident x, "⟨", "⟨", "-", ",", ident hx₁, "⟩", ",", "-", ",", ident hx₂, "⟩"],
    exact [expr not_le.2 hx₂ hx₁] }
end

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supr_succ_eq_sup
{α}
(f : exprℕ() → α → «exprℝ≥0∞»())
(m : exprℕ())
(a : α) : «expr = »(«expr⨆ , »((k : exprℕ())
  (hk : «expr ≤ »(k, «expr + »(m, 1))), f k a), «expr ⊔ »(f m.succ a, «expr⨆ , »((k : exprℕ())
   (hk : «expr ≤ »(k, m)), f k a))) :=
begin
  ext [] [ident x] [],
  simp [] [] ["only"] ["[", expr option.mem_def, ",", expr ennreal.some_eq_coe, "]"] [] [],
  split; intro [ident h]; rw ["<-", expr h] [],
  symmetry,
  all_goals { set [] [ident c] [] [":="] [expr «expr⨆ , »((k : exprℕ())
      (hk : «expr ≤ »(k, «expr + »(m, 1))), f k a)] ["with", ident hc],
    set [] [ident d] [] [":="] [expr «expr ⊔ »(f m.succ a, «expr⨆ , »((k : exprℕ())
       (hk : «expr ≤ »(k, m)), f k a))] ["with", ident hd],
    suffices [] [":", expr «expr ∧ »(«expr ≤ »(c, d), «expr ≤ »(d, c))],
    { change [expr «expr = »(c, d)] [] [],
      exact [expr le_antisymm this.1 this.2] },
    rw ["[", expr hc, ",", expr hd, "]"] [],
    refine [expr ⟨_, _⟩],
    { refine [expr bsupr_le (λ n hn, _)],
      rcases [expr nat.of_le_succ hn, "with", "(", ident h, "|", ident h, ")"],
      { exact [expr le_sup_of_le_right (le_bsupr n h)] },
      { exact [expr «expr ▸ »(h, le_sup_left)] } },
    { refine [expr sup_le _ _],
      { convert [] [expr @le_bsupr _ _ _ (λ i, «expr ≤ »(i, «expr + »(m, 1))) _ m.succ (le_refl _)] [],
        refl },
      { refine [expr bsupr_le (λ n hn, _)],
        have [] [] [":=", expr le_trans hn (nat.le_succ m)],
        exact [expr le_bsupr n this] } } }
end

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supr_mem_measurable_le
(f : exprℕ() → α → «exprℝ≥0∞»())
(hf : ∀ n, «expr ∈ »(f n, measurable_le μ ν))
(n : exprℕ()) : «expr ∈ »(λ x, «expr⨆ , »((k) (hk : «expr ≤ »(k, n)), f k x), measurable_le μ ν) :=
begin
  induction [expr n] [] ["with", ident m, ident hm] [],
  { refine [expr ⟨_, _⟩],
    { simp [] [] [] ["[", expr (hf 0).1, "]"] [] [] },
    { intros [ident A, ident hA],
      simp [] [] [] ["[", expr (hf 0).2 A hA, "]"] [] [] } },
  { have [] [":", expr «expr = »(λ
      a : α, «expr⨆ , »((k : exprℕ())
       (hk : «expr ≤ »(k, «expr + »(m, 1))), f k a), λ
      a, «expr ⊔ »(f m.succ a, «expr⨆ , »((k : exprℕ()) (hk : «expr ≤ »(k, m)), f k a)))] [],
    { exact [expr funext (λ _, supr_succ_eq_sup _ _ _)] },
    refine [expr ⟨measurable_supr (λ n, measurable.supr_Prop _ (hf n).1), λ A hA, _⟩],
    rw [expr this] [],
    exact [expr (sup_mem_measurable_le (hf m.succ) hm).2 A hA] }
end

theorem supr_mem_measurable_le' (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) :
  (⨆(k : _)(hk : k ≤ n), f k) ∈ measurable_le μ ν :=
  by 
    convert supr_mem_measurable_le f hf n 
    ext 
    simp 

section SuprLemmas

omit m

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem supr_monotone
{α : Type*}
(f : exprℕ() → α → «exprℝ≥0∞»()) : monotone (λ n x, «expr⨆ , »((k) (hk : «expr ≤ »(k, n)), f k x)) :=
begin
  intros [ident n, ident m, ident hnm, ident x],
  simp [] [] ["only"] [] [] [],
  refine [expr bsupr_le (λ k hk, _)],
  have [] [":", expr «expr ≤ »(k, m)] [":=", expr le_trans hk hnm],
  exact [expr le_bsupr k this]
end

theorem supr_monotone' {α : Type _} (f : ℕ → α → ℝ≥0∞) (x : α) : Monotone fun n => ⨆(k : _)(hk : k ≤ n), f k x :=
  fun n m hnm => supr_monotone f hnm x

theorem supr_le_le {α : Type _} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
  f k ≤ fun x => ⨆(k : _)(hk : k ≤ n), f k x :=
  fun x => le_bsupr k hk

end SuprLemmas

/-- `measurable_le_eval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurable_le μ ν`. -/
def measurable_le_eval (μ ν : Measureₓ α) : Set ℝ≥0∞ :=
  (fun f : α → ℝ≥0∞ => ∫⁻x, f x ∂μ) '' measurable_le μ ν

end LebesgueDecomposition

open LebesgueDecomposition

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any pair of finite measures `μ` and `ν`, `have_lebesgue_decomposition`. That is to say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular
with respect to `ν` and `μ = ξ + ν.with_density f`.

This is not an instance since this is also shown for the more general σ-finite measures with
`measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite`. -/
theorem have_lebesgue_decomposition_of_finite_measure
[is_finite_measure μ]
[is_finite_measure ν] : have_lebesgue_decomposition μ ν :=
⟨begin
   have [ident h] [] [":=", expr @exists_seq_tendsto_Sup _ _ _ _ _ (measurable_le_eval ν μ) ⟨0, 0, zero_mem_measurable_le, by simp [] [] [] [] [] []⟩ (order_top.bdd_above _)],
   choose [] [ident g] [ident hmono, ident hg₂, ident f, ident hf₁, ident hf₂] ["using", expr h],
   set [] [ident ξ] [] [":="] [expr «expr⨆ , »((n k) (hk : «expr ≤ »(k, n)), f k)] ["with", ident hξ],
   have [ident hξ₁] [":", expr «expr = »(Sup (measurable_le_eval ν μ), «expr∫⁻ , ∂ »((a), ξ a, ν))] [],
   { have [] [] [":=", expr @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (λ
       n, «expr⨆ , »((k) (hk : «expr ≤ »(k, n)), f k)) «expr⨆ , »((n k) (hk : «expr ≤ »(k, n)), f k) _ _ _],
     { refine [expr tendsto_nhds_unique _ this],
       refine [expr tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _],
       { intro [ident n],
         rw ["<-", expr hf₂ n] [],
         apply [expr lintegral_mono],
         simp [] [] ["only"] ["[", expr supr_apply, ",", expr supr_le_le f n n (le_refl _), "]"] [] [] },
       { intro [ident n],
         exact [expr le_Sup ⟨«expr⨆ , »((k : exprℕ())
            (hk : «expr ≤ »(k, n)), f k), supr_mem_measurable_le' _ hf₁ _, rfl⟩] } },
     { intro [ident n],
       refine [expr measurable.ae_measurable _],
       convert [] [expr (supr_mem_measurable_le _ hf₁ n).1] [],
       ext [] [] [],
       simp [] [] [] [] [] [] },
     { refine [expr filter.eventually_of_forall (λ a, _)],
       simp [] [] [] ["[", expr supr_monotone' f _, "]"] [] [] },
     { refine [expr filter.eventually_of_forall (λ a, _)],
       simp [] [] [] ["[", expr tendsto_at_top_supr (supr_monotone' f a), "]"] [] [] } },
   have [ident hξm] [":", expr measurable ξ] [],
   { convert [] [expr measurable_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1)] [],
     ext [] [] [],
     simp [] [] [] ["[", expr hξ, "]"] [] [] },
   set [] [ident μ₁] [] [":="] [expr «expr - »(μ, ν.with_density ξ)] ["with", ident hμ₁],
   have [ident hle] [":", expr «expr ≤ »(ν.with_density ξ, μ)] [],
   { intros [ident B, ident hB],
     rw ["[", expr hξ, ",", expr with_density_apply _ hB, "]"] [],
     simp_rw ["[", expr supr_apply, "]"] [],
     rw [expr lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _)] [],
     exact [expr supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB)] },
   haveI [] [":", expr is_finite_measure (ν.with_density ξ)] [],
   { refine [expr is_finite_measure_with_density _],
     have [ident hle'] [] [":=", expr hle set.univ measurable_set.univ],
     rw ["[", expr with_density_apply _ measurable_set.univ, ",", expr measure.restrict_univ, "]"] ["at", ident hle'],
     exact [expr ne_top_of_le_ne_top (measure_ne_top _ _) hle'] },
   refine [expr ⟨⟨μ₁, ξ⟩, hξm, _, _⟩],
   { by_contra [],
     obtain ["⟨", ident ε, ",", ident hε₁, ",", ident E, ",", ident hE₁, ",", ident hE₂, ",", ident hE₃, "⟩", ":=", expr exists_positive_of_not_mutually_singular μ₁ ν h],
     simp_rw [expr hμ₁] ["at", ident hE₃],
     have [ident hξle] [":", expr ∀ A, measurable_set A → «expr ≤ »(«expr∫⁻ in , ∂ »((a), A, ξ a, ν), μ A)] [],
     { intros [ident A, ident hA],
       rw [expr hξ] [],
       simp_rw ["[", expr supr_apply, "]"] [],
       rw [expr lintegral_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1) (supr_monotone _)] [],
       exact [expr supr_le (λ n, (supr_mem_measurable_le _ hf₁ n).2 A hA)] },
     have [ident hε₂] [":", expr ∀
      A : set α, measurable_set A → «expr ≤ »(«expr∫⁻ in , ∂ »((a), «expr ∩ »(A, E), «expr + »(ε, ξ a), ν), μ «expr ∩ »(A, E))] [],
     { intros [ident A, ident hA],
       have [] [] [":=", expr subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ (set.inter_subset_right A E)],
       rwa ["[", expr zero_apply, ",", expr to_signed_measure_sub_apply (hA.inter hE₁), ",", expr measure.sub_apply (hA.inter hE₁) hle, ",", expr ennreal.to_real_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), ",", expr sub_nonneg, ",", expr le_sub_iff_add_le, ",", "<-", expr ennreal.to_real_add, ",", expr ennreal.to_real_le_to_real, ",", expr measure.coe_nnreal_smul, ",", expr pi.smul_apply, ",", expr with_density_apply _ (hA.inter hE₁), ",", expr show «expr = »(«expr • »(ε, ν «expr ∩ »(A, E)), «expr * »((ε : «exprℝ≥0∞»()), ν «expr ∩ »(A, E))), by refl, ",", "<-", expr set_lintegral_const, ",", "<-", expr lintegral_add measurable_const hξm, "]"] ["at", ident this],
       { rw ["[", expr ne.def, ",", expr ennreal.add_eq_top, ",", expr not_or_distrib, "]"] [],
         exact [expr ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩] },
       { exact [expr ne_of_lt (measure_lt_top _ _)] },
       { exact [expr ne_of_lt (measure_lt_top _ _)] },
       { exact [expr ne_of_lt (measure_lt_top _ _)] },
       { rw [expr with_density_apply _ (hA.inter hE₁)] [],
         exact [expr hξle «expr ∩ »(A, E) (hA.inter hE₁)] },
       { apply_instance } },
     have [ident hξε] [":", expr «expr ∈ »(«expr + »(ξ, E.indicator (λ _, ε)), measurable_le ν μ)] [],
     { refine [expr ⟨measurable.add hξm (measurable.indicator measurable_const hE₁), λ A hA, _⟩],
       have [] [":", expr «expr = »(«expr∫⁻ in , ∂ »((a), A, «expr + »(ξ, E.indicator (λ
            _, ε)) a, ν), «expr + »(«expr∫⁻ in , ∂ »((a), «expr ∩ »(A, E), «expr + »(ε, ξ a), ν), «expr∫⁻ in , ∂ »((a), «expr ∩ »(A, «expr ᶜ»(E)), ξ a, ν)))] [],
       { rw ["[", expr lintegral_add measurable_const hξm, ",", expr add_assoc, ",", "<-", expr lintegral_union (hA.inter hE₁) (hA.inter hE₁.compl) (disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _) disjoint_compl_right), ",", expr set.inter_union_compl, "]"] [],
         simp_rw ["[", expr pi.add_apply, "]"] [],
         rw ["[", expr lintegral_add hξm (measurable.indicator measurable_const hE₁), ",", expr add_comm, "]"] [],
         refine [expr congr_fun (congr_arg has_add.add _) _],
         rw ["[", expr set_lintegral_const, ",", expr lintegral_indicator _ hE₁, ",", expr set_lintegral_const, ",", expr measure.restrict_apply hE₁, ",", expr set.inter_comm, "]"] [] },
       conv_rhs [] [] { rw ["<-", expr set.inter_union_compl A E] },
       rw ["[", expr this, ",", expr measure_union _ (hA.inter hE₁) (hA.inter hE₁.compl), "]"] [],
       { exact [expr add_le_add (hε₂ A hA) (hξle «expr ∩ »(A, «expr ᶜ»(E)) (hA.inter hE₁.compl))] },
       { exact [expr disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _) disjoint_compl_right] } },
     have [] [":", expr «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr + »(ξ a, E.indicator (λ
          _, ε) a), ν), Sup (measurable_le_eval ν μ))] [":=", expr le_Sup ⟨«expr + »(ξ, E.indicator (λ
         _, ε)), hξε, rfl⟩],
     refine [expr not_lt.2 this _],
     rw ["[", expr hξ₁, ",", expr lintegral_add hξm (measurable.indicator measurable_const hE₁), ",", expr lintegral_indicator _ hE₁, ",", expr set_lintegral_const, "]"] [],
     refine [expr ennreal.lt_add_right _ (ennreal.mul_pos_iff.2 ⟨ennreal.coe_pos.2 hε₁, hE₂⟩).ne'],
     have [] [] [":=", expr measure_ne_top (ν.with_density ξ) set.univ],
     rwa ["[", expr with_density_apply _ measurable_set.univ, ",", expr measure.restrict_univ, "]"] ["at", ident this] },
   { rw [expr hμ₁] [],
     ext1 [] [ident A, ident hA],
     rw ["[", expr measure.coe_add, ",", expr pi.add_apply, ",", expr measure.sub_apply hA hle, ",", expr add_comm, ",", expr add_tsub_cancel_of_le (hle A hA), "]"] [] }
 end⟩

attribute [local instance] have_lebesgue_decomposition_of_finite_measure

instance  {S : μ.finite_spanning_sets_in { s:Set α | MeasurableSet s }} (n : ℕ) :
  is_finite_measure (μ.restrict$ S.set n) :=
  ⟨by 
      rw [restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact S.finite _⟩

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **The Lebesgue decomposition theorem**: Any pair of σ-finite measures `μ` and `ν`
`have_lebesgue_decomposition`. That is to say, there exist a measure `ξ` and a measurable function
`f`, such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.with_density f` -/
@[priority 100]
instance have_lebesgue_decomposition_of_sigma_finite
(μ ν : measure α)
[sigma_finite μ]
[sigma_finite ν] : have_lebesgue_decomposition μ ν :=
⟨begin
   obtain ["⟨", ident S, ",", ident T, ",", ident h₁, ",", ident h₂, "⟩", ":=", expr exists_eq_disjoint_finite_spanning_sets_in μ ν],
   have [ident h₃] [":", expr pairwise «expr on »(disjoint, T.set)] [":=", expr «expr ▸ »(h₁, h₂)],
   set [] [ident μn] [":", expr exprℕ() → measure α] [":="] [expr λ n, μ.restrict (S.set n)] ["with", ident hμn],
   have [ident hμ] [":", expr «expr = »(μ, sum μn)] [],
   { rw ["[", expr hμn, ",", "<-", expr restrict_Union h₂ S.set_mem, ",", expr S.spanning, ",", expr restrict_univ, "]"] [] },
   set [] [ident νn] [":", expr exprℕ() → measure α] [":="] [expr λ n, ν.restrict (T.set n)] ["with", ident hνn],
   have [ident hν] [":", expr «expr = »(ν, sum νn)] [],
   { rw ["[", expr hνn, ",", "<-", expr restrict_Union h₃ T.set_mem, ",", expr T.spanning, ",", expr restrict_univ, "]"] [] },
   set [] [ident ξ] [] [":="] [expr sum (λ n, singular_part (μn n) (νn n))] ["with", ident hξ],
   set [] [ident f] [] [":="] [expr «expr∑' , »((n), (S.set n).indicator (rn_deriv (μn n) (νn n)))] ["with", ident hf],
   refine [expr ⟨⟨ξ, f⟩, _, _, _⟩],
   { exact [expr measurable.ennreal_tsum' (λ
       n, measurable.indicator (measurable_rn_deriv (μn n) (νn n)) (S.set_mem n))] },
   { choose [] [ident A] [ident hA₁, ident hA₂, ident hA₃] ["using", expr λ
      n, mutually_singular_singular_part (μn n) (νn n)],
     simp [] [] ["only"] ["[", expr hξ, "]"] [] [],
     refine [expr ⟨«expr⋃ , »((j), «expr ∩ »(S.set j, A j)), measurable_set.Union (λ
        n, (S.set_mem n).inter (hA₁ n)), _, _⟩],
     { rw ["[", expr measure_Union, "]"] [],
       { have [] [":", expr ∀
          i, «expr = »(sum (λ
            n, (μn n).singular_part (νn n)) «expr ∩ »(S.set i, A i), (μn i).singular_part (νn i) «expr ∩ »(S.set i, A i))] [],
         { intro [ident i],
           rw ["[", expr sum_apply _ ((S.set_mem i).inter (hA₁ i)), ",", expr tsum_eq_single i, "]"] [],
           { intros [ident j, ident hij],
             rw ["[", expr hμn, ",", "<-", expr nonpos_iff_eq_zero, "]"] [],
             refine [expr le_trans (singular_part_le _ _ _ ((S.set_mem i).inter (hA₁ i))) (le_of_eq _)],
             rw ["[", expr restrict_apply ((S.set_mem i).inter (hA₁ i)), ",", expr set.inter_comm, ",", "<-", expr set.inter_assoc, "]"] [],
             have [] [":", expr disjoint (S.set j) (S.set i)] [":=", expr h₂ j i hij],
             rw [expr set.disjoint_iff_inter_eq_empty] ["at", ident this],
             rw ["[", expr this, ",", expr set.empty_inter, ",", expr measure_empty, "]"] [] },
           { apply_instance } },
         simp_rw ["[", expr this, ",", expr tsum_eq_zero_iff ennreal.summable, "]"] [],
         intro [ident n],
         exact [expr measure_mono_null (set.inter_subset_right _ _) (hA₂ n)] },
       { exact [expr h₂.mono (λ i j, disjoint.mono inf_le_left inf_le_left)] },
       { exact [expr λ n, (S.set_mem n).inter (hA₁ n)] } },
     { have [ident hcompl] [":", expr is_compl «expr⋃ , »((n), «expr ∩ »(S.set n, A n)) «expr⋃ , »((n), «expr ∩ »(S.set n, «expr ᶜ»(A n)))] [],
       { split,
         { rintro [ident x, "⟨", ident hx₁, ",", ident hx₂, "⟩"],
           rw [expr set.mem_Union] ["at", ident hx₁, ident hx₂],
           obtain ["⟨", "⟨", ident i, ",", ident hi₁, ",", ident hi₂, "⟩", ",", "⟨", ident j, ",", ident hj₁, ",", ident hj₂, "⟩", "⟩", ":=", "⟨", expr hx₁, ",", expr hx₂, "⟩"],
           have [] [":", expr «expr = »(i, j)] [],
           { by_contra [ident hij],
             exact [expr h₂ i j hij ⟨hi₁, hj₁⟩] },
           exact [expr hj₂ «expr ▸ »(this, hi₂)] },
         { intros [ident x, ident hx],
           simp [] [] ["only"] ["[", expr set.mem_Union, ",", expr set.sup_eq_union, ",", expr set.mem_inter_eq, ",", expr set.mem_union_eq, ",", expr set.mem_compl_eq, ",", expr or_iff_not_imp_left, "]"] [] [],
           intro [ident h],
           push_neg ["at", ident h],
           rw ["[", expr set.top_eq_univ, ",", "<-", expr S.spanning, ",", expr set.mem_Union, "]"] ["at", ident hx],
           obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr hx],
           exact [expr ⟨i, hi, h i hi⟩] } },
       rw ["[", expr hcompl.compl_eq, ",", expr measure_Union, ",", expr tsum_eq_zero_iff ennreal.summable, "]"] [],
       { intro [ident n],
         rw ["[", expr set.inter_comm, ",", "<-", expr restrict_apply (hA₁ n).compl, ",", "<-", expr hA₃ n, ",", expr hνn, ",", expr h₁, "]"] [] },
       { exact [expr h₂.mono (λ i j, disjoint.mono inf_le_left inf_le_left)] },
       { exact [expr λ n, (S.set_mem n).inter (hA₁ n).compl] } } },
   { simp [] [] ["only"] ["[", expr hξ, ",", expr hf, ",", expr hμ, "]"] [] [],
     rw ["[", expr with_density_tsum _, ",", expr sum_add_sum, "]"] [],
     { refine [expr sum_congr (λ n, _)],
       conv_lhs [] [] { rw [expr have_lebesgue_decomposition_add (μn n) (νn n)] },
       suffices [ident heq] [":", expr «expr = »((νn n).with_density ((μn n).rn_deriv (νn n)), ν.with_density ((S.set n).indicator ((μn n).rn_deriv (νn n))))],
       { rw [expr heq] [] },
       rw ["[", expr hν, ",", expr with_density_indicator (S.set_mem n), ",", expr restrict_sum _ (S.set_mem n), "]"] [],
       suffices [ident hsumeq] [":", expr «expr = »(sum (λ i : exprℕ(), (νn i).restrict (S.set n)), νn n)],
       { rw [expr hsumeq] [] },
       ext1 [] [ident s, ident hs],
       rw ["[", expr sum_apply _ hs, ",", expr tsum_eq_single n, ",", expr hνn, ",", expr h₁, ",", expr restrict_restrict (T.set_mem n), ",", expr set.inter_self, "]"] [],
       { intros [ident m, ident hm],
         rw ["[", expr hνn, ",", expr h₁, ",", expr restrict_restrict (T.set_mem n), ",", expr set.inter_comm, ",", expr set.disjoint_iff_inter_eq_empty.1 (h₃ m n hm), ",", expr restrict_empty, ",", expr coe_zero, ",", expr pi.zero_apply, "]"] [] },
       { apply_instance } },
     { exact [expr λ n, measurable.indicator (measurable_rn_deriv _ _) (S.set_mem n)] } }
 end⟩

end Measureₓ

namespace SignedMeasure

open Measureₓ

/-- A signed measure `s` is said to `have_lebesgue_decomposition` with respect to a measure `μ`
if the positive part and the negative part of `s` both `have_lebesgue_decomposition` with
respect to `μ`. -/
class have_lebesgue_decomposition(s : signed_measure α)(μ : Measureₓ α) : Prop where 
  posPart : s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition μ 
  negPart : s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition μ

attribute [instance] have_lebesgue_decomposition.pos_part

attribute [instance] have_lebesgue_decomposition.neg_part

theorem not_have_lebesgue_decomposition_iff (s : signed_measure α) (μ : Measureₓ α) :
  ¬s.have_lebesgue_decomposition μ ↔
    ¬s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition μ ∨
      ¬s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_distrib.2 h) ⟨hl.1, hl.2⟩⟩

instance (priority := 100)have_lebesgue_decomposition_of_sigma_finite (s : signed_measure α) (μ : Measureₓ α)
  [sigma_finite μ] : s.have_lebesgue_decomposition μ :=
  { posPart := inferInstance, negPart := inferInstance }

instance have_lebesgue_decomposition_neg (s : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ] :
  (-s).HaveLebesgueDecomposition μ :=
  { posPart :=
      by 
        rw [to_jordan_decomposition_neg, jordan_decomposition.neg_pos_part]
        infer_instance,
    negPart :=
      by 
        rw [to_jordan_decomposition_neg, jordan_decomposition.neg_neg_part]
        infer_instance }

instance have_lebesgue_decomposition_smul (s : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  (r :  ℝ≥0 ) : (r • s).HaveLebesgueDecomposition μ :=
  { posPart :=
      by 
        rw [to_jordan_decomposition_smul, jordan_decomposition.smul_pos_part]
        infer_instance,
    negPart :=
      by 
        rw [to_jordan_decomposition_smul, jordan_decomposition.smul_neg_part]
        infer_instance }

instance have_lebesgue_decomposition_smul_real (s : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  (r : ℝ) : (r • s).HaveLebesgueDecomposition μ :=
  by 
    byCases' hr : 0 ≤ r
    ·
      lift r to  ℝ≥0  using hr 
      exact s.have_lebesgue_decomposition_smul μ _
    ·
      rw [not_leₓ] at hr 
      refine'
        { posPart :=
            by 
              rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_pos_part_neg _ _ hr]
              infer_instance,
          negPart :=
            by 
              rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_neg_part_neg _ _ hr]
              infer_instance }

/-- Given a signed measure `s` and a measure `μ`, `s.singular_part μ` is the signed measure
such that `s.singular_part μ + μ.with_densityᵥ (s.rn_deriv μ) = s` and
`s.singular_part μ` is mutually singular with respect to `μ`. -/
def singular_part (s : signed_measure α) (μ : Measureₓ α) : signed_measure α :=
  (s.to_jordan_decomposition.pos_part.singular_part μ).toSignedMeasure -
    (s.to_jordan_decomposition.neg_part.singular_part μ).toSignedMeasure

section 

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singular_part_mutually_singular
(s : signed_measure α)
(μ : measure α) : «expr ⊥ₘ »(s.to_jordan_decomposition.pos_part.singular_part μ, s.to_jordan_decomposition.neg_part.singular_part μ) :=
begin
  by_cases [expr hl, ":", expr s.have_lebesgue_decomposition μ],
  { haveI [] [] [":=", expr hl],
    obtain ["⟨", ident i, ",", ident hi, ",", ident hpos, ",", ident hneg, "⟩", ":=", expr s.to_jordan_decomposition.mutually_singular],
    rw [expr s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ] ["at", ident hpos],
    rw [expr s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ] ["at", ident hneg],
    rw ["[", expr add_apply, ",", expr add_eq_zero_iff, "]"] ["at", ident hpos, ident hneg],
    exact [expr ⟨i, hi, hpos.1, hneg.1⟩] },
  { rw [expr not_have_lebesgue_decomposition_iff] ["at", ident hl],
    cases [expr hl] ["with", ident hp, ident hn],
    { rw ["[", expr measure.singular_part, ",", expr dif_neg hp, "]"] [],
      exact [expr mutually_singular.zero_left] },
    { rw ["[", expr measure.singular_part, ",", expr measure.singular_part, ",", expr dif_neg hn, "]"] [],
      exact [expr mutually_singular.zero_right] } }
end

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singular_part_total_variation
(s : signed_measure α)
(μ : measure α) : «expr = »((s.singular_part μ).total_variation, «expr + »(s.to_jordan_decomposition.pos_part.singular_part μ, s.to_jordan_decomposition.neg_part.singular_part μ)) :=
begin
  have [] [":", expr «expr = »((s.singular_part μ).to_jordan_decomposition, ⟨s.to_jordan_decomposition.pos_part.singular_part μ, s.to_jordan_decomposition.neg_part.singular_part μ, singular_part_mutually_singular s μ⟩)] [],
  { refine [expr jordan_decomposition.to_signed_measure_injective _],
    rw [expr to_signed_measure_to_jordan_decomposition] [],
    refl },
  { rw ["[", expr total_variation, ",", expr this, "]"] [] }
end

theorem mutually_singular_singular_part (s : signed_measure α) (μ : Measureₓ α) :
  singular_part s μ ⊥ᵥ μ.to_ennreal_vector_measure :=
  by 
    rw [mutually_singular_ennreal_iff, singular_part_total_variation]
    change _ ⊥ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ)
    rw [vector_measure.equiv_measure.right_inv μ]
    exact (mutually_singular_singular_part _ _).add_left (mutually_singular_singular_part _ _)

end 

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`rn_deriv s μ` satisfies `μ.with_densityᵥ (s.rn_deriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`measure_theory.signed_measure.absolutely_continuous_iff_with_density_rn_deriv_eq`
and can be found in `measure_theory.decomposition.radon_nikodym`. -/
def rn_deriv (s : signed_measure α) (μ : Measureₓ α) : α → ℝ :=
  fun x =>
    (s.to_jordan_decomposition.pos_part.rn_deriv μ x).toReal - (s.to_jordan_decomposition.neg_part.rn_deriv μ x).toReal

variable{s t : signed_measure α}

@[measurability]
theorem measurable_rn_deriv (s : signed_measure α) (μ : Measureₓ α) : Measurable (rn_deriv s μ) :=
  by 
    rw [rn_deriv]
    measurability

theorem integrable_rn_deriv (s : signed_measure α) (μ : Measureₓ α) : integrable (rn_deriv s μ) μ :=
  by 
    refine' integrable.sub _ _ <;>
      ·
        split 
        measurability 
        exact has_finite_integral_to_real_of_lintegral_ne_top (lintegral_rn_deriv_lt_top _ μ).Ne

/-- **The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed measure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with respect to `μ`
and `s = t + μ.with_densityᵥ f`. In this case `t = s.singular_part μ` and
`f = s.rn_deriv μ`. -/
theorem singular_part_add_with_density_rn_deriv_eq [s.have_lebesgue_decomposition μ] :
  (s.singular_part μ+μ.with_densityᵥ (s.rn_deriv μ)) = s :=
  by 
    convRHS => rw [←to_signed_measure_to_jordan_decomposition s, jordan_decomposition.to_signed_measure]
    rw [singular_part, rn_deriv,
      with_densityᵥ_sub' (integrable_to_real_of_lintegral_ne_top _ _) (integrable_to_real_of_lintegral_ne_top _ _),
      with_densityᵥ_to_real, with_densityᵥ_to_real, sub_eq_add_neg, sub_eq_add_neg,
      add_commₓ (s.to_jordan_decomposition.pos_part.singular_part μ).toSignedMeasure, ←add_assocₓ,
      add_assocₓ (-(s.to_jordan_decomposition.neg_part.singular_part μ).toSignedMeasure), ←to_signed_measure_add,
      add_commₓ, ←add_assocₓ, ←neg_add, ←to_signed_measure_add, add_commₓ, ←sub_eq_add_neg]
    convert rfl
    ·
      exact s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition_add μ
    ·
      rw [add_commₓ]
      exact s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition_add μ 
    all_goals 
      first |
        exact (lintegral_rn_deriv_lt_top _ _).Ne|
        measurability

theorem jordan_decomposition_add_with_density_mutually_singular {f : α → ℝ} (hf : Measurable f)
  (htμ : t ⊥ᵥ μ.to_ennreal_vector_measure) :
  (t.to_jordan_decomposition.pos_part+μ.with_density fun x : α => Ennreal.ofReal (f x)) ⊥ₘ
    t.to_jordan_decomposition.neg_part+μ.with_density fun x : α => Ennreal.ofReal (-f x) :=
  by 
    rw [mutually_singular_ennreal_iff, total_variation_mutually_singular_iff] at htμ 
    change
      _ ⊥ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) ∧
        _ ⊥ₘ vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ) at
      htμ 
    rw [vector_measure.equiv_measure.right_inv] at htμ 
    exact
      ((jordan_decomposition.mutually_singular _).add_right
            (htμ.1.mono_ac (refl _) (with_density_absolutely_continuous _ _))).add_left
        ((htμ.2.symm.mono_ac (with_density_absolutely_continuous _ _) (refl _)).add_right
          (with_density_of_real_mutually_singular hf))

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_jordan_decomposition_eq_of_eq_add_with_density
{f : α → exprℝ()}
(hf : measurable f)
(hfi : integrable f μ)
(htμ : «expr ⊥ᵥ »(t, μ.to_ennreal_vector_measure))
(hadd : «expr = »(s, «expr + »(t, μ.with_densityᵥ f))) : «expr = »(s.to_jordan_decomposition, @jordan_decomposition.mk α _ «expr + »(t.to_jordan_decomposition.pos_part, μ.with_density (λ
   x, ennreal.of_real (f x))) «expr + »(t.to_jordan_decomposition.neg_part, μ.with_density (λ
   x, ennreal.of_real «expr- »(f x))) (by { haveI [] [] [":=", expr is_finite_measure_with_density_of_real hfi.2],
    apply_instance }) (by { haveI [] [] [":=", expr is_finite_measure_with_density_of_real hfi.neg.2],
    apply_instance }) (jordan_decomposition_add_with_density_mutually_singular hf htμ)) :=
begin
  haveI [] [] [":=", expr is_finite_measure_with_density_of_real hfi.2],
  haveI [] [] [":=", expr is_finite_measure_with_density_of_real hfi.neg.2],
  refine [expr to_jordan_decomposition_eq _],
  simp_rw ["[", expr jordan_decomposition.to_signed_measure, ",", expr hadd, "]"] [],
  ext [] [ident i, ident hi] [],
  rw ["[", expr vector_measure.sub_apply, ",", expr to_signed_measure_apply_measurable hi, ",", expr to_signed_measure_apply_measurable hi, ",", expr add_apply, ",", expr add_apply, ",", expr ennreal.to_real_add, ",", expr ennreal.to_real_add, ",", expr add_sub_comm, ",", "<-", expr to_signed_measure_apply_measurable hi, ",", "<-", expr to_signed_measure_apply_measurable hi, ",", "<-", expr vector_measure.sub_apply, ",", "<-", expr jordan_decomposition.to_signed_measure, ",", expr to_signed_measure_to_jordan_decomposition, ",", expr vector_measure.add_apply, ",", "<-", expr to_signed_measure_apply_measurable hi, ",", "<-", expr to_signed_measure_apply_measurable hi, ",", expr with_densityᵥ_eq_with_density_pos_part_sub_with_density_neg_part hfi, ",", expr vector_measure.sub_apply, "]"] []; exact [expr (measure_lt_top _ _).ne]
end

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem have_lebesgue_decomposition_mk'
(μ : measure α)
{f : α → exprℝ()}
(hf : measurable f)
(hfi : integrable f μ)
(htμ : «expr ⊥ᵥ »(t, μ.to_ennreal_vector_measure))
(hadd : «expr = »(s, «expr + »(t, μ.with_densityᵥ f))) : s.have_lebesgue_decomposition μ :=
begin
  have [ident htμ'] [] [":=", expr htμ],
  rw [expr mutually_singular_ennreal_iff] ["at", ident htμ],
  change [expr «expr ⊥ₘ »(_, vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ))] [] ["at", ident htμ],
  rw ["[", expr vector_measure.equiv_measure.right_inv, ",", expr total_variation_mutually_singular_iff, "]"] ["at", ident htμ],
  refine [expr { pos_part := by { use [expr ⟨t.to_jordan_decomposition.pos_part, λ x, ennreal.of_real (f x)⟩],
       refine [expr ⟨hf.ennreal_of_real, htμ.1, _⟩],
       rw [expr to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd] [] },
     neg_part := by { use [expr ⟨t.to_jordan_decomposition.neg_part, λ x, ennreal.of_real «expr- »(f x)⟩],
       refine [expr ⟨hf.neg.ennreal_of_real, htμ.2, _⟩],
       rw [expr to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd] [] } }]
end

theorem have_lebesgue_decomposition_mk (μ : Measureₓ α) {f : α → ℝ} (hf : Measurable f)
  (htμ : t ⊥ᵥ μ.to_ennreal_vector_measure) (hadd : s = t+μ.with_densityᵥ f) : s.have_lebesgue_decomposition μ :=
  by 
    byCases' hfi : integrable f μ
    ·
      exact have_lebesgue_decomposition_mk' μ hf hfi htμ hadd
    ·
      rw [with_densityᵥ, dif_neg hfi, add_zeroₓ] at hadd 
      refine' have_lebesgue_decomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ _ 
      rwa [with_densityᵥ_zero, add_zeroₓ]

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem eq_singular_part'
(t : signed_measure α)
{f : α → exprℝ()}
(hf : measurable f)
(hfi : integrable f μ)
(htμ : «expr ⊥ᵥ »(t, μ.to_ennreal_vector_measure))
(hadd : «expr = »(s, «expr + »(t, μ.with_densityᵥ f))) : «expr = »(t, s.singular_part μ) :=
begin
  have [ident htμ'] [] [":=", expr htμ],
  rw ["[", expr mutually_singular_ennreal_iff, ",", expr total_variation_mutually_singular_iff, "]"] ["at", ident htμ],
  change [expr «expr ∧ »(«expr ⊥ₘ »(_, vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ)), «expr ⊥ₘ »(_, vector_measure.equiv_measure.to_fun (vector_measure.equiv_measure.inv_fun μ)))] [] ["at", ident htμ],
  rw ["[", expr vector_measure.equiv_measure.right_inv, "]"] ["at", ident htμ],
  { rw ["[", expr singular_part, ",", "<-", expr t.to_signed_measure_to_jordan_decomposition, ",", expr jordan_decomposition.to_signed_measure, "]"] [],
    congr,
    { have [ident hfpos] [":", expr measurable (λ x, ennreal.of_real (f x))] [],
      { measurability [] [] },
      refine [expr eq_singular_part hfpos htμ.1 _],
      rw [expr to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd] [] },
    { have [ident hfneg] [":", expr measurable (λ x, ennreal.of_real «expr- »(f x))] [],
      { measurability [] [] },
      refine [expr eq_singular_part hfneg htμ.2 _],
      rw [expr to_jordan_decomposition_eq_of_eq_add_with_density hf hfi htμ' hadd] [] } }
end

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.with_densityᵥ f`, we have
`t = singular_part s μ`, i.e. `t` is the singular part of the Lebesgue decomposition between
`s` and `μ`. -/
theorem eq_singular_part (t : signed_measure α) (f : α → ℝ) (htμ : t ⊥ᵥ μ.to_ennreal_vector_measure)
  (hadd : s = t+μ.with_densityᵥ f) : t = s.singular_part μ :=
  by 
    byCases' hfi : integrable f μ
    ·
      refine' eq_singular_part' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ _ 
      convert hadd using 2 
      exact with_densityᵥ_eq.congr_ae hfi.1.ae_eq_mk.symm
    ·
      rw [with_densityᵥ, dif_neg hfi, add_zeroₓ] at hadd 
      refine' eq_singular_part' t measurable_zero (integrable_zero _ _ μ) htμ _ 
      rwa [with_densityᵥ_zero, add_zeroₓ]

theorem singular_part_zero (μ : Measureₓ α) : (0 : signed_measure α).singularPart μ = 0 :=
  by 
    refine' (eq_singular_part 0 0 vector_measure.mutually_singular.zero_left _).symm 
    rw [zero_addₓ, with_densityᵥ_zero]

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singular_part_neg
(s : signed_measure α)
(μ : measure α) : «expr = »(«expr- »(s).singular_part μ, «expr- »(s.singular_part μ)) :=
begin
  have [ident h₁] [":", expr «expr = »((«expr- »(s).to_jordan_decomposition.pos_part.singular_part μ).to_signed_measure, (s.to_jordan_decomposition.neg_part.singular_part μ).to_signed_measure)] [],
  { refine [expr to_signed_measure_congr _],
    rw ["[", expr to_jordan_decomposition_neg, ",", expr jordan_decomposition.neg_pos_part, "]"] [] },
  have [ident h₂] [":", expr «expr = »((«expr- »(s).to_jordan_decomposition.neg_part.singular_part μ).to_signed_measure, (s.to_jordan_decomposition.pos_part.singular_part μ).to_signed_measure)] [],
  { refine [expr to_signed_measure_congr _],
    rw ["[", expr to_jordan_decomposition_neg, ",", expr jordan_decomposition.neg_neg_part, "]"] [] },
  rw ["[", expr singular_part, ",", expr singular_part, ",", expr neg_sub, ",", expr h₁, ",", expr h₂, "]"] []
end

theorem singular_part_smul_nnreal (s : signed_measure α) (μ : Measureₓ α) (r :  ℝ≥0 ) :
  (r • s).singularPart μ = r • s.singular_part μ :=
  by 
    rw [singular_part, singular_part, smul_sub, ←to_signed_measure_smul, ←to_signed_measure_smul]
    convLHS =>
      congr
        congr
        rw [to_jordan_decomposition_smul, jordan_decomposition.smul_pos_part,
        singular_part_smul]skip
        congr rw [to_jordan_decomposition_smul, jordan_decomposition.smul_neg_part, singular_part_smul]

theorem singular_part_smul (s : signed_measure α) (μ : Measureₓ α) (r : ℝ) :
  (r • s).singularPart μ = r • s.singular_part μ :=
  by 
    byCases' hr : 0 ≤ r
    ·
      lift r to  ℝ≥0  using hr 
      exact singular_part_smul_nnreal s μ r
    ·
      rw [singular_part, singular_part]
      convLHS =>
        congr
          congr
          rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_pos_part_neg _ _ (not_leₓ.1 hr),
          singular_part_smul]skip
          congr
          rw [to_jordan_decomposition_smul_real, jordan_decomposition.real_smul_neg_part_neg _ _ (not_leₓ.1 hr),
          singular_part_smul]
      rw [to_signed_measure_smul, to_signed_measure_smul, ←neg_sub, ←smul_sub]
      change -(((-r).toNnreal : ℝ) • _) = _ 
      rw [←neg_smul, Real.coe_to_nnreal _ (le_of_ltₓ (neg_pos.mpr (not_leₓ.1 hr))), neg_negₓ]

theorem singular_part_add (s t : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  [t.have_lebesgue_decomposition μ] : (s+t).singularPart μ = s.singular_part μ+t.singular_part μ :=
  by 
    refine'
      (eq_singular_part _ (s.rn_deriv μ+t.rn_deriv μ)
          ((mutually_singular_singular_part s μ).add_left (mutually_singular_singular_part t μ)) _).symm
        
    erw [with_densityᵥ_add (integrable_rn_deriv s μ) (integrable_rn_deriv t μ)]
    rw [add_assocₓ, add_commₓ (t.singular_part μ), add_assocₓ, add_commₓ _ (t.singular_part μ),
      singular_part_add_with_density_rn_deriv_eq, ←add_assocₓ, singular_part_add_with_density_rn_deriv_eq]

theorem singular_part_sub (s t : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  [t.have_lebesgue_decomposition μ] : (s - t).singularPart μ = s.singular_part μ - t.singular_part μ :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, singular_part_add, singular_part_neg]

-- error in MeasureTheory.Decomposition.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.with_densityᵥ f`, we have
`f = rn_deriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`. -/
theorem eq_rn_deriv
(t : signed_measure α)
(f : α → exprℝ())
(hfi : integrable f μ)
(htμ : «expr ⊥ᵥ »(t, μ.to_ennreal_vector_measure))
(hadd : «expr = »(s, «expr + »(t, μ.with_densityᵥ f))) : «expr =ᵐ[ ] »(f, μ, s.rn_deriv μ) :=
begin
  set [] [ident f'] [] [":="] [expr hfi.1.mk f] [],
  have [ident hadd'] [":", expr «expr = »(s, «expr + »(t, μ.with_densityᵥ f'))] [],
  { convert [] [expr hadd] ["using", 2],
    exact [expr with_densityᵥ_eq.congr_ae hfi.1.ae_eq_mk.symm] },
  haveI [] [] [":=", expr have_lebesgue_decomposition_mk μ hfi.1.measurable_mk htμ hadd'],
  refine [expr (integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _) hfi _).symm],
  rw ["[", "<-", expr add_right_inj t, ",", "<-", expr hadd, ",", expr eq_singular_part _ f htμ hadd, ",", expr singular_part_add_with_density_rn_deriv_eq, "]"] []
end

theorem rn_deriv_neg (s : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ] :
  (-s).rnDeriv μ =ᵐ[μ] -s.rn_deriv μ :=
  by 
    refine' integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _) (integrable_rn_deriv _ _).neg _ 
    rw [with_densityᵥ_neg, ←add_right_injₓ ((-s).singularPart μ), singular_part_add_with_density_rn_deriv_eq,
      singular_part_neg, ←neg_add, singular_part_add_with_density_rn_deriv_eq]

theorem rn_deriv_smul (s : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ] (r : ℝ) :
  (r • s).rnDeriv μ =ᵐ[μ] r • s.rn_deriv μ :=
  by 
    refine' integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _) ((integrable_rn_deriv _ _).smul r) _ 
    change _ = μ.with_densityᵥ ((r : ℝ) • s.rn_deriv μ)
    rw [with_densityᵥ_smul (rn_deriv s μ) (r : ℝ), ←add_right_injₓ ((r • s).singularPart μ),
      singular_part_add_with_density_rn_deriv_eq, singular_part_smul]
    change _ = _+r • _ 
    rw [←smul_add, singular_part_add_with_density_rn_deriv_eq]

theorem rn_deriv_add (s t : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  [t.have_lebesgue_decomposition μ] [(s+t).HaveLebesgueDecomposition μ] :
  (s+t).rnDeriv μ =ᵐ[μ] s.rn_deriv μ+t.rn_deriv μ :=
  by 
    refine'
      integrable.ae_eq_of_with_densityᵥ_eq (integrable_rn_deriv _ _)
        ((integrable_rn_deriv _ _).add (integrable_rn_deriv _ _)) _ 
    rw [←add_right_injₓ ((s+t).singularPart μ), singular_part_add_with_density_rn_deriv_eq,
      with_densityᵥ_add (integrable_rn_deriv _ _) (integrable_rn_deriv _ _), singular_part_add, add_assocₓ,
      add_commₓ (t.singular_part μ), add_assocₓ, add_commₓ _ (t.singular_part μ),
      singular_part_add_with_density_rn_deriv_eq, ←add_assocₓ, singular_part_add_with_density_rn_deriv_eq]

theorem rn_deriv_sub (s t : signed_measure α) (μ : Measureₓ α) [s.have_lebesgue_decomposition μ]
  [t.have_lebesgue_decomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
  (s - t).rnDeriv μ =ᵐ[μ] s.rn_deriv μ - t.rn_deriv μ :=
  by 
    rw [sub_eq_add_neg] at hst 
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact ae_eq_trans (rn_deriv_add _ _ _) (Filter.EventuallyEq.add (ae_eq_refl _) (rn_deriv_neg _ _))

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is said to `have_lebesgue_decomposition` with respect to a positive measure
if both its real and imaginary part `have_lebesgue_decomposition` with respect to that measure. -/
class have_lebesgue_decomposition(c : complex_measure α)(μ : Measureₓ α) : Prop where 
  re_part : c.re.have_lebesgue_decomposition μ 
  im_part : c.im.have_lebesgue_decomposition μ

attribute [instance] have_lebesgue_decomposition.re_part

attribute [instance] have_lebesgue_decomposition.im_part

/-- The singular part between a complex measure `c` and a positive measure `μ` is the complex
measure satisfying `c.singular_part μ + μ.with_densityᵥ (c.rn_deriv μ) = c`. This property is given
by `measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq`. -/
def singular_part (c : complex_measure α) (μ : Measureₓ α) : complex_measure α :=
  (c.re.singular_part μ).toComplexMeasure (c.im.singular_part μ)

/-- The Radon-Nikodym derivative between a complex measure and a positive measure. -/
def rn_deriv (c : complex_measure α) (μ : Measureₓ α) : α → ℂ :=
  fun x => ⟨c.re.rn_deriv μ x, c.im.rn_deriv μ x⟩

variable{c : complex_measure α}

theorem integrable_rn_deriv (c : complex_measure α) (μ : Measureₓ α) : integrable (c.rn_deriv μ) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable, ←mem_ℒp_re_im_iff]
    exact
      ⟨mem_ℒp_one_iff_integrable.2 (signed_measure.integrable_rn_deriv _ _),
        mem_ℒp_one_iff_integrable.2 (signed_measure.integrable_rn_deriv _ _)⟩

theorem singular_part_add_with_density_rn_deriv_eq [c.have_lebesgue_decomposition μ] :
  (c.singular_part μ+μ.with_densityᵥ (c.rn_deriv μ)) = c :=
  by 
    convRHS => rw [←c.to_complex_measure_to_signed_measure]
    ext i hi
    ·
      rw [vector_measure.add_apply, signed_measure.to_complex_measure_apply, Complex.add_re, re_apply,
        with_densityᵥ_apply (c.integrable_rn_deriv μ) hi,
        ←set_integral_re_add_im (c.integrable_rn_deriv μ).IntegrableOn]
      suffices  : ((c.singular_part μ i).re+∫x in i, (c.rn_deriv μ x).re ∂μ) = (c i).re
      ·
        simpa 
      rw [←with_densityᵥ_apply _ hi]
      ·
        change (c.re.singular_part μ+μ.with_densityᵥ (c.re.rn_deriv μ)) i = _ 
        rw [@signed_measure.singular_part_add_with_density_rn_deriv_eq _ _ μ c.re _]
        rfl
      ·
        exact signed_measure.integrable_rn_deriv _ _
    ·
      rw [vector_measure.add_apply, signed_measure.to_complex_measure_apply, Complex.add_im, im_apply,
        with_densityᵥ_apply (c.integrable_rn_deriv μ) hi,
        ←set_integral_re_add_im (c.integrable_rn_deriv μ).IntegrableOn]
      suffices  : ((c.singular_part μ i).im+∫x in i, (c.rn_deriv μ x).im ∂μ) = (c i).im
      ·
        simpa 
      rw [←with_densityᵥ_apply _ hi]
      ·
        change (c.im.singular_part μ+μ.with_densityᵥ (c.im.rn_deriv μ)) i = _ 
        rw [@signed_measure.singular_part_add_with_density_rn_deriv_eq _ _ μ c.im _]
        rfl
      ·
        exact signed_measure.integrable_rn_deriv _ _

end ComplexMeasure

end MeasureTheory

