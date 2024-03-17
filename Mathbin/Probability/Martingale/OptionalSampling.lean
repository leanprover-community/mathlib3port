/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Order.SuccPred.LinearLocallyFinite
import Probability.Martingale.Basic

#align_import probability.martingale.optional_sampling from "leanprover-community/mathlib"@"f2ad3645af9effcdb587637dc28a6074edc813f9"

/-!
# Optional sampling theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `τ` is a bounded stopping time and `σ` is another stopping time, then the value of a martingale
`f` at the stopping time `min τ σ` is almost everywhere equal to
`μ[stopped_value f τ | hσ.measurable_space]`.

## Main results

* `stopped_value_ae_eq_condexp_of_le_const`: the value of a martingale `f` at a stopping time `τ`
  bounded by `n` is the conditional expectation of `f n` with respect to the σ-algebra generated by
  `τ`.
* `stopped_value_ae_eq_condexp_of_le`: if `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is
  bounded, then the value of a martingale `f` at `σ` is the conditional expectation of its value at
  `τ` with respect to the σ-algebra generated by `σ`.
* `stopped_value_min_ae_eq_condexp`: the optional sampling theorem. If `τ` is a bounded stopping
  time and `σ` is another stopping time, then the value of a martingale `f` at the stopping time
  `min τ σ` is almost everywhere equal to the conditional expectation of `f` stopped at `τ`
  with respect to the σ-algebra generated by `σ`.

-/


open scoped MeasureTheory BigOperators ENNReal

open TopologicalSpace

/- warning: discrete_topology.second_countable_topology_of_countable clashes with discrete_topology.second_countable_topology_of_encodable -> DiscreteTopology.secondCountableTopology_of_countable
Case conversion may be inaccurate. Consider using '#align discrete_topology.second_countable_topology_of_countable DiscreteTopology.secondCountableTopology_of_countableₓ'. -/
#print DiscreteTopology.secondCountableTopology_of_countable /-
-- TODO after the port: move to topology/instances/discrete
instance (priority := 100) DiscreteTopology.secondCountableTopology_of_countable {α : Type _}
    [TopologicalSpace α] [DiscreteTopology α] [Countable α] : SecondCountableTopology α :=
  @DiscreteTopology.secondCountableTopology_of_countable _ _ _ (Encodable.ofCountable _)
#align discrete_topology.second_countable_topology_of_countable DiscreteTopology.secondCountableTopology_of_countable
-/

namespace MeasureTheory

namespace Martingale

variable {Ω E : Type _} {m : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]

section FirstCountableTopology

variable {ι : Type _} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [FirstCountableTopology ι] {ℱ : Filtration ι m} [SigmaFiniteFiltration μ ℱ] {τ σ : Ω → ι}
  {f : ι → Ω → E} {i n : ι}

#print MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const /-
theorem condexp_stopping_time_ae_eq_restrict_eq_const
    [(Filter.atTop : Filter ι).IsCountablyGenerated] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) [SigmaFinite (μ.trim hτ.measurableSpace_le)] (hin : i ≤ n) :
    μ[f n|hτ.MeasurableSpace] =ᵐ[μ.restrict {x | τ x = i}] f i :=
  by
  refine' Filter.EventuallyEq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin))
  refine'
    condexp_ae_eq_restrict_of_measurable_space_eq_on hτ.measurable_space_le (ℱ.le i)
      (hτ.measurable_set_eq' i) fun t => _
  rw [Set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff]
#align measure_theory.martingale.condexp_stopping_time_ae_eq_restrict_eq_const MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const
-/

#print MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const /-
theorem condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] (i : ι) :
    μ[f n|hτ.MeasurableSpace] =ᵐ[μ.restrict {x | τ x = i}] f i :=
  by
  by_cases hin : i ≤ n
  · refine' Filter.EventuallyEq.trans _ (ae_restrict_of_ae (h.condexp_ae_eq hin))
    refine'
      condexp_ae_eq_restrict_of_measurable_space_eq_on (hτ.measurable_space_le_of_le hτ_le) (ℱ.le i)
        (hτ.measurable_set_eq' i) fun t => _
    rw [Set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff]
  · suffices {x : Ω | τ x = i} = ∅ by simp [this]
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    rintro rfl
    exact hin (hτ_le x)
#align measure_theory.martingale.condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const MeasureTheory.Martingale.condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const
-/

#print MeasureTheory.Martingale.stoppedValue_ae_eq_restrict_eq /-
theorem stoppedValue_ae_eq_restrict_eq (h : Martingale f ℱ μ) (hτ : IsStoppingTime ℱ τ)
    (hτ_le : ∀ x, τ x ≤ n) [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] (i : ι) :
    stoppedValue f τ =ᵐ[μ.restrict {x | τ x = i}] μ[f n|hτ.MeasurableSpace] :=
  by
  refine'
    Filter.EventuallyEq.trans _
      (condexp_stopping_time_ae_eq_restrict_eq_const_of_le_const h hτ hτ_le i).symm
  rw [Filter.EventuallyEq, ae_restrict_iff' (ℱ.le _ _ (hτ.measurable_set_eq i))]
  refine' Filter.eventually_of_forall fun x hx => _
  rw [Set.mem_setOf_eq] at hx
  simp_rw [stopped_value, hx]
#align measure_theory.martingale.stopped_value_ae_eq_restrict_eq MeasureTheory.Martingale.stoppedValue_ae_eq_restrict_eq
-/

#print MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range /-
/-- The value of a martingale `f` at a stopping time `τ` bounded by `n` is the conditional
expectation of `f n` with respect to the σ-algebra generated by `τ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_const_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n) (h_countable_range : (Set.range τ).Countable)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] :
    stoppedValue f τ =ᵐ[μ] μ[f n|hτ.MeasurableSpace] :=
  by
  have : Set.univ = ⋃ i ∈ Set.range τ, {x | τ x = i} :=
    by
    ext1 x
    simp only [Set.mem_univ, Set.mem_range, true_and_iff, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.mem_iUnion, Set.mem_setOf_eq, exists_apply_eq_apply']
  nth_rw 1 [← @measure.restrict_univ Ω _ μ]
  rw [this, ae_eq_restrict_bUnion_iff _ h_countable_range]
  exact fun i hi => stopped_value_ae_eq_restrict_eq h _ hτ_le i
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_const_of_countable_range MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range
-/

#print MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const /-
/-- The value of a martingale `f` at a stopping time `τ` bounded by `n` is the conditional
expectation of `f n` with respect to the σ-algebra generated by `τ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_const [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim (hτ.measurableSpace_le_of_le hτ_le))] :
    stoppedValue f τ =ᵐ[μ] μ[f n|hτ.MeasurableSpace] :=
  h.stoppedValue_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le (Set.to_countable _)
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_const MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_const
-/

#print MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_of_countable_range /-
/-- If `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is bounded, then the value of a
martingale `f` at `σ` is the conditional expectation of its value at `τ` with respect to the
σ-algebra generated by `σ`. -/
theorem stoppedValue_ae_eq_condexp_of_le_of_countable_range (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    (hτ_countable_range : (Set.range τ).Countable) (hσ_countable_range : (Set.range σ).Countable)
    [SigmaFinite (μ.trim (hσ.measurableSpace_le_of_le fun x => (hσ_le_τ x).trans (hτ_le x)))] :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ|hσ.MeasurableSpace] :=
  by
  have : sigma_finite (μ.trim (hτ.measurable_space_le_of_le hτ_le)) :=
    sigma_finite_trim_mono _ (is_stopping_time.measurable_space_mono hσ hτ hσ_le_τ)
  have :
    μ[stopped_value f τ|hσ.measurable_space] =ᵐ[μ]
      μ[μ[f n|hτ.measurable_space]|hσ.measurable_space] :=
    condexp_congr_ae
      (h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hτ hτ_le hτ_countable_range)
  refine'
    (Filter.EventuallyEq.trans _
          (condexp_condexp_of_le _ (hτ.measurable_space_le_of_le hτ_le)).symm).trans
      this.symm
  ·
    exact
      h.stopped_value_ae_eq_condexp_of_le_const_of_countable_range hσ
        (fun x => (hσ_le_τ x).trans (hτ_le x)) hσ_countable_range
  · exact hσ.measurable_space_mono hτ hσ_le_τ
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le_of_countable_range MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le_of_countable_range
-/

#print MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le /-
/-- If `τ` and `σ` are two stopping times with `σ ≤ τ` and `τ` is bounded, then the value of a
martingale `f` at `σ` is the conditional expectation of its value at `τ` with respect to the
σ-algebra generated by `σ`. -/
theorem stoppedValue_ae_eq_condexp_of_le [Countable ι] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ x, τ x ≤ n)
    [SigmaFinite (μ.trim hσ.measurableSpace_le)] :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ|hσ.MeasurableSpace] :=
  h.stoppedValue_ae_eq_condexp_of_le_of_countable_range hτ hσ hσ_le_τ hτ_le (Set.to_countable _)
    (Set.to_countable _)
#align measure_theory.martingale.stopped_value_ae_eq_condexp_of_le MeasureTheory.Martingale.stoppedValue_ae_eq_condexp_of_le
-/

end FirstCountableTopology

section SubsetOfNat

/-! In the following results the index set verifies `[linear_order ι] [locally_finite_order ι]` and
`[order_bot ι]`, which means that it is order-isomorphic to a subset of `ℕ`. `ι` is equipped with
the discrete topology, which is also the order topology, and is a measurable space with the Borel
σ-algebra. -/


variable {ι : Type _} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] [TopologicalSpace ι]
  [DiscreteTopology ι] [MeasurableSpace ι] [BorelSpace ι] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {ℱ : Filtration ι m} {τ σ : Ω → ι} {f : ι → Ω → E} {i n : ι}

#print MeasureTheory.Martingale.condexp_stoppedValue_stopping_time_ae_eq_restrict_le /-
theorem condexp_stoppedValue_stopping_time_ae_eq_restrict_le (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) [SigmaFinite (μ.trim hσ.measurableSpace_le)]
    (hτ_le : ∀ x, τ x ≤ n) :
    μ[stoppedValue f τ|hσ.MeasurableSpace] =ᵐ[μ.restrict {x : Ω | τ x ≤ σ x}] stoppedValue f τ :=
  by
  rw [ae_eq_restrict_iff_indicator_ae_eq
      (hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ))]
  swap; infer_instance
  refine'
    (condexp_indicator (integrable_stopped_value ι hτ h.integrable hτ_le)
            (hτ.measurable_set_stopping_time_le hσ)).symm.trans
      _
  have h_int : integrable ({ω : Ω | τ ω ≤ σ ω}.indicator (stopped_value (fun n : ι => f n) τ)) μ :=
    by
    refine' (integrable_stopped_value ι hτ h.integrable hτ_le).indicator _
    exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ)
  have h_meas :
    ae_strongly_measurable' hσ.measurable_space
      ({ω : Ω | τ ω ≤ σ ω}.indicator (stopped_value (fun n : ι => f n) τ)) μ :=
    by
    refine' strongly_measurable.ae_strongly_measurable' _
    refine'
      strongly_measurable.strongly_measurable_of_measurable_space_le_on
        (hτ.measurable_set_le_stopping_time hσ) _ _ _
    · intro t ht
      rw [Set.inter_comm _ t] at ht ⊢
      rw [hτ.measurable_set_inter_le_iff, is_stopping_time.measurable_set_min_iff hτ hσ] at ht
      exact ht.2
    · refine' strongly_measurable.indicator _ (hτ.measurable_set_le_stopping_time hσ)
      refine' Measurable.stronglyMeasurable _
      exact measurable_stopped_value h.adapted.prog_measurable_of_discrete hτ
    · intro x hx
      simp only [hx, Set.indicator_of_not_mem, not_false_iff]
  exact condexp_of_ae_strongly_measurable' hσ.measurable_space_le h_meas h_int
#align measure_theory.martingale.condexp_stopped_value_stopping_time_ae_eq_restrict_le MeasureTheory.Martingale.condexp_stoppedValue_stopping_time_ae_eq_restrict_le
-/

#print MeasureTheory.Martingale.stoppedValue_min_ae_eq_condexp /-
/-- **Optional Sampling theorem**. If `τ` is a bounded stopping time and `σ` is another stopping
time, then the value of a martingale `f` at the stopping time `min τ σ` is almost everywhere equal
to the conditional expectation of `f` stopped at `τ` with respect to the σ-algebra generated
by `σ`. -/
theorem stoppedValue_min_ae_eq_condexp [SigmaFiniteFiltration μ ℱ] (h : Martingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) {n : ι} (hτ_le : ∀ x, τ x ≤ n)
    [h_sf_min : SigmaFinite (μ.trim (hτ.min hσ).measurableSpace_le)] :
    (stoppedValue f fun x => min (σ x) (τ x)) =ᵐ[μ] μ[stoppedValue f τ|hσ.MeasurableSpace] :=
  by
  refine'
    (h.stopped_value_ae_eq_condexp_of_le hτ (hσ.min hτ) (fun x => min_le_right _ _) hτ_le).trans _
  refine' ae_of_ae_restrict_of_ae_restrict_compl {x | σ x ≤ τ x} _ _
  · exact condexp_min_stopping_time_ae_eq_restrict_le hσ hτ
  · suffices
      μ[stopped_value f τ|(hσ.min hτ).MeasurableSpace] =ᵐ[μ.restrict {x | τ x ≤ σ x}]
        μ[stopped_value f τ|hσ.measurable_space]
      by
      rw [ae_restrict_iff' (hσ.measurable_space_le _ (hσ.measurable_set_le_stopping_time hτ).compl)]
      rw [Filter.EventuallyEq, ae_restrict_iff'] at this
      swap; · exact hτ.measurable_space_le _ (hτ.measurable_set_le_stopping_time hσ)
      filter_upwards [this] with x hx hx_mem
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx_mem
      exact hx hx_mem.le
    refine'
      Filter.EventuallyEq.trans _ ((condexp_min_stopping_time_ae_eq_restrict_le hτ hσ).trans _)
    · exact stopped_value f τ
    · rw [is_stopping_time.measurable_space_min, is_stopping_time.measurable_space_min, inf_comm]
    · have h1 : μ[stopped_value f τ|hτ.measurable_space] = stopped_value f τ :=
        by
        refine' condexp_of_strongly_measurable hτ.measurable_space_le _ _
        · refine' Measurable.stronglyMeasurable _
          exact measurable_stopped_value h.adapted.prog_measurable_of_discrete hτ
        · exact integrable_stopped_value ι hτ h.integrable hτ_le
      rw [h1]
      exact (condexp_stopped_value_stopping_time_ae_eq_restrict_le h hτ hσ hτ_le).symm
#align measure_theory.martingale.stopped_value_min_ae_eq_condexp MeasureTheory.Martingale.stoppedValue_min_ae_eq_condexp
-/

end SubsetOfNat

end Martingale

end MeasureTheory

