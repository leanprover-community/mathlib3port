/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.basic
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.MeasureTheory.Function.L2Space
import Mathbin.MeasureTheory.Function.AeEqOfIntegral

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m0`) and a measurable space
structure `m` with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexp_L1_clm` applied to `[f]`, the equivalence class of `f` in `L¹`.

## Main results

The conditional expectation and its properties

* `condexp (m : measurable_space α) (μ : measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `strongly_measurable_condexp` : `condexp` is `m`-strongly-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `Lp.ae_eq_of_forall_set_integral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[sigma_finite (μ.trim hm)]`.
* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

## Tags

conditional expectation, conditional expected value

-/


noncomputable section

open TopologicalSpace MeasureTheory.lp Filter ContinuousLinearMap

open Nnreal Ennreal Topology BigOperators MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `ae_strongly_measurable' m f μ` if it is `μ`-a.e. equal to
an `m`-strongly measurable function. This is similar to `ae_strongly_measurable`, but the
`measurable_space` structures used for the measurability statement and for the measure are
different. -/
def AeStronglyMeasurable' {α β} [TopologicalSpace β] (m : MeasurableSpace α)
    {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g : α → β, strongly_measurable[m] g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable' MeasureTheory.AeStronglyMeasurable'

namespace AeStronglyMeasurable'

variable {α β 𝕜 : Type _} {m m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  {f g : α → β}

theorem congr (hf : AeStronglyMeasurable' m f μ) (hfg : f =ᵐ[μ] g) : AeStronglyMeasurable' m g μ :=
  by
  obtain ⟨f', hf'_meas, hff'⟩ := hf
  exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩
#align measure_theory.ae_strongly_measurable'.congr MeasureTheory.AeStronglyMeasurable'.congr

theorem add [Add β] [HasContinuousAdd β] (hf : AeStronglyMeasurable' m f μ)
    (hg : AeStronglyMeasurable' m g μ) : AeStronglyMeasurable' m (f + g) μ :=
  by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  rcases hg with ⟨g', h_g'_meas, hgg'⟩
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩
#align measure_theory.ae_strongly_measurable'.add MeasureTheory.AeStronglyMeasurable'.add

theorem neg [AddGroup β] [TopologicalAddGroup β] {f : α → β} (hfm : AeStronglyMeasurable' m f μ) :
    AeStronglyMeasurable' m (-f) μ :=
  by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine' ⟨-f', hf'_meas.neg, hf_ae.mono fun x hx => _⟩
  simp_rw [Pi.neg_apply]
  rw [hx]
#align measure_theory.ae_strongly_measurable'.neg MeasureTheory.AeStronglyMeasurable'.neg

theorem sub [AddGroup β] [TopologicalAddGroup β] {f g : α → β} (hfm : AeStronglyMeasurable' m f μ)
    (hgm : AeStronglyMeasurable' m g μ) : AeStronglyMeasurable' m (f - g) μ :=
  by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩
  refine' ⟨f' - g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => _)⟩
  simp_rw [Pi.sub_apply]
  rw [hx1, hx2]
#align measure_theory.ae_strongly_measurable'.sub MeasureTheory.AeStronglyMeasurable'.sub

theorem constSmul [SMul 𝕜 β] [HasContinuousConstSMul 𝕜 β] (c : 𝕜)
    (hf : AeStronglyMeasurable' m f μ) : AeStronglyMeasurable' m (c • f) μ :=
  by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  refine' ⟨c • f', h_f'_meas.const_smul c, _⟩
  exact EventuallyEq.fun_comp hff' fun x => c • x
#align measure_theory.ae_strongly_measurable'.const_smul MeasureTheory.AeStronglyMeasurable'.constSmul

theorem constInner {𝕜 β} [IsROrC 𝕜] [InnerProductSpace 𝕜 β] {f : α → β}
    (hfm : AeStronglyMeasurable' m f μ) (c : β) :
    AeStronglyMeasurable' m (fun x => (inner c (f x) : 𝕜)) μ :=
  by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine'
    ⟨fun x => (inner c (f' x) : 𝕜), (@strongly_measurable_const _ _ m _ _).inner hf'_meas,
      hf_ae.mono fun x hx => _⟩
  dsimp only
  rw [hx]
#align measure_theory.ae_strongly_measurable'.const_inner MeasureTheory.AeStronglyMeasurable'.constInner

/-- An `m`-strongly measurable function almost everywhere equal to `f`. -/
def mk (f : α → β) (hfm : AeStronglyMeasurable' m f μ) : α → β :=
  hfm.choose
#align measure_theory.ae_strongly_measurable'.mk MeasureTheory.AeStronglyMeasurable'.mk

theorem stronglyMeasurable_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) :
    strongly_measurable[m] (hfm.mk f) :=
  hfm.choose_spec.1
#align measure_theory.ae_strongly_measurable'.strongly_measurable_mk MeasureTheory.AeStronglyMeasurable'.stronglyMeasurable_mk

theorem ae_eq_mk {f : α → β} (hfm : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.choose_spec.2
#align measure_theory.ae_strongly_measurable'.ae_eq_mk MeasureTheory.AeStronglyMeasurable'.ae_eq_mk

theorem continuousComp {γ} [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : Continuous g)
    (hf : AeStronglyMeasurable' m f μ) : AeStronglyMeasurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x),
    @Continuous.comp_stronglyMeasurable _ _ _ m _ _ _ _ hg hf.stronglyMeasurable_mk,
    hf.ae_eq_mk.mono fun x hx => by rw [Function.comp_apply, hx]⟩
#align measure_theory.ae_strongly_measurable'.continuous_comp MeasureTheory.AeStronglyMeasurable'.continuousComp

end AeStronglyMeasurable'

theorem aeStronglyMeasurable'OfAeStronglyMeasurable'Trim {α β} {m m0 m0' : MeasurableSpace α}
    [TopologicalSpace β] (hm0 : m0 ≤ m0') {μ : Measure α} {f : α → β}
    (hf : AeStronglyMeasurable' m f (μ.trim hm0)) : AeStronglyMeasurable' m f μ :=
  by
  obtain ⟨g, hg_meas, hfg⟩ := hf
  exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩
#align measure_theory.ae_strongly_measurable'_of_ae_strongly_measurable'_trim MeasureTheory.aeStronglyMeasurable'OfAeStronglyMeasurable'Trim

theorem StronglyMeasurable.aeStronglyMeasurable' {α β} {m m0 : MeasurableSpace α}
    [TopologicalSpace β] {μ : Measure α} {f : α → β} (hf : strongly_measurable[m] f) :
    AeStronglyMeasurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩
#align measure_theory.strongly_measurable.ae_strongly_measurable' MeasureTheory.StronglyMeasurable.aeStronglyMeasurable'

theorem ae_eq_trim_iff_of_aeStronglyMeasurable' {α β} [TopologicalSpace β] [MetrizableSpace β]
    {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AeStronglyMeasurable' m f μ) (hgm : AeStronglyMeasurable' m g μ) :
    hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.stronglyMeasurable_mk hgm.stronglyMeasurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h =>
      hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩
#align measure_theory.ae_eq_trim_iff_of_ae_strongly_measurable' MeasureTheory.ae_eq_trim_iff_of_aeStronglyMeasurable'

/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` almost
everywhere supported on `s` is `m`-ae-strongly-measurable, then `f` is also
`m₂`-ae-strongly-measurable. -/
theorem AeStronglyMeasurable'.aeStronglyMeasurable'OfMeasurableSpaceLeOn {α E}
    {m m₂ m0 : MeasurableSpace α} {μ : Measure α} [TopologicalSpace E] [Zero E] (hm : m ≤ m0)
    {s : Set α} {f : α → E} (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
    (hf : AeStronglyMeasurable' m f μ) (hf_zero : f =ᵐ[μ.restrict (sᶜ)] 0) :
    AeStronglyMeasurable' m₂ f μ := by
  let f' := hf.mk f
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f :=
    by
    refine'
      Filter.EventuallyEq.trans _ (indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero)
    filter_upwards [hf.ae_eq_mk]with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx]
    · simp [hxs]
  suffices : strongly_measurable[m₂] (s.indicator (hf.mk f))
  exact AeStronglyMeasurable'.congr this.ae_strongly_measurable' h_ind_eq
  have hf_ind : strongly_measurable[m] (s.indicator (hf.mk f)) :=
    hf.strongly_measurable_mk.indicator hs_m
  exact
    hf_ind.strongly_measurable_of_measurable_space_le_on hs_m hs fun x hxs =>
      Set.indicator_of_not_mem hxs _
#align measure_theory.ae_strongly_measurable'.ae_strongly_measurable'_of_measurable_space_le_on MeasureTheory.AeStronglyMeasurable'.aeStronglyMeasurable'OfMeasurableSpaceLeOn

variable {α β γ E E' F F' G G' H 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  [TopologicalSpace β]
  -- β for a generic topological space
  -- E for an inner product space
  [InnerProductSpace 𝕜 E]
  -- E' for an inner product space on which we compute integrals
  [InnerProductSpace 𝕜 E']
  [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']
  -- H for a normed group (hypotheses of mem_ℒp)
  [NormedAddCommGroup H]

section LpMeas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    AddSubgroup (lp F p μ)
    where
  carrier := { f : lp F p μ | AeStronglyMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, lp.coeFn_zero _ _ _⟩
  add_mem' f g hf hg := (hf.add hg).congr (lp.coeFn_add f g).symm
  neg_mem' f hf := AeStronglyMeasurable'.congr hf.neg (lp.coeFn_neg f).symm
#align measure_theory.Lp_meas_subgroup MeasureTheory.lpMeasSubgroup

variable (𝕜)

/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_strongly_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to
an `m`-strongly measurable function. -/
def lpMeas (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (lp F p μ)
    where
  carrier := { f : lp F p μ | AeStronglyMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @stronglyMeasurable_zero _ _ m _ _, lp.coeFn_zero _ _ _⟩
  add_mem' f g hf hg := (hf.add hg).congr (lp.coeFn_add f g).symm
  smul_mem' c f hf := (hf.constSmul c).congr (lp.coeFn_smul c f).symm
#align measure_theory.Lp_meas MeasureTheory.lpMeas

variable {F 𝕜}

variable ()

theorem mem_lpMeasSubgroup_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : lp F p μ} : f ∈ lpMeasSubgroup F m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← AddSubgroup.mem_carrier, lpMeasSubgroup, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_subgroup_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeasSubgroup_iff_aeStronglyMeasurable'

theorem mem_lpMeas_iff_aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    {f : lp F p μ} : f ∈ lpMeas F 𝕜 m p μ ↔ AeStronglyMeasurable' m f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, lpMeas, Set.mem_setOf_eq]
#align measure_theory.mem_Lp_meas_iff_ae_strongly_measurable' MeasureTheory.mem_lpMeas_iff_aeStronglyMeasurable'

theorem lpMeas.aeStronglyMeasurable' {m m0 : MeasurableSpace α} {μ : Measure α}
    (f : lpMeas F 𝕜 m p μ) : AeStronglyMeasurable' m f μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mp f.mem
#align measure_theory.Lp_meas.ae_strongly_measurable' MeasureTheory.lpMeas.aeStronglyMeasurable'

theorem mem_lpMeas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : lp F p μ) :
    f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_lpMeas_iff_aeStronglyMeasurable'.mpr (lp.aeStronglyMeasurable f)
#align measure_theory.mem_Lp_meas_self MeasureTheory.mem_lpMeas_self

theorem lpMeasSubgroup_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    ⇑f = (f : lp F p μ) :=
  coeFn_coeBase f
#align measure_theory.Lp_meas_subgroup_coe MeasureTheory.lpMeasSubgroup_coe

theorem lpMeas_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} :
    ⇑f = (f : lp F p μ) :=
  coeFn_coeBase f
#align measure_theory.Lp_meas_coe MeasureTheory.lpMeas_coe

theorem mem_lpMeas_indicatorConstLp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α}
    {s : Set α} (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {c : F} :
    indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun x : α => c, (@stronglyMeasurable_const _ _ m _ _).indicator hs,
    indicatorConstLp_coeFn⟩
#align measure_theory.mem_Lp_meas_indicator_const_Lp MeasureTheory.mem_lpMeas_indicatorConstLp

section CompleteSubspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometry_equiv` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/


variable {ι : Type _} {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem memℒpTrimOfMemLpMeasSubgroup (hm : m ≤ m0) (f : lp F p μ)
    (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp hf_meas).choose p (μ.trim hm) :=
  by
  have hf : AeStronglyMeasurable' m f μ :=
    mem_Lp_meas_subgroup_iff_ae_strongly_measurable'.mp hf_meas
  let g := hf.some
  obtain ⟨hg, hfg⟩ := hf.some_spec
  change Memℒp g p (μ.trim hm)
  refine' ⟨hg.ae_strongly_measurable, _⟩
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ :=
    by
    rw [snorm_trim hm hg]
    exact snorm_congr_ae hfg.symm
  rw [h_snorm_fg]
  exact lp.snorm_lt_top f
#align measure_theory.mem_ℒp_trim_of_mem_Lp_meas_subgroup MeasureTheory.memℒpTrimOfMemLpMeasSubgroup

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
theorem mem_lpMeasSubgroup_toLp_of_trim (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    (memℒpOfMemℒpTrim hm (lp.memℒp f)).toLp f ∈ lpMeasSubgroup F m p μ :=
  by
  let hf_mem_ℒp := memℒpOfMemℒpTrim hm (lp.memℒp f)
  rw [mem_lpMeasSubgroup_iff_aeStronglyMeasurable']
  refine' AeStronglyMeasurable'.congr _ (Memℒp.coeFn_toLp hf_mem_ℒp).symm
  refine' aeStronglyMeasurable'OfAeStronglyMeasurable'Trim hm _
  exact lp.aeStronglyMeasurable f
#align measure_theory.mem_Lp_meas_subgroup_to_Lp_of_trim MeasureTheory.mem_lpMeasSubgroup_toLp_of_trim

variable (F p μ)

/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose
    (memℒpTrimOfMemLpMeasSubgroup hm f f.mem)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim MeasureTheory.lpMeasSubgroupToLpTrim

variable (𝕜)

/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_lpMeas_iff_aeStronglyMeasurable'.mp f.mem).choose
    (memℒpTrimOfMemLpMeasSubgroup hm f f.mem)
#align measure_theory.Lp_meas_to_Lp_trim MeasureTheory.lpMeasToLpTrim

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeasSubgroup F m p μ :=
  ⟨(memℒpOfMemℒpTrim hm (lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas_subgroup MeasureTheory.lpTrimToLpMeasSubgroup

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def lpTrimToLpMeas (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(memℒpOfMemℒpTrim hm (lp.memℒp f)).toLp f, mem_lpMeasSubgroup_toLp_of_trim hm f⟩
#align measure_theory.Lp_trim_to_Lp_meas MeasureTheory.lpTrimToLpMeas

variable {F 𝕜 p μ}

theorem lpMeasSubgroupToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒpTrimOfMemLpMeasSubgroup hm (↑f) f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose_spec.2.symm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_ae_eq MeasureTheory.lpMeasSubgroupToLpTrim_ae_eq

theorem lpTrimToLpMeasSubgroup_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  Memℒp.coeFn_toLp _
#align measure_theory.Lp_trim_to_Lp_meas_subgroup_ae_eq MeasureTheory.lpTrimToLpMeasSubgroup_ae_eq

theorem lpMeasToLpTrim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp (memℒpTrimOfMemLpMeasSubgroup hm (↑f) f.mem))).trans
    (mem_lpMeasSubgroup_iff_aeStronglyMeasurable'.mp f.mem).choose_spec.2.symm
#align measure_theory.Lp_meas_to_Lp_trim_ae_eq MeasureTheory.lpMeasToLpTrim_ae_eq

theorem lpTrimToLpMeas_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  Memℒp.coeFn_toLp _
#align measure_theory.Lp_trim_to_Lp_meas_ae_eq MeasureTheory.lpTrimToLpMeas_ae_eq

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem lpMeasSubgroupToLpTrim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) :=
  by
  intro f
  ext1
  refine' ae_eq_trim_of_stronglyMeasurable hm (lp.stronglyMeasurable _) (lp.stronglyMeasurable _) _
  exact (lpMeasSubgroupToLpTrim_ae_eq hm _).trans (lpTrimToLpMeasSubgroup_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_right_inv MeasureTheory.lpMeasSubgroupToLpTrim_right_inv

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem lpMeasSubgroupToLpTrim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) :=
  by
  intro f
  ext1
  ext1
  rw [← lpMeasSubgroup_coe]
  exact (lpTrimToLpMeasSubgroup_ae_eq hm _).trans (lpMeasSubgroupToLpTrim_ae_eq hm _)
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_left_inv MeasureTheory.lpMeasSubgroupToLpTrim_left_inv

theorem lpMeasSubgroupToLpTrim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) =
      lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g :=
  by
  ext1
  refine' EventuallyEq.trans _ (lp.coeFn_add _ _).symm
  refine' ae_eq_trim_of_stronglyMeasurable hm (lp.stronglyMeasurable _) _ _
  · exact (lp.stronglyMeasurable _).add (lp.stronglyMeasurable _)
  refine' (lpMeasSubgroupToLpTrim_ae_eq hm _).trans _
  refine'
    EventuallyEq.trans _
      (EventuallyEq.add (lpMeasSubgroupToLpTrim_ae_eq hm f).symm
        (lpMeasSubgroupToLpTrim_ae_eq hm g).symm)
  refine' (lp.coeFn_add _ _).trans _
  simp_rw [lpMeasSubgroup_coe]
  exact eventually_of_forall fun x => by rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_add MeasureTheory.lpMeasSubgroupToLpTrim_add

theorem lpMeasSubgroupToLpTrim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f :=
  by
  ext1
  refine' EventuallyEq.trans _ (lp.coeFn_neg _).symm
  refine' ae_eq_trim_of_stronglyMeasurable hm (lp.stronglyMeasurable _) _ _
  · exact @strongly_measurable.neg _ _ _ m _ _ _ (lp.stronglyMeasurable _)
  refine' (lpMeasSubgroupToLpTrim_ae_eq hm _).trans _
  refine' EventuallyEq.trans _ (EventuallyEq.neg (lpMeasSubgroupToLpTrim_ae_eq hm f).symm)
  refine' (lp.coeFn_neg _).trans _
  simp_rw [lpMeasSubgroup_coe]
  exact eventually_of_forall fun x => by rfl
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_neg MeasureTheory.lpMeasSubgroupToLpTrim_neg

theorem lpMeasSubgroupToLpTrim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) =
      lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g :=
  by rw [sub_eq_add_neg, sub_eq_add_neg, lpMeasSubgroupToLpTrim_add, lpMeasSubgroupToLpTrim_neg]
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_sub MeasureTheory.lpMeasSubgroupToLpTrim_sub

theorem lpMeasToLpTrim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f :=
  by
  ext1
  refine' EventuallyEq.trans _ (lp.coeFn_smul _ _).symm
  refine' ae_eq_trim_of_stronglyMeasurable hm (lp.stronglyMeasurable _) _ _
  · exact (lp.stronglyMeasurable _).const_smul c
  refine' (lpMeasToLpTrim_ae_eq hm _).trans _
  refine' (lp.coeFn_smul _ _).trans _
  refine' (lpMeasToLpTrim_ae_eq hm f).mono fun x hx => _
  rw [Pi.smul_apply, Pi.smul_apply, hx]
  rfl
#align measure_theory.Lp_meas_to_Lp_trim_smul MeasureTheory.lpMeasToLpTrim_smul

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
theorem lpMeasSubgroupToLpTrim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0)
    (f : lpMeasSubgroup F m p μ) : ‖lpMeasSubgroupToLpTrim F p μ hm f‖ = ‖f‖ :=
  by
  rw [lp.norm_def, snorm_trim hm (lp.stronglyMeasurable _),
    snorm_congr_ae (lpMeasSubgroupToLpTrim_ae_eq hm _), lpMeasSubgroup_coe, ← lp.norm_def]
  congr
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_norm_map MeasureTheory.lpMeasSubgroupToLpTrim_norm_map

theorem isometry_lpMeasSubgroupToLpTrim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, ← lpMeasSubgroupToLpTrim_sub, lpMeasSubgroupToLpTrim_norm_map, dist_eq_norm]
#align measure_theory.isometry_Lp_meas_subgroup_to_Lp_trim MeasureTheory.isometry_lpMeasSubgroupToLpTrim

variable (F p μ)

/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
def lpMeasSubgroupToLpTrimIso [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    lpMeasSubgroup F m p μ ≃ᵢ lp F p (μ.trim hm)
    where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  isometry_toFun := isometry_lpMeasSubgroupToLpTrim hm
#align measure_theory.Lp_meas_subgroup_to_Lp_trim_iso MeasureTheory.lpMeasSubgroupToLpTrimIso

variable (𝕜)

/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
def lpMeasSubgroupToLpMeasIso [hp : Fact (1 ≤ p)] : lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  IsometryEquiv.refl (lpMeasSubgroup F m p μ)
#align measure_theory.Lp_meas_subgroup_to_Lp_meas_iso MeasureTheory.lpMeasSubgroupToLpMeasIso

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
def lpMeasToLpTrimLie [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] lp F p (μ.trim hm)
    where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := lpMeasSubgroupToLpTrim_left_inv hm
  right_inv := lpMeasSubgroupToLpTrim_right_inv hm
  map_add' := lpMeasSubgroupToLpTrim_add hm
  map_smul' := lpMeasToLpTrim_smul hm
  norm_map' := lpMeasSubgroupToLpTrim_norm_map hm
#align measure_theory.Lp_meas_to_Lp_trim_lie MeasureTheory.lpMeasToLpTrimLie

variable {F 𝕜 p μ}

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeasSubgroup F m p μ) :=
  by
  rw [(lpMeasSubgroupToLpTrimIso F p μ hm.elim).completeSpace_iff]
  infer_instance

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] :
    CompleteSpace (lpMeas F 𝕜 m p μ) :=
  by
  rw [(lpMeasSubgroupToLpMeasIso F 𝕜 p μ).symm.completeSpace_iff]
  infer_instance

theorem isComplete_aeStronglyMeasurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete { f : lp F p μ | AeStronglyMeasurable' m f μ } :=
  by
  rw [← completeSpace_coe_iff_isComplete]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (lpMeasSubgroup F m p μ)
  infer_instance
#align measure_theory.is_complete_ae_strongly_measurable' MeasureTheory.isComplete_aeStronglyMeasurable'

theorem isClosed_aeStronglyMeasurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed { f : lp F p μ | AeStronglyMeasurable' m f μ } :=
  IsComplete.isClosed (isComplete_aeStronglyMeasurable' hm)
#align measure_theory.is_closed_ae_strongly_measurable' MeasureTheory.isClosed_aeStronglyMeasurable'

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top,
    (lpMeasSubgroupToLpTrim_ae_eq hm f).symm⟩
#align measure_theory.Lp_meas.ae_fin_strongly_measurable' MeasureTheory.lpMeas.ae_fin_strongly_measurable'

/-- When applying the inverse of `Lp_meas_to_Lp_trim_lie` (which takes a function in the Lp space of
the sub-sigma algebra and returns its version in the larger Lp space) to an indicator of the
sub-sigma-algebra, we obtain an indicator in the Lp space of the larger sigma-algebra. -/
theorem lpMeasToLpTrimLie_symm_indicator [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] {hm : m ≤ m0}
    {s : Set α} {μ : Measure α} (hs : measurable_set[m] s) (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (indicatorConstLp p hs hμs c) : lp F p μ) =
      indicatorConstLp p (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).ne c :=
  by
  ext1
  rw [← lpMeas_coe]
  change
    lpTrimToLpMeas F ℝ p μ hm (indicatorConstLp p hs hμs c) =ᵐ[μ] (indicatorConstLp p _ _ c : α → F)
  refine' (lpTrimToLpMeas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim indicatorConstLp_coeFn).trans indicator_const_Lp_coe_fn.symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_indicator MeasureTheory.lpMeasToLpTrimLie_symm_indicator

theorem lpMeasToLpTrimLie_symm_toLp [one_le_p : Fact (1 ≤ p)] [NormedSpace ℝ F] (hm : m ≤ m0)
    (f : α → F) (hf : Memℒp f p (μ.trim hm)) :
    ((lpMeasToLpTrimLie F ℝ p μ hm).symm (hf.toLp f) : lp F p μ) =
      (memℒpOfMemℒpTrim hm hf).toLp f :=
  by
  ext1
  rw [← lpMeas_coe]
  refine' (lpTrimToLpMeas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim (Memℒp.coeFn_toLp hf)).trans (Memℒp.coeFn_toLp _).symm
#align measure_theory.Lp_meas_to_Lp_trim_lie_symm_to_Lp MeasureTheory.lpMeasToLpTrimLie_symm_toLp

end StronglyMeasurable

end LpMeas

section Induction

variable {m m0 : MeasurableSpace α} {μ : Measure α} [Fact (1 ≤ p)] [NormedSpace ℝ F]

/-- Auxiliary lemma for `Lp.induction_strongly_measurable`. -/
@[elab_as_elim]
theorem lp.inductionStronglyMeasurableAux (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : AeStronglyMeasurable' m f μ,
              ∀ hgm : AeStronglyMeasurable' m g μ,
                Disjoint (Function.support f) (Function.support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f }) :
    ∀ f : lp F p μ, AeStronglyMeasurable' m f μ → P f :=
  by
  intro f hf
  let f' := (⟨f, hf⟩ : lpMeas F ℝ m p μ)
  let g := lpMeasToLpTrimLie F ℝ p μ hm f'
  have hfg : f' = (lpMeasToLpTrimLie F ℝ p μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  change P ↑f'
  rw [hfg]
  refine'
    @Lp.induction α F m _ p (μ.trim hm) _ hp_ne_top
      (fun g => P ((lpMeasToLpTrimLie F ℝ p μ hm).symm g)) _ _ _ g
  · intro b t ht hμt
    rw [lp.simpleFunc.coe_indicatorConst, lpMeasToLpTrimLie_symm_indicator ht hμt.ne b]
    have hμt' : μ t < ∞ := (le_trim hm).trans_lt hμt
    specialize h_ind b ht hμt'
    rwa [lp.simpleFunc.coe_indicatorConst] at h_ind
  · intro f g hf hg h_disj hfP hgP
    rw [LinearIsometryEquiv.map_add]
    push_cast
    have h_eq :
      ∀ (f : α → F) (hf : Memℒp f p (μ.trim hm)),
        ((lpMeasToLpTrimLie F ℝ p μ hm).symm (Memℒp.toLp f hf) : lp F p μ) =
          (memℒpOfMemℒpTrim hm hf).toLp f :=
      lpMeasToLpTrimLie_symm_toLp hm
    rw [h_eq f hf] at hfP⊢
    rw [h_eq g hg] at hgP⊢
    exact
      h_add (memℒpOfMemℒpTrim hm hf) (memℒpOfMemℒpTrim hm hg)
        (aeStronglyMeasurable'OfAeStronglyMeasurable'Trim hm hf.ae_strongly_measurable)
        (aeStronglyMeasurable'OfAeStronglyMeasurable'Trim hm hg.ae_strongly_measurable) h_disj hfP
        hgP
  · change IsClosed ((lpMeasToLpTrimLie F ℝ p μ hm).symm ⁻¹' { g : lpMeas F ℝ m p μ | P ↑g })
    exact IsClosed.preimage (LinearIsometryEquiv.continuous _) h_closed
#align measure_theory.Lp.induction_strongly_measurable_aux MeasureTheory.lp.inductionStronglyMeasurableAux

/-- To prove something for an `Lp` function a.e. strongly measurable with respect to a
sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in `Lp` strongly measurable w.r.t. `m` for which the property holds is
  closed.
-/
@[elab_as_elim]
theorem lp.inductionStronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : lp F p μ → Prop)
    (h_ind :
      ∀ (c : F) {s : Set α} (hs : measurable_set[m] s) (hμs : μ s < ∞),
        P (lp.simpleFunc.indicatorConst p (hm s hs) hμs.ne c))
    (h_add :
      ∀ ⦃f g⦄,
        ∀ hf : Memℒp f p μ,
          ∀ hg : Memℒp g p μ,
            ∀ hfm : strongly_measurable[m] f,
              ∀ hgm : strongly_measurable[m] g,
                Disjoint (Function.support f) (Function.support g) →
                  P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f }) :
    ∀ f : lp F p μ, AeStronglyMeasurable' m f μ → P f :=
  by
  intro f hf
  suffices h_add_ae :
    ∀ ⦃f g⦄,
      ∀ hf : Memℒp f p μ,
        ∀ hg : Memℒp g p μ,
          ∀ hfm : AeStronglyMeasurable' m f μ,
            ∀ hgm : AeStronglyMeasurable' m g μ,
              Disjoint (Function.support f) (Function.support g) →
                P (hf.toLp f) → P (hg.toLp g) → P (hf.toLp f + hg.toLp g)
  exact lp.inductionStronglyMeasurableAux hm hp_ne_top P h_ind h_add_ae h_closed f hf
  intro f g hf hg hfm hgm h_disj hPf hPg
  let s_f : Set α := Function.support (hfm.mk f)
  have hs_f : measurable_set[m] s_f := hfm.strongly_measurable_mk.measurable_set_support
  have hs_f_eq : s_f =ᵐ[μ] Function.support f := hfm.ae_eq_mk.symm.support
  let s_g : Set α := Function.support (hgm.mk g)
  have hs_g : measurable_set[m] s_g := hgm.strongly_measurable_mk.measurable_set_support
  have hs_g_eq : s_g =ᵐ[μ] Function.support g := hgm.ae_eq_mk.symm.support
  have h_inter_empty : (s_f ∩ s_g : Set α) =ᵐ[μ] (∅ : Set α) :=
    by
    refine' (hs_f_eq.inter hs_g_eq).trans _
    suffices Function.support f ∩ Function.support g = ∅ by rw [this]
    exact set.disjoint_iff_inter_eq_empty.mp h_disj
  let f' := (s_f \ s_g).indicator (hfm.mk f)
  have hff' : f =ᵐ[μ] f' :=
    by
    have : s_f \ s_g =ᵐ[μ] s_f :=
      by
      rw [← Set.diff_inter_self_eq_diff, Set.inter_comm]
      refine' ((ae_eq_refl s_f).diff h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hfm.ae_eq_mk.symm
  have hf'_meas : strongly_measurable[m] f' := hfm.strongly_measurable_mk.indicator (hs_f.diff hs_g)
  have hf'_Lp : Memℒp f' p μ := hf.ae_eq hff'
  let g' := (s_g \ s_f).indicator (hgm.mk g)
  have hgg' : g =ᵐ[μ] g' :=
    by
    have : s_g \ s_f =ᵐ[μ] s_g := by
      rw [← Set.diff_inter_self_eq_diff]
      refine' ((ae_eq_refl s_g).diff h_inter_empty).trans _
      rw [Set.diff_empty]
    refine' ((indicator_ae_eq_of_ae_eq_set this).trans _).symm
    rw [Set.indicator_support]
    exact hgm.ae_eq_mk.symm
  have hg'_meas : strongly_measurable[m] g' := hgm.strongly_measurable_mk.indicator (hs_g.diff hs_f)
  have hg'_Lp : Memℒp g' p μ := hg.ae_eq hgg'
  have h_disj : Disjoint (Function.support f') (Function.support g') :=
    haveI : Disjoint (s_f \ s_g) (s_g \ s_f) := disjoint_sdiff_sdiff
    this.mono Set.support_indicator_subset Set.support_indicator_subset
  rw [← Memℒp.toLp_congr hf'_Lp hf hff'.symm] at hPf⊢
  rw [← Memℒp.toLp_congr hg'_Lp hg hgg'.symm] at hPg⊢
  exact h_add hf'_Lp hg'_Lp hf'_meas hg'_meas h_disj hPf hPg
#align measure_theory.Lp.induction_strongly_measurable MeasureTheory.lp.inductionStronglyMeasurable

/-- To prove something for an arbitrary `mem_ℒp` function a.e. strongly measurable with respect
to a sub-σ-algebra `m` in a normed space, it suffices to show that
* the property holds for (multiples of) characteristic functions which are measurable w.r.t. `m`;
* is closed under addition;
* the set of functions in the `Lᵖ` space strongly measurable w.r.t. `m` for which the property
  holds is closed.
* the property is closed under the almost-everywhere equal relation.
-/
@[elab_as_elim]
theorem Memℒp.inductionStronglyMeasurable (hm : m ≤ m0) (hp_ne_top : p ≠ ∞) (P : (α → F) → Prop)
    (h_ind : ∀ (c : F) ⦃s⦄, measurable_set[m] s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add :
      ∀ ⦃f g : α → F⦄,
        Disjoint (Function.support f) (Function.support g) →
          Memℒp f p μ →
            Memℒp g p μ →
              strongly_measurable[m] f → strongly_measurable[m] g → P f → P g → P (f + g))
    (h_closed : IsClosed { f : lpMeas F ℝ m p μ | P f })
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Memℒp f p μ → P f → P g) :
    ∀ ⦃f : α → F⦄ (hf : Memℒp f p μ) (hfm : AeStronglyMeasurable' m f μ), P f :=
  by
  intro f hf hfm
  let f_Lp := hf.to_Lp f
  have hfm_Lp : AeStronglyMeasurable' m f_Lp μ := hfm.congr hf.coe_fn_to_Lp.symm
  refine' h_ae hf.coe_fn_to_Lp (lp.memℒp _) _
  change P f_Lp
  refine' lp.inductionStronglyMeasurable hm hp_ne_top (fun f => P ⇑f) _ _ h_closed f_Lp hfm_Lp
  · intro c s hs hμs
    rw [lp.simpleFunc.coe_indicatorConst]
    refine' h_ae indicator_const_Lp_coe_fn.symm _ (h_ind c hs hμs)
    exact memℒpIndicatorConst p (hm s hs) c (Or.inr hμs.ne)
  · intro f g hf_mem hg_mem hfm hgm h_disj hfP hgP
    have hfP' : P f := h_ae hf_mem.coe_fn_to_Lp (lp.memℒp _) hfP
    have hgP' : P g := h_ae hg_mem.coe_fn_to_Lp (lp.memℒp _) hgP
    specialize h_add h_disj hf_mem hg_mem hfm hgm hfP' hgP'
    refine' h_ae _ (hf_mem.add hg_mem) h_add
    exact (hf_mem.coe_fn_to_Lp.symm.add hg_mem.coe_fn_to_Lp.symm).trans (lp.coeFn_add _ _).symm
#align measure_theory.mem_ℒp.induction_strongly_measurable MeasureTheory.Memℒp.inductionStronglyMeasurable

end Induction

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

theorem lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 :=
  by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine' hfg.trans _
  refine' ae_eq_zero_of_forall_set_integral_eq_of_finStronglyMeasurable_trim hm _ _ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
#align measure_theory.Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero MeasureTheory.lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero

include 𝕜

theorem lp.ae_eq_zero_of_forall_set_integral_eq_zero' (hm : m ≤ m0) (f : lp E' p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0)
    (hf_meas : AeStronglyMeasurable' m f μ) : f =ᵐ[μ] 0 :=
  by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp only [coeFn_coe_base', Subtype.coe_mk]
  refine' hf_f_meas.trans _
  refine' lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [IntegrableOn, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
#align measure_theory.Lp.ae_eq_zero_of_forall_set_integral_eq_zero' MeasureTheory.lp.ae_eq_zero_of_forall_set_integral_eq_zero'

/-- **Uniqueness of the conditional expectation** -/
theorem lp.ae_eq_of_forall_set_integral_eq' (hm : m ≤ m0) (f g : lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hf_meas : AeStronglyMeasurable' m f μ) (hg_meas : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g :=
  by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0
  · rw [← sub_ae_eq_zero]
    exact (lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 :=
    by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn (⇑(f - g)) s μ :=
    by
    intro s hs hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae (lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  have hfg_meas : AeStronglyMeasurable' m (⇑(f - g)) μ :=
    AeStronglyMeasurable'.congr (hf_meas.sub hg_meas) (lp.coeFn_sub f g).symm
  exact
    lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
      hfg_meas
#align measure_theory.Lp.ae_eq_of_forall_set_integral_eq' MeasureTheory.lp.ae_eq_of_forall_set_integral_eq'

omit 𝕜

theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hfm : AeStronglyMeasurable' m f μ) (hgm : AeStronglyMeasurable' m g μ) : f =ᵐ[μ] g :=
  by
  rw [← ae_eq_trim_iff_of_aeStronglyMeasurable' hm hfm hgm]
  have hf_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hfm.mk f) s (μ.trim hm) :=
    by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn, restrict_trim hm _ hs]
    refine' Integrable.trim hm _ hfm.strongly_measurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ (hgm.mk g) s (μ.trim hm) :=
    by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn, restrict_trim hm _ hs]
    refine' Integrable.trim hm _ hgm.strongly_measurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      measurable_set[m] s →
        μ.trim hm s < ∞ → (∫ x in s, hfm.mk f x ∂μ.trim hm) = ∫ x in s, hgm.mk g x ∂μ.trim hm :=
    by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.strongly_measurable_mk, ←
      integral_trim hm hgm.strongly_measurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_set_integral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq
#align measure_theory.ae_eq_of_forall_set_integral_eq_of_sigma_finite' MeasureTheory.ae_eq_of_forall_set_integral_eq_of_sigma_finite'

end UniquenessOfConditionalExpectation

section IntegralNormLe

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ)
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) : (∫ x in s, ‖g x‖ ∂μ) ≤ ∫ x in s, ‖f x‖ ∂μ :=
  by
  rw [integral_norm_eq_pos_sub_neg (hg.mono hm) hgi, integral_norm_eq_pos_sub_neg hf hfi]
  have h_meas_nonneg_g : measurable_set[m] { x | 0 ≤ g x } :=
    (@strongly_measurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet { x | 0 ≤ f x } :=
    strongly_measurable_const.measurable_set_le hf
  have h_meas_nonpos_g : measurable_set[m] { x | g x ≤ 0 } :=
    hg.measurable_set_le (@strongly_measurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet { x | f x ≤ 0 } :=
    hf.measurable_set_le stronglyMeasurable_const
  refine' sub_le_sub _ _
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@measurable_set.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi
#align measure_theory.integral_norm_le_of_forall_fin_meas_integral_eq MeasureTheory.integral_norm_le_of_forall_fin_meas_integral_eq

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ‖g x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : strongly_measurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ)
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) : (∫⁻ x in s, ‖g x‖₊ ∂μ) ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
  by
  rw [← ofReal_integral_norm_eq_lintegral_nnnorm hfi, ←
    ofReal_integral_norm_eq_lintegral_nnnorm hgi, Ennreal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · exact integral_nonneg fun x => norm_nonneg _
#align measure_theory.lintegral_nnnorm_le_of_forall_fin_meas_integral_eq MeasureTheory.lintegral_nnnorm_le_of_forall_fin_meas_integral_eq

end IntegralNormLe

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/


section CondexpL2

variable [CompleteSpace E] {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «expr⟪ , ⟫₂»
local notation "⟪" x ", " y "⟫₂" => @inner 𝕜 (α →₂[μ] E) _ x y

variable (𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  @orthogonalProjection 𝕜 (α →₂[μ] E) _ _ (lpMeas E 𝕜 m 2 μ)
    haveI : Fact (m ≤ m0) := ⟨hm⟩
    inferInstance
#align measure_theory.condexp_L2 MeasureTheory.condexpL2

variable {𝕜}

theorem aeStronglyMeasurable'CondexpL2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AeStronglyMeasurable' m (condexpL2 𝕜 hm f) μ :=
  lpMeas.aeStronglyMeasurable' _
#align measure_theory.ae_strongly_measurable'_condexp_L2 MeasureTheory.aeStronglyMeasurable'CondexpL2

theorem integrableOnCondexpL2OfMeasureNeTop (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (condexpL2 𝕜 hm f) s μ :=
  integrableOnLpOfMeasureNeTop (condexpL2 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim hμs
#align measure_theory.integrable_on_condexp_L2_of_measure_ne_top MeasureTheory.integrableOnCondexpL2OfMeasureNeTop

theorem integrableCondexpL2OfIsFiniteMeasure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (condexpL2 𝕜 hm f) μ :=
  integrableOn_univ.mp <| integrableOnCondexpL2OfMeasureNeTop hm (measure_ne_top _ _) f
#align measure_theory.integrable_condexp_L2_of_is_finite_measure MeasureTheory.integrableCondexpL2OfIsFiniteMeasure

theorem norm_condexpL2_le_one (hm : m ≤ m0) : ‖@condexpL2 α E 𝕜 _ _ _ _ _ μ hm‖ ≤ 1 :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  orthogonalProjection_norm_le _
#align measure_theory.norm_condexp_L2_le_one MeasureTheory.norm_condexpL2_le_one

theorem norm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condexpL2 𝕜 hm f‖ ≤ ‖f‖ :=
  ((@condexpL2 _ E 𝕜 _ _ _ _ _ μ hm).le_op_norm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexpL2_le_one hm))
#align measure_theory.norm_condexp_L2_le MeasureTheory.norm_condexpL2_le

theorem snorm_condexpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    snorm (condexpL2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
  by
  rw [lpMeas_coe, ← Ennreal.toReal_le_toReal (lp.snorm_ne_top _) (lp.snorm_ne_top _), ← lp.norm_def,
    ← lp.norm_def, Submodule.norm_coe]
  exact norm_condexpL2_le hm f
#align measure_theory.snorm_condexp_L2_le MeasureTheory.snorm_condexpL2_le

theorem norm_condexpL2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖(condexpL2 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ :=
  by
  rw [lp.norm_def, lp.norm_def, ← lpMeas_coe]
  refine' (Ennreal.toReal_le_toReal _ (lp.snorm_ne_top _)).mpr (snorm_condexpL2_le hm f)
  exact lp.snorm_ne_top _
#align measure_theory.norm_condexp_L2_coe_le MeasureTheory.norm_condexpL2_coe_le

theorem inner_condexpL2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexpL2 𝕜 hm g : α →₂[μ] E)⟫₂ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  inner_orthogonalProjection_left_eq_right _ f g
#align measure_theory.inner_condexp_L2_left_eq_right MeasureTheory.inner_condexpL2_left_eq_right

theorem condexpL2_indicator_of_measurable (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞)
    (c : E) :
    (condexpL2 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c :=
  by
  rw [condexpL2]
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c ∈ lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := by rfl
  have h_orth_mem := orthogonalProjection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]
#align measure_theory.condexp_L2_indicator_of_measurable MeasureTheory.condexpL2_indicator_of_measurable

theorem inner_condexpL2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AeStronglyMeasurable' m g μ) : ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
  by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condexpL2]
  simp only [mem_Lp_meas_iff_ae_strongly_measurable'.mpr hg, orthogonalProjection_inner_eq_zero]
#align measure_theory.inner_condexp_L2_eq_inner_fun MeasureTheory.inner_condexpL2_eq_inner_fun

section Real

variable {hm : m ≤ m0}

theorem integral_condexpL2_eq_of_fin_meas_real (f : lp 𝕜 2 μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  rw [← L2.inner_indicatorConstLp_one (hm s hs) hμs]
  have h_eq_inner :
    (∫ x in s, condexpL2 𝕜 hm f x ∂μ) =
      inner (indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜)) (condexpL2 𝕜 hm f) :=
    by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
    congr
  rw [h_eq_inner, ← inner_condexpL2_left_eq_right, condexpL2_indicator_of_measurable hm hs hμs]
#align measure_theory.integral_condexp_L2_eq_of_fin_meas_real MeasureTheory.integral_condexpL2_eq_of_fin_meas_real

theorem lintegral_nnnorm_condexpL2_le (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (f : lp ℝ 2 μ) :
    (∫⁻ x in s, ‖condexpL2 ℝ hm f x‖₊ ∂μ) ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ :=
  by
  let h_meas := lpMeas.aeStronglyMeasurable' (condexpL2 ℝ hm f)
  let g := h_meas.some
  have hg_meas : strongly_measurable[m] g := h_meas.some_spec.1
  have hg_eq : g =ᵐ[μ] condexpL2 ℝ hm f := h_meas.some_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexpL2 ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq :
    (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x => (‖condexpL2 ℝ hm f x‖₊ : ℝ≥0∞) :=
    by
    refine' hg_eq_restrict.mono fun x hx => _
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine'
    lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (lp.stronglyMeasurable f) _ _ _ _ hs hμs
  · exact integrableOnLpOfMeasureNeTop f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOnCondexpL2OfMeasureNeTop hm hμs f
  · intro t ht hμt
    rw [← integral_condexpL2_eq_of_fin_meas_real f ht hμt.ne]
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
#align measure_theory.lintegral_nnnorm_condexp_L2_le MeasureTheory.lintegral_nnnorm_condexpL2_le

theorem condexpL2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {f : lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condexpL2 ℝ hm f =ᵐ[μ.restrict s] 0 :=
  by
  suffices h_nnnorm_eq_zero : (∫⁻ x in s, ‖condexpL2 ℝ hm f x‖₊ ∂μ) = 0
  · rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    refine' h_nnnorm_eq_zero.mono fun x hx => _
    dsimp only at hx
    rw [Pi.zero_apply] at hx⊢
    · rwa [Ennreal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
      rw [lpMeas_coe]
      exact (lp.stronglyMeasurable _).measurable
  refine' le_antisymm _ (zero_le _)
  refine' (lintegral_nnnorm_condexpL2_le hs hμs f).trans (le_of_eq _)
  rw [lintegral_eq_zero_iff]
  · refine' hf.mono fun x hx => _
    dsimp only
    rw [hx]
    simp
  · exact (lp.stronglyMeasurable _).ennnorm
#align measure_theory.condexp_L2_ae_eq_zero_of_ae_eq_zero MeasureTheory.condexpL2_ae_eq_zero_of_ae_eq_zero

theorem lintegral_nnnorm_condexpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ) ≤ μ (s ∩ t) :=
  by
  refine' (lintegral_nnnorm_condexpL2_le ht hμt _).trans (le_of_eq _)
  have h_eq :
    (∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ) =
      ∫⁻ x in t, s.indicator (fun x => (1 : ℝ≥0∞)) x ∂μ :=
    by
    refine' lintegral_congr_ae (ae_restrict_of_ae _)
    refine' (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => _
    rw [hx]
    classical
      simp_rw [Set.indicator_apply]
      split_ifs <;> simp
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le_real MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le_real

end Real

/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
theorem condexpL2_constInner (hm : m ≤ m0) (f : lp E 2 μ) (c : E) :
    condexpL2 𝕜 hm (((lp.memℒp f).constInner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ] fun a =>
      ⟪c, condexpL2 𝕜 hm f a⟫ :=
  by
  rw [lpMeas_coe]
  have h_mem_Lp : Memℒp (fun a => ⟪c, condexpL2 𝕜 hm f a⟫) 2 μ :=
    by
    refine' Memℒp.constInner _ _
    rw [lpMeas_coe]
    exact lp.memℒp _
  have h_eq : h_mem_Lp.to_Lp _ =ᵐ[μ] fun a => ⟪c, condexpL2 𝕜 hm f a⟫ := h_mem_Lp.coe_fn_to_Lp
  refine' EventuallyEq.trans _ h_eq
  refine'
    lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrableOnCondexpL2OfMeasureNeTop hm hμs.ne _) _ _ _ _
  · intro s hs hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOnCondexpL2OfMeasureNeTop hm hμs.ne _).constInner _
  · intro s hs hμs
    rw [← lpMeas_coe, integral_condexpL2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), lpMeas_coe, ←
      L2.inner_indicatorConstLp_eq_set_integral_inner 𝕜 (↑(condexpL2 𝕜 hm f)) (hm s hs) c hμs.ne, ←
      inner_condexpL2_left_eq_right, condexpL2_indicator_of_measurable,
      L2.inner_indicatorConstLp_eq_set_integral_inner 𝕜 f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs)
        ((Memℒp.coeFn_toLp ((lp.memℒp f).constInner c)).mono fun x hx hxs => hx)]
  · rw [← lpMeas_coe]
    exact lpMeas.aeStronglyMeasurable' _
  · refine' AeStronglyMeasurable'.congr _ h_eq.symm
    exact (lpMeas.aeStronglyMeasurable' _).constInner _
#align measure_theory.condexp_L2_const_inner MeasureTheory.condexpL2_constInner

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexpL2_eq (hm : m ≤ m0) (f : lp E' 2 μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  rw [← sub_eq_zero, lpMeas_coe, ←
    integral_sub' (integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs)
      (integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs)]
  refine' integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _
  · rw [integrable_congr (ae_restrict_of_ae (lp.coeFn_sub (↑(condexpL2 𝕜 hm f)) f).symm)]
    exact integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub ((integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs).constInner c)
      ((integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs).constInner c)]
  have h_ae_eq_f := Memℒp.coeFn_toLp ((lp.memℒp f).constInner c)
  rw [← lpMeas_coe, sub_eq_zero, ←
    set_integral_congr_ae (hm s hs) ((condexpL2_constInner hm f c).mono fun x hx _ => hx), ←
    set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condexpL2_eq_of_fin_meas_real _ hs hμs
#align measure_theory.integral_condexp_L2_eq MeasureTheory.integral_condexpL2_eq

variable {E'' 𝕜' : Type _} [IsROrC 𝕜'] [InnerProductSpace 𝕜' E''] [CompleteSpace E'']
  [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condexpL2_comp_continuousLinearMap (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condexpL2 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ] T.compLp (condexpL2 𝕜 hm f : α →₂[μ] E') :=
  by
  refine'
    lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrableOnCondexpL2OfMeasureNeTop hm hμs.ne _)
      (fun s hs hμs => integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs.Ne) _ _ _
  · intro s hs hμs
    rw [T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrableOnLpOfMeasureNeTop _ fact_one_le_two_ennreal.elim hμs.ne), ←
      lpMeas_coe, ← lpMeas_coe, integral_condexpL2_eq hm f hs hμs.ne,
      integral_condexpL2_eq hm (T.comp_Lp f) hs hμs.ne, T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrableOnLpOfMeasureNeTop f fact_one_le_two_ennreal.elim hμs.ne)]
  · rw [← lpMeas_coe]
    exact lpMeas.aeStronglyMeasurable' _
  · have h_coe := T.coe_fn_comp_Lp (condexpL2 𝕜 hm f : α →₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine' AeStronglyMeasurable'.congr _ h_coe.symm
    exact (lpMeas.aeStronglyMeasurable' (condexpL2 𝕜 hm f)).continuousComp T.continuous
#align measure_theory.condexp_L2_comp_continuous_linear_map MeasureTheory.condexpL2_comp_continuousLinearMap

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condexpL2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') :
    condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condexpL2_comp_continuousLinearMap ℝ 𝕜 hm (toSpanSingleton ℝ x)
      (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← lpMeas_coe] at h_comp
  refine' h_comp.trans _
  exact (toSpanSingleton ℝ x).coeFn_compLp _
#align measure_theory.condexp_L2_indicator_ae_eq_smul MeasureTheory.condexpL2_indicator_ae_eq_smul

theorem condexpL2_indicator_eq_toSpanSingleton_comp (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') :
    (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
      (toSpanSingleton ℝ x).compLp (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) :=
  by
  ext1
  rw [← lpMeas_coe]
  refine' (condexpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _
  have h_comp :=
    (toSpanSingleton ℝ x).coeFn_compLp
      (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) : α →₂[μ] ℝ)
  rw [← EventuallyEq] at h_comp
  refine' EventuallyEq.trans _ h_comp.symm
  refine' eventually_of_forall fun y => _
  rfl
#align measure_theory.condexp_L2_indicator_eq_to_span_singleton_comp MeasureTheory.condexpL2_indicator_eq_toSpanSingleton_comp

variable {𝕜}

theorem set_lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ) ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    (∫⁻ a in t, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ) =
        ∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha hat => by rw [ha])
    _ = (∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ) * ‖x‖₊ :=
      by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, lpMeas_coe]
      exact (lp.stronglyMeasurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      Ennreal.mul_le_mul (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) le_rfl
    
#align measure_theory.set_lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.set_lintegral_nnnorm_condexpL2_indicator_le

theorem lintegral_nnnorm_condexpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    (∫⁻ a, ‖condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a‖₊ ∂μ) ≤ μ s * ‖x‖₊ :=
  by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · rw [lpMeas_coe]
    exact (lp.aeStronglyMeasurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexpL2_indicator_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)
#align measure_theory.lintegral_nnnorm_condexp_L2_indicator_le MeasureTheory.lintegral_nnnorm_condexpL2_indicator_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrableCondexpL2Indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') : Integrable (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ :=
  by
  refine'
    integrableOfForallFinMeasLe' hm (μ s * ‖x‖₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · rw [lpMeas_coe]
    exact lp.aeStronglyMeasurable _
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexpL2_indicator_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
#align measure_theory.integrable_condexp_L2_indicator MeasureTheory.integrableCondexpL2Indicator

end CondexpL2Indicator

section CondexpIndSmul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
def condexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) : lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))
#align measure_theory.condexp_ind_smul MeasureTheory.condexpIndSmul

theorem aeStronglyMeasurable'CondexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : AeStronglyMeasurable' m (condexpIndSmul hm hs hμs x) μ :=
  by
  have h : AeStronglyMeasurable' m (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) μ :=
    aeStronglyMeasurable'CondexpL2 _ _
  rw [condexpIndSmul]
  suffices
    AeStronglyMeasurable' m
      (toSpanSingleton ℝ x ∘ condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) μ
    by
    refine' AeStronglyMeasurable'.congr this _
    refine' EventuallyEq.trans _ (coeFn_compLpL _ _).symm
    rw [lpMeas_coe]
  exact AeStronglyMeasurable'.continuousComp (toSpanSingleton ℝ x).continuous h
#align measure_theory.ae_strongly_measurable'_condexp_ind_smul MeasureTheory.aeStronglyMeasurable'CondexpIndSmul

theorem condexpIndSmul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndSmul hm hs hμs (x + y) = condexpIndSmul hm hs hμs x + condexpIndSmul hm hs hμs y :=
  by
  simp_rw [condexpIndSmul]
  rw [toSpanSingleton_add, add_compLpL, add_apply]
#align measure_theory.condexp_ind_smul_add MeasureTheory.condexpIndSmul_add

theorem condexpIndSmul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x :=
  by
  simp_rw [condexpIndSmul]
  rw [toSpanSingleton_smul, smul_compLpL, smul_apply]
#align measure_theory.condexp_ind_smul_smul MeasureTheory.condexpIndSmul_smul

theorem condexpIndSmul_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  rw [condexpIndSmul, condexpIndSmul, toSpanSingleton_smul',
    (toSpanSingleton ℝ x).smul_compLpL_apply c
      ↑(condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))]
#align measure_theory.condexp_ind_smul_smul' MeasureTheory.condexpIndSmul_smul'

theorem condexpIndSmul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndSmul hm hs hμs x =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  (toSpanSingleton ℝ x).coeFn_compLpL _
#align measure_theory.condexp_ind_smul_ae_eq_smul MeasureTheory.condexpIndSmul_ae_eq_smul

theorem set_lintegral_nnnorm_condexpIndSmul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ) ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    (∫⁻ a in t, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ) =
        ∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x‖₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexpIndSmul_ae_eq_smul hm hs hμs x).mono fun a ha hat => by rw [ha])
    _ = (∫⁻ a in t, ‖condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a‖₊ ∂μ) * ‖x‖₊ :=
      by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, lpMeas_coe]
      exact (lp.stronglyMeasurable _).ennnorm
    _ ≤ μ (s ∩ t) * ‖x‖₊ :=
      Ennreal.mul_le_mul (lintegral_nnnorm_condexpL2_indicator_le_real hs hμs ht hμt) le_rfl
    
#align measure_theory.set_lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.set_lintegral_nnnorm_condexpIndSmul_le

theorem lintegral_nnnorm_condexpIndSmul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : (∫⁻ a, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ) ≤ μ s * ‖x‖₊ :=
  by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ‖x‖₊) _ fun t ht hμt => _
  · exact (lp.aeStronglyMeasurable _).ennnorm
  refine' (set_lintegral_nnnorm_condexpIndSmul_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)
#align measure_theory.lintegral_nnnorm_condexp_ind_smul_le MeasureTheory.lintegral_nnnorm_condexpIndSmul_le

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrableCondexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condexpIndSmul hm hs hμs x) μ :=
  by
  refine'
    integrableOfForallFinMeasLe' hm (μ s * ‖x‖₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · exact lp.aeStronglyMeasurable _
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexpIndSmul_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
#align measure_theory.integrable_condexp_ind_smul MeasureTheory.integrableCondexpIndSmul

theorem condexpIndSmul_empty {x : G} :
    condexpIndSmul hm MeasurableSet.empty ((@measure_empty _ _ μ).le.trans_lt Ennreal.coe_lt_top).ne
        x =
      0 :=
  by
  rw [condexpIndSmul, indicator_const_empty]
  simp only [coeFn_coeBase, Submodule.coe_zero, ContinuousLinearMap.map_zero]
#align measure_theory.condexp_ind_smul_empty MeasureTheory.condexpIndSmul_empty

theorem set_integral_condexpL2_indicator (hs : measurable_set[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    (∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ) = (μ (t ∩ s)).toReal :=
  calc
    (∫ x in s, (condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ))) x ∂μ) =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condexpL2_eq α _ ℝ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = (μ (t ∩ s)).toReal • 1 := set_integral_indicatorConstLp (hm s hs) ht hμt (1 : ℝ)
    _ = (μ (t ∩ s)).toReal := by rw [smul_eq_mul, mul_one]
    
#align measure_theory.set_integral_condexp_L2_indicator MeasureTheory.set_integral_condexpL2_indicator

theorem set_integral_condexpIndSmul (hs : measurable_set[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
    (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) =
        ∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a • x ∂μ :=
      set_integral_congr_ae (hm s hs)
        ((condexpIndSmul_ae_eq_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a ∂μ) • x :=
      integral_smul_const _ x
    _ = (μ (t ∩ s)).toReal • x := by rw [set_integral_condexpL2_indicator hs ht hμs hμt]
    
#align measure_theory.set_integral_condexp_ind_smul MeasureTheory.set_integral_condexpIndSmul

theorem condexpL2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    [SigmaFinite (μ.trim hm)] : 0 ≤ᵐ[μ] condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) :=
  by
  have h : AeStronglyMeasurable' m (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) μ :=
    aeStronglyMeasurable'CondexpL2 _ _
  refine' EventuallyLe.trans_eq _ h.ae_eq_mk.symm
  refine' @ae_le_of_ae_le_trim _ _ _ _ _ _ hm _ _ _
  refine' ae_nonneg_of_forall_set_integral_nonneg_of_sigmaFinite _ _
  · intro t ht hμt
    refine' @integrable.integrable_on _ _ m _ _ _ _ _
    refine' Integrable.trim hm _ _
    · rw [integrable_congr h.ae_eq_mk.symm]
      exact integrableCondexpL2Indicator hm hs hμs _
    · exact h.strongly_measurable_mk
  · intro t ht hμt
    rw [← set_integral_trim hm h.strongly_measurable_mk ht]
    have h_ae : ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) x :=
      by
      filter_upwards [h.ae_eq_mk]with x hx
      exact fun _ => hx.symm
    rw [set_integral_congr_ae (hm t ht) h_ae,
      set_integral_condexpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact Ennreal.toReal_nonneg
#align measure_theory.condexp_L2_indicator_nonneg MeasureTheory.condexpL2_indicator_nonneg

theorem condexpIndSmul_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    0 ≤ᵐ[μ] condexpIndSmul hm hs hμs x :=
  by
  refine' EventuallyLe.trans_eq _ (condexpIndSmul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condexpL2_indicator_nonneg hm hs hμs]with a ha
  exact smul_nonneg ha hx
#align measure_theory.condexp_ind_smul_nonneg MeasureTheory.condexpIndSmul_nonneg

end CondexpIndSmul

end CondexpL2

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrableCondexpIndSmul hm hs hμs x).toL1 _
#align measure_theory.condexp_ind_L1_fin MeasureTheory.condexpIndL1Fin

theorem condexpIndL1Fin_ae_eq_condexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSmul hm hs hμs x :=
  (integrableCondexpIndSmul hm hs hμs x).coeFn_toL1
#align measure_theory.condexp_ind_L1_fin_ae_eq_condexp_ind_smul MeasureTheory.condexpIndL1Fin_ae_eq_condexpIndSmul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) = condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y :=
  by
  ext1
  refine' (Memℒp.coeFn_toLp _).trans _
  refine' EventuallyEq.trans _ (lp.coeFn_add _ _).symm
  refine'
    EventuallyEq.trans _ (EventuallyEq.add (Memℒp.coeFn_toLp _).symm (Memℒp.coeFn_toLp _).symm)
  rw [condexpIndSmul_add]
  refine' (lp.coeFn_add _ _).trans (eventually_of_forall fun a => _)
  rfl
#align measure_theory.condexp_ind_L1_fin_add MeasureTheory.condexpIndL1Fin_add

theorem condexpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x :=
  by
  ext1
  refine' (Memℒp.coeFn_toLp _).trans _
  refine' EventuallyEq.trans _ (lp.coeFn_smul _ _).symm
  rw [condexpIndSmul_smul hs hμs c x]
  refine' (lp.coeFn_smul _ _).trans _
  refine' (condexpIndL1Fin_ae_eq_condexpIndSmul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]
#align measure_theory.condexp_ind_L1_fin_smul MeasureTheory.condexpIndL1Fin_smul

theorem condexpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x :=
  by
  ext1
  refine' (Memℒp.coeFn_toLp _).trans _
  refine' EventuallyEq.trans _ (lp.coeFn_smul _ _).symm
  rw [condexpIndSmul_smul' hs hμs c x]
  refine' (lp.coeFn_smul _ _).trans _
  refine' (condexpIndL1Fin_ae_eq_condexpIndSmul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]
#align measure_theory.condexp_ind_L1_fin_smul' MeasureTheory.condexpIndL1Fin_smul'

theorem norm_condexpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condexpIndL1Fin hm hs hμs x‖ ≤ (μ s).toReal * ‖x‖ :=
  by
  have : 0 ≤ ∫ a : α, ‖condexpIndL1Fin hm hs hμs x a‖ ∂μ := integral_nonneg fun a => norm_nonneg _
  rw [L1.norm_eq_integral_norm, ← Ennreal.toReal_ofReal (norm_nonneg x), ← Ennreal.toReal_mul, ←
    Ennreal.toReal_ofReal this,
    Ennreal.toReal_le_toReal Ennreal.ofReal_ne_top (Ennreal.mul_ne_top hμs Ennreal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_nnnorm]
  swap
  · rw [← memℒp_one_iff_integrable]
    exact lp.memℒp _
  have h_eq :
    (∫⁻ a, ‖condexpIndL1Fin hm hs hμs x a‖₊ ∂μ) = ∫⁻ a, ‖condexpIndSmul hm hs hμs x a‖₊ ∂μ :=
    by
    refine' lintegral_congr_ae _
    refine' (condexpIndL1Fin_ae_eq_condexpIndSmul hm hs hμs x).mono fun z hz => _
    dsimp only
    rw [hz]
  rw [h_eq, ofReal_norm_eq_coe_nnnorm]
  exact lintegral_nnnorm_condexpIndSmul_le hm hs hμs x
#align measure_theory.norm_condexp_ind_L1_fin_le MeasureTheory.norm_condexpIndL1Fin_le

theorem condexpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1Fin hm (hs.union ht)
        ((measure_union_le s t).trans_lt
            (lt_top_iff_ne_top.mpr (Ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
        x =
      condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x :=
  by
  ext1
  have hμst :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  refine' (condexpIndL1Fin_ae_eq_condexpIndSmul hm (hs.union ht) hμst x).trans _
  refine' EventuallyEq.trans _ (lp.coeFn_add _ _).symm
  have hs_eq := condexpIndL1Fin_ae_eq_condexpIndSmul hm hs hμs x
  have ht_eq := condexpIndL1Fin_ae_eq_condexpIndSmul hm ht hμt x
  refine' EventuallyEq.trans _ (EventuallyEq.add hs_eq.symm ht_eq.symm)
  rw [condexpIndSmul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condexpL2 ℝ hm).map_add]
  push_cast
  rw [((toSpanSingleton ℝ x).compLpL 2 μ).map_add]
  refine' (lp.coeFn_add _ _).trans _
  refine' eventually_of_forall fun y => _
  rfl
#align measure_theory.condexp_ind_L1_fin_disjoint_union MeasureTheory.condexpIndL1Fin_disjoint_union

end CondexpIndL1Fin

open Classical

section CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α)
    [SigmaFinite (μ.trim hm)] (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0
#align measure_theory.condexp_ind_L1 MeasureTheory.condexpIndL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexpIndL1_of_measurableSet_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [condexpIndL1, And.intro hs hμs, dif_pos, Ne.def, not_false_iff, and_self_iff]
#align measure_theory.condexp_ind_L1_of_measurable_set_of_measure_ne_top MeasureTheory.condexpIndL1_of_measurableSet_of_measure_ne_top

theorem condexpIndL1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hμs, eq_self_iff_true, not_true, Ne.def, dif_neg, not_false_iff,
    and_false_iff]
#align measure_theory.condexp_ind_L1_of_measure_eq_top MeasureTheory.condexpIndL1_of_measure_eq_top

theorem condexpIndL1_of_not_measurableSet (hs : ¬MeasurableSet s) (x : G) :
    condexpIndL1 hm μ s x = 0 := by
  simp only [condexpIndL1, hs, dif_neg, not_false_iff, false_and_iff]
#align measure_theory.condexp_ind_L1_of_not_measurable_set MeasureTheory.condexpIndL1_of_not_measurableSet

theorem condexpIndL1_add (x y : G) :
    condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y :=
  by
  by_cases hs : MeasurableSet s
  swap;
  · simp_rw [condexpIndL1_of_not_measurableSet hs]
    rw [zero_add]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]
    rw [zero_add]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_add hs hμs x y
#align measure_theory.condexp_ind_L1_add MeasureTheory.condexpIndL1_add

theorem condexpIndL1_smul (c : ℝ) (x : G) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x :=
  by
  by_cases hs : MeasurableSet s
  swap;
  · simp_rw [condexpIndL1_of_not_measurableSet hs]
    rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]
    rw [smul_zero]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_smul hs hμs c x
#align measure_theory.condexp_ind_L1_smul MeasureTheory.condexpIndL1_smul

theorem condexpIndL1_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x :=
  by
  by_cases hs : MeasurableSet s
  swap;
  · simp_rw [condexpIndL1_of_not_measurableSet hs]
    rw [smul_zero]
  by_cases hμs : μ s = ∞
  · simp_rw [condexpIndL1_of_measure_eq_top hμs]
    rw [smul_zero]
  · simp_rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs]
    exact condexpIndL1Fin_smul' hs hμs c x
#align measure_theory.condexp_ind_L1_smul' MeasureTheory.condexpIndL1_smul'

theorem norm_condexpIndL1_le (x : G) : ‖condexpIndL1 hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  by
  by_cases hs : MeasurableSet s
  swap;
  · simp_rw [condexpIndL1_of_not_measurableSet hs]
    rw [lp.norm_zero]
    exact mul_nonneg Ennreal.toReal_nonneg (norm_nonneg _)
  by_cases hμs : μ s = ∞
  · rw [condexpIndL1_of_measure_eq_top hμs x, lp.norm_zero]
    exact mul_nonneg Ennreal.toReal_nonneg (norm_nonneg _)
  · rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x]
    exact norm_condexpIndL1Fin_le hs hμs x
#align measure_theory.norm_condexp_ind_L1_le MeasureTheory.norm_condexpIndL1_le

theorem continuous_condexpIndL1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexpIndL1_add condexpIndL1_smul norm_condexpIndL1_le
#align measure_theory.continuous_condexp_ind_L1 MeasureTheory.continuous_condexpIndL1

theorem condexpIndL1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x :=
  by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne
  rw [condexpIndL1_of_measurableSet_of_measure_ne_top hs hμs x,
    condexpIndL1_of_measurableSet_of_measure_ne_top ht hμt x,
    condexpIndL1_of_measurableSet_of_measure_ne_top (hs.union ht) hμst x]
  exact condexpIndL1Fin_disjoint_union hs ht hμs hμt hst x
#align measure_theory.condexp_ind_L1_disjoint_union MeasureTheory.condexpIndL1_disjoint_union

end CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)]
    (s : Set α) : G →L[ℝ] α →₁[μ] G
    where
  toFun := condexpIndL1 hm μ s
  map_add' := condexpIndL1_add
  map_smul' := condexpIndL1_smul
  cont := continuous_condexpIndL1
#align measure_theory.condexp_ind MeasureTheory.condexpInd

theorem condexpInd_ae_eq_condexpIndSmul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpInd hm μ s x =ᵐ[μ] condexpIndSmul hm hs hμs x :=
  by
  refine' EventuallyEq.trans _ (condexpIndL1Fin_ae_eq_condexpIndSmul hm hs hμs x)
  simp [condexpInd, condexpIndL1, hs, hμs]
#align measure_theory.condexp_ind_ae_eq_condexp_ind_smul MeasureTheory.condexpInd_ae_eq_condexpIndSmul

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aeStronglyMeasurable'CondexpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AeStronglyMeasurable' m (condexpInd hm μ s x) μ :=
  AeStronglyMeasurable'.congr (aeStronglyMeasurable'CondexpIndSmul hm hs hμs x)
    (condexpInd_ae_eq_condexpIndSmul hm hs hμs x).symm
#align measure_theory.ae_strongly_measurable'_condexp_ind MeasureTheory.aeStronglyMeasurable'CondexpInd

@[simp]
theorem condexpInd_empty : condexpInd hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) :=
  by
  ext1
  ext1
  refine' (condexpInd_ae_eq_condexpIndSmul hm MeasurableSet.empty (by simp) x).trans _
  rw [condexpIndSmul_empty]
  refine' (lp.coeFn_zero G 2 μ).trans _
  refine' EventuallyEq.trans _ (lp.coeFn_zero G 1 μ).symm
  rfl
#align measure_theory.condexp_ind_empty MeasureTheory.condexpInd_empty

theorem condexpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd hm μ s (c • x) = c • condexpInd hm μ s x :=
  condexpIndL1_smul' c x
#align measure_theory.condexp_ind_smul' MeasureTheory.condexpInd_smul'

theorem norm_condexpInd_apply_le (x : G) : ‖condexpInd hm μ s x‖ ≤ (μ s).toReal * ‖x‖ :=
  norm_condexpIndL1_le x
#align measure_theory.norm_condexp_ind_apply_le MeasureTheory.norm_condexpInd_apply_le

theorem norm_condexpInd_le : ‖(condexpInd hm μ s : G →L[ℝ] α →₁[μ] G)‖ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ Ennreal.toReal_nonneg norm_condexpInd_apply_le
#align measure_theory.norm_condexp_ind_le MeasureTheory.norm_condexpInd_le

theorem condexpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (x : G) :
    condexpInd hm μ (s ∪ t) x = condexpInd hm μ s x + condexpInd hm μ t x :=
  condexpIndL1_disjoint_union hs ht hμs hμt hst x
#align measure_theory.condexp_ind_disjoint_union_apply MeasureTheory.condexpInd_disjoint_union_apply

theorem condexpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) :
    (condexpInd hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexpInd hm μ s + condexpInd hm μ t :=
  by
  ext1
  push_cast
  exact condexpInd_disjoint_union_apply hs ht hμs hμt hst x
#align measure_theory.condexp_ind_disjoint_union MeasureTheory.condexpInd_disjoint_union

variable (G)

theorem dominatedFinMeasAdditiveCondexpInd (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun s t => condexpInd_disjoint_union, fun s _ _ => norm_condexpInd_le.trans (one_mul _).symm.le⟩
#align measure_theory.dominated_fin_meas_additive_condexp_ind MeasureTheory.dominatedFinMeasAdditiveCondexpInd

variable {G}

theorem set_integral_condexpInd (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : (∫ a in s, condexpInd hm μ t x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, condexpInd hm μ t x a ∂μ) = ∫ a in s, condexpIndSmul hm ht hμt x a ∂μ :=
      set_integral_congr_ae (hm s hs)
        ((condexpInd_ae_eq_condexpIndSmul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexpIndSmul hs ht hμs hμt x
    
#align measure_theory.set_integral_condexp_ind MeasureTheory.set_integral_condexpInd

theorem condexpInd_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd hm μ s c = indicatorConstLp 1 (hm s hs) hμs c :=
  by
  ext1
  refine' EventuallyEq.trans _ indicator_const_Lp_coe_fn.symm
  refine' (condexpInd_ae_eq_condexpIndSmul hm (hm s hs) hμs c).trans _
  refine' (condexpIndSmul_ae_eq_smul hm (hm s hs) hμs c).trans _
  rw [lpMeas_coe, condexpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine' (@indicator_const_Lp_coe_fn α _ _ 2 μ _ s (hm s hs) hμs (1 : ℝ)).mono fun x hx => _
  dsimp only
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]
#align measure_theory.condexp_ind_of_measurable MeasureTheory.condexpInd_of_measurable

theorem condexpInd_nonneg {E} [NormedLatticeAddCommGroup E] [NormedSpace ℝ E] [OrderedSMul ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) : 0 ≤ condexpInd hm μ s x :=
  by
  rw [← coeFn_le]
  refine' EventuallyLe.trans_eq _ (condexpInd_ae_eq_condexpIndSmul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condexpIndSmul_nonneg hs hμs x hx)
#align measure_theory.condexp_ind_nonneg MeasureTheory.condexpInd_nonneg

end CondexpInd

section CondexpL1

variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1Clm (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditiveCondexpInd F' hm μ)
#align measure_theory.condexp_L1_clm MeasureTheory.condexpL1Clm

theorem condexpL1Clm_smul (c : 𝕜) (f : α →₁[μ] F') :
    condexpL1Clm hm μ (c • f) = c • condexpL1Clm hm μ f :=
  L1.setToL1_smul (dominatedFinMeasAdditiveCondexpInd F' hm μ) (fun c s x => condexpInd_smul' c x) c
    f
#align measure_theory.condexp_L1_clm_smul MeasureTheory.condexpL1Clm_smul

theorem condexpL1Clm_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd hm μ s x :=
  L1.setToL1_indicatorConstLp (dominatedFinMeasAdditiveCondexpInd F' hm μ) hs hμs x
#align measure_theory.condexp_L1_clm_indicator_const_Lp MeasureTheory.condexpL1Clm_indicatorConstLp

theorem condexpL1Clm_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd hm μ s x :=
  by
  rw [lp.simpleFunc.coe_indicatorConst]
  exact condexpL1Clm_indicatorConstLp hs hμs x
#align measure_theory.condexp_L1_clm_indicator_const MeasureTheory.condexpL1Clm_indicatorConst

/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
theorem set_integral_condexpL1Clm_of_measure_ne_top (f : α →₁[μ] F') (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  refine'
    lp.induction Ennreal.one_ne_top
      (fun f : α →₁[μ] F' => (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ) _ _
      (isClosed_eq _ _) f
  · intro x t ht hμt
    simp_rw [condexpL1Clm_indicatorConst ht hμt.ne x]
    rw [lp.simpleFunc.coe_indicatorConst, set_integral_indicatorConstLp (hm _ hs)]
    exact set_integral_condexpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp hfg_disj hf hg
    simp_rw [(condexpL1Clm hm μ).map_add]
    rw [set_integral_congr_ae (hm s hs)
        ((lp.coeFn_add (condexpL1Clm hm μ (hf_Lp.to_Lp f)) (condexpL1Clm hm μ (hg_Lp.to_Lp g))).mono
          fun x hx hxs => hx)]
    rw [set_integral_congr_ae (hm s hs)
        ((lp.coeFn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono fun x hx hxs => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrableCoeFn _).integrableOn (L1.integrableCoeFn _).integrableOn,
      integral_add (L1.integrableCoeFn _).integrableOn (L1.integrableCoeFn _).integrableOn, hf, hg]
  · exact (continuous_set_integral s).comp (condexpL1Clm hm μ).continuous
  · exact continuous_set_integral s
#align measure_theory.set_integral_condexp_L1_clm_of_measure_ne_top MeasureTheory.set_integral_condexpL1Clm_of_measure_ne_top

/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1Clm (f : α →₁[μ] F') (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  let S := spanningSets (μ.trim hm)
  have hS_meas : ∀ i, measurable_set[m] (S i) := measurable_spanningSets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_unionᵢ, unionᵢ_spanningSets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ :=
    by
    refine' fun i => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s :=
    by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condexpL1Clm hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      set_integral_condexpL1Clm_of_measure_ne_top f (@measurable_set.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) :=
    by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrableCoeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left :
    Tendsto (fun i => ∫ x in S i ∩ s, condexpL1Clm hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condexpL1Clm hm μ f x ∂μ)) :=
    by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrableCoeFn (condexpL1Clm hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right
#align measure_theory.set_integral_condexp_L1_clm MeasureTheory.set_integral_condexpL1Clm

theorem aeStronglyMeasurable'CondexpL1Clm (f : α →₁[μ] F') :
    AeStronglyMeasurable' m (condexpL1Clm hm μ f) μ :=
  by
  refine'
    lp.induction Ennreal.one_ne_top
      (fun f : α →₁[μ] F' => AeStronglyMeasurable' m (condexpL1Clm hm μ f) μ) _ _ _ f
  · intro c s hs hμs
    rw [condexpL1Clm_indicatorConst hs hμs.ne c]
    exact aeStronglyMeasurable'CondexpInd hs hμs.ne c
  · intro f g hf hg h_disj hfm hgm
    rw [(condexpL1Clm hm μ).map_add]
    refine' AeStronglyMeasurable'.congr _ (coeFn_add _ _).symm
    exact AeStronglyMeasurable'.add hfm hgm
  · have :
      { f : lp F' 1 μ | AeStronglyMeasurable' m (condexpL1Clm hm μ f) μ } =
        condexpL1Clm hm μ ⁻¹' { f | AeStronglyMeasurable' m f μ } :=
      by rfl
    rw [this]
    refine' IsClosed.preimage (condexpL1Clm hm μ).continuous _
    exact isClosed_aeStronglyMeasurable' hm
#align measure_theory.ae_strongly_measurable'_condexp_L1_clm MeasureTheory.aeStronglyMeasurable'CondexpL1Clm

theorem condexpL1Clm_lpMeas (f : lpMeas F' ℝ m 1 μ) : condexpL1Clm hm μ (f : α →₁[μ] F') = ↑f :=
  by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine'
    @Lp.induction α F' m _ 1 (μ.trim hm) _ Ennreal.coe_ne_top
      (fun g : α →₁[μ.trim hm] F' =>
        condexpL1Clm hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
          ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g))
      _ _ _ g
  · intro c s hs hμs
    rw [lp.simpleFunc.coe_indicatorConst, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condexpL1Clm_indicatorConstLp]
    exact condexpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg hfg_disj hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine' isClosed_eq _ _
    · refine' (condexpL1Clm hm μ).continuous.comp (continuous_induced_dom.comp _)
      exact LinearIsometryEquiv.continuous _
    · refine' continuous_induced_dom.comp _
      exact LinearIsometryEquiv.continuous _
#align measure_theory.condexp_L1_clm_Lp_meas MeasureTheory.condexpL1Clm_lpMeas

theorem condexpL1Clm_of_aeStronglyMeasurable' (f : α →₁[μ] F') (hfm : AeStronglyMeasurable' m f μ) :
    condexpL1Clm hm μ f = f :=
  condexpL1Clm_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)
#align measure_theory.condexp_L1_clm_of_ae_strongly_measurable' MeasureTheory.condexpL1Clm_of_aeStronglyMeasurable'

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd hm μ) (dominatedFinMeasAdditiveCondexpInd F' hm μ) f
#align measure_theory.condexp_L1 MeasureTheory.condexpL1

theorem condexpL1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  setToFun_undef (dominatedFinMeasAdditiveCondexpInd F' hm μ) hf
#align measure_theory.condexp_L1_undef MeasureTheory.condexpL1_undef

theorem condexpL1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1Clm hm μ (hf.toL1 f) :=
  setToFun_eq (dominatedFinMeasAdditiveCondexpInd F' hm μ) hf
#align measure_theory.condexp_L1_eq MeasureTheory.condexpL1_eq

@[simp]
theorem condexpL1_zero : condexpL1 hm μ (0 : α → F') = 0 :=
  setToFun_zero _
#align measure_theory.condexp_L1_zero MeasureTheory.condexpL1_zero

@[simp]
theorem condexpL1_measure_zero (hm : m ≤ m0) : condexpL1 hm (0 : Measure α) f = 0 :=
  setToFun_measure_zero _ rfl
#align measure_theory.condexp_L1_measure_zero MeasureTheory.condexpL1_measure_zero

theorem aeStronglyMeasurable'CondexpL1 {f : α → F'} :
    AeStronglyMeasurable' m (condexpL1 hm μ f) μ :=
  by
  by_cases hf : Integrable f μ
  · rw [condexpL1_eq hf]
    exact aeStronglyMeasurable'CondexpL1Clm _
  · rw [condexpL1_undef hf]
    refine' AeStronglyMeasurable'.congr _ (coeFn_zero _ _ _).symm
    exact StronglyMeasurable.aeStronglyMeasurable' (@strongly_measurable_zero _ _ m _ _)
#align measure_theory.ae_strongly_measurable'_condexp_L1 MeasureTheory.aeStronglyMeasurable'CondexpL1

theorem condexpL1_congr_ae (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (h : f =ᵐ[μ] g) :
    condexpL1 hm μ f = condexpL1 hm μ g :=
  setToFun_congr_ae _ h
#align measure_theory.condexp_L1_congr_ae MeasureTheory.condexpL1_congr_ae

theorem integrableCondexpL1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrableCoeFn _
#align measure_theory.integrable_condexp_L1 MeasureTheory.integrableCondexpL1

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexpL1 (hf : Integrable f μ) (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1 hm μ f x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  simp_rw [condexpL1_eq hf]
  rw [set_integral_condexpL1Clm (hf.to_L1 f) hs]
  exact set_integral_congr_ae (hm s hs) (hf.coe_fn_to_L1.mono fun x hx hxs => hx)
#align measure_theory.set_integral_condexp_L1 MeasureTheory.set_integral_condexpL1

theorem condexpL1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  setToFun_add _ hf hg
#align measure_theory.condexp_L1_add MeasureTheory.condexpL1_add

theorem condexpL1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  setToFun_neg _ f
#align measure_theory.condexp_L1_neg MeasureTheory.condexpL1_neg

theorem condexpL1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f :=
  setToFun_smul _ (fun c _ x => condexpInd_smul' c x) c f
#align measure_theory.condexp_L1_smul MeasureTheory.condexpL1_smul

theorem condexpL1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  setToFun_sub _ hf hg
#align measure_theory.condexp_L1_sub MeasureTheory.condexpL1_sub

theorem condexpL1_of_aeStronglyMeasurable' (hfm : AeStronglyMeasurable' m f μ)
    (hfi : Integrable f μ) : condexpL1 hm μ f =ᵐ[μ] f :=
  by
  rw [condexpL1_eq hfi]
  refine' EventuallyEq.trans _ (Integrable.coeFn_toL1 hfi)
  rw [condexpL1Clm_of_aeStronglyMeasurable']
  exact AeStronglyMeasurable'.congr hfm (Integrable.coeFn_toL1 hfi).symm
#align measure_theory.condexp_L1_of_ae_strongly_measurable' MeasureTheory.condexpL1_of_aeStronglyMeasurable'

theorem condexpL1_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    condexpL1 hm μ f ≤ᵐ[μ] condexpL1 hm μ g :=
  by
  rw [coeFn_le]
  have h_nonneg : ∀ s, MeasurableSet s → μ s < ∞ → ∀ x : E, 0 ≤ x → 0 ≤ condexpInd hm μ s x :=
    fun s hs hμs x hx => condexpInd_nonneg hs hμs.ne x hx
  exact setToFun_mono (dominatedFinMeasAdditiveCondexpInd E hm μ) h_nonneg hf hg hfg
#align measure_theory.condexp_L1_mono MeasureTheory.condexpL1_mono

end CondexpL1

section Condexp

/-! ### Conditional expectation of a function -/


open Classical

variable {𝕜} {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m0`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
irreducible_def condexp (m : MeasurableSpace α) {m0 : MeasurableSpace α} (μ : Measure α)
  (f : α → F') : α → F' :=
  if hm : m ≤ m0 then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if strongly_measurable[m] f then f
      else
        (@aeStronglyMeasurable'CondexpL1 _ _ _ _ _ m m0 μ hm h.1 _).mk
          (@condexpL1 _ _ _ _ _ _ _ hm μ h.1 f)
    else 0
  else 0
#align measure_theory.condexp MeasureTheory.condexp

-- mathport name: measure_theory.condexp
-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
scoped notation μ "[" f "|" m "]" => MeasureTheory.condexp m μ f

theorem condexp_of_not_le (hm_not : ¬m ≤ m0) : μ[f|m] = 0 := by rw [condexp, dif_neg hm_not]
#align measure_theory.condexp_of_not_le MeasureTheory.condexp_of_not_le

theorem condexp_of_not_sigmaFinite (hm : m ≤ m0) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ[f|m] = 0 := by
  rw [condexp, dif_pos hm, dif_neg]
  push_neg
  exact fun h => absurd h hμm_not
#align measure_theory.condexp_of_not_sigma_finite MeasureTheory.condexp_of_not_sigmaFinite

theorem condexp_of_sigmaFinite (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f|m] =
      if Integrable f μ then
        if strongly_measurable[m] f then f else aeStronglyMeasurable'CondexpL1.mk (condexpL1 hm μ f)
      else 0 :=
  by
  rw [condexp, dif_pos hm]
  simp only [hμm, Ne.def, true_and_iff]
  by_cases hf : Integrable f μ
  · rw [dif_pos hf, if_pos hf]
  · rw [dif_neg hf, if_neg hf]
#align measure_theory.condexp_of_sigma_finite MeasureTheory.condexp_of_sigmaFinite

theorem condexp_of_stronglyMeasurable (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : strongly_measurable[m] f) (hfi : Integrable f μ) : μ[f|m] = f :=
  by
  rw [condexp_of_sigmaFinite hm, if_pos hfi, if_pos hf]
  infer_instance
#align measure_theory.condexp_of_strongly_measurable MeasureTheory.condexp_of_stronglyMeasurable

theorem condexp_const (hm : m ≤ m0) (c : F') [IsFiniteMeasure μ] :
    μ[fun x : α => c|m] = fun _ => c :=
  condexp_of_stronglyMeasurable hm (@stronglyMeasurable_const _ _ m _ _) (integrableConst c)
#align measure_theory.condexp_const MeasureTheory.condexp_const

theorem condexp_ae_eq_condexpL1 (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (f : α → F') :
    μ[f|m] =ᵐ[μ] condexpL1 hm μ f :=
  by
  rw [condexp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : strongly_measurable[m] f
    · rw [if_pos hfm]
      exact
        (condexpL1_of_aeStronglyMeasurable' (StronglyMeasurable.aeStronglyMeasurable' hfm) hfi).symm
    · rw [if_neg hfm]
      exact (AeStronglyMeasurable'.ae_eq_mk aeStronglyMeasurable'CondexpL1).symm
  rw [if_neg hfi, condexpL1_undef hfi]
  exact (coeFn_zero _ _ _).symm
#align measure_theory.condexp_ae_eq_condexp_L1 MeasureTheory.condexp_ae_eq_condexpL1

theorem condexp_ae_eq_condexpL1Clm (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f|m] =ᵐ[μ] condexpL1Clm hm μ (hf.toL1 f) :=
  by
  refine' (condexp_ae_eq_condexpL1 hm f).trans (eventually_of_forall fun x => _)
  rw [condexpL1_eq hf]
#align measure_theory.condexp_ae_eq_condexp_L1_clm MeasureTheory.condexp_ae_eq_condexpL1Clm

theorem condexp_undef (hf : ¬Integrable f μ) : μ[f|m] = 0 :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  rw [condexp_of_sigmaFinite, if_neg hf]
#align measure_theory.condexp_undef MeasureTheory.condexp_undef

@[simp]
theorem condexp_zero : μ[(0 : α → F')|m] = 0 :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact
    condexp_of_stronglyMeasurable hm (@strongly_measurable_zero _ _ m _ _) (integrableZero _ _ _)
#align measure_theory.condexp_zero MeasureTheory.condexp_zero

theorem stronglyMeasurable_condexp : strongly_measurable[m] (μ[f|m]) :=
  by
  by_cases hm : m ≤ m0
  swap;
  · rw [condexp_of_not_le hm]
    exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap;
  · rw [condexp_of_not_sigmaFinite hm hμm]
    exact stronglyMeasurable_zero
  haveI : SigmaFinite (μ.trim hm) := hμm
  rw [condexp_of_sigmaFinite hm]
  swap; · infer_instance
  split_ifs with hfi hfm
  · exact hfm
  · exact AeStronglyMeasurable'.stronglyMeasurable_mk _
  · exact stronglyMeasurable_zero
#align measure_theory.strongly_measurable_condexp MeasureTheory.stronglyMeasurable_condexp

theorem condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] :=
  by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexpL1 hm f).trans
      (Filter.EventuallyEq.trans (by rw [condexpL1_congr_ae hm h])
        (condexp_ae_eq_condexpL1 hm g).symm)
#align measure_theory.condexp_congr_ae MeasureTheory.condexp_congr_ae

theorem condexp_of_aeStronglyMeasurable' (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : AeStronglyMeasurable' m f μ) (hfi : Integrable f μ) : μ[f|m] =ᵐ[μ] f :=
  by
  refine' ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm
  rw [condexp_of_stronglyMeasurable hm hf.strongly_measurable_mk
      ((integrable_congr hf.ae_eq_mk).mp hfi)]
#align measure_theory.condexp_of_ae_strongly_measurable' MeasureTheory.condexp_of_aeStronglyMeasurable'

theorem integrableCondexp : Integrable (μ[f|m]) μ :=
  by
  by_cases hm : m ≤ m0
  swap;
  · rw [condexp_of_not_le hm]
    exact integrableZero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap;
  · rw [condexp_of_not_sigmaFinite hm hμm]
    exact integrableZero _ _ _
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact (integrableCondexpL1 f).congr (condexp_ae_eq_condexpL1 hm f).symm
#align measure_theory.integrable_condexp MeasureTheory.integrableCondexp

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem set_integral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : measurable_set[m] s) : (∫ x in s, (μ[f|m]) x ∂μ) = ∫ x in s, f x ∂μ :=
  by
  rw [set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexpL1 hm f).mono fun x hx _ => hx)]
  exact set_integral_condexpL1 hf hs
#align measure_theory.set_integral_condexp MeasureTheory.set_integral_condexp

theorem integral_condexp (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    (∫ x, (μ[f|m]) x ∂μ) = ∫ x, f x ∂μ :=
  by
  suffices (∫ x in Set.univ, (μ[f|m]) x ∂μ) = ∫ x in Set.univ, f x ∂μ
    by
    simp_rw [integral_univ] at this
    exact this
  exact set_integral_condexp hm hf (@measurable_set.univ _ m)
#align measure_theory.integral_condexp MeasureTheory.integral_condexp

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, g x ∂μ) = ∫ x in s, f x ∂μ)
    (hgm : AeStronglyMeasurable' m g μ) : g =ᵐ[μ] μ[f|m] :=
  by
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite
      (fun s hs hμs => integrable_condexp.integrable_on) (fun s hs hμs => _) hgm
      (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs]
#align measure_theory.ae_eq_condexp_of_forall_set_integral_eq MeasureTheory.ae_eq_condexp_of_forall_set_integral_eq

theorem condexp_bot' [hμ : μ.ae.NeBot] (f : α → F') :
    μ[f|⊥] = fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ :=
  by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condexp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, Ennreal.top_toReal, inv_zero, zero_smul]
    rfl
  haveI : IsFiniteMeasure μ := hμ_finite
  by_cases hf : Integrable f μ
  swap;
  · rw [integral_undef hf, smul_zero, condexp_undef hf]
    rfl
  have h_meas : strongly_measurable[⊥] (μ[f|⊥]) := stronglyMeasurable_condexp
  obtain ⟨c, h_eq⟩ := strongly_measurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : (∫ x, (μ[f|⊥]) x ∂μ) = ∫ x, f x ∂μ := integral_condexp bot_le hf
  simp_rw [h_eq, integral_const] at h_integral
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul]
  rw [Ne.def, Ennreal.toReal_eq_zero_iff, Auto.not_or_eq, Measure.measure_univ_eq_zero, ← ae_eq_bot,
    ← Ne.def, ← neBot_iff]
  exact ⟨hμ, measure_ne_top μ Set.univ⟩
#align measure_theory.condexp_bot' MeasureTheory.condexp_bot'

theorem condexp_bot_ae_eq (f : α → F') :
    μ[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ :=
  by
  by_cases μ.ae.ne_bot
  · refine' eventually_of_forall fun x => _
    rw [condexp_bot' f]
    exact h
  · rw [neBot_iff, Classical.not_not, ae_eq_bot] at h
    simp only [h, ae_zero]
#align measure_theory.condexp_bot_ae_eq MeasureTheory.condexp_bot_ae_eq

theorem condexp_bot [IsProbabilityMeasure μ] (f : α → F') : μ[f|⊥] = fun _ => ∫ x, f x ∂μ :=
  by
  refine' (condexp_bot' f).trans _
  rw [measure_univ, Ennreal.one_toReal, inv_one, one_smul]
#align measure_theory.condexp_bot MeasureTheory.condexp_bot

theorem condexp_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] :=
  by
  by_cases hm : m ≤ m0
  swap;
  · simp_rw [condexp_of_not_le hm]
    simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap;
  · simp_rw [condexp_of_not_sigmaFinite hm hμm]
    simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexpL1 hm _).trans _
  rw [condexpL1_add hf hg]
  exact
    (coeFn_add _ _).trans
      ((condexp_ae_eq_condexpL1 hm _).symm.add (condexp_ae_eq_condexpL1 hm _).symm)
#align measure_theory.condexp_add MeasureTheory.condexp_add

theorem condexp_finset_sum {ι : Type _} {s : Finset ι} {f : ι → α → F'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : μ[∑ i in s, f i|m] =ᵐ[μ] ∑ i in s, μ[f i|m] :=
  by
  induction' s using Finset.induction_on with i s his heq hf
  · rw [Finset.sum_empty, Finset.sum_empty, condexp_zero]
  · rw [Finset.sum_insert his, Finset.sum_insert his]
    exact
      (condexp_add (hf i <| Finset.mem_insert_self i s) <|
            integrableFinsetSum' _ fun j hmem => hf j <| Finset.mem_insert_of_mem hmem).trans
        ((EventuallyEq.refl _ _).add (heq fun j hmem => hf j <| Finset.mem_insert_of_mem hmem))
#align measure_theory.condexp_finset_sum MeasureTheory.condexp_finset_sum

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|m] =ᵐ[μ] c • μ[f|m] :=
  by
  by_cases hm : m ≤ m0
  swap;
  · simp_rw [condexp_of_not_le hm]
    simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap;
  · simp_rw [condexp_of_not_sigmaFinite hm hμm]
    simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexpL1 hm _).trans _
  rw [condexpL1_smul c f]
  refine' (@condexp_ae_eq_condexp_L1 _ _ _ _ _ m _ _ hm _ f).mp _
  refine' (coeFn_smul c (condexpL1 hm μ f)).mono fun x hx1 hx2 => _
  rw [hx1, Pi.smul_apply, Pi.smul_apply, hx2]
#align measure_theory.condexp_smul MeasureTheory.condexp_smul

theorem condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] -μ[f|m] := by
  letI : Module ℝ (α → F') := @pi.module α (fun _ => F') ℝ _ _ fun _ => inferInstance <;>
    calc
      μ[-f|m] = μ[(-1 : ℝ) • f|m] := by rw [neg_one_smul ℝ f]
      _ =ᵐ[μ] (-1 : ℝ) • μ[f|m] := condexp_smul (-1) f
      _ = -μ[f|m] := neg_one_smul ℝ (μ[f|m])
      
#align measure_theory.condexp_neg MeasureTheory.condexp_neg

theorem condexp_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f - g|m] =ᵐ[μ] μ[f|m] - μ[g|m] :=
  by
  simp_rw [sub_eq_add_neg]
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g))
#align measure_theory.condexp_sub MeasureTheory.condexp_sub

theorem condexp_condexp_of_le {m₁ m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] :=
  by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condexp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]
  haveI : SigmaFinite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  by_cases hf : Integrable f μ
  swap; · simp_rw [condexp_undef hf, condexp_zero]
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂)
      (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => integrable_condexp.integrable_on) _
      (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
      (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
  intro s hs hμs
  rw [set_integral_condexp (hm₁₂.trans hm₂) integrableCondexp hs]
  swap; · infer_instance
  rw [set_integral_condexp (hm₁₂.trans hm₂) hf hs, set_integral_condexp hm₂ hf (hm₁₂ s hs)]
#align measure_theory.condexp_condexp_of_le MeasureTheory.condexp_condexp_of_le

theorem condexp_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    μ[f|m] ≤ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexpL1 hm _).trans_le
      ((condexpL1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexpL1 hm _).symm)
#align measure_theory.condexp_mono MeasureTheory.condexp_mono

theorem condexp_nonneg {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f|m] :=
  by
  by_cases hfint : Integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono (integrableZero _ _ _) hfint hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonneg MeasureTheory.condexp_nonneg

theorem condexp_nonpos {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : f ≤ᵐ[μ] 0) : μ[f|m] ≤ᵐ[μ] 0 :=
  by
  by_cases hfint : Integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono hfint (integrableZero _ _ _) hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonpos MeasureTheory.condexp_nonpos

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condexp_L1`. -/
theorem tendsto_condexpL1_of_dominated_convergence (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → F'} {f : α → F'} (bound_fs : α → ℝ)
    (hfs_meas : ∀ n, AeStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condexpL1 hm μ (fs n)) atTop (𝓝 (condexpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs
#align measure_theory.tendsto_condexp_L1_of_dominated_convergence MeasureTheory.tendsto_condexpL1_of_dominated_convergence

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
theorem tendsto_condexp_unique (fs gs : ℕ → α → F') (f g : α → F')
    (hfs_int : ∀ n, Integrable (fs n) μ) (hgs_int : ∀ n, Integrable (gs n) μ)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
    (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
    (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ[fs n|m] =ᵐ[μ] μ[gs n|m]) :
    μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0
  swap
  · simp_rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap
  · simp_rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexpL1 hm f).trans ((condexp_ae_eq_condexpL1 hm g).trans _).symm
  rw [← lp.ext_iff]
  have hn_eq : ∀ n, condexpL1 hm μ (gs n) = condexpL1 hm μ (fs n) :=
    by
    intro n
    ext1
    refine' (condexp_ae_eq_condexpL1 hm (gs n)).symm.trans ((hfg n).symm.trans _)
    exact condexp_ae_eq_condexpL1 hm (fs n)
  have hcond_fs : Tendsto (fun n => condexpL1 hm μ (fs n)) atTop (𝓝 (condexpL1 hm μ f)) :=
    tendsto_condexpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : Tendsto (fun n => condexpL1 hm μ (gs n)) atTop (𝓝 (condexpL1 hm μ g)) :=
    tendsto_condexpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (eventually_of_forall hn_eq)
#align measure_theory.tendsto_condexp_unique MeasureTheory.tendsto_condexp_unique

end Condexp

end MeasureTheory

