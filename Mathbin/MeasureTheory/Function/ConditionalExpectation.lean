/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.MeasureTheory.Function.L2Space
import Mathbin.MeasureTheory.Decomposition.RadonNikodym

/-! # Conditional expectation

We build the conditional expectation of a function `f` with value in a Banach space with respect to
a measure `μ` (defined on a measurable space structure `m0`) and a measurable space structure `m`
with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-measurable function `μ[f|hm]` which is
integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable sets `s`.
It is unique as an element of `L¹`.

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

* `condexp (hm : m ≤ m0) (μ : measure α) (f : α → E)`: conditional expectation of `f` with respect
  to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `measurable_condexp` : `condexp` is `m`-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : the conditional
  expectation verifies `∫ x in s, condexp hm μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable
  set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `Lp.ae_eq_of_forall_set_integral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal everywhere.
* `ae_eq_of_forall_set_integral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal everywhere.
  Requires `[sigma_finite (μ.trim hm)]`.
* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-sigma-algebra) and a function `f`, we define the notation
* `μ[f|hm] = condexp hm μ f`.

## Implementation notes

Most of the results in this file are valid for a second countable, borel, real normed space `F`.
However, some lemmas also use `𝕜 : is_R_or_C`:
* `condexp_L2` is defined only for an `inner_product_space` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `normed_space 𝕜 F`.

## Tags

conditional expectation, conditional expected value

-/


noncomputable section

open TopologicalSpace MeasureTheory.lp Filter ContinuousLinearMap

open_locale Nnreal Ennreal TopologicalSpace BigOperators MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `ae_measurable' m f μ` if it is `μ`-a.e. equal to an `m`-measurable
function. This is similar to `ae_measurable`, but the `measurable_space` structures used for the
measurability statement and for the measure are different. -/
def AeMeasurable' {α β} [MeasurableSpace β] (m : MeasurableSpace α) {m0 : MeasurableSpace α} (f : α → β)
    (μ : Measure α) : Prop :=
  ∃ g : α → β, measurable[m] g ∧ f =ᵐ[μ] g

namespace AeMeasurable'

variable {α β 𝕜 : Type _} {m m0 : MeasurableSpace α} {μ : Measure α} [MeasurableSpace β] [MeasurableSpace 𝕜]
  {f g : α → β}

theorem congr (hf : AeMeasurable' m f μ) (hfg : f =ᵐ[μ] g) : AeMeasurable' m g μ := by
  obtain ⟨f', hf'_meas, hff'⟩ := hf
  exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩

theorem add [Add β] [HasMeasurableAdd₂ β] (hf : AeMeasurable' m f μ) (hg : AeMeasurable' m g μ) :
    AeMeasurable' m (f + g) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  rcases hg with ⟨g', h_g'_meas, hgg'⟩
  exact ⟨f' + g', h_f'_meas.add h_g'_meas, hff'.add hgg'⟩

theorem neg [Neg β] [HasMeasurableNeg β] {f : α → β} (hfm : AeMeasurable' m f μ) : AeMeasurable' m (-f) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine' ⟨-f', hf'_meas.neg, hf_ae.mono fun x hx => _⟩
  simp_rw [Pi.neg_apply]
  rw [hx]

theorem sub [Sub β] [HasMeasurableSub₂ β] {f g : α → β} (hfm : AeMeasurable' m f μ) (hgm : AeMeasurable' m g μ) :
    AeMeasurable' m (f - g) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  rcases hgm with ⟨g', hg'_meas, hg_ae⟩
  refine' ⟨f' - g', hf'_meas.sub hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => _)⟩
  simp_rw [Pi.sub_apply]
  rw [hx1, hx2]

theorem const_smul [HasScalar 𝕜 β] [HasMeasurableSmul 𝕜 β] (c : 𝕜) (hf : AeMeasurable' m f μ) :
    AeMeasurable' m (c • f) μ := by
  rcases hf with ⟨f', h_f'_meas, hff'⟩
  refine' ⟨c • f', h_f'_meas.const_smul c, _⟩
  exact eventually_eq.fun_comp hff' fun x => c • x

theorem const_inner {𝕜} [IsROrC 𝕜] [InnerProductSpace 𝕜 β] [SecondCountableTopology β] [OpensMeasurableSpace β]
    {f : α → β} (hfm : AeMeasurable' m f μ) (c : β) : AeMeasurable' m (fun x => (inner c (f x) : 𝕜)) μ := by
  rcases hfm with ⟨f', hf'_meas, hf_ae⟩
  refine' ⟨fun x => (inner c (f' x) : 𝕜), (@measurable_const _ _ _ m _).inner hf'_meas, hf_ae.mono fun x hx => _⟩
  dsimp only
  rw [hx]

/-- A m-measurable function almost everywhere equal to `f`. -/
def mk (f : α → β) (hfm : AeMeasurable' m f μ) : α → β :=
  hfm.some

theorem measurable_mk {f : α → β} (hfm : AeMeasurable' m f μ) : measurable[m] (hfm.mk f) :=
  hfm.some_spec.1

theorem ae_eq_mk {f : α → β} (hfm : AeMeasurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.some_spec.2

theorem measurable_comp {γ} [MeasurableSpace γ] {f : α → β} {g : β → γ} (hg : Measurable g) (hf : AeMeasurable' m f μ) :
    AeMeasurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x), @Measurable.comp _ _ _ m _ _ _ _ hg hf.measurable_mk,
    hf.ae_eq_mk.mono fun x hx => by
      rw [Function.comp_applyₓ, hx]⟩

end AeMeasurable'

theorem ae_measurable'_of_ae_measurable'_trim {α β} {m m0 m0' : MeasurableSpace α} [MeasurableSpace β] (hm0 : m0 ≤ m0')
    {μ : Measure α} {f : α → β} (hf : AeMeasurable' m f (μ.trim hm0)) : AeMeasurable' m f μ := by
  obtain ⟨g, hg_meas, hfg⟩ := hf
  exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

theorem Measurable.ae_measurable' {α β} {m m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {f : α → β}
    (hf : measurable[m] f) : AeMeasurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩

theorem ae_eq_trim_iff_of_ae_measurable' {α β} [AddGroupₓ β] [MeasurableSpace β] [MeasurableSingletonClass β]
    [HasMeasurableSub₂ β] {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β} (hm : m ≤ m0)
    (hfm : AeMeasurable' m f μ) (hgm : AeMeasurable' m g μ) : hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.measurable_mk hgm.measurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h => hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

variable {α β γ E E' F F' G G' H 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  [MeasurableSpace β]
  -- β for a generic measurable space
  -- E for an inner product space
  [InnerProductSpace 𝕜 E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  -- E' for an inner product space on which we compute integrals
  [InnerProductSpace 𝕜 E']
  [MeasurableSpace E'] [BorelSpace E'] [SecondCountableTopology E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedGroup F]
  [NormedSpace 𝕜 F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  -- F' for integrals on a Lp submodule
  [NormedGroup F']
  [NormedSpace 𝕜 F'] [MeasurableSpace F'] [BorelSpace F'] [SecondCountableTopology F'] [NormedSpace ℝ F']
  [CompleteSpace F']
  -- G for a Lp add_subgroup
  [NormedGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  -- G' for integrals on a Lp add_subgroup
  [NormedGroup G']
  [MeasurableSpace G'] [BorelSpace G'] [SecondCountableTopology G'] [NormedSpace ℝ G'] [CompleteSpace G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [MeasurableSpace H]
  [NormedGroup H]

section LpMeas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable (F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def lpMeasSubgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) : AddSubgroup (lp F p μ) where
  Carrier := { f : lp F p μ | AeMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α m _ _, lp.coe_fn_zero _ _ _⟩
  add_mem' := fun f g hf hg => (hf.add hg).congr (lp.coe_fn_add f g).symm
  neg_mem' := fun f hf => AeMeasurable'.congr hf.neg (lp.coe_fn_neg f).symm

variable (𝕜)

/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def lpMeas [OpensMeasurableSpace 𝕜] (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measure α) :
    Submodule 𝕜 (lp F p μ) where
  Carrier := { f : lp F p μ | AeMeasurable' m f μ }
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α m _ _, lp.coe_fn_zero _ _ _⟩
  add_mem' := fun f g hf hg => (hf.add hg).congr (lp.coe_fn_add f g).symm
  smul_mem' := fun c f hf => (hf.const_smul c).congr (lp.coe_fn_smul c f).symm

variable {F 𝕜}

variable [OpensMeasurableSpace 𝕜]

theorem mem_Lp_meas_subgroup_iff_ae_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} {f : lp F p μ} :
    f ∈ lpMeasSubgroup F m p μ ↔ AeMeasurable' m f μ := by
  rw [← AddSubgroup.mem_carrier, Lp_meas_subgroup, Set.mem_set_of_eq]

theorem mem_Lp_meas_iff_ae_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} {f : lp F p μ} :
    f ∈ lpMeas F 𝕜 m p μ ↔ AeMeasurable' m f μ := by
  rw [← SetLike.mem_coe, ← Submodule.mem_carrier, Lp_meas, Set.mem_set_of_eq]

theorem lpMeas.ae_measurable' {m m0 : MeasurableSpace α} {μ : Measure α} (f : lpMeas F 𝕜 m p μ) : AeMeasurable' m f μ :=
  mem_Lp_meas_iff_ae_measurable'.mp f.Mem

theorem mem_Lp_meas_self {m0 : MeasurableSpace α} (μ : Measure α) (f : lp F p μ) : f ∈ lpMeas F 𝕜 m0 p μ :=
  mem_Lp_meas_iff_ae_measurable'.mpr (lp.ae_measurable f)

theorem Lp_meas_subgroup_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeasSubgroup F m p μ} :
    ⇑f = (f : lp F p μ) :=
  coe_fn_coe_base f

theorem Lp_meas_coe {m m0 : MeasurableSpace α} {μ : Measure α} {f : lpMeas F 𝕜 m p μ} : ⇑f = (f : lp F p μ) :=
  coe_fn_coe_base f

theorem mem_Lp_meas_indicator_const_Lp {m m0 : MeasurableSpace α} (hm : m ≤ m0) {μ : Measure α} {s : Set α}
    (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {c : F} : indicatorConstLp p (hm s hs) hμs c ∈ lpMeas F 𝕜 m p μ :=
  ⟨s.indicator fun x : α => c, (@measurable_const _ α _ m _).indicator hs, indicator_const_Lp_coe_fn⟩

section CompleteSubspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometric` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/


variable {ι : Type _} {m m0 : MeasurableSpace α} {μ : Measure α}

/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem mem_ℒp_trim_of_mem_Lp_meas_subgroup (hm : m ≤ m0) (f : lp F p μ) (hf_meas : f ∈ lpMeasSubgroup F m p μ) :
    Memℒp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) := by
  have hf : ae_measurable' m f μ := mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas
  let g := hf.some
  obtain ⟨hg, hfg⟩ := hf.some_spec
  change mem_ℒp g p (μ.trim hm)
  refine' ⟨hg.ae_measurable, _⟩
  have h_snorm_fg : snorm g p (μ.trim hm) = snorm f p μ := by
    rw [snorm_trim hm hg]
    exact snorm_congr_ae hfg.symm
  rw [h_snorm_fg]
  exact Lp.snorm_lt_top f

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
theorem mem_Lp_meas_subgroup_to_Lp_of_trim (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    (mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f ∈ lpMeasSubgroup F m p μ := by
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)
  rw [mem_Lp_meas_subgroup_iff_ae_measurable']
  refine' ae_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm
  refine' ae_measurable'_of_ae_measurable'_trim hm _
  exact Lp.ae_measurable f

variable (F p μ)

/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
def lpMeasSubgroupToLpTrim (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.Mem).some (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.Mem)

variable (𝕜)

/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def lpMeasToLpTrim (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : lp F p (μ.trim hm) :=
  Memℒp.toLp (mem_Lp_meas_iff_ae_measurable'.mp f.Mem).some (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.Mem)

variable {𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
def lpTrimToLpMeasSubgroup (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeasSubgroup F m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable (𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def lpTrimToLpMeas (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpMeas F 𝕜 m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable {F 𝕜 p μ}

theorem Lp_meas_subgroup_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm (↑f) f.Mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.Mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_subgroup_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) :
    lpTrimToLpMeasSubgroup F p μ hm f =ᵐ[μ] f :=
  Memℒp.coe_fn_to_Lp _

theorem Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) : lpMeasToLpTrim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (Memℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm (↑f) f.Mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.Mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : lp F p (μ.trim hm)) : lpTrimToLpMeas F 𝕜 p μ hm f =ᵐ[μ] f :=
  Memℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_right_inv (hm : m ≤ m0) :
    Function.RightInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  refine' ae_eq_trim_of_measurable hm (Lp.measurable _) (Lp.measurable _) _
  exact (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _)

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_left_inv (hm : m ≤ m0) :
    Function.LeftInverse (lpTrimToLpMeasSubgroup F p μ hm) (lpMeasSubgroupToLpTrim F p μ hm) := by
  intro f
  ext1
  ext1
  rw [← Lp_meas_subgroup_coe]
  exact (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _).trans (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _)

theorem Lp_meas_subgroup_to_Lp_trim_add (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f + g) = lpMeasSubgroupToLpTrim F p μ hm f + lpMeasSubgroupToLpTrim F p μ hm g :=
  by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
  · exact (Lp.measurable _).add (Lp.measurable _)
    
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine'
    eventually_eq.trans _
      (eventually_eq.add (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm (Lp_meas_subgroup_to_Lp_trim_ae_eq hm g).symm)
  refine' (Lp.coe_fn_add _ _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact
    eventually_of_forall fun x => by
      rfl

theorem Lp_meas_subgroup_to_Lp_trim_neg (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (-f) = -lpMeasSubgroupToLpTrim F p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_neg _).symm
  refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
  · exact @Measurable.neg _ _ _ _ _ m _ (Lp.measurable _)
    
  refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _
  refine' eventually_eq.trans _ (eventually_eq.neg (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm)
  refine' (Lp.coe_fn_neg _).trans _
  simp_rw [Lp_meas_subgroup_coe]
  exact
    eventually_of_forall fun x => by
      rfl

theorem Lp_meas_subgroup_to_Lp_trim_sub (hm : m ≤ m0) (f g : lpMeasSubgroup F m p μ) :
    lpMeasSubgroupToLpTrim F p μ hm (f - g) = lpMeasSubgroupToLpTrim F p μ hm f - lpMeasSubgroupToLpTrim F p μ hm g :=
  by
  rw [sub_eq_add_neg, sub_eq_add_neg, Lp_meas_subgroup_to_Lp_trim_add, Lp_meas_subgroup_to_Lp_trim_neg]

theorem Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : lpMeas F 𝕜 m p μ) :
    lpMeasToLpTrim F 𝕜 p μ hm (c • f) = c • lpMeasToLpTrim F 𝕜 p μ hm f := by
  ext1
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
  · exact (Lp.measurable _).const_smul c
    
  refine' (Lp_meas_to_Lp_trim_ae_eq hm _).trans _
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (Lp_meas_to_Lp_trim_ae_eq hm f).mono fun x hx => _
  rw [Pi.smul_apply, Pi.smul_apply, hx]
  rfl

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
theorem Lp_meas_subgroup_to_Lp_trim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0) (f : lpMeasSubgroup F m p μ) :
    ∥lpMeasSubgroupToLpTrim F p μ hm f∥ = ∥f∥ := by
  rw [Lp.norm_def, snorm_trim hm (Lp.measurable _)]
  swap
  · infer_instance
    
  rw [snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _), Lp_meas_subgroup_coe, ← Lp.norm_def]
  congr

theorem isometry_Lp_meas_subgroup_to_Lp_trim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
    Isometry (lpMeasSubgroupToLpTrim F p μ hm) := by
  rw [isometry_emetric_iff_metric]
  intro f g
  rw [dist_eq_norm, ← Lp_meas_subgroup_to_Lp_trim_sub, Lp_meas_subgroup_to_Lp_trim_norm_map, dist_eq_norm]

variable (F p μ)

/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
def lpMeasSubgroupToLpTrimIso [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : lpMeasSubgroup F m p μ ≃ᵢ lp F p (μ.trim hm) where
  toFun := lpMeasSubgroupToLpTrim F p μ hm
  invFun := lpTrimToLpMeasSubgroup F p μ hm
  left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm
  isometry_to_fun := isometry_Lp_meas_subgroup_to_Lp_trim hm

variable (𝕜)

/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
def lpMeasSubgroupToLpMeasIso [hp : Fact (1 ≤ p)] : lpMeasSubgroup F m p μ ≃ᵢ lpMeas F 𝕜 m p μ :=
  Isometric.refl (lpMeasSubgroup F m p μ)

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
def lpMeasToLpTrimLie [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] lp F p (μ.trim hm) where
  toFun := lpMeasToLpTrim F 𝕜 p μ hm
  invFun := lpTrimToLpMeas F 𝕜 p μ hm
  left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm
  right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm
  map_add' := Lp_meas_subgroup_to_Lp_trim_add hm
  map_smul' := Lp_meas_to_Lp_trim_smul hm
  norm_map' := Lp_meas_subgroup_to_Lp_trim_norm_map hm

variable {F 𝕜 p μ}

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (lpMeasSubgroup F m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).complete_space_iff]
  infer_instance

instance [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (lpMeas F 𝕜 m p μ) := by
  rw [(Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.complete_space_iff]
  infer_instance

theorem is_complete_ae_measurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsComplete { f : lp F p μ | AeMeasurable' m f μ } := by
  rw [← complete_space_coe_iff_is_complete]
  have : Fact (m ≤ m0) := ⟨hm⟩
  change CompleteSpace (Lp_meas_subgroup F m p μ)
  infer_instance

theorem is_closed_ae_measurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
    IsClosed { f : lp F p μ | AeMeasurable' m f μ } :=
  IsComplete.is_closed (is_complete_ae_measurable' hm)

end CompleteSubspace

section StronglyMeasurable

variable {m m0 : MeasurableSpace α} {μ : Measure α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem lpMeas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : lpMeas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : ∃ g, FinStronglyMeasurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
  ⟨lpMeasSubgroupToLpTrim F p μ hm f, lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top,
    (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm⟩

end StronglyMeasurable

end LpMeas

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/


variable {m m0 : MeasurableSpace α} {μ : Measure α}

theorem lpMeas.ae_eq_zero_of_forall_set_integral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) : f =ᵐ[μ] 0 := by
  obtain ⟨g, hg_sm, hfg⟩ := Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine' hfg.trans _
  refine' ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
    
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
    

include 𝕜

theorem lp.ae_eq_zero_of_forall_set_integral_eq_zero' (hm : m ≤ m0) (f : lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = 0) (hf_meas : AeMeasurable' m f μ) :
    f =ᵐ[μ] 0 := by
  let f_meas : Lp_meas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by
    simp only [coe_fn_coe_base', Subtype.coe_mk]
  refine' hf_f_meas.trans _
  refine' Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integrable_on, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
    
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] f_meas := ae_restrict_of_ae hf_f_meas
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs
    

/-- **Uniqueness of the conditional expectation** -/
theorem lp.ae_eq_of_forall_set_integral_eq' (hm : m ≤ m0) (f g : lp E' p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hf_meas : AeMeasurable' m f μ) (hg_meas : AeMeasurable' m g μ) : f =ᵐ[μ] g := by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0
  · rw [← sub_ae_eq_zero]
    exact (Lp.coe_fn_sub f g).symm.trans h_sub
    
  have hfg' : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  have hfg_meas : ae_measurable' m (⇑(f - g)) μ := ae_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm
  exact Lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg' hfg_meas

omit 𝕜

theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {f g : α → F'}
    (hf_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂μ)
    (hfm : AeMeasurable' m f μ) (hgm : AeMeasurable' m g μ) : f =ᵐ[μ] g := by
  rw [← ae_eq_trim_iff_of_ae_measurable' hm hfm hgm]
  have hf_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hfm.measurable_mk
    exact integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite :
    ∀ s, measurable_set[m] s → μ.trim hm s < ∞ → @integrable_on _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [integrable_on, restrict_trim hm _ hs]
    refine' integrable.trim hm _ hgm.measurable_mk
    exact integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      measurable_set[m] s → μ.trim hm s < ∞ → (∫ x in s, hfm.mk f x ∂μ.trim hm) = ∫ x in s, hgm.mk g x ∂μ.trim hm :=
    by
    intro s hs hμs
    rw [trim_measurable_set_eq hm hs] at hμs
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.measurable_mk, ← integral_trim hm hgm.measurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm), integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

end UniquenessOfConditionalExpectation

section IntegralNormLe

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f s μ) (hg : measurable[m] g) (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫ x in s, ∥g x∥ ∂μ) ≤ ∫ x in s, ∥f x∥ ∂μ := by
  rw [integral_norm_eq_pos_sub_neg (hg.mono hm le_rfl) hgi, integral_norm_eq_pos_sub_neg hf hfi]
  have h_meas_nonneg_g : measurable_set[m] { x | 0 ≤ g x } :=
    @measurable_set_le _ α _ _ _ m _ _ _ _ g (@measurable_const _ α _ m _) hg
  have h_meas_nonneg_f : MeasurableSet { x | 0 ≤ f x } := measurable_set_le measurable_const hf
  have h_meas_nonpos_g : measurable_set[m] { x | g x ≤ 0 } :=
    @measurable_set_le _ α _ _ _ m _ _ _ g _ hg (@measurable_const _ α _ m _)
  have h_meas_nonpos_f : MeasurableSet { x | f x ≤ 0 } := measurable_set_le hf measurable_const
  refine' sub_le_sub _ _
  · rw [measure.restrict_restrict (hm _ h_meas_nonneg_g), measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonneg_g), ← measure.restrict_restrict h_meas_nonneg_f]
    exact set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
    
  · rw [measure.restrict_restrict (hm _ h_meas_nonpos_g), measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono (Set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← measure.restrict_restrict (hm _ h_meas_nonpos_g), ← measure.restrict_restrict h_meas_nonpos_f]
    exact set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi
    

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ∥g x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f s μ) (hg : measurable[m] g) (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫ x in t, g x ∂μ) = ∫ x in t, f x ∂μ) (hs : measurable_set[m] s)
    (hμs : μ s ≠ ∞) : (∫⁻ x in s, ∥g x∥₊ ∂μ) ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ := by
  rw [← of_real_integral_norm_eq_lintegral_nnnorm hfi, ← of_real_integral_norm_eq_lintegral_nnnorm hgi,
    Ennreal.of_real_le_of_real_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
    
  · exact integral_nonneg fun x => norm_nonneg _
    

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
    (have : Fact (m ≤ m0) := ⟨hm⟩
    inferInstance)

variable {𝕜}

theorem ae_measurable'_condexp_L2 (hm : m ≤ m0) (f : α →₂[μ] E) : AeMeasurable' m (condexpL2 𝕜 hm f) μ :=
  lpMeas.ae_measurable' _

theorem integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (condexpL2 𝕜 hm f) s μ :=
  integrable_on_Lp_of_measure_ne_top (condexpL2 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim hμs

theorem integrable_condexp_L2_of_is_finite_measure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (condexpL2 𝕜 hm f) μ :=
  integrable_on_univ.mp <| integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

theorem norm_condexp_L2_le_one (hm : m ≤ m0) : ∥@condexpL2 α E 𝕜 _ _ _ _ _ _ _ _ μ hm∥ ≤ 1 :=
  have : Fact (m ≤ m0) := ⟨hm⟩
  orthogonal_projection_norm_le _

theorem norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥condexpL2 𝕜 hm f∥ ≤ ∥f∥ :=
  ((@condexpL2 _ E 𝕜 _ _ _ _ _ _ _ _ μ hm).le_op_norm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

theorem snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : snorm (condexpL2 𝕜 hm f) 2 μ ≤ snorm f 2 μ := by
  rw [Lp_meas_coe, ← Ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ← Lp.norm_def, ← Lp.norm_def,
    Submodule.norm_coe]
  exact norm_condexp_L2_le hm f

theorem norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥(condexpL2 𝕜 hm f : α →₂[μ] E)∥ ≤ ∥f∥ := by
  rw [Lp.norm_def, Lp.norm_def, ← Lp_meas_coe]
  refine' (Ennreal.to_real_le_to_real _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f)
  exact Lp.snorm_ne_top _

theorem inner_condexp_L2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, (condexpL2 𝕜 hm g : α →₂[μ] E)⟫₂ :=
  have : Fact (m ≤ m0) := ⟨hm⟩
  inner_orthogonal_projection_left_eq_right _ f g

theorem condexp_L2_indicator_of_measurable (hm : m ≤ m0) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : E) :
    (condexpL2 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condexp_L2]
  have : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ := mem_Lp_meas_indicator_const_Lp hm hs hμs
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicator_const_Lp 2 (hm s hs) hμs c := by
    rfl
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]

theorem inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AeMeasurable' m g μ) :
    ⟪(condexpL2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ := by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2]
  simp only [mem_Lp_meas_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero]

section Real

variable {hm : m ≤ m0}

theorem integral_condexp_L2_eq_of_fin_meas_real (f : lp 𝕜 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicator_const_Lp_one (hm s hs) hμs]
  have h_eq_inner :
    (∫ x in s, condexp_L2 𝕜 hm f x ∂μ) = inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f) := by
    rw [L2.inner_indicator_const_Lp_one (hm s hs) hμs]
    congr
  rw [h_eq_inner, ← inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable hm hs hμs]

theorem lintegral_nnnorm_condexp_L2_le (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (f : lp ℝ 2 μ) :
    (∫⁻ x in s, ∥condexpL2 ℝ hm f x∥₊ ∂μ) ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ := by
  let h_meas := Lp_meas.ae_measurable' (condexp_L2 ℝ hm f)
  let g := h_meas.some
  have hg_meas : measurable[m] g := h_meas.some_spec.1
  have hg_eq : g =ᵐ[μ] condexp_L2 ℝ hm f := h_meas.some_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condexp_L2 ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (∥g x∥₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x => (∥condexp_L2 ℝ hm f x∥₊ : ℝ≥0∞) := by
    refine' hg_eq_restrict.mono fun x hx => _
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine' lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.measurable f) _ _ _ _ hs hμs
  · exact integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
    
  · exact hg_meas
    
  · rw [integrable_on, integrable_congr hg_eq_restrict]
    exact integrable_on_condexp_L2_of_measure_ne_top hm hμs f
    
  · intro t ht hμt
    rw [← integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne]
    exact set_integral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
    

theorem condexp_L2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {f : lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condexpL2 ℝ hm f =ᵐ[μ.restrict s] 0 := by
  suffices h_nnnorm_eq_zero : (∫⁻ x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ) = 0
  · rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    refine' h_nnnorm_eq_zero.mono fun x hx => _
    dsimp only  at hx
    rw [Pi.zero_apply] at hx⊢
    · rwa [Ennreal.coe_eq_zero, nnnorm_eq_zero] at hx
      
    · refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
      rw [Lp_meas_coe]
      exact Lp.measurable _
      
    
  refine' le_antisymmₓ _ (zero_le _)
  refine' (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eqₓ _)
  rw [lintegral_eq_zero_iff]
  · refine' hf.mono fun x hx => _
    dsimp only
    rw [hx]
    simp
    
  · exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal
    

theorem lintegral_nnnorm_condexp_L2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : measurable_set[m] t)
    (hμt : μ t ≠ ∞) : (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) ≤ μ (s ∩ t) := by
  refine' (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eqₓ _)
  have h_eq :
    (∫⁻ x in t, ∥(indicator_const_Lp 2 hs hμs (1 : ℝ)) x∥₊ ∂μ) = ∫⁻ x in t, s.indicator (fun x => (1 : ℝ≥0∞)) x ∂μ := by
    refine' lintegral_congr_ae (ae_restrict_of_ae _)
    refine' (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ _ hs hμs (1 : ℝ) _ _).mono fun x hx => _
    rw [hx]
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator _ hs, lintegral_const, measure.restrict_restrict hs]
  simp only [one_mulₓ, Set.univ_inter, MeasurableSet.univ, measure.restrict_apply]

end Real

/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
theorem condexp_L2_const_inner (hm : m ≤ m0) (f : lp E 2 μ) (c : E) :
    condexpL2 𝕜 hm (((lp.mem_ℒp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ] fun a => ⟪c, condexpL2 𝕜 hm f a⟫ := by
  rw [Lp_meas_coe]
  have h_mem_Lp : mem_ℒp (fun a => ⟪c, condexp_L2 𝕜 hm f a⟫) 2 μ := by
    refine' mem_ℒp.const_inner _ _
    rw [Lp_meas_coe]
    exact Lp.mem_ℒp _
  have h_eq : h_mem_Lp.to_Lp _ =ᵐ[μ] fun a => ⟪c, condexp_L2 𝕜 hm f a⟫ := h_mem_Lp.coe_fn_to_Lp
  refine' eventually_eq.trans _ h_eq
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _) _ _ _ _
  · intro s hs hμs
    rw [integrable_on, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _
    
  · intro s hs hμs
    rw [← Lp_meas_coe, integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne, integral_congr_ae (ae_restrict_of_ae h_eq),
      Lp_meas_coe, ← L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 (↑(condexp_L2 𝕜 hm f)) (hm s hs) c hμs.ne, ←
      inner_condexp_L2_left_eq_right, condexp_L2_indicator_of_measurable,
      L2.inner_indicator_const_Lp_eq_set_integral_inner 𝕜 f (hm s hs) c hμs.ne,
      set_integral_congr_ae (hm s hs) ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono fun x hx hxs => hx)]
    
  · rw [← Lp_meas_coe]
    exact Lp_meas.ae_measurable' _
    
  · refine' ae_measurable'.congr _ h_eq.symm
    exact (Lp_meas.ae_measurable' _).const_inner _
    

/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexp_L2_eq (hm : m ≤ m0) (f : lp E' 2 μ) (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL2 𝕜 hm f x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero, Lp_meas_coe, ←
    integral_sub' (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine' integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub (↑(condexp_L2 𝕜 hm f)) f).symm)]
    exact integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
    
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw
    [integral_sub ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)
  rw [← Lp_meas_coe, sub_eq_zero, ←
    set_integral_congr_ae (hm s hs) ((condexp_L2_const_inner hm f c).mono fun x hx _ => hx), ←
    set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condexp_L2_eq_of_fin_meas_real _ hs hμs

variable {E'' 𝕜' : Type _} [IsROrC 𝕜'] [MeasurableSpace E''] [InnerProductSpace 𝕜' E''] [BorelSpace E'']
  [SecondCountableTopology E''] [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')

theorem condexp_L2_comp_continuous_linear_map (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condexpL2 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ] T.compLp (condexpL2 𝕜 hm f : α →₂[μ] E') := by
  refine'
    Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm Ennreal.coe_ne_top
      (fun s hs hμs => integrable_on_condexp_L2_of_measure_ne_top hm hμs.Ne _)
      (fun s hs hμs => integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.Ne) _ _ _
  · intro s hs hμs
    rw [T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne), ← Lp_meas_coe, ←
      Lp_meas_coe, integral_condexp_L2_eq hm f hs hμs.ne, integral_condexp_L2_eq hm (T.comp_Lp f) hs hμs.ne,
      T.set_integral_comp_Lp _ (hm s hs),
      T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
    
  · rw [← Lp_meas_coe]
    exact Lp_meas.ae_measurable' _
    
  · have h_coe := T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : α →₂[μ] E')
    rw [← eventually_eq] at h_coe
    refine' ae_measurable'.congr _ h_coe.symm
    exact (Lp_meas.ae_measurable' (condexp_L2 𝕜 hm f)).measurable_comp T.measurable
    

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

theorem condexp_L2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  by
  rw [indicator_const_Lp_eq_to_span_singleton_comp_Lp hs hμs x]
  have h_comp :=
    condexp_L2_comp_continuous_linear_map ℝ 𝕜 hm (to_span_singleton ℝ x) (indicator_const_Lp 2 hs hμs (1 : ℝ))
  rw [← Lp_meas_coe] at h_comp
  refine' h_comp.trans _
  exact (to_span_singleton ℝ x).coe_fn_comp_Lp _

theorem condexp_L2_indicator_eq_to_span_singleton_comp (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
      (toSpanSingleton ℝ x).compLp (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ))) :=
  by
  ext1
  rw [← Lp_meas_coe]
  refine' (condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _
  have h_comp :=
    (to_span_singleton ℝ x).coe_fn_comp_Lp (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) : α →₂[μ] ℝ)
  rw [← eventually_eq] at h_comp
  refine' eventually_eq.trans _ h_comp.symm
  refine' eventually_of_forall fun y => _
  rfl

variable {𝕜}

theorem set_lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
    {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) ≤ μ (s ∩ t) * ∥x∥₊ :=
  calc
    (∫⁻ a in t, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) =
        ∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha hat => by
          rw [ha])
    _ = (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) * ∥x∥₊ := by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal
    _ ≤ μ (s ∩ t) * ∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
    [SigmaFinite (μ.trim hm)] : (∫⁻ a, ∥condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x) a∥₊ ∂μ) ≤ μ s * ∥x∥₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ fun t ht hμt => _
  · rw [Lp_meas_coe]
    exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal
    
  refine' (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_L2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') : Integrable (condexpL2 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine' integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · rw [Lp_meas_coe]
    exact Lp.ae_measurable _
    
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
    

end CondexpL2Indicator

section CondexpIndSmul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
def condexpIndSmul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) : lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))

theorem ae_measurable'_condexp_ind_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AeMeasurable' m (condexpIndSmul hm hs hμs x) μ := by
  have h : ae_measurable' m (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ := ae_measurable'_condexp_L2 _ _
  rw [condexp_ind_smul]
  suffices ae_measurable' m (to_span_singleton ℝ x ∘ condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))) μ by
    refine' ae_measurable'.congr this _
    refine' eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm
    rw [Lp_meas_coe]
  exact ae_measurable'.measurable_comp (to_span_singleton ℝ x).Measurable h

theorem condexp_ind_smul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndSmul hm hs hμs (x + y) = condexpIndSmul hm hs hμs x + condexpIndSmul hm hs hμs y := by
  simp_rw [condexp_ind_smul]
  rw [to_span_singleton_add, add_comp_LpL, add_apply]

theorem condexp_ind_smul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  simp_rw [condexp_ind_smul]
  rw [to_span_singleton_smul, smul_comp_LpL, smul_apply]

theorem condexp_ind_smul_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
    (x : F) : condexpIndSmul hm hs hμs (c • x) = c • condexpIndSmul hm hs hμs x := by
  rw [condexp_ind_smul, condexp_ind_smul, to_span_singleton_smul',
    (to_span_singleton ℝ x).smul_comp_LpL_apply c ↑(condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))]

theorem condexp_ind_smul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndSmul hm hs hμs x =ᵐ[μ] fun a => condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x :=
  (toSpanSingleton ℝ x).coe_fn_comp_LpL _

theorem set_lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
    {t : Set α} (ht : measurable_set[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) ≤ μ (s ∩ t) * ∥x∥₊ :=
  calc
    (∫⁻ a in t, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) =
        ∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
      set_lintegral_congr_fun (hm t ht)
        ((condexp_ind_smul_ae_eq_smul hm hs hμs x).mono fun a ha hat => by
          rw [ha])
    _ = (∫⁻ a in t, ∥condexpL2 ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ) * ∥x∥₊ := by
      simp_rw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal
    _ ≤ μ (s ∩ t) * ∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
    [SigmaFinite (μ.trim hm)] : (∫⁻ a, ∥condexpIndSmul hm hs hμs x a∥₊ ∂μ) ≤ μ s * ∥x∥₊ := by
  refine' lintegral_le_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) _ fun t ht hμt => _
  · exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal
    
  refine' (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
  refine' Ennreal.mul_le_mul _ le_rfl
  exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : Integrable (condexpIndSmul hm hs hμs x) μ := by
  refine' integrable_of_forall_fin_meas_le' hm (μ s * ∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
  · exact Lp.ae_measurable _
    
  · refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _
    exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl
    

theorem condexp_ind_smul_empty {x : G} :
    condexpIndSmul hm MeasurableSet.empty ((@measure_empty _ _ μ).le.trans_lt Ennreal.coe_lt_top).Ne x = 0 := by
  rw [condexp_ind_smul, indicator_const_empty]
  simp only [coe_fn_coe_base, Submodule.coe_zero, ContinuousLinearMap.map_zero]

theorem set_integral_condexp_ind_smul (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (x : G') : (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, (condexpIndSmul hm ht hμt x) a ∂μ) =
        ∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a • x ∂μ :=
      set_integral_congr_ae (hm s hs) ((condexp_ind_smul_ae_eq_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (∫ a in s, condexpL2 ℝ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) a ∂μ) • x := integral_smul_const _ x
    _ = (∫ a in s, indicatorConstLp 2 ht hμt (1 : ℝ) a ∂μ) • x := by
      rw [@integral_condexp_L2_eq α _ ℝ _ _ _ _ _ _ _ _ _ _ _ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) hs hμs]
    _ = (μ (t ∩ s)).toReal • x := by
      rw [set_integral_indicator_const_Lp (hm s hs), smul_assoc, one_smul]
    

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
def condexpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    α →₁[μ] G :=
  (integrable_condexp_ind_smul hm hs hμs x).toL1 _

theorem condexp_ind_L1_fin_ae_eq_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : condexpIndL1Fin hm hs hμs x =ᵐ[μ] condexpIndSmul hm hs hμs x :=
  (integrable_condexp_ind_smul hm hs hμs x).coe_fn_to_L1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexp_ind_L1_fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condexpIndL1Fin hm hs hμs (x + y) = condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm hs hμs y := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine' eventually_eq.trans _ (eventually_eq.add (mem_ℒp.coe_fn_to_Lp _).symm (mem_ℒp.coe_fn_to_Lp _).symm)
  rw [condexp_ind_smul_add]
  refine' (Lp.coe_fn_add _ _).trans (eventually_of_forall fun a => _)
  rfl

theorem condexp_ind_L1_fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]

theorem condexp_ind_L1_fin_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
    (x : F) : condexpIndL1Fin hm hs hμs (c • x) = c • condexpIndL1Fin hm hs hμs x := by
  ext1
  refine' (mem_ℒp.coe_fn_to_Lp _).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  rw [condexp_ind_smul_smul' hs hμs c x]
  refine' (Lp.coe_fn_smul _ _).trans _
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _
  rw [Pi.smul_apply, Pi.smul_apply, hy]

theorem norm_condexp_ind_L1_fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ∥condexpIndL1Fin hm hs hμs x∥ ≤ (μ s).toReal * ∥x∥ := by
  have : 0 ≤ ∫ a : α, ∥condexp_ind_L1_fin hm hs hμs x a∥ ∂μ := integral_nonneg fun a => norm_nonneg _
  rw [L1.norm_eq_integral_norm, ← Ennreal.to_real_of_real (norm_nonneg x), ← Ennreal.to_real_mul, ←
    Ennreal.to_real_of_real this,
    Ennreal.to_real_le_to_real Ennreal.of_real_ne_top (Ennreal.mul_ne_top hμs Ennreal.of_real_ne_top),
    of_real_integral_norm_eq_lintegral_nnnorm]
  swap
  · rw [← mem_ℒp_one_iff_integrable]
    exact Lp.mem_ℒp _
    
  have h_eq : (∫⁻ a, ∥condexp_ind_L1_fin hm hs hμs x a∥₊ ∂μ) = ∫⁻ a, nnnorm (condexp_ind_smul hm hs hμs x a) ∂μ := by
    refine' lintegral_congr_ae _
    refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun z hz => _
    dsimp only
    rw [hz]
  rw [h_eq, of_real_norm_eq_coe_nnnorm]
  exact lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x

theorem condexp_ind_L1_fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) :
    condexpIndL1Fin hm (hs.union ht)
        ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (Ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne x =
      condexpIndL1Fin hm hs hμs x + condexpIndL1Fin hm ht hμt x :=
  by
  ext1
  have hμst := ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm (hs.union ht) hμst x).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  have hs_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x
  have ht_eq := condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm ht hμt x
  refine' eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm)
  rw [condexp_ind_smul]
  rw [indicator_const_Lp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [(condexp_L2 ℝ hm).map_add]
  push_cast
  rw [((to_span_singleton ℝ x).compLpL 2 μ).map_add]
  refine' (Lp.coe_fn_add _ _).trans _
  refine' eventually_of_forall fun y => _
  rfl

end CondexpIndL1Fin

open_locale Classical

section CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexpIndL1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) (s : Set α) [SigmaFinite (μ.trim hm)]
    (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexpIndL1Fin hm hs.1 hs.2 x else 0

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condexpIndL1 hm μ s x = condexpIndL1Fin hm hs hμs x := by
  simp only [condexp_ind_L1, And.intro hs hμs, dif_pos, Ne.def, not_false_iff, and_selfₓ]

theorem condexp_ind_L1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexp_ind_L1, hμs, eq_self_iff_true, not_true, Ne.def, dif_neg, not_false_iff, and_falseₓ]

theorem condexp_ind_L1_of_not_measurable_set (hs : ¬MeasurableSet s) (x : G) : condexpIndL1 hm μ s x = 0 := by
  simp only [condexp_ind_L1, hs, dif_neg, not_false_iff, false_andₓ]

theorem condexp_ind_L1_add (x y : G) : condexpIndL1 hm μ s (x + y) = condexpIndL1 hm μ s x + condexpIndL1 hm μ s y := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [zero_addₓ]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [zero_addₓ]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_add hs hμs x y
    

theorem condexp_ind_L1_smul (c : ℝ) (x : G) : condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [smul_zero]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [smul_zero]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul hs hμs c x
    

theorem condexp_ind_L1_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpIndL1 hm μ s (c • x) = c • condexpIndL1 hm μ s x := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [smul_zero]
    
  by_cases' hμs : μ s = ∞
  · simp_rw [condexp_ind_L1_of_measure_eq_top hμs]
    rw [smul_zero]
    
  · simp_rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
    exact condexp_ind_L1_fin_smul' hs hμs c x
    

theorem norm_condexp_ind_L1_le (x : G) : ∥condexpIndL1 hm μ s x∥ ≤ (μ s).toReal * ∥x∥ := by
  by_cases' hs : MeasurableSet s
  swap
  · simp_rw [condexp_ind_L1_of_not_measurable_set hs]
    rw [Lp.norm_zero]
    exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    
  by_cases' hμs : μ s = ∞
  · rw [condexp_ind_L1_of_measure_eq_top hμs x, Lp.norm_zero]
    exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    
  · rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x]
    exact norm_condexp_ind_L1_fin_le hs hμs x
    

theorem continuous_condexp_ind_L1 : Continuous fun x : G => condexpIndL1 hm μ s x :=
  continuous_of_linear_of_bound condexp_ind_L1_add condexp_ind_L1_smul norm_condexp_ind_L1_le

theorem condexp_ind_L1_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) : condexpIndL1 hm μ (s ∪ t) x = condexpIndL1 hm μ s x + condexpIndL1 hm μ t x := by
  have hμst : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
  rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top ht hμt x,
    condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs.union ht) hμst x]
  exact condexp_ind_L1_fin_disjoint_union hs ht hμs hμt hst x

end CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexpInd {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (s : Set α) :
    G →L[ℝ] α →₁[μ] G where
  toFun := condexpIndL1 hm μ s
  map_add' := condexp_ind_L1_add
  map_smul' := condexp_ind_L1_smul
  cont := continuous_condexp_ind_L1

theorem condexp_ind_ae_eq_condexp_ind_smul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : condexpInd hm μ s x =ᵐ[μ] condexpIndSmul hm hs hμs x := by
  refine' eventually_eq.trans _ (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x)
  simp [condexp_ind, condexp_ind_L1, hs, hμs]

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem ae_measurable'_condexp_ind (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AeMeasurable' m (condexpInd hm μ s x) μ :=
  AeMeasurable'.congr (ae_measurable'_condexp_ind_smul hm hs hμs x)
    (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm

@[simp]
theorem condexp_ind_empty : condexpInd hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext1
  ext1
  refine'
    (condexp_ind_ae_eq_condexp_ind_smul hm MeasurableSet.empty
          (by
            simp )
          x).trans
      _
  rw [condexp_ind_smul_empty]
  refine' (Lp.coe_fn_zero G 2 μ).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_zero G 1 μ).symm
  rfl

theorem condexp_ind_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
    condexpInd hm μ s (c • x) = c • condexpInd hm μ s x :=
  condexp_ind_L1_smul' c x

theorem norm_condexp_ind_apply_le (x : G) : ∥condexpInd hm μ s x∥ ≤ (μ s).toReal * ∥x∥ :=
  norm_condexp_ind_L1_le x

theorem norm_condexp_ind_le : ∥(condexpInd hm μ s : G →L[ℝ] α →₁[μ] G)∥ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ Ennreal.to_real_nonneg norm_condexp_ind_apply_le

theorem condexp_ind_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) (x : G) : condexpInd hm μ (s ∪ t) x = condexpInd hm μ s x + condexpInd hm μ t x :=
  condexp_ind_L1_disjoint_union hs ht hμs hμt hst x

theorem condexp_ind_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : s ∩ t = ∅) : (condexpInd hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexpInd hm μ s + condexpInd hm μ t := by
  ext1
  push_cast
  exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x

variable (G)

theorem dominated_fin_meas_additive_condexp_ind (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (condexpInd hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun s t => condexp_ind_disjoint_union, fun s _ _ => norm_condexp_ind_le.trans (one_mulₓ _).symm.le⟩

variable {G}

theorem set_integral_condexp_ind (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (x : G') : (∫ a in s, condexpInd hm μ t x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫ a in s, condexpInd hm μ t x a ∂μ) = ∫ a in s, condexpIndSmul hm ht hμt x a ∂μ :=
      set_integral_congr_ae (hm s hs) ((condexp_ind_ae_eq_condexp_ind_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexp_ind_smul hs ht hμs hμt x
    

theorem condexp_ind_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
    condexpInd hm μ s c = indicatorConstLp 1 (hm s hs) hμs c := by
  ext1
  refine' eventually_eq.trans _ indicator_const_Lp_coe_fn.symm
  refine' (condexp_ind_ae_eq_condexp_ind_smul hm (hm s hs) hμs c).trans _
  refine' (condexp_ind_smul_ae_eq_smul hm (hm s hs) hμs c).trans _
  rw [Lp_meas_coe, condexp_L2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  refine' (@indicator_const_Lp_coe_fn α _ _ 2 μ _ _ s (hm s hs) hμs (1 : ℝ) _ _).mono fun x hx => _
  dsimp only
  rw [hx]
  by_cases' hx_mem : x ∈ s <;> simp [hx_mem]

end CondexpInd

section CondexpL1

variable {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)] {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexpL1Clm (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] : (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominated_fin_meas_additive_condexp_ind F' hm μ)

theorem condexp_L1_clm_smul (c : 𝕜) (f : α →₁[μ] F') : condexpL1Clm hm μ (c • f) = c • condexpL1Clm hm μ f :=
  L1.set_to_L1_smul (dominated_fin_meas_additive_condexp_ind F' hm μ) (fun c s x => condexp_ind_smul' c x) c f

theorem condexp_L1_clm_indicator_const_Lp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) (indicatorConstLp 1 hs hμs x) = condexpInd hm μ s x :=
  L1.set_to_L1_indicator_const_Lp (dominated_fin_meas_additive_condexp_ind F' hm μ) hs hμs x

theorem condexp_L1_clm_indicator_const (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condexpL1Clm hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) = condexpInd hm μ s x := by
  rw [Lp.simple_func.coe_indicator_const]
  exact condexp_L1_clm_indicator_const_Lp hs hμs x

/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
theorem set_integral_condexp_L1_clm_of_measure_ne_top (f : α →₁[μ] F') (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) :
    (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  refine'
    Lp.induction Ennreal.one_ne_top (fun f : α →₁[μ] F' => (∫ x in s, condexp_L1_clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ) _
      _ (is_closed_eq _ _) f
  · intro x t ht hμt
    simp_rw [condexp_L1_clm_indicator_const ht hμt.ne x]
    rw [Lp.simple_func.coe_indicator_const, set_integral_indicator_const_Lp (hm _ hs)]
    exact set_integral_condexp_ind hs ht hμs hμt.ne x
    
  · intro f g hf_Lp hg_Lp hfg_disj hf hg
    simp_rw [(condexp_L1_clm hm μ).map_add]
    rw
      [set_integral_congr_ae (hm s hs)
        ((Lp.coe_fn_add (condexp_L1_clm hm μ (hf_Lp.to_Lp f)) (condexp_L1_clm hm μ (hg_Lp.to_Lp g))).mono
          fun x hx hxs => hx)]
    rw [set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono fun x hx hxs => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn,
      integral_add (L1.integrable_coe_fn _).IntegrableOn (L1.integrable_coe_fn _).IntegrableOn, hf, hg]
    
  · exact (continuous_set_integral s).comp (condexp_L1_clm hm μ).Continuous
    
  · exact continuous_set_integral s
    

/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1_clm (f : α →₁[μ] F') (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1Clm hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  let S := spanning_sets (μ.trim hm)
  have hS_meas : ∀ i, measurable_set[m] (S i) := measurable_spanning_sets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm _ (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_Union, Union_spanning_sets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine' fun i => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have hS_finite_trim := measure_spanning_sets_lt_top (μ.trim hm) i
    rwa [trim_measurable_set_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanning_sets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall : (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      set_integral_condexp_L1_clm_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs) (hS_finite i).Ne
  have h_right : tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) at_top (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn f).IntegrableOn
    rwa [← hs_eq] at h
  have h_left :
    tendsto (fun i => ∫ x in S i ∩ s, condexp_L1_clm hm μ f x ∂μ) at_top (𝓝 (∫ x in s, condexp_L1_clm hm μ f x ∂μ)) :=
    by
    have h :=
      tendsto_set_integral_of_monotone (fun i => (hS_meas0 i).inter (hm s hs)) h_mono
        (L1.integrable_coe_fn (condexp_L1_clm hm μ f)).IntegrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

theorem ae_measurable'_condexp_L1_clm (f : α →₁[μ] F') : AeMeasurable' m (condexpL1Clm hm μ f) μ := by
  refine' Lp.induction Ennreal.one_ne_top (fun f : α →₁[μ] F' => ae_measurable' m (condexp_L1_clm hm μ f) μ) _ _ _ f
  · intro c s hs hμs
    rw [condexp_L1_clm_indicator_const hs hμs.ne c]
    exact ae_measurable'_condexp_ind hs hμs.ne c
    
  · intro f g hf hg h_disj hfm hgm
    rw [(condexp_L1_clm hm μ).map_add]
    refine' ae_measurable'.congr _ (coe_fn_add _ _).symm
    exact ae_measurable'.add hfm hgm
    
  · have :
      { f : Lp F' 1 μ | ae_measurable' m (condexp_L1_clm hm μ f) μ } =
        condexp_L1_clm hm μ ⁻¹' { f | ae_measurable' m f μ } :=
      by
      rfl
    rw [this]
    refine' IsClosed.preimage (condexp_L1_clm hm μ).Continuous _
    exact is_closed_ae_measurable' hm
    

theorem Lp_meas_to_Lp_trim_lie_symm_indicator [NormedSpace ℝ F] {μ : Measure α} (hs : measurable_set[m] s)
    (hμs : μ.trim hm s ≠ ∞) (c : F) :
    ((lpMeasToLpTrimLie F ℝ 1 μ hm).symm (indicatorConstLp 1 hs hμs c) : α →₁[μ] F) =
      indicatorConstLp 1 (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).Ne c :=
  by
  ext1
  rw [← Lp_meas_coe]
  change Lp_trim_to_Lp_meas F ℝ 1 μ hm (indicator_const_Lp 1 hs hμs c) =ᵐ[μ] (indicator_const_Lp 1 _ _ c : α → F)
  refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _
  exact (ae_eq_of_ae_eq_trim indicator_const_Lp_coe_fn).trans indicator_const_Lp_coe_fn.symm

theorem condexp_L1_clm_Lp_meas (f : lpMeas F' ℝ m 1 μ) : condexpL1Clm hm μ (f : α →₁[μ] F') = ↑f := by
  let g := Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm f
  have hfg : f = (Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g := by
    simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine'
    @Lp.induction α F' m _ _ _ _ 1 (μ.trim hm) _ Ennreal.coe_ne_top
      (fun g : α →₁[μ.trim hm] F' =>
        condexp_L1_clm hm μ ((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
          ↑((Lp_meas_to_Lp_trim_lie F' ℝ 1 μ hm).symm g))
      _ _ _ g
  · intro c s hs hμs
    rw [Lp.simple_func.coe_indicator_const, Lp_meas_to_Lp_trim_lie_symm_indicator hs hμs.ne c,
      condexp_L1_clm_indicator_const_Lp]
    exact condexp_ind_of_measurable hs ((le_trim hm).trans_lt hμs).Ne c
    
  · intro f g hf hg hfg_disj hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
    
  · refine' is_closed_eq _ _
    · refine' (condexp_L1_clm hm μ).Continuous.comp (continuous_induced_dom.comp _)
      exact LinearIsometryEquiv.continuous _
      
    · refine' continuous_induced_dom.comp _
      exact LinearIsometryEquiv.continuous _
      
    

theorem condexp_L1_clm_of_ae_measurable' (f : α →₁[μ] F') (hfm : AeMeasurable' m f μ) : condexpL1Clm hm μ f = f :=
  condexp_L1_clm_Lp_meas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexpL1 (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  setToFun μ (condexpInd hm μ) (dominated_fin_meas_additive_condexp_ind F' hm μ) f

theorem condexp_L1_undef (hf : ¬Integrable f μ) : condexpL1 hm μ f = 0 :=
  set_to_fun_undef (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_eq (hf : Integrable f μ) : condexpL1 hm μ f = condexpL1Clm hm μ (hf.toL1 f) :=
  set_to_fun_eq (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_zero : condexpL1 hm μ (0 : α → F') = 0 :=
  set_to_fun_zero _

theorem ae_measurable'_condexp_L1 {f : α → F'} : AeMeasurable' m (condexpL1 hm μ f) μ := by
  by_cases' hf : integrable f μ
  · rw [condexp_L1_eq hf]
    exact ae_measurable'_condexp_L1_clm _
    
  · rw [condexp_L1_undef hf]
    refine' ae_measurable'.congr _ (coe_fn_zero _ _ _).symm
    exact measurable.ae_measurable' (@measurable_zero _ _ m _ _)
    

theorem integrable_condexp_L1 (f : α → F') : Integrable (condexpL1 hm μ f) μ :=
  L1.integrable_coe_fn _

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1 (hf : Integrable f μ) (hs : measurable_set[m] s) :
    (∫ x in s, condexpL1 hm μ f x ∂μ) = ∫ x in s, f x ∂μ := by
  simp_rw [condexp_L1_eq hf]
  rw [set_integral_condexp_L1_clm (hf.to_L1 f) hs]
  exact set_integral_congr_ae (hm s hs) (hf.coe_fn_to_L1.mono fun x hx hxs => hx)

theorem condexp_L1_add (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f + g) = condexpL1 hm μ f + condexpL1 hm μ g :=
  set_to_fun_add _ hf hg

theorem condexp_L1_neg (f : α → F') : condexpL1 hm μ (-f) = -condexpL1 hm μ f :=
  set_to_fun_neg _ f

theorem condexp_L1_smul (c : 𝕜) (f : α → F') : condexpL1 hm μ (c • f) = c • condexpL1 hm μ f :=
  set_to_fun_smul _ (fun c _ x => condexp_ind_smul' c x) c f

theorem condexp_L1_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    condexpL1 hm μ (f - g) = condexpL1 hm μ f - condexpL1 hm μ g :=
  set_to_fun_sub _ hf hg

theorem condexp_L1_of_ae_measurable' (hfm : AeMeasurable' m f μ) (hfi : Integrable f μ) : condexpL1 hm μ f =ᵐ[μ] f := by
  rw [condexp_L1_eq hfi]
  refine' eventually_eq.trans _ (integrable.coe_fn_to_L1 hfi)
  rw [condexp_L1_clm_of_ae_measurable']
  exact ae_measurable'.congr hfm (integrable.coe_fn_to_L1 hfi).symm

end CondexpL1

section Condexp

/-! ### Conditional expectation of a function -/


open_locale Classical

variable {𝕜} {m m0 : MeasurableSpace α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)] {f g : α → F'}
  {s : Set α}

variable (m)

/-- Conditional expectation of a function. Its value is 0 if the function is not integrable. -/
irreducible_def condexp (hm : m ≤ m0) (μ : Measure α) [SigmaFinite (μ.trim hm)] (f : α → F') : α → F' :=
  if measurable[m] f ∧ Integrable f μ then f else ae_measurable'_condexp_L1.mk (condexpL1 hm μ f)

variable {m}

-- mathport name: «expr [ | ]»
-- We define notations `μ[f|hm]` and `μ[f|m,hm]` for the conditional expectation of `f` with
-- respect to `m`. Both can be used in code but only the second one will be used by the goal view.
-- The first notation avoids the repetition of `m`, which is already present in `hm`. The second
-- one ensures that `m` stays visible in the goal view: when `hm` is complicated, it gets rendered
-- as `_` and the measurable space would not be visible in `μ[f|_]`, but is clear in `μ[f|m,_]`.
localized [MeasureTheory] notation μ "[" f "|" hm "]" => MeasureTheory.condexp _ hm μ f

-- mathport name: «expr [ | , ]»
localized [MeasureTheory] notation μ "[" f "|" m "," hm "]" => MeasureTheory.condexp m hm μ f

theorem condexp_of_measurable {f : α → F'} (hf : measurable[m] f) (hfi : Integrable f μ) : μ[f|m,hm] = f := by
  rw [condexp, if_pos (⟨hf, hfi⟩ : measurable[m] f ∧ integrable f μ)]

theorem condexp_const (c : F') [IsFiniteMeasure μ] : μ[fun x : α => c|m,hm] = fun _ => c :=
  condexp_of_measurable (@measurable_const _ _ _ m _) (integrable_const c)

theorem condexp_ae_eq_condexp_L1 (f : α → F') : μ[f|m,hm] =ᵐ[μ] condexpL1 hm μ f := by
  unfold condexp
  by_cases' hfm : measurable[m] f
  · by_cases' hfi : integrable f μ
    · rw [if_pos (⟨hfm, hfi⟩ : measurable[m] f ∧ integrable f μ)]
      exact (condexp_L1_of_ae_measurable' (measurable.ae_measurable' hfm) hfi).symm
      
    · simp only [hfi, if_false, and_falseₓ]
      exact (ae_measurable'.ae_eq_mk ae_measurable'_condexp_L1).symm
      
    
  simp only [hfm, if_false, false_andₓ]
  exact (ae_measurable'.ae_eq_mk ae_measurable'_condexp_L1).symm

theorem condexp_ae_eq_condexp_L1_clm (hf : Integrable f μ) : μ[f|m,hm] =ᵐ[μ] condexpL1Clm hm μ (hf.toL1 f) := by
  refine' (condexp_ae_eq_condexp_L1 f).trans (eventually_of_forall fun x => _)
  rw [condexp_L1_eq hf]

theorem condexp_undef (hf : ¬Integrable f μ) : μ[f|m,hm] =ᵐ[μ] 0 := by
  refine' (condexp_ae_eq_condexp_L1 f).trans (eventually_eq.trans _ (coe_fn_zero _ 1 _))
  rw [condexp_L1_undef hf]

@[simp]
theorem condexp_zero : μ[(0 : α → F')|m,hm] = 0 :=
  condexp_of_measurable (@measurable_zero _ _ m _ _) (integrable_zero _ _ _)

theorem measurable_condexp : measurable[m] (μ[f|m,hm]) := by
  unfold condexp
  by_cases' hfm : measurable[m] f
  · by_cases' hfi : integrable f μ
    · rwa [if_pos (⟨hfm, hfi⟩ : measurable[m] f ∧ integrable f μ)]
      
    · simp only [hfi, if_false, and_falseₓ]
      exact ae_measurable'.measurable_mk _
      
    
  simp only [hfm, if_false, false_andₓ]
  exact ae_measurable'.measurable_mk _

theorem integrable_condexp : Integrable (μ[f|m,hm]) μ :=
  (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 f).symm

variable (hm)

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem set_integral_condexp (hf : Integrable f μ) (hs : measurable_set[m] s) :
    (∫ x in s, (μ[f|m,hm]) x ∂μ) = ∫ x in s, f x ∂μ := by
  rw [set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 f).mono fun x hx _ => hx)]
  exact set_integral_condexp_L1 hf hs

variable {hm}

theorem integral_condexp (hf : Integrable f μ) : (∫ x, (μ[f|m,hm]) x ∂μ) = ∫ x, f x ∂μ := by
  suffices (∫ x in Set.Univ, (μ[f|m,hm]) x ∂μ) = ∫ x in Set.Univ, f x ∂μ by
    simp_rw [integral_univ]  at this
    exact this
  exact set_integral_condexp hm hf (@MeasurableSet.univ _ m)

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {f g : α → F'}
    (hf : Integrable f μ) (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → (∫ x in s, g x ∂μ) = ∫ x in s, f x ∂μ)
    (hgm : AeMeasurable' m g μ) : g =ᵐ[μ] μ[f|m,hm] := by
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => _) hgm (measurable.ae_measurable' measurable_condexp)
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs]

theorem condexp_add (hf : Integrable f μ) (hg : Integrable g μ) : μ[f + g|m,hm] =ᵐ[μ] μ[f|m,hm] + μ[g|m,hm] := by
  refine' (condexp_ae_eq_condexp_L1 _).trans _
  rw [condexp_L1_add hf hg]
  exact (coe_fn_add _ _).trans ((condexp_ae_eq_condexp_L1 _).symm.add (condexp_ae_eq_condexp_L1 _).symm)

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|m,hm] =ᵐ[μ] c • μ[f|m,hm] := by
  refine' (condexp_ae_eq_condexp_L1 _).trans _
  rw [condexp_L1_smul c f]
  refine' (@condexp_ae_eq_condexp_L1 _ _ _ _ _ _ _ _ m _ _ hm _ f).mp _
  refine' (coe_fn_smul c (condexp_L1 hm μ f)).mono fun x hx1 hx2 => _
  rw [hx1, Pi.smul_apply, Pi.smul_apply, hx2]

theorem condexp_neg (f : α → F') : μ[-f|m,hm] =ᵐ[μ] -μ[f|m,hm] := by
  let this' : Module ℝ (α → F') := @Pi.module α (fun _ => F') ℝ _ _ fun _ => inferInstance <;>
    calc μ[-f|m,hm] = μ[(-1 : ℝ) • f|m,hm] := by
        rw [neg_one_smul ℝ f]_ =ᵐ[μ] (-1 : ℝ) • μ[f|m,hm] := condexp_smul (-1) f _ = -μ[f|m,hm] :=
        neg_one_smul ℝ (μ[f|m,hm])

theorem condexp_sub (hf : Integrable f μ) (hg : Integrable g μ) : μ[f - g|m,hm] =ᵐ[μ] μ[f|m,hm] - μ[g|m,hm] := by
  simp_rw [sub_eq_add_neg]
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g))

theorem condexp_condexp_of_le {m₁ m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0)
    [SigmaFinite (μ.trim (hm₁₂.trans hm₂))] [SigmaFinite (μ.trim hm₂)] :
    μ[μ[f|m₂,hm₂]|m₁,hm₁₂.trans hm₂] =ᵐ[μ] μ[f|m₁,hm₁₂.trans hm₂] := by
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂) (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => integrable_condexp.integrable_on) _ (measurable.ae_measurable' measurable_condexp)
      (measurable.ae_measurable' measurable_condexp)
  intro s hs hμs
  rw [set_integral_condexp _ integrable_condexp hs]
  by_cases' hf : integrable f μ
  · rw [set_integral_condexp _ hf hs, set_integral_condexp _ hf (hm₁₂ s hs)]
    
  · simp_rw [integral_congr_ae (ae_restrict_of_ae (condexp_undef hf))]
    

section Real

theorem rn_deriv_ae_eq_condexp {f : α → ℝ} (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f|m,hm] := by
  refine' ae_eq_condexp_of_forall_set_integral_eq hm hf _ _ _
  · exact fun _ _ _ =>
      (integrable_of_integrable_trim hm
          (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm))).IntegrableOn
    
  · intro s hs hlt
    conv_rhs =>
      rw [← hf.with_densityᵥ_trim_eq_integral hm hs, ←
        signed_measure.with_densityᵥ_rn_deriv_eq ((μ.with_densityᵥ f).trim hm) (μ.trim hm)
          (hf.with_densityᵥ_trim_absolutely_continuous hm)]
    rw [with_densityᵥ_apply (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm)) hs, ←
      set_integral_trim hm _ hs]
    exact signed_measure.measurable_rn_deriv _ _
    
  · exact measurable.ae_measurable' (signed_measure.measurable_rn_deriv _ _)
    

end Real

end Condexp

end MeasureTheory

