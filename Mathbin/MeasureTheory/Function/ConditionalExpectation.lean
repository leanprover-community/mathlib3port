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
  have `normed_space 𝕜 F` and `is_scalar_tower ℝ 𝕜 F'`.

## Tags

conditional expectation, conditional expected value

-/


noncomputable theory

open TopologicalSpace MeasureTheory.lp Filter ContinuousLinearMap

open_locale Nnreal Ennreal TopologicalSpace BigOperators MeasureTheory

namespace MeasureTheory

/-- A function `f` verifies `ae_measurable' m f μ` if it is `μ`-a.e. equal to an `m`-measurable
function. This is similar to `ae_measurable`, but the `measurable_space` structures used for the
measurability statement and for the measure are different. -/
def ae_measurable' {α β} [MeasurableSpace β] (m : MeasurableSpace α) {m0 : MeasurableSpace α} (f : α → β)
  (μ : Measureₓ α) : Prop :=
  ∃ g : α → β, @Measurable α β m _ g ∧ f =ᵐ[μ] g

namespace AeMeasurable'

variable{α β 𝕜 : Type _}{m m0 : MeasurableSpace α}{μ : Measureₓ α}[MeasurableSpace β][MeasurableSpace 𝕜]{f g : α → β}

theorem congr (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) : ae_measurable' m g μ :=
  by 
    obtain ⟨f', hf'_meas, hff'⟩ := hf 
    exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩

theorem add [Add β] [HasMeasurableAdd₂ β] (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
  by 
    rcases hf with ⟨f', h_f'_meas, hff'⟩
    rcases hg with ⟨g', h_g'_meas, hgg'⟩
    exact ⟨f'+g', @Measurable.add _ _ _ _ m _ f' g' h_f'_meas h_g'_meas, hff'.add hgg'⟩

theorem neg [Neg β] [HasMeasurableNeg β] {f : α → β} (hfm : ae_measurable' m f μ) : ae_measurable' m (-f) μ :=
  by 
    rcases hfm with ⟨f', hf'_meas, hf_ae⟩
    refine' ⟨-f', @Measurable.neg _ _ _ _ _ m _ hf'_meas, hf_ae.mono fun x hx => _⟩
    simpRw [Pi.neg_apply]
    rw [hx]

theorem sub [Sub β] [HasMeasurableSub₂ β] {f g : α → β} (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
  by 
    rcases hfm with ⟨f', hf'_meas, hf_ae⟩
    rcases hgm with ⟨g', hg'_meas, hg_ae⟩
    refine' ⟨f' - g', @Measurable.sub _ _ _ _ m _ _ _ hf'_meas hg'_meas, hf_ae.mp (hg_ae.mono fun x hx1 hx2 => _)⟩
    simpRw [Pi.sub_apply]
    rw [hx1, hx2]

theorem const_smul [HasScalar 𝕜 β] [HasMeasurableSmul 𝕜 β] (c : 𝕜) (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
  by 
    rcases hf with ⟨f', h_f'_meas, hff'⟩
    refine' ⟨c • f', @Measurable.const_smul _ _ _ _ _ _ m _ f' h_f'_meas c, _⟩
    exact eventually_eq.fun_comp hff' fun x => c • x

theorem const_inner {𝕜} [IsROrC 𝕜] [InnerProductSpace 𝕜 β] [second_countable_topology β] [OpensMeasurableSpace β]
  {f : α → β} (hfm : ae_measurable' m f μ) (c : β) : ae_measurable' m (fun x => (inner c (f x) : 𝕜)) μ :=
  by 
    rcases hfm with ⟨f', hf'_meas, hf_ae⟩
    refine'
      ⟨fun x => (inner c (f' x) : 𝕜), @Measurable.inner _ _ _ _ _ m _ _ _ _ _ (@measurable_const _ _ _ m _) hf'_meas,
        hf_ae.mono fun x hx => _⟩
    dsimp only 
    rw [hx]

/-- A m-measurable function almost everywhere equal to `f`. -/
def mk (f : α → β) (hfm : ae_measurable' m f μ) : α → β :=
  hfm.some

theorem measurable_mk {f : α → β} (hfm : ae_measurable' m f μ) : measurable[m] (hfm.mk f) :=
  hfm.some_spec.1

theorem ae_eq_mk {f : α → β} (hfm : ae_measurable' m f μ) : f =ᵐ[μ] hfm.mk f :=
  hfm.some_spec.2

theorem measurable_comp {γ} [MeasurableSpace γ] {f : α → β} {g : β → γ} (hg : Measurable g)
  (hf : ae_measurable' m f μ) : ae_measurable' m (g ∘ f) μ :=
  ⟨fun x => g (hf.mk _ x), @Measurable.comp _ _ _ m _ _ _ _ hg hf.measurable_mk,
    hf.ae_eq_mk.mono
      fun x hx =>
        by 
          rw [Function.comp_apply, hx]⟩

end AeMeasurable'

theorem ae_measurable'_of_ae_measurable'_trim {α β} {m m0 m0' : MeasurableSpace α} [MeasurableSpace β] (hm0 : m0 ≤ m0')
  {μ : Measureₓ α} {f : α → β} (hf : ae_measurable' m f (μ.trim hm0)) : ae_measurable' m f μ :=
  by 
    obtain ⟨g, hg_meas, hfg⟩ := hf 
    exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩

theorem measurable.ae_measurable' {α β} {m m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measureₓ α} {f : α → β}
  (hf : measurable[m] f) : ae_measurable' m f μ :=
  ⟨f, hf, ae_eq_refl _⟩

theorem ae_eq_trim_iff_of_ae_measurable' {α β} [AddGroupₓ β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [HasMeasurableSub₂ β] {m m0 : MeasurableSpace α} {μ : Measureₓ α} {f g : α → β} (hm : m ≤ m0)
  (hfm : ae_measurable' m f μ) (hgm : ae_measurable' m g μ) : hfm.mk f =ᵐ[μ.trim hm] hgm.mk g ↔ f =ᵐ[μ] g :=
  (ae_eq_trim_iff hm hfm.measurable_mk hgm.measurable_mk).trans
    ⟨fun h => hfm.ae_eq_mk.trans (h.trans hgm.ae_eq_mk.symm), fun h => hfm.ae_eq_mk.symm.trans (h.trans hgm.ae_eq_mk)⟩

variable{α β γ E E' F F' G G' H 𝕜 :
    Type
      _}{p :
    ℝ≥0∞}[IsROrC
      𝕜][MeasurableSpace
      β][InnerProductSpace 𝕜
      E][MeasurableSpace
      E][BorelSpace
      E][second_countable_topology
      E][InnerProductSpace 𝕜
      E'][MeasurableSpace
      E'][BorelSpace
      E'][second_countable_topology
      E'][CompleteSpace
      E'][NormedSpace ℝ
      E'][NormedGroup
      F][NormedSpace 𝕜
      F][MeasurableSpace
      F][BorelSpace
      F][second_countable_topology
      F][NormedGroup
      F'][NormedSpace 𝕜
      F'][MeasurableSpace
      F'][BorelSpace
      F'][second_countable_topology
      F'][NormedSpace ℝ
      F'][CompleteSpace
      F'][NormedGroup
      G][MeasurableSpace
      G][BorelSpace
      G][second_countable_topology
      G][NormedGroup
      G'][MeasurableSpace
      G'][BorelSpace
      G'][second_countable_topology G'][NormedSpace ℝ G'][CompleteSpace G'][MeasurableSpace H][NormedGroup H]

section LpMeas

/-! ## The subset `Lp_meas` of `Lp` functions a.e. measurable with respect to a sub-sigma-algebra -/


variable(F)

/-- `Lp_meas_subgroup F m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def Lp_meas_subgroup (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measureₓ α) : AddSubgroup (Lp F p μ) :=
  { Carrier := { f:Lp F p μ | ae_measurable' m f μ },
    zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
    add_mem' := fun f g hf hg => (hf.add hg).congr (Lp.coe_fn_add f g).symm,
    neg_mem' := fun f hf => ae_measurable'.congr hf.neg (Lp.coe_fn_neg f).symm }

variable(𝕜)

/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def Lp_meas [OpensMeasurableSpace 𝕜] (m : MeasurableSpace α) [MeasurableSpace α] (p : ℝ≥0∞) (μ : Measureₓ α) :
  Submodule 𝕜 (Lp F p μ) :=
  { Carrier := { f:Lp F p μ | ae_measurable' m f μ },
    zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
    add_mem' := fun f g hf hg => (hf.add hg).congr (Lp.coe_fn_add f g).symm,
    smul_mem' := fun c f hf => (hf.const_smul c).congr (Lp.coe_fn_smul c f).symm }

variable{F 𝕜}

variable[OpensMeasurableSpace 𝕜]

theorem mem_Lp_meas_subgroup_iff_ae_measurable' {m m0 : MeasurableSpace α} {μ : Measureₓ α} {f : Lp F p μ} :
  f ∈ Lp_meas_subgroup F m p μ ↔ ae_measurable' m f μ :=
  by 
    rw [←AddSubgroup.mem_carrier, Lp_meas_subgroup, Set.mem_set_of_eq]

theorem mem_Lp_meas_iff_ae_measurable' {m m0 : MeasurableSpace α} {μ : Measureₓ α} {f : Lp F p μ} :
  f ∈ Lp_meas F 𝕜 m p μ ↔ ae_measurable' m f μ :=
  by 
    rw [←SetLike.mem_coe, ←Submodule.mem_carrier, Lp_meas, Set.mem_set_of_eq]

theorem Lp_meas.ae_measurable' {m m0 : MeasurableSpace α} {μ : Measureₓ α} (f : Lp_meas F 𝕜 m p μ) :
  ae_measurable' m f μ :=
  mem_Lp_meas_iff_ae_measurable'.mp f.mem

theorem mem_Lp_meas_self {m0 : MeasurableSpace α} (μ : Measureₓ α) (f : Lp F p μ) : f ∈ Lp_meas F 𝕜 m0 p μ :=
  mem_Lp_meas_iff_ae_measurable'.mpr (Lp.ae_measurable f)

theorem Lp_meas_subgroup_coe {m m0 : MeasurableSpace α} {μ : Measureₓ α} {f : Lp_meas_subgroup F m p μ} :
  «expr⇑ » f = (f : Lp F p μ) :=
  coe_fn_coe_base f

theorem Lp_meas_coe {m m0 : MeasurableSpace α} {μ : Measureₓ α} {f : Lp_meas F 𝕜 m p μ} : «expr⇑ » f = (f : Lp F p μ) :=
  coe_fn_coe_base f

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mem_Lp_meas_indicator_const_Lp
{m m0 : measurable_space α}
(hm : «expr ≤ »(m, m0))
{μ : measure α}
{s : set α}
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
{c : F} : «expr ∈ »(indicator_const_Lp p (hm s hs) hμs c, Lp_meas F 𝕜 m p μ) :=
⟨s.indicator (λ
  x : α, c), @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs, indicator_const_Lp_coe_fn⟩

section CompleteSubspace

/-! ## The subspace `Lp_meas` is complete.

We define an `isometric` between `Lp_meas_subgroup` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas_subgroup` (and `Lp_meas`). -/


variable{ι : Type _}{m m0 : MeasurableSpace α}{μ : Measureₓ α}

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` belongs to `Lp_meas_subgroup F m p μ`, then the measurable function it is almost
everywhere equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
theorem mem_ℒp_trim_of_mem_Lp_meas_subgroup
(hm : «expr ≤ »(m, m0))
(f : Lp F p μ)
(hf_meas : «expr ∈ »(f, Lp_meas_subgroup F m p μ)) : mem_ℒp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have [ident hf] [":", expr ae_measurable' m f μ] [],
  from [expr mem_Lp_meas_subgroup_iff_ae_measurable'.mp hf_meas],
  let [ident g] [] [":=", expr hf.some],
  obtain ["⟨", ident hg, ",", ident hfg, "⟩", ":=", expr hf.some_spec],
  change [expr mem_ℒp g p (μ.trim hm)] [] [],
  refine [expr ⟨hg.ae_measurable, _⟩],
  have [ident h_snorm_fg] [":", expr «expr = »(snorm g p (μ.trim hm), snorm f p μ)] [],
  by { rw [expr snorm_trim hm hg] [],
    exact [expr snorm_congr_ae hfg.symm] },
  rw [expr h_snorm_fg] [],
  exact [expr Lp.snorm_lt_top f]
end

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subgroup
`Lp_meas_subgroup F m p μ`. -/
theorem mem_Lp_meas_subgroup_to_Lp_of_trim (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  (mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).toLp f ∈ Lp_meas_subgroup F m p μ :=
  by 
    let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)
    rw [mem_Lp_meas_subgroup_iff_ae_measurable']
    refine' ae_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm 
    refine' ae_measurable'_of_ae_measurable'_trim hm _ 
    exact Lp.ae_measurable f

variable(F p μ)

/-- Map from `Lp_meas_subgroup` to `Lp F p (μ.trim hm)`. -/
def Lp_meas_subgroup_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) : Lp F p (μ.trim hm) :=
  mem_ℒp.to_Lp (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.mem).some (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.mem)

variable(𝕜)

/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def Lp_meas_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) : Lp F p (μ.trim hm) :=
  mem_ℒp.to_Lp (mem_Lp_meas_iff_ae_measurable'.mp f.mem).some (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm f f.mem)

variable{𝕜}

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas_subgroup`, inverse of
`Lp_meas_subgroup_to_Lp_trim`. -/
def Lp_trim_to_Lp_meas_subgroup (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_meas_subgroup F m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable(𝕜)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def Lp_trim_to_Lp_meas (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_meas F 𝕜 m p μ :=
  ⟨(mem_ℒp_of_mem_ℒp_trim hm (Lp.mem_ℒp f)).toLp f, mem_Lp_meas_subgroup_to_Lp_of_trim hm f⟩

variable{F 𝕜 p μ}

theorem Lp_meas_subgroup_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm («expr↑ » f) f.mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_subgroup_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) :
  Lp_trim_to_Lp_meas_subgroup F p μ hm f =ᵐ[μ] f :=
  mem_ℒp.coe_fn_to_Lp _

theorem Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) : Lp_meas_to_Lp_trim F 𝕜 p μ hm f =ᵐ[μ] f :=
  (ae_eq_of_ae_eq_trim (mem_ℒp.coe_fn_to_Lp (mem_ℒp_trim_of_mem_Lp_meas_subgroup hm («expr↑ » f) f.mem))).trans
    (mem_Lp_meas_subgroup_iff_ae_measurable'.mp f.mem).some_spec.2.symm

theorem Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : Lp F p (μ.trim hm)) : Lp_trim_to_Lp_meas F 𝕜 p μ hm f =ᵐ[μ] f :=
  mem_ℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas_subgroup` is a right inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_right_inv (hm : m ≤ m0) :
  Function.RightInverse (Lp_trim_to_Lp_meas_subgroup F p μ hm) (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
  by 
    intro f 
    ext1 
    refine' ae_eq_trim_of_measurable hm (Lp.measurable _) (Lp.measurable _) _ 
    exact (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _)

/-- `Lp_trim_to_Lp_meas_subgroup` is a left inverse of `Lp_meas_subgroup_to_Lp_trim`. -/
theorem Lp_meas_subgroup_to_Lp_trim_left_inv (hm : m ≤ m0) :
  Function.LeftInverse (Lp_trim_to_Lp_meas_subgroup F p μ hm) (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
  by 
    intro f 
    ext1 
    ext1 
    rw [←Lp_meas_subgroup_coe]
    exact (Lp_trim_to_Lp_meas_subgroup_ae_eq hm _).trans (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _)

theorem Lp_meas_subgroup_to_Lp_trim_add (hm : m ≤ m0) (f g : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (f+g) =
    Lp_meas_subgroup_to_Lp_trim F p μ hm f+Lp_meas_subgroup_to_Lp_trim F p μ hm g :=
  by 
    ext1 
    refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm 
    refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
    ·
      exact @Measurable.add _ _ _ _ m _ _ _ (Lp.measurable _) (Lp.measurable _)
    refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _ 
    refine'
      eventually_eq.trans _
        (eventually_eq.add (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm (Lp_meas_subgroup_to_Lp_trim_ae_eq hm g).symm)
    refine' (Lp.coe_fn_add _ _).trans _ 
    simpRw [Lp_meas_subgroup_coe]
    exact
      eventually_of_forall
        fun x =>
          by 
            rfl

theorem Lp_meas_subgroup_to_Lp_trim_neg (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (-f) = -Lp_meas_subgroup_to_Lp_trim F p μ hm f :=
  by 
    ext1 
    refine' eventually_eq.trans _ (Lp.coe_fn_neg _).symm 
    refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
    ·
      exact @Measurable.neg _ _ _ _ _ m _ (Lp.measurable _)
    refine' (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _).trans _ 
    refine' eventually_eq.trans _ (eventually_eq.neg (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm)
    refine' (Lp.coe_fn_neg _).trans _ 
    simpRw [Lp_meas_subgroup_coe]
    exact
      eventually_of_forall
        fun x =>
          by 
            rfl

theorem Lp_meas_subgroup_to_Lp_trim_sub (hm : m ≤ m0) (f g : Lp_meas_subgroup F m p μ) :
  Lp_meas_subgroup_to_Lp_trim F p μ hm (f - g) =
    Lp_meas_subgroup_to_Lp_trim F p μ hm f - Lp_meas_subgroup_to_Lp_trim F p μ hm g :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, Lp_meas_subgroup_to_Lp_trim_add, Lp_meas_subgroup_to_Lp_trim_neg]

theorem Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (c • f) = c • Lp_meas_to_Lp_trim F 𝕜 p μ hm f :=
  by 
    ext1 
    refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm 
    refine' ae_eq_trim_of_measurable hm (Lp.measurable _) _ _
    ·
      exact @Measurable.const_smul _ _ α _ _ _ m _ _ (Lp.measurable _) c 
    refine' (Lp_meas_to_Lp_trim_ae_eq hm _).trans _ 
    refine' (Lp.coe_fn_smul _ _).trans _ 
    refine' (Lp_meas_to_Lp_trim_ae_eq hm f).mono fun x hx => _ 
    rw [Pi.smul_apply, Pi.smul_apply, hx]
    rfl

/-- `Lp_meas_subgroup_to_Lp_trim` preserves the norm. -/
theorem Lp_meas_subgroup_to_Lp_trim_norm_map [hp : Fact (1 ≤ p)] (hm : m ≤ m0) (f : Lp_meas_subgroup F m p μ) :
  ∥Lp_meas_subgroup_to_Lp_trim F p μ hm f∥ = ∥f∥ :=
  by 
    rw [Lp.norm_def, snorm_trim hm (Lp.measurable _)]
    swap
    ·
      infer_instance 
    rw [snorm_congr_ae (Lp_meas_subgroup_to_Lp_trim_ae_eq hm _), Lp_meas_subgroup_coe, ←Lp.norm_def]
    congr

theorem isometry_Lp_meas_subgroup_to_Lp_trim [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
  Isometry (Lp_meas_subgroup_to_Lp_trim F p μ hm) :=
  by 
    rw [isometry_emetric_iff_metric]
    intro f g 
    rw [dist_eq_norm, ←Lp_meas_subgroup_to_Lp_trim_sub, Lp_meas_subgroup_to_Lp_trim_norm_map, dist_eq_norm]

variable(F p μ)

/-- `Lp_meas_subgroup` and `Lp F p (μ.trim hm)` are isometric. -/
def Lp_meas_subgroup_to_Lp_trim_iso [hp : Fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas_subgroup F m p μ ≃ᵢ Lp F p (μ.trim hm) :=
  { toFun := Lp_meas_subgroup_to_Lp_trim F p μ hm, invFun := Lp_trim_to_Lp_meas_subgroup F p μ hm,
    left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm, right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm,
    isometry_to_fun := isometry_Lp_meas_subgroup_to_Lp_trim hm }

variable(𝕜)

/-- `Lp_meas_subgroup` and `Lp_meas` are isometric. -/
def Lp_meas_subgroup_to_Lp_meas_iso [hp : Fact (1 ≤ p)] : Lp_meas_subgroup F m p μ ≃ᵢ Lp_meas F 𝕜 m p μ :=
  Isometric.refl (Lp_meas_subgroup F m p μ)

/-- `Lp_meas` and `Lp F p (μ.trim hm)` are isometric, with a linear equivalence. -/
def Lp_meas_to_Lp_trim_lie [hp : Fact (1 ≤ p)] (hm : m ≤ m0) : Lp_meas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm) :=
  { toFun := Lp_meas_to_Lp_trim F 𝕜 p μ hm, invFun := Lp_trim_to_Lp_meas F 𝕜 p μ hm,
    left_inv := Lp_meas_subgroup_to_Lp_trim_left_inv hm, right_inv := Lp_meas_subgroup_to_Lp_trim_right_inv hm,
    map_add' := Lp_meas_subgroup_to_Lp_trim_add hm, map_smul' := Lp_meas_to_Lp_trim_smul hm,
    norm_map' := Lp_meas_subgroup_to_Lp_trim_norm_map hm }

variable{F 𝕜 p μ}

instance  [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp_meas_subgroup F m p μ) :=
  by 
    rw [(Lp_meas_subgroup_to_Lp_trim_iso F p μ hm.elim).complete_space_iff]
    infer_instance

instance  [hm : Fact (m ≤ m0)] [CompleteSpace F] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp_meas F 𝕜 m p μ) :=
  by 
    rw [(Lp_meas_subgroup_to_Lp_meas_iso F 𝕜 p μ).symm.complete_space_iff]
    infer_instance

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_complete_ae_measurable'
[hp : fact «expr ≤ »(1, p)]
[complete_space F]
(hm : «expr ≤ »(m, m0)) : is_complete {f : Lp F p μ | ae_measurable' m f μ} :=
begin
  rw ["<-", expr complete_space_coe_iff_is_complete] [],
  haveI [] [":", expr fact «expr ≤ »(m, m0)] [":=", expr ⟨hm⟩],
  change [expr complete_space (Lp_meas_subgroup F m p μ)] [] [],
  apply_instance
end

theorem is_closed_ae_measurable' [hp : Fact (1 ≤ p)] [CompleteSpace F] (hm : m ≤ m0) :
  IsClosed { f:Lp F p μ | ae_measurable' m f μ } :=
  IsComplete.is_closed (is_complete_ae_measurable' hm)

end CompleteSubspace

section StronglyMeasurable

variable{m m0 : MeasurableSpace α}{μ : Measureₓ α}

/-- We do not get `ae_fin_strongly_measurable f (μ.trim hm)`, since we don't have
`f =ᵐ[μ.trim hm] Lp_meas_to_Lp_trim F 𝕜 p μ hm f` but only the weaker
`f =ᵐ[μ] Lp_meas_to_Lp_trim F 𝕜 p μ hm f`. -/
theorem Lp_meas.ae_fin_strongly_measurable' (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) : ∃ g, fin_strongly_measurable g (μ.trim hm) ∧ f =ᵐ[μ] g :=
  ⟨Lp_meas_subgroup_to_Lp_trim F p μ hm f, Lp.fin_strongly_measurable _ hp_ne_zero hp_ne_top,
    (Lp_meas_subgroup_to_Lp_trim_ae_eq hm f).symm⟩

end StronglyMeasurable

end LpMeas

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/


variable{m m0 : MeasurableSpace α}{μ : Measureₓ α}

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero
(hm : «expr ≤ »(m, m0))
(f : Lp_meas E' 𝕜 m p μ)
(hp_ne_zero : «expr ≠ »(p, 0))
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
(hf_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀
 s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0)) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  obtain ["⟨", ident g, ",", ident hg_sm, ",", ident hfg, "⟩", ":=", expr Lp_meas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top],
  refine [expr hfg.trans _],
  refine [expr ae_eq_zero_of_forall_set_integral_eq_of_fin_strongly_measurable_trim hm _ _ hg_sm],
  { intros [ident s, ident hs, ident hμs],
    have [ident hfg_restrict] [":", expr «expr =ᵐ[ ] »(f, μ.restrict s, g)] [],
    from [expr ae_restrict_of_ae hfg],
    rw ["[", expr integrable_on, ",", expr integrable_congr hfg_restrict.symm, "]"] [],
    exact [expr hf_int_finite s hs hμs] },
  { intros [ident s, ident hs, ident hμs],
    have [ident hfg_restrict] [":", expr «expr =ᵐ[ ] »(f, μ.restrict s, g)] [],
    from [expr ae_restrict_of_ae hfg],
    rw [expr integral_congr_ae hfg_restrict.symm] [],
    exact [expr hf_zero s hs hμs] }
end

include 𝕜

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Lp.ae_eq_zero_of_forall_set_integral_eq_zero'
(hm : «expr ≤ »(m, m0))
(f : Lp E' p μ)
(hp_ne_zero : «expr ≠ »(p, 0))
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
(hf_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hf_zero : ∀
 s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), 0))
(hf_meas : ae_measurable' m f μ) : «expr =ᵐ[ ] »(f, μ, 0) :=
begin
  let [ident f_meas] [":", expr Lp_meas E' 𝕜 m p μ] [":=", expr ⟨f, hf_meas⟩],
  have [ident hf_f_meas] [":", expr «expr =ᵐ[ ] »(f, μ, f_meas)] [],
  by simp [] [] ["only"] ["[", expr coe_fn_coe_base', ",", expr subtype.coe_mk, "]"] [] [],
  refine [expr hf_f_meas.trans _],
  refine [expr Lp_meas.ae_eq_zero_of_forall_set_integral_eq_zero hm f_meas hp_ne_zero hp_ne_top _ _],
  { intros [ident s, ident hs, ident hμs],
    have [ident hfg_restrict] [":", expr «expr =ᵐ[ ] »(f, μ.restrict s, f_meas)] [],
    from [expr ae_restrict_of_ae hf_f_meas],
    rw ["[", expr integrable_on, ",", expr integrable_congr hfg_restrict.symm, "]"] [],
    exact [expr hf_int_finite s hs hμs] },
  { intros [ident s, ident hs, ident hμs],
    have [ident hfg_restrict] [":", expr «expr =ᵐ[ ] »(f, μ.restrict s, f_meas)] [],
    from [expr ae_restrict_of_ae hf_f_meas],
    rw [expr integral_congr_ae hfg_restrict.symm] [],
    exact [expr hf_zero s hs hμs] }
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Uniqueness of the conditional expectation** -/
theorem Lp.ae_eq_of_forall_set_integral_eq'
(hm : «expr ≤ »(m, m0))
(f g : Lp E' p μ)
(hp_ne_zero : «expr ≠ »(p, 0))
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
(hf_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hg_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on g s μ)
(hfg : ∀
 s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ)))
(hf_meas : ae_measurable' m f μ)
(hg_meas : ae_measurable' m g μ) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  suffices [ident h_sub] [":", expr «expr =ᵐ[ ] »(«expr⇑ »(«expr - »(f, g)), μ, 0)],
  by { rw ["<-", expr sub_ae_eq_zero] [],
    exact [expr (Lp.coe_fn_sub f g).symm.trans h_sub] },
  have [ident hfg'] [":", expr ∀
   s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, «expr - »(f, g) x, μ), 0)] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr integral_congr_ae (ae_restrict_of_ae (Lp.coe_fn_sub f g))] [],
    rw [expr integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)] [],
    exact [expr sub_eq_zero.mpr (hfg s hs hμs)] },
  have [ident hfg_int] [":", expr ∀
   s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on «expr⇑ »(«expr - »(f, g)) s μ] [],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integrable_on, ",", expr integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub f g)), "]"] [],
    exact [expr (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)] },
  have [ident hfg_meas] [":", expr ae_measurable' m «expr⇑ »(«expr - »(f, g)) μ] [],
  from [expr ae_measurable'.congr (hf_meas.sub hg_meas) (Lp.coe_fn_sub f g).symm],
  exact [expr Lp.ae_eq_zero_of_forall_set_integral_eq_zero' hm «expr - »(f, g) hp_ne_zero hp_ne_top hfg_int hfg' hfg_meas]
end

omit 𝕜

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_eq_of_forall_set_integral_eq_of_sigma_finite'
(hm : «expr ≤ »(m, m0))
[sigma_finite (μ.trim hm)]
{f g : α → F'}
(hf_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on f s μ)
(hg_int_finite : ∀ s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → integrable_on g s μ)
(hfg_eq : ∀
 s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, f x, μ), «expr∫ in , ∂ »((x), s, g x, μ)))
(hfm : ae_measurable' m f μ)
(hgm : ae_measurable' m g μ) : «expr =ᵐ[ ] »(f, μ, g) :=
begin
  rw ["<-", expr ae_eq_trim_iff_of_ae_measurable' hm hfm hgm] [],
  have [ident hf_mk_int_finite] [":", expr ∀
   s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ.trim hm s, «expr∞»()) → @integrable_on _ _ m _ _ (hfm.mk f) s (μ.trim hm)] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr trim_measurable_set_eq hm hs] ["at", ident hμs],
    rw ["[", expr integrable_on, ",", expr restrict_trim hm _ hs, "]"] [],
    refine [expr integrable.trim hm _ hfm.measurable_mk],
    exact [expr integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)] },
  have [ident hg_mk_int_finite] [":", expr ∀
   s, «exprmeasurable_set[ ]»(m) s → «expr < »(μ.trim hm s, «expr∞»()) → @integrable_on _ _ m _ _ (hgm.mk g) s (μ.trim hm)] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr trim_measurable_set_eq hm hs] ["at", ident hμs],
    rw ["[", expr integrable_on, ",", expr restrict_trim hm _ hs, "]"] [],
    refine [expr integrable.trim hm _ hgm.measurable_mk],
    exact [expr integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)] },
  have [ident hfg_mk_eq] [":", expr ∀
   s : set α, «exprmeasurable_set[ ]»(m) s → «expr < »(μ.trim hm s, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), s, hfm.mk f x, μ.trim hm), «expr∫ in , ∂ »((x), s, hgm.mk g x, μ.trim hm))] [],
  { intros [ident s, ident hs, ident hμs],
    rw [expr trim_measurable_set_eq hm hs] ["at", ident hμs],
    rw ["[", expr restrict_trim hm _ hs, ",", "<-", expr integral_trim hm hfm.measurable_mk, ",", "<-", expr integral_trim hm hgm.measurable_mk, ",", expr integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm), ",", expr integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm), "]"] [],
    exact [expr hfg_eq s hs hμs] },
  exact [expr ae_eq_of_forall_set_integral_eq_of_sigma_finite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq]
end

end UniquenessOfConditionalExpectation

section IntegralNormLe

variable{m m0 : MeasurableSpace α}{μ : Measureₓ α}{s : Set α}

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ∥g x∥ ∂μ ≤ ∫ x in s, ∥f x∥ ∂μ` on all `m`-measurable sets with finite measure. -/
theorem integral_norm_le_of_forall_fin_meas_integral_eq
(hm : «expr ≤ »(m, m0))
{f g : α → exprℝ()}
(hf : measurable f)
(hfi : integrable_on f s μ)
(hg : «exprmeasurable[ ]»(m) g)
(hgi : integrable_on g s μ)
(hgf : ∀
 t, «exprmeasurable_set[ ]»(m) t → «expr < »(μ t, «expr∞»()) → «expr = »(«expr∫ in , ∂ »((x), t, g x, μ), «expr∫ in , ∂ »((x), t, f x, μ)))
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»())) : «expr ≤ »(«expr∫ in , ∂ »((x), s, «expr∥ ∥»(g x), μ), «expr∫ in , ∂ »((x), s, «expr∥ ∥»(f x), μ)) :=
begin
  rw ["[", expr integral_norm_eq_pos_sub_neg (hg.mono hm le_rfl) hgi, ",", expr integral_norm_eq_pos_sub_neg hf hfi, "]"] [],
  have [ident h_meas_nonneg_g] [":", expr «exprmeasurable_set[ ]»(m) {x | «expr ≤ »(0, g x)}] [],
  from [expr @measurable_set_le _ α _ _ _ m _ _ _ _ g (@measurable_const _ α _ m _) hg],
  have [ident h_meas_nonneg_f] [":", expr measurable_set {x | «expr ≤ »(0, f x)}] [],
  from [expr measurable_set_le measurable_const hf],
  have [ident h_meas_nonpos_g] [":", expr «exprmeasurable_set[ ]»(m) {x | «expr ≤ »(g x, 0)}] [],
  from [expr @measurable_set_le _ α _ _ _ m _ _ _ g _ hg (@measurable_const _ α _ m _)],
  have [ident h_meas_nonpos_f] [":", expr measurable_set {x | «expr ≤ »(f x, 0)}] [],
  from [expr measurable_set_le hf measurable_const],
  refine [expr sub_le_sub _ _],
  { rw ["[", expr measure.restrict_restrict (hm _ h_meas_nonneg_g), ",", expr measure.restrict_restrict h_meas_nonneg_f, ",", expr hgf _ (@measurable_set.inter α m _ _ h_meas_nonneg_g hs) ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)), ",", "<-", expr measure.restrict_restrict (hm _ h_meas_nonneg_g), ",", "<-", expr measure.restrict_restrict h_meas_nonneg_f, "]"] [],
    exact [expr set_integral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi] },
  { rw ["[", expr measure.restrict_restrict (hm _ h_meas_nonpos_g), ",", expr measure.restrict_restrict h_meas_nonpos_f, ",", expr hgf _ (@measurable_set.inter α m _ _ h_meas_nonpos_g hs) ((measure_mono (set.inter_subset_right _ _)).trans_lt (lt_top_iff_ne_top.mpr hμs)), ",", "<-", expr measure.restrict_restrict (hm _ h_meas_nonpos_g), ",", "<-", expr measure.restrict_restrict h_meas_nonpos_f, "]"] [],
    exact [expr set_integral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi] }
end

/-- Let `m` be a sub-σ-algebra of `m0`, `f` a `m0`-measurable function and `g` a `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ∥g x∥₊ ∂μ ≤ ∫⁻ x in s, ∥f x∥₊ ∂μ` on all `m`-measurable sets with finite
measure. -/
theorem lintegral_nnnorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ} (hf : Measurable f)
  (hfi : integrable_on f s μ) (hg : measurable[m] g) (hgi : integrable_on g s μ)
  (hgf : ∀ t, measurable_set[m] t → μ t < ∞ → (∫x in t, g x ∂μ) = ∫x in t, f x ∂μ) (hs : measurable_set[m] s)
  (hμs : μ s ≠ ∞) : (∫⁻x in s, ∥g x∥₊ ∂μ) ≤ ∫⁻x in s, ∥f x∥₊ ∂μ :=
  by 
    rw [←of_real_integral_norm_eq_lintegral_nnnorm hfi, ←of_real_integral_norm_eq_lintegral_nnnorm hgi,
      Ennreal.of_real_le_of_real_iff]
    ·
      exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
    ·
      exact integral_nonneg fun x => norm_nonneg _

end IntegralNormLe

/-! ## Conditional expectation in L2

We define a conditional expectation in `L2`: it is the orthogonal projection on the subspace
`Lp_meas`. -/


section CondexpL2

attribute [local instance] fact_one_le_two_ennreal

variable[CompleteSpace E]{m m0 : MeasurableSpace α}{μ : Measureₓ α}{s t : Set α}

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local notation "⟪" x ", " y "⟫₂" => @inner 𝕜 (α →₂[μ] E) _ x y

variable(𝕜)

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 (hm : «expr ≤ »(m, m0)) : «expr →L[ ] »(«expr →₂[ ] »(α, μ, E), 𝕜, Lp_meas E 𝕜 m 2 μ) :=
@orthogonal_projection 𝕜 «expr →₂[ ] »(α, μ, E) _ _ (Lp_meas E 𝕜 m 2 μ) (by { haveI [] [":", expr fact «expr ≤ »(m, m0)] [":=", expr ⟨hm⟩],
   exact [expr infer_instance] })

variable{𝕜}

theorem ae_measurable'_condexp_L2 (hm : m ≤ m0) (f : α →₂[μ] E) : ae_measurable' m (condexp_L2 𝕜 hm f) μ :=
  Lp_meas.ae_measurable' _

theorem integrable_on_condexp_L2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
  integrable_on (condexp_L2 𝕜 hm f) s μ :=
  integrable_on_Lp_of_measure_ne_top (condexp_L2 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim hμs

theorem integrable_condexp_L2_of_is_finite_measure (hm : m ≤ m0) [is_finite_measure μ] {f : α →₂[μ] E} :
  integrable (condexp_L2 𝕜 hm f) μ :=
  integrable_on_univ.mp$ integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_condexp_L2_le_one
(hm : «expr ≤ »(m, m0)) : «expr ≤ »(«expr∥ ∥»(@condexp_L2 α E 𝕜 _ _ _ _ _ _ _ _ μ hm), 1) :=
by { haveI [] [":", expr fact «expr ≤ »(m, m0)] [":=", expr ⟨hm⟩],
  exact [expr orthogonal_projection_norm_le _] }

theorem norm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥condexp_L2 𝕜 hm f∥ ≤ ∥f∥ :=
  ((@condexp_L2 _ E 𝕜 _ _ _ _ _ _ _ _ μ hm).le_op_norm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condexp_L2_le_one hm))

theorem snorm_condexp_L2_le (hm : m ≤ m0) (f : α →₂[μ] E) : snorm (condexp_L2 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
  by 
    rw [Lp_meas_coe, ←Ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ←Lp.norm_def, ←Lp.norm_def,
      Submodule.norm_coe]
    exact norm_condexp_L2_le hm f

theorem norm_condexp_L2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) : ∥(condexp_L2 𝕜 hm f : α →₂[μ] E)∥ ≤ ∥f∥ :=
  by 
    rw [Lp.norm_def, Lp.norm_def, ←Lp_meas_coe]
    refine' (Ennreal.to_real_le_to_real _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f)
    exact Lp.snorm_ne_top _

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inner_condexp_L2_left_eq_right
(hm : «expr ≤ »(m, m0))
{f
 g : «expr →₂[ ] »(α, μ, E)} : «expr = »(«expr⟪ , ⟫₂»((condexp_L2 𝕜 hm f : «expr →₂[ ] »(α, μ, E)), g), «expr⟪ , ⟫₂»(f, (condexp_L2 𝕜 hm g : «expr →₂[ ] »(α, μ, E)))) :=
by { haveI [] [":", expr fact «expr ≤ »(m, m0)] [":=", expr ⟨hm⟩],
  exact [expr inner_orthogonal_projection_left_eq_right _ f g] }

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_L2_indicator_of_measurable
(hm : «expr ≤ »(m, m0))
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(c : E) : «expr = »((condexp_L2 𝕜 hm (indicator_const_Lp 2 (hm s hs) hμs c) : «expr →₂[ ] »(α, μ, E)), indicator_const_Lp 2 (hm s hs) hμs c) :=
begin
  rw [expr condexp_L2] [],
  haveI [] [":", expr fact «expr ≤ »(m, m0)] [":=", expr ⟨hm⟩],
  have [ident h_mem] [":", expr «expr ∈ »(indicator_const_Lp 2 (hm s hs) hμs c, Lp_meas E 𝕜 m 2 μ)] [],
  from [expr mem_Lp_meas_indicator_const_Lp hm hs hμs],
  let [ident ind] [] [":=", expr (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ)],
  have [ident h_coe_ind] [":", expr «expr = »((ind : «expr →₂[ ] »(α, μ, E)), indicator_const_Lp 2 (hm s hs) hμs c)] [],
  by refl,
  have [ident h_orth_mem] [] [":=", expr orthogonal_projection_mem_subspace_eq_self ind],
  rw ["[", "<-", expr h_coe_ind, ",", expr h_orth_mem, "]"] []
end

theorem inner_condexp_L2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : ae_measurable' m g μ) :
  ⟪(condexp_L2 𝕜 hm f : α →₂[μ] E), g⟫₂ = ⟪f, g⟫₂ :=
  by 
    symm 
    rw [←sub_eq_zero, ←inner_sub_left, condexp_L2]
    simp only [mem_Lp_meas_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero]

section Real

variable{hm : m ≤ m0}

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_condexp_L2_eq_of_fin_meas_real
(f : Lp 𝕜 2 μ)
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»())) : «expr = »(«expr∫ in , ∂ »((x), s, condexp_L2 𝕜 hm f x, μ), «expr∫ in , ∂ »((x), s, f x, μ)) :=
begin
  rw ["<-", expr L2.inner_indicator_const_Lp_one (hm s hs) hμs] [],
  have [ident h_eq_inner] [":", expr «expr = »(«expr∫ in , ∂ »((x), s, condexp_L2 𝕜 hm f x, μ), inner (indicator_const_Lp 2 (hm s hs) hμs (1 : 𝕜)) (condexp_L2 𝕜 hm f))] [],
  { rw [expr L2.inner_indicator_const_Lp_one (hm s hs) hμs] [],
    congr },
  rw ["[", expr h_eq_inner, ",", "<-", expr inner_condexp_L2_left_eq_right, ",", expr condexp_L2_indicator_of_measurable hm hs hμs, "]"] []
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_nnnorm_condexp_L2_le
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(f : Lp exprℝ() 2 μ) : «expr ≤ »(«expr∫⁻ in , ∂ »((x), s, «expr∥ ∥₊»(condexp_L2 exprℝ() hm f x), μ), «expr∫⁻ in , ∂ »((x), s, «expr∥ ∥₊»(f x), μ)) :=
begin
  let [ident h_meas] [] [":=", expr Lp_meas.ae_measurable' (condexp_L2 exprℝ() hm f)],
  let [ident g] [] [":=", expr h_meas.some],
  have [ident hg_meas] [":", expr «exprmeasurable[ ]»(m) g] [],
  from [expr h_meas.some_spec.1],
  have [ident hg_eq] [":", expr «expr =ᵐ[ ] »(g, μ, condexp_L2 exprℝ() hm f)] [],
  from [expr h_meas.some_spec.2.symm],
  have [ident hg_eq_restrict] [":", expr «expr =ᵐ[ ] »(g, μ.restrict s, condexp_L2 exprℝ() hm f)] [],
  from [expr ae_restrict_of_ae hg_eq],
  have [ident hg_nnnorm_eq] [":", expr «expr =ᵐ[ ] »(λ
    x, («expr∥ ∥₊»(g x) : «exprℝ≥0∞»()), μ.restrict s, λ x, («expr∥ ∥₊»(condexp_L2 exprℝ() hm f x) : «exprℝ≥0∞»()))] [],
  { refine [expr hg_eq_restrict.mono (λ x hx, _)],
    dsimp ["only"] [] [] [],
    rw [expr hx] [] },
  rw [expr lintegral_congr_ae hg_nnnorm_eq.symm] [],
  refine [expr lintegral_nnnorm_le_of_forall_fin_meas_integral_eq hm (Lp.measurable f) _ _ _ _ hs hμs],
  { exact [expr integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs] },
  { exact [expr hg_meas] },
  { rw ["[", expr integrable_on, ",", expr integrable_congr hg_eq_restrict, "]"] [],
    exact [expr integrable_on_condexp_L2_of_measure_ne_top hm hμs f] },
  { intros [ident t, ident ht, ident hμt],
    rw ["<-", expr integral_condexp_L2_eq_of_fin_meas_real f ht hμt.ne] [],
    exact [expr set_integral_congr_ae (hm t ht) (hg_eq.mono (λ x hx _, hx))] }
end

theorem condexp_L2_ae_eq_zero_of_ae_eq_zero (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) {f : Lp ℝ 2 μ}
  (hf : f =ᵐ[μ.restrict s] 0) : condexp_L2 ℝ hm f =ᵐ[μ.restrict s] 0 :=
  by 
    suffices h_nnnorm_eq_zero : (∫⁻x in s, ∥condexp_L2 ℝ hm f x∥₊ ∂μ) = 0
    ·
      rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero 
      refine' h_nnnorm_eq_zero.mono fun x hx => _ 
      dsimp only  at hx 
      rw [Pi.zero_apply] at hx⊢
      ·
        rwa [Ennreal.coe_eq_zero, nnnorm_eq_zero] at hx
      ·
        refine' Measurable.coe_nnreal_ennreal (Measurable.nnnorm _)
        rw [Lp_meas_coe]
        exact Lp.measurable _ 
    refine' le_antisymmₓ _ (zero_le _)
    refine' (lintegral_nnnorm_condexp_L2_le hs hμs f).trans (le_of_eqₓ _)
    rw [lintegral_eq_zero_iff]
    ·
      refine' hf.mono fun x hx => _ 
      dsimp only 
      rw [hx]
      simp 
    ·
      exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_nnnorm_condexp_L2_indicator_le_real
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(ht : «exprmeasurable_set[ ]»(m) t)
(hμt : «expr ≠ »(μ t, «expr∞»())) : «expr ≤ »(«expr∫⁻ in , ∂ »((a), t, «expr∥ ∥₊»(condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ())) a), μ), μ «expr ∩ »(s, t)) :=
begin
  refine [expr (lintegral_nnnorm_condexp_L2_le ht hμt _).trans (le_of_eq _)],
  have [ident h_eq] [":", expr «expr = »(«expr∫⁻ in , ∂ »((x), t, «expr∥ ∥₊»(indicator_const_Lp 2 hs hμs (1 : exprℝ()) x), μ), «expr∫⁻ in , ∂ »((x), t, s.indicator (λ
      x, (1 : «exprℝ≥0∞»())) x, μ))] [],
  { refine [expr lintegral_congr_ae (ae_restrict_of_ae _)],
    refine [expr (@indicator_const_Lp_coe_fn _ _ _ 2 _ _ _ _ hs hμs (1 : exprℝ()) _ _).mono (λ x hx, _)],
    rw [expr hx] [],
    simp_rw [expr set.indicator_apply] [],
    split_ifs [] []; simp [] [] [] [] [] [] },
  rw ["[", expr h_eq, ",", expr lintegral_indicator _ hs, ",", expr lintegral_const, ",", expr measure.restrict_restrict hs, "]"] [],
  simp [] [] ["only"] ["[", expr one_mul, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr measure.restrict_apply, "]"] [] []
end

end Real

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `condexp_L2` commutes with taking inner products with constants. See the lemma
`condexp_L2_comp_continuous_linear_map` for a more general result about commuting with continuous
linear maps. -/
theorem condexp_L2_const_inner
(hm : «expr ≤ »(m, m0))
(f : Lp E 2 μ)
(c : E) : «expr =ᵐ[ ] »(condexp_L2 𝕜 hm (((Lp.mem_ℒp f).const_inner c).to_Lp (λ
   a, «expr⟪ , ⟫»(c, f a))), μ, λ a, «expr⟪ , ⟫»(c, condexp_L2 𝕜 hm f a)) :=
begin
  rw [expr Lp_meas_coe] [],
  have [ident h_mem_Lp] [":", expr mem_ℒp (λ a, «expr⟪ , ⟫»(c, condexp_L2 𝕜 hm f a)) 2 μ] [],
  { refine [expr mem_ℒp.const_inner _ _],
    rw [expr Lp_meas_coe] [],
    exact [expr Lp.mem_ℒp _] },
  have [ident h_eq] [":", expr «expr =ᵐ[ ] »(h_mem_Lp.to_Lp _, μ, λ a, «expr⟪ , ⟫»(c, condexp_L2 𝕜 hm f a))] [],
  from [expr h_mem_Lp.coe_fn_to_Lp],
  refine [expr eventually_eq.trans _ h_eq],
  refine [expr Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm ennreal.coe_ne_top (λ
    s hs hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _) _ _ _ _],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr integrable_on, ",", expr integrable_congr (ae_restrict_of_ae h_eq), "]"] [],
    exact [expr (integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _).const_inner _] },
  { intros [ident s, ident hs, ident hμs],
    rw ["[", "<-", expr Lp_meas_coe, ",", expr integral_condexp_L2_eq_of_fin_meas_real _ hs hμs.ne, ",", expr integral_congr_ae (ae_restrict_of_ae h_eq), ",", expr Lp_meas_coe, ",", "<-", expr L2.inner_indicator_const_Lp_eq_set_integral_inner «expr↑ »(condexp_L2 𝕜 hm f) (hm s hs) c hμs.ne, ",", "<-", expr inner_condexp_L2_left_eq_right, ",", expr condexp_L2_indicator_of_measurable, ",", expr L2.inner_indicator_const_Lp_eq_set_integral_inner f (hm s hs) c hμs.ne, ",", expr set_integral_congr_ae (hm s hs) ((mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)).mono (λ
       x hx hxs, hx)), "]"] [] },
  { rw ["<-", expr Lp_meas_coe] [],
    exact [expr Lp_meas.ae_measurable' _] },
  { refine [expr ae_measurable'.congr _ h_eq.symm],
    exact [expr (Lp_meas.ae_measurable' _).const_inner _] }
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `condexp_L2` verifies the equality of integrals defining the conditional expectation. -/
theorem integral_condexp_L2_eq
[is_scalar_tower exprℝ() 𝕜 E']
(hm : «expr ≤ »(m, m0))
(f : Lp E' 2 μ)
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»())) : «expr = »(«expr∫ in , ∂ »((x), s, condexp_L2 𝕜 hm f x, μ), «expr∫ in , ∂ »((x), s, f x, μ)) :=
begin
  rw ["[", "<-", expr sub_eq_zero, ",", expr Lp_meas_coe, ",", "<-", expr integral_sub' (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs) (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs), "]"] [],
  refine [expr integral_eq_zero_of_forall_integral_inner_eq_zero _ _ _],
  { rw [expr integrable_congr (ae_restrict_of_ae (Lp.coe_fn_sub «expr↑ »(condexp_L2 𝕜 hm f) f).symm)] [],
    exact [expr integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs] },
  intro [ident c],
  simp_rw ["[", expr pi.sub_apply, ",", expr inner_sub_right, "]"] [],
  rw [expr integral_sub ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c) ((integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)] [],
  have [ident h_ae_eq_f] [] [":=", expr mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).const_inner c)],
  rw ["[", "<-", expr Lp_meas_coe, ",", expr sub_eq_zero, ",", "<-", expr set_integral_congr_ae (hm s hs) ((condexp_L2_const_inner hm f c).mono (λ
     x hx _, hx)), ",", "<-", expr set_integral_congr_ae (hm s hs) (h_ae_eq_f.mono (λ x hx _, hx)), "]"] [],
  exact [expr integral_condexp_L2_eq_of_fin_meas_real _ hs hμs]
end

variable{E'' 𝕜' :
    Type
      _}[IsROrC
      𝕜'][MeasurableSpace
      E''][InnerProductSpace 𝕜'
      E''][BorelSpace
      E''][second_countable_topology
      E''][CompleteSpace E''][NormedSpace ℝ E''][IsScalarTower ℝ 𝕜 E'][IsScalarTower ℝ 𝕜' E'']

variable(𝕜 𝕜')

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_L2_comp_continuous_linear_map
(hm : «expr ≤ »(m, m0))
(T : «expr →L[ ] »(E', exprℝ(), E''))
(f : «expr →₂[ ] »(α, μ, E')) : «expr =ᵐ[ ] »((condexp_L2 𝕜' hm (T.comp_Lp f) : «expr →₂[ ] »(α, μ, E'')), μ, T.comp_Lp (condexp_L2 𝕜 hm f : «expr →₂[ ] »(α, μ, E'))) :=
begin
  refine [expr Lp.ae_eq_of_forall_set_integral_eq' hm _ _ ennreal.zero_lt_two.ne.symm ennreal.coe_ne_top (λ
    s
    hs
    hμs, integrable_on_condexp_L2_of_measure_ne_top hm hμs.ne _) (λ
    s hs hμs, integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) _ _ _],
  { intros [ident s, ident hs, ident hμs],
    rw ["[", expr T.set_integral_comp_Lp _ (hm s hs), ",", expr T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne), ",", "<-", expr Lp_meas_coe, ",", "<-", expr Lp_meas_coe, ",", expr integral_condexp_L2_eq hm f hs hμs.ne, ",", expr integral_condexp_L2_eq hm (T.comp_Lp f) hs hμs.ne, ",", expr T.set_integral_comp_Lp _ (hm s hs), ",", expr T.integral_comp_comm (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne), "]"] [] },
  { rw ["<-", expr Lp_meas_coe] [],
    exact [expr Lp_meas.ae_measurable' _] },
  { have [ident h_coe] [] [":=", expr T.coe_fn_comp_Lp (condexp_L2 𝕜 hm f : «expr →₂[ ] »(α, μ, E'))],
    rw ["<-", expr eventually_eq] ["at", ident h_coe],
    refine [expr ae_measurable'.congr _ h_coe.symm],
    exact [expr (Lp_meas.ae_measurable' (condexp_L2 𝕜 hm f)).measurable_comp T.measurable] }
end

variable{𝕜 𝕜'}

section CondexpL2Indicator

variable(𝕜)

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_L2_indicator_ae_eq_smul
(hm : «expr ≤ »(m, m0))
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(x : E') : «expr =ᵐ[ ] »(condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x), μ, λ
 a, «expr • »(condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ())) a, x)) :=
begin
  rw [expr indicator_const_Lp_eq_to_span_singleton_comp_Lp hs hμs x] [],
  have [ident h_comp] [] [":=", expr condexp_L2_comp_continuous_linear_map exprℝ() 𝕜 hm (to_span_singleton exprℝ() x) (indicator_const_Lp 2 hs hμs (1 : exprℝ()))],
  rw ["<-", expr Lp_meas_coe] ["at", ident h_comp],
  refine [expr h_comp.trans _],
  exact [expr (to_span_singleton exprℝ() x).coe_fn_comp_Lp _]
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_L2_indicator_eq_to_span_singleton_comp
(hm : «expr ≤ »(m, m0))
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(x : E') : «expr = »((condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) : «expr →₂[ ] »(α, μ, E')), (to_span_singleton exprℝ() x).comp_Lp (condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ())))) :=
begin
  ext1 [] [],
  rw ["<-", expr Lp_meas_coe] [],
  refine [expr (condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans _],
  have [ident h_comp] [] [":=", expr (to_span_singleton exprℝ() x).coe_fn_comp_Lp (condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ())) : «expr →₂[ ] »(α, μ, exprℝ()))],
  rw ["<-", expr eventually_eq] ["at", ident h_comp],
  refine [expr eventually_eq.trans _ h_comp.symm],
  refine [expr eventually_of_forall (λ y, _)],
  refl
end

variable{𝕜}

theorem set_lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
  {t : Set α} (ht : @MeasurableSet _ m t) (hμt : μ t ≠ ∞) :
  (∫⁻a in t, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ) ≤ μ (s ∩ t)*∥x∥₊ :=
  calc
    (∫⁻a in t, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ) =
      ∫⁻a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
    set_lintegral_congr_fun (hm t ht)
      ((condexp_L2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono
        fun a ha hat =>
          by 
            rw [ha])
    _ = (∫⁻a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ)*∥x∥₊ :=
    by 
      simpRw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal 
    _ ≤ μ (s ∩ t)*∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_L2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E')
  [sigma_finite (μ.trim hm)] : (∫⁻a, ∥condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x) a∥₊ ∂μ) ≤ μ s*∥x∥₊ :=
  by 
    refine' lintegral_le_of_forall_fin_meas_le' hm (μ s*∥x∥₊) _ fun t ht hμt => _
    ·
      rw [Lp_meas_coe]
      exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal 
    refine' (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _ 
    refine' Ennreal.mul_le_mul _ le_rfl 
    exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_L2_indicator (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
  (x : E') : integrable (condexp_L2 𝕜 hm (indicator_const_Lp 2 hs hμs x)) μ :=
  by 
    refine' integrable_of_forall_fin_meas_le' hm (μ s*∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
    ·
      rw [Lp_meas_coe]
      exact Lp.ae_measurable _
    ·
      refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_L2_indicator_le hm hs hμs x ht hμt).trans _ 
      exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl

end CondexpL2Indicator

section CondexpIndSmul

variable[NormedSpace ℝ G]{hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
def condexp_ind_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) : Lp G 2 μ :=
  (to_span_singleton ℝ x).compLpL 2 μ (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)))

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_measurable'_condexp_ind_smul
(hm : «expr ≤ »(m, m0))
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(x : G) : ae_measurable' m (condexp_ind_smul hm hs hμs x) μ :=
begin
  have [ident h] [":", expr ae_measurable' m (condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ()))) μ] [],
  from [expr ae_measurable'_condexp_L2 _ _],
  rw [expr condexp_ind_smul] [],
  suffices [] [":", expr ae_measurable' m «expr ∘ »(to_span_singleton exprℝ() x, condexp_L2 exprℝ() hm (indicator_const_Lp 2 hs hμs (1 : exprℝ()))) μ],
  { refine [expr ae_measurable'.congr this _],
    refine [expr eventually_eq.trans _ (coe_fn_comp_LpL _ _).symm],
    rw [expr Lp_meas_coe] [] },
  exact [expr ae_measurable'.measurable_comp (to_span_singleton exprℝ() x).measurable h]
end

theorem condexp_ind_smul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
  condexp_ind_smul hm hs hμs (x+y) = condexp_ind_smul hm hs hμs x+condexp_ind_smul hm hs hμs y :=
  by 
    simpRw [condexp_ind_smul]
    rw [to_span_singleton_add, add_comp_LpL, add_apply]

theorem condexp_ind_smul_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
  condexp_ind_smul hm hs hμs (c • x) = c • condexp_ind_smul hm hs hμs x :=
  by 
    simpRw [condexp_ind_smul]
    rw [to_span_singleton_smul, smul_comp_LpL, smul_apply]

theorem condexp_ind_smul_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
  (x : F) : condexp_ind_smul hm hs hμs (c • x) = c • condexp_ind_smul hm hs hμs x :=
  by 
    rw [condexp_ind_smul, condexp_ind_smul, to_span_singleton_smul',
      (to_span_singleton ℝ x).smul_comp_LpL_apply c («expr↑ » (condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ))))]

theorem condexp_ind_smul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind_smul hm hs hμs x =ᵐ[μ] fun a => condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a • x :=
  (to_span_singleton ℝ x).coe_fn_comp_LpL _

theorem set_lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
  {t : Set α} (ht : @MeasurableSet _ m t) (hμt : μ t ≠ ∞) :
  (∫⁻a in t, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ) ≤ μ (s ∩ t)*∥x∥₊ :=
  calc
    (∫⁻a in t, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ) =
      ∫⁻a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a • x∥₊ ∂μ :=
    set_lintegral_congr_fun (hm t ht)
      ((condexp_ind_smul_ae_eq_smul hm hs hμs x).mono
        fun a ha hat =>
          by 
            rw [ha])
    _ = (∫⁻a in t, ∥condexp_L2 ℝ hm (indicator_const_Lp 2 hs hμs (1 : ℝ)) a∥₊ ∂μ)*∥x∥₊ :=
    by 
      simpRw [nnnorm_smul, Ennreal.coe_mul]
      rw [lintegral_mul_const, Lp_meas_coe]
      exact (Lp.measurable _).nnnorm.coe_nnreal_ennreal 
    _ ≤ μ (s ∩ t)*∥x∥₊ := Ennreal.mul_le_mul (lintegral_nnnorm_condexp_L2_indicator_le_real hs hμs ht hμt) le_rfl
    

theorem lintegral_nnnorm_condexp_ind_smul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G)
  [sigma_finite (μ.trim hm)] : (∫⁻a, ∥condexp_ind_smul hm hs hμs x a∥₊ ∂μ) ≤ μ s*∥x∥₊ :=
  by 
    refine' lintegral_le_of_forall_fin_meas_le' hm (μ s*∥x∥₊) _ fun t ht hμt => _
    ·
      exact (Lp.ae_measurable _).nnnorm.coe_nnreal_ennreal 
    refine' (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _ 
    refine' Ennreal.mul_le_mul _ le_rfl 
    exact measure_mono (Set.inter_subset_left _ _)

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
theorem integrable_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
  (x : G) : integrable (condexp_ind_smul hm hs hμs x) μ :=
  by 
    refine' integrable_of_forall_fin_meas_le' hm (μ s*∥x∥₊) (Ennreal.mul_lt_top hμs Ennreal.coe_ne_top) _ _
    ·
      exact Lp.ae_measurable _
    ·
      refine' fun t ht hμt => (set_lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x ht hμt).trans _ 
      exact Ennreal.mul_le_mul (measure_mono (Set.inter_subset_left _ _)) le_rfl

theorem condexp_ind_smul_empty {x : G} :
  condexp_ind_smul hm MeasurableSet.empty ((@measure_empty _ _ μ).le.trans_lt Ennreal.coe_lt_top).Ne x = 0 :=
  by 
    rw [condexp_ind_smul, indicator_const_empty]
    simp only [coe_fn_coe_base, Submodule.coe_zero, ContinuousLinearMap.map_zero]

theorem set_integral_condexp_ind_smul (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
  (x : G') : (∫a in s, (condexp_ind_smul hm ht hμt x) a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc
    (∫a in s, (condexp_ind_smul hm ht hμt x) a ∂μ) =
      ∫a in s, condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) a • x ∂μ :=
    set_integral_congr_ae (hm s hs) ((condexp_ind_smul_ae_eq_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (∫a in s, condexp_L2 ℝ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) a ∂μ) • x := integral_smul_const _ x 
    _ = (∫a in s, indicator_const_Lp 2 ht hμt (1 : ℝ) a ∂μ) • x :=
    by 
      rw [@integral_condexp_L2_eq α _ ℝ _ _ _ _ _ _ _ _ _ _ _ _ hm (indicator_const_Lp 2 ht hμt (1 : ℝ)) hs hμs]
    _ = (μ (t ∩ s)).toReal • x :=
    by 
      rw [set_integral_indicator_const_Lp (hm s hs), smul_assoc, one_smul]
    

end CondexpIndSmul

end CondexpL2

section CondexpInd

/-! ## Conditional expectation of an indicator as a condinuous linear map.

The goal of this section is to build
`condexp_ind (hm : m ≤ m0) (μ : measure α) (s : set s) : G →L[ℝ] α →₁[μ] G`, which
takes `x : G` to the conditional expectation of the indicator of the set `s` with value `x`,
seen as an element of `α →₁[μ] G`.
-/


attribute [local instance] fact_one_le_two_ennreal

variable{m m0 : MeasurableSpace α}{μ : Measureₓ α}[IsScalarTower ℝ 𝕜 E']{s t : Set α}[NormedSpace ℝ G]

section CondexpIndL1Fin

/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condexp_ind_L1_fin (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
  α →₁[μ] G :=
  (integrable_condexp_ind_smul hm hs hμs x).toL1 _

theorem condexp_ind_L1_fin_ae_eq_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : G) : condexp_ind_L1_fin hm hs hμs x =ᵐ[μ] condexp_ind_smul hm hs hμs x :=
  (integrable_condexp_ind_smul hm hs hμs x).coe_fn_to_L1

variable{hm : m ≤ m0}[sigma_finite (μ.trim hm)]

theorem condexp_ind_L1_fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
  condexp_ind_L1_fin hm hs hμs (x+y) = condexp_ind_L1_fin hm hs hμs x+condexp_ind_L1_fin hm hs hμs y :=
  by 
    ext1 
    refine' (mem_ℒp.coe_fn_to_Lp _).trans _ 
    refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm 
    refine' eventually_eq.trans _ (eventually_eq.add (mem_ℒp.coe_fn_to_Lp _).symm (mem_ℒp.coe_fn_to_Lp _).symm)
    rw [condexp_ind_smul_add]
    refine' (Lp.coe_fn_add _ _).trans (eventually_of_forall fun a => _)
    rfl

theorem condexp_ind_L1_fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
  condexp_ind_L1_fin hm hs hμs (c • x) = c • condexp_ind_L1_fin hm hs hμs x :=
  by 
    ext1 
    refine' (mem_ℒp.coe_fn_to_Lp _).trans _ 
    refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm 
    rw [condexp_ind_smul_smul hs hμs c x]
    refine' (Lp.coe_fn_smul _ _).trans _ 
    refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _ 
    rw [Pi.smul_apply, Pi.smul_apply, hy]

theorem condexp_ind_L1_fin_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜)
  (x : F) : condexp_ind_L1_fin hm hs hμs (c • x) = c • condexp_ind_L1_fin hm hs hμs x :=
  by 
    ext1 
    refine' (mem_ℒp.coe_fn_to_Lp _).trans _ 
    refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm 
    rw [condexp_ind_smul_smul' hs hμs c x]
    refine' (Lp.coe_fn_smul _ _).trans _ 
    refine' (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono fun y hy => _ 
    rw [Pi.smul_apply, Pi.smul_apply, hy]

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_condexp_ind_L1_fin_le
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(x : G) : «expr ≤ »(«expr∥ ∥»(condexp_ind_L1_fin hm hs hμs x), «expr * »((μ s).to_real, «expr∥ ∥»(x))) :=
begin
  have [] [":", expr «expr ≤ »(0, «expr∫ , ∂ »((a : α), «expr∥ ∥»(condexp_ind_L1_fin hm hs hμs x a), μ))] [],
  from [expr integral_nonneg (λ a, norm_nonneg _)],
  rw ["[", expr L1.norm_eq_integral_norm, ",", "<-", expr ennreal.to_real_of_real (norm_nonneg x), ",", "<-", expr ennreal.to_real_mul, ",", "<-", expr ennreal.to_real_of_real this, ",", expr ennreal.to_real_le_to_real ennreal.of_real_ne_top (ennreal.mul_ne_top hμs ennreal.of_real_ne_top), ",", expr of_real_integral_norm_eq_lintegral_nnnorm, "]"] [],
  swap,
  { rw ["[", "<-", expr mem_ℒp_one_iff_integrable, "]"] [],
    exact [expr Lp.mem_ℒp _] },
  have [ident h_eq] [":", expr «expr = »(«expr∫⁻ , ∂ »((a), «expr∥ ∥₊»(condexp_ind_L1_fin hm hs hμs x a), μ), «expr∫⁻ , ∂ »((a), nnnorm (condexp_ind_smul hm hs hμs x a), μ))] [],
  { refine [expr lintegral_congr_ae _],
    refine [expr (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x).mono (λ z hz, _)],
    dsimp ["only"] [] [] [],
    rw [expr hz] [] },
  rw ["[", expr h_eq, ",", expr of_real_norm_eq_coe_nnnorm, "]"] [],
  exact [expr lintegral_nnnorm_condexp_ind_smul_le hm hs hμs x]
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_ind_L1_fin_disjoint_union
(hs : measurable_set s)
(ht : measurable_set t)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(hμt : «expr ≠ »(μ t, «expr∞»()))
(hst : «expr = »(«expr ∩ »(s, t), «expr∅»()))
(x : G) : «expr = »(condexp_ind_L1_fin hm (hs.union ht) ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x, «expr + »(condexp_ind_L1_fin hm hs hμs x, condexp_ind_L1_fin hm ht hμt x)) :=
begin
  ext1 [] [],
  have [ident hμst] [] [":=", expr ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne],
  refine [expr (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm (hs.union ht) hμst x).trans _],
  refine [expr eventually_eq.trans _ (Lp.coe_fn_add _ _).symm],
  have [ident hs_eq] [] [":=", expr condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x],
  have [ident ht_eq] [] [":=", expr condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm ht hμt x],
  refine [expr eventually_eq.trans _ (eventually_eq.add hs_eq.symm ht_eq.symm)],
  rw [expr condexp_ind_smul] [],
  rw [expr indicator_const_Lp_disjoint_union hs ht hμs hμt hst (1 : exprℝ())] [],
  rw [expr (condexp_L2 exprℝ() hm).map_add] [],
  push_cast [] [],
  rw [expr ((to_span_singleton exprℝ() x).comp_LpL 2 μ).map_add] [],
  refine [expr (Lp.coe_fn_add _ _).trans _],
  refine [expr eventually_of_forall (λ y, _)],
  refl
end

end CondexpIndL1Fin

open_locale Classical

section CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a function in L1. Its value for sets
which are not both measurable and of finite measure is not used: we set it to 0. -/
def condexp_ind_L1 {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measureₓ α) (s : Set α) [sigma_finite (μ.trim hm)]
  (x : G) : α →₁[μ] G :=
  if hs : MeasurableSet s ∧ μ s ≠ ∞ then condexp_ind_L1_fin hm hs.1 hs.2 x else 0

variable{hm : m ≤ m0}[sigma_finite (μ.trim hm)]

theorem condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
  condexp_ind_L1 hm μ s x = condexp_ind_L1_fin hm hs hμs x :=
  by 
    simp only [condexp_ind_L1, And.intro hs hμs, dif_pos, Ne.def, not_false_iff, and_selfₓ]

theorem condexp_ind_L1_of_measure_eq_top (hμs : μ s = ∞) (x : G) : condexp_ind_L1 hm μ s x = 0 :=
  by 
    simp only [condexp_ind_L1, hμs, eq_self_iff_true, not_true, Ne.def, dif_neg, not_false_iff, and_falseₓ]

theorem condexp_ind_L1_of_not_measurable_set (hs : ¬MeasurableSet s) (x : G) : condexp_ind_L1 hm μ s x = 0 :=
  by 
    simp only [condexp_ind_L1, hs, dif_neg, not_false_iff, false_andₓ]

theorem condexp_ind_L1_add (x y : G) : condexp_ind_L1 hm μ s (x+y) = condexp_ind_L1 hm μ s x+condexp_ind_L1 hm μ s y :=
  by 
    byCases' hs : MeasurableSet s 
    swap
    ·
      simpRw [condexp_ind_L1_of_not_measurable_set hs]
      rw [zero_addₓ]
    byCases' hμs : μ s = ∞
    ·
      simpRw [condexp_ind_L1_of_measure_eq_top hμs]
      rw [zero_addₓ]
    ·
      simpRw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
      exact condexp_ind_L1_fin_add hs hμs x y

theorem condexp_ind_L1_smul (c : ℝ) (x : G) : condexp_ind_L1 hm μ s (c • x) = c • condexp_ind_L1 hm μ s x :=
  by 
    byCases' hs : MeasurableSet s 
    swap
    ·
      simpRw [condexp_ind_L1_of_not_measurable_set hs]
      rw [smul_zero]
    byCases' hμs : μ s = ∞
    ·
      simpRw [condexp_ind_L1_of_measure_eq_top hμs]
      rw [smul_zero]
    ·
      simpRw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
      exact condexp_ind_L1_fin_smul hs hμs c x

theorem condexp_ind_L1_smul' [NormedSpace ℝ F] [SmulCommClass ℝ 𝕜 F] (c : 𝕜) (x : F) :
  condexp_ind_L1 hm μ s (c • x) = c • condexp_ind_L1 hm μ s x :=
  by 
    byCases' hs : MeasurableSet s 
    swap
    ·
      simpRw [condexp_ind_L1_of_not_measurable_set hs]
      rw [smul_zero]
    byCases' hμs : μ s = ∞
    ·
      simpRw [condexp_ind_L1_of_measure_eq_top hμs]
      rw [smul_zero]
    ·
      simpRw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs]
      exact condexp_ind_L1_fin_smul' hs hμs c x

theorem norm_condexp_ind_L1_le (x : G) : ∥condexp_ind_L1 hm μ s x∥ ≤ (μ s).toReal*∥x∥ :=
  by 
    byCases' hs : MeasurableSet s 
    swap
    ·
      simpRw [condexp_ind_L1_of_not_measurable_set hs]
      rw [Lp.norm_zero]
      exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    byCases' hμs : μ s = ∞
    ·
      rw [condexp_ind_L1_of_measure_eq_top hμs x, Lp.norm_zero]
      exact mul_nonneg Ennreal.to_real_nonneg (norm_nonneg _)
    ·
      rw [condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x]
      exact norm_condexp_ind_L1_fin_le hs hμs x

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_condexp_ind_L1 : continuous (λ x : G, condexp_ind_L1 hm μ s x) :=
continuous_of_linear_of_bound condexp_ind_L1_add condexp_ind_L1_smul norm_condexp_ind_L1_le

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_ind_L1_disjoint_union
(hs : measurable_set s)
(ht : measurable_set t)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(hμt : «expr ≠ »(μ t, «expr∞»()))
(hst : «expr = »(«expr ∩ »(s, t), «expr∅»()))
(x : G) : «expr = »(condexp_ind_L1 hm μ «expr ∪ »(s, t) x, «expr + »(condexp_ind_L1 hm μ s x, condexp_ind_L1 hm μ t x)) :=
begin
  have [ident hμst] [":", expr «expr ≠ »(μ «expr ∪ »(s, t), «expr∞»())] [],
  from [expr ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne],
  rw ["[", expr condexp_ind_L1_of_measurable_set_of_measure_ne_top hs hμs x, ",", expr condexp_ind_L1_of_measurable_set_of_measure_ne_top ht hμt x, ",", expr condexp_ind_L1_of_measurable_set_of_measure_ne_top (hs.union ht) hμst x, "]"] [],
  exact [expr condexp_ind_L1_fin_disjoint_union hs ht hμs hμt hst x]
end

end CondexpIndL1

/-- Conditional expectation of the indicator of a set, as a linear map from `G` to L1. -/
def condexp_ind {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : Measureₓ α) [sigma_finite (μ.trim hm)] (s : Set α) :
  G →L[ℝ] α →₁[μ] G :=
  { toFun := condexp_ind_L1 hm μ s, map_add' := condexp_ind_L1_add, map_smul' := condexp_ind_L1_smul,
    cont := continuous_condexp_ind_L1 }

theorem condexp_ind_ae_eq_condexp_ind_smul (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : G) : condexp_ind hm μ s x =ᵐ[μ] condexp_ind_smul hm hs hμs x :=
  by 
    refine' eventually_eq.trans _ (condexp_ind_L1_fin_ae_eq_condexp_ind_smul hm hs hμs x)
    simp [condexp_ind, condexp_ind_L1, hs, hμs]

variable{hm : m ≤ m0}[sigma_finite (μ.trim hm)]

theorem ae_measurable'_condexp_ind (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
  ae_measurable' m (condexp_ind hm μ s x) μ :=
  ae_measurable'.congr (ae_measurable'_condexp_ind_smul hm hs hμs x)
    (condexp_ind_ae_eq_condexp_ind_smul hm hs hμs x).symm

@[simp]
theorem condexp_ind_empty : condexp_ind hm μ ∅ = (0 : G →L[ℝ] α →₁[μ] G) :=
  by 
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
  condexp_ind hm μ s (c • x) = c • condexp_ind hm μ s x :=
  condexp_ind_L1_smul' c x

theorem norm_condexp_ind_apply_le (x : G) : ∥condexp_ind hm μ s x∥ ≤ (μ s).toReal*∥x∥ :=
  norm_condexp_ind_L1_le x

theorem norm_condexp_ind_le : ∥(condexp_ind hm μ s : G →L[ℝ] α →₁[μ] G)∥ ≤ (μ s).toReal :=
  ContinuousLinearMap.op_norm_le_bound _ Ennreal.to_real_nonneg norm_condexp_ind_apply_le

theorem condexp_ind_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
  (hst : s ∩ t = ∅) (x : G) : condexp_ind hm μ (s ∪ t) x = condexp_ind hm μ s x+condexp_ind hm μ t x :=
  condexp_ind_L1_disjoint_union hs ht hμs hμt hst x

theorem condexp_ind_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
  (hst : s ∩ t = ∅) : (condexp_ind hm μ (s ∪ t) : G →L[ℝ] α →₁[μ] G) = condexp_ind hm μ s+condexp_ind hm μ t :=
  by 
    ext1 
    pushCast 
    exact condexp_ind_disjoint_union_apply hs ht hμs hμt hst x

variable(G)

theorem dominated_fin_meas_additive_condexp_ind (hm : m ≤ m0) (μ : Measureₓ α) [sigma_finite (μ.trim hm)] :
  dominated_fin_meas_additive μ (condexp_ind hm μ : Set α → G →L[ℝ] α →₁[μ] G) 1 :=
  ⟨fun s t => condexp_ind_disjoint_union, fun s => norm_condexp_ind_le.trans (one_mulₓ _).symm.le⟩

variable{G}

theorem set_integral_condexp_ind (hs : measurable_set[m] s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
  (x : G') : (∫a in s, condexp_ind hm μ t x a ∂μ) = (μ (t ∩ s)).toReal • x :=
  calc (∫a in s, condexp_ind hm μ t x a ∂μ) = ∫a in s, condexp_ind_smul hm ht hμt x a ∂μ :=
    set_integral_congr_ae (hm s hs) ((condexp_ind_ae_eq_condexp_ind_smul hm ht hμt x).mono fun x hx hxs => hx)
    _ = (μ (t ∩ s)).toReal • x := set_integral_condexp_ind_smul hs ht hμs hμt x
    

theorem condexp_ind_of_measurable (hs : measurable_set[m] s) (hμs : μ s ≠ ∞) (c : G) :
  condexp_ind hm μ s c = indicator_const_Lp 1 (hm s hs) hμs c :=
  by 
    ext1 
    refine' eventually_eq.trans _ indicator_const_Lp_coe_fn.symm 
    refine' (condexp_ind_ae_eq_condexp_ind_smul hm (hm s hs) hμs c).trans _ 
    refine' (condexp_ind_smul_ae_eq_smul hm (hm s hs) hμs c).trans _ 
    rw [Lp_meas_coe, condexp_L2_indicator_of_measurable hm hs hμs (1 : ℝ)]
    refine' (@indicator_const_Lp_coe_fn α _ _ 2 μ _ _ s (hm s hs) hμs (1 : ℝ) _ _).mono fun x hx => _ 
    dsimp only 
    rw [hx]
    byCases' hx_mem : x ∈ s <;> simp [hx_mem]

end CondexpInd

section CondexpL1

attribute [local instance] fact_one_le_one_ennreal

variable{m m0 :
    MeasurableSpace
      α}{μ : Measureₓ α}[IsScalarTower ℝ 𝕜 F']{hm : m ≤ m0}[sigma_finite (μ.trim hm)]{f g : α → F'}{s : Set α}

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condexp_L1_clm (hm : m ≤ m0) (μ : Measureₓ α) [sigma_finite (μ.trim hm)] : (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.set_to_L1 (dominated_fin_meas_additive_condexp_ind F' hm μ)

theorem condexp_L1_clm_smul (c : 𝕜) (f : α →₁[μ] F') : condexp_L1_clm hm μ (c • f) = c • condexp_L1_clm hm μ f :=
  L1.set_to_L1_smul (dominated_fin_meas_additive_condexp_ind F' hm μ) (fun c s x => condexp_ind_smul' c x) c f

theorem condexp_L1_clm_indicator_const_Lp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
  (condexp_L1_clm hm μ) (indicator_const_Lp 1 hs hμs x) = condexp_ind hm μ s x :=
  L1.set_to_L1_indicator_const_Lp (dominated_fin_meas_additive_condexp_ind F' hm μ) hs hμs x

theorem condexp_L1_clm_indicator_const (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
  (condexp_L1_clm hm μ) («expr↑ » (simple_func.indicator_const 1 hs hμs x)) = condexp_ind hm μ s x :=
  by 
    rw [Lp.simple_func.coe_indicator_const]
    exact condexp_L1_clm_indicator_const_Lp hs hμs x

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Auxiliary lemma used in the proof of `set_integral_condexp_L1_clm`. -/
theorem set_integral_condexp_L1_clm_of_measure_ne_top
(f : «expr →₁[ ] »(α, μ, F'))
(hs : «exprmeasurable_set[ ]»(m) s)
(hμs : «expr ≠ »(μ s, «expr∞»())) : «expr = »(«expr∫ in , ∂ »((x), s, condexp_L1_clm hm μ f x, μ), «expr∫ in , ∂ »((x), s, f x, μ)) :=
begin
  refine [expr Lp.induction ennreal.one_ne_top (λ
    f : «expr →₁[ ] »(α, μ, F'), «expr = »(«expr∫ in , ∂ »((x), s, condexp_L1_clm hm μ f x, μ), «expr∫ in , ∂ »((x), s, f x, μ))) _ _ (is_closed_eq _ _) f],
  { intros [ident x, ident t, ident ht, ident hμt],
    simp_rw [expr condexp_L1_clm_indicator_const ht hμt.ne x] [],
    rw ["[", expr Lp.simple_func.coe_indicator_const, ",", expr set_integral_indicator_const_Lp (hm _ hs), "]"] [],
    exact [expr set_integral_condexp_ind hs ht hμs hμt.ne x] },
  { intros [ident f, ident g, ident hf_Lp, ident hg_Lp, ident hfg_disj, ident hf, ident hg],
    simp_rw [expr (condexp_L1_clm hm μ).map_add] [],
    rw [expr set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (condexp_L1_clm hm μ (hf_Lp.to_Lp f)) (condexp_L1_clm hm μ (hg_Lp.to_Lp g))).mono (λ
       x hx hxs, hx))] [],
    rw [expr set_integral_congr_ae (hm s hs) ((Lp.coe_fn_add (hf_Lp.to_Lp f) (hg_Lp.to_Lp g)).mono (λ
       x hx hxs, hx))] [],
    simp_rw [expr pi.add_apply] [],
    rw ["[", expr integral_add (L1.integrable_coe_fn _).integrable_on (L1.integrable_coe_fn _).integrable_on, ",", expr integral_add (L1.integrable_coe_fn _).integrable_on (L1.integrable_coe_fn _).integrable_on, ",", expr hf, ",", expr hg, "]"] [] },
  { exact [expr (continuous_set_integral s).comp (condexp_L1_clm hm μ).continuous] },
  { exact [expr continuous_set_integral s] }
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The integral of the conditional expectation `condexp_L1_clm` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1_clm
(f : «expr →₁[ ] »(α, μ, F'))
(hs : «exprmeasurable_set[ ]»(m) s) : «expr = »(«expr∫ in , ∂ »((x), s, condexp_L1_clm hm μ f x, μ), «expr∫ in , ∂ »((x), s, f x, μ)) :=
begin
  let [ident S] [] [":=", expr spanning_sets (μ.trim hm)],
  have [ident hS_meas] [":", expr ∀
   i, «exprmeasurable_set[ ]»(m) (S i)] [":=", expr measurable_spanning_sets (μ.trim hm)],
  have [ident hS_meas0] [":", expr ∀ i, measurable_set (S i)] [":=", expr λ i, hm _ (hS_meas i)],
  have [ident hs_eq] [":", expr «expr = »(s, «expr⋃ , »((i), «expr ∩ »(S i, s)))] [],
  { simp_rw [expr set.inter_comm] [],
    rw ["[", "<-", expr set.inter_Union, ",", expr Union_spanning_sets (μ.trim hm), ",", expr set.inter_univ, "]"] [] },
  have [ident hS_finite] [":", expr ∀ i, «expr < »(μ «expr ∩ »(S i, s), «expr∞»())] [],
  { refine [expr λ i, (measure_mono (set.inter_subset_left _ _)).trans_lt _],
    have [ident hS_finite_trim] [] [":=", expr measure_spanning_sets_lt_top (μ.trim hm) i],
    rwa [expr trim_measurable_set_eq hm (hS_meas i)] ["at", ident hS_finite_trim] },
  have [ident h_mono] [":", expr monotone (λ i, «expr ∩ »(S i, s))] [],
  { intros [ident i, ident j, ident hij, ident x],
    simp_rw [expr set.mem_inter_iff] [],
    exact [expr λ h, ⟨monotone_spanning_sets (μ.trim hm) hij h.1, h.2⟩] },
  have [ident h_eq_forall] [":", expr «expr = »(λ
    i, «expr∫ in , ∂ »((x), «expr ∩ »(S i, s), condexp_L1_clm hm μ f x, μ), λ
    i, «expr∫ in , ∂ »((x), «expr ∩ »(S i, s), f x, μ))] [],
  from [expr funext (λ
    i, set_integral_condexp_L1_clm_of_measure_ne_top f (@measurable_set.inter α m _ _ (hS_meas i) hs) (hS_finite i).ne)],
  have [ident h_right] [":", expr tendsto (λ
    i, «expr∫ in , ∂ »((x), «expr ∩ »(S i, s), f x, μ)) at_top (expr𝓝() «expr∫ in , ∂ »((x), s, f x, μ))] [],
  { have [ident h] [] [":=", expr tendsto_set_integral_of_monotone (λ
      i, (hS_meas0 i).inter (hm s hs)) h_mono (L1.integrable_coe_fn f).integrable_on],
    rwa ["<-", expr hs_eq] ["at", ident h] },
  have [ident h_left] [":", expr tendsto (λ
    i, «expr∫ in , ∂ »((x), «expr ∩ »(S i, s), condexp_L1_clm hm μ f x, μ)) at_top (expr𝓝() «expr∫ in , ∂ »((x), s, condexp_L1_clm hm μ f x, μ))] [],
  { have [ident h] [] [":=", expr tendsto_set_integral_of_monotone (λ
      i, (hS_meas0 i).inter (hm s hs)) h_mono (L1.integrable_coe_fn (condexp_L1_clm hm μ f)).integrable_on],
    rwa ["<-", expr hs_eq] ["at", ident h] },
  rw [expr h_eq_forall] ["at", ident h_left],
  exact [expr tendsto_nhds_unique h_left h_right]
end

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_measurable'_condexp_L1_clm (f : «expr →₁[ ] »(α, μ, F')) : ae_measurable' m (condexp_L1_clm hm μ f) μ :=
begin
  refine [expr Lp.induction ennreal.one_ne_top (λ
    f : «expr →₁[ ] »(α, μ, F'), ae_measurable' m (condexp_L1_clm hm μ f) μ) _ _ _ f],
  { intros [ident c, ident s, ident hs, ident hμs],
    rw [expr condexp_L1_clm_indicator_const hs hμs.ne c] [],
    exact [expr ae_measurable'_condexp_ind hs hμs.ne c] },
  { intros [ident f, ident g, ident hf, ident hg, ident h_disj, ident hfm, ident hgm],
    rw [expr (condexp_L1_clm hm μ).map_add] [],
    refine [expr ae_measurable'.congr _ (coe_fn_add _ _).symm],
    exact [expr ae_measurable'.add hfm hgm] },
  { have [] [":", expr «expr = »({f : Lp F' 1 μ | ae_measurable' m (condexp_L1_clm hm μ f) μ}, «expr ⁻¹' »(condexp_L1_clm hm μ, {f | ae_measurable' m f μ}))] [],
    by refl,
    rw [expr this] [],
    refine [expr is_closed.preimage (condexp_L1_clm hm μ).continuous _],
    exact [expr is_closed_ae_measurable' hm] }
end

theorem Lp_meas_to_Lp_trim_lie_symm_indicator [NormedSpace ℝ F] {μ : Measureₓ α} (hs : measurable_set[m] s)
  (hμs : μ.trim hm s ≠ ∞) (c : F) :
  ((Lp_meas_to_Lp_trim_lie F ℝ 1 μ hm).symm (indicator_const_Lp 1 hs hμs c) : α →₁[μ] F) =
    indicator_const_Lp 1 (hm s hs) ((le_trim hm).trans_lt hμs.lt_top).Ne c :=
  by 
    ext1 
    rw [←Lp_meas_coe]
    change Lp_trim_to_Lp_meas F ℝ 1 μ hm (indicator_const_Lp 1 hs hμs c) =ᵐ[μ] (indicator_const_Lp 1 _ _ c : α → F)
    refine' (Lp_trim_to_Lp_meas_ae_eq hm _).trans _ 
    exact (ae_eq_of_ae_eq_trim indicator_const_Lp_coe_fn).trans indicator_const_Lp_coe_fn.symm

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem condexp_L1_clm_Lp_meas
(f : Lp_meas F' exprℝ() m 1 μ) : «expr = »(condexp_L1_clm hm μ (f : «expr →₁[ ] »(α, μ, F')), «expr↑ »(f)) :=
begin
  let [ident g] [] [":=", expr Lp_meas_to_Lp_trim_lie F' exprℝ() 1 μ hm f],
  have [ident hfg] [":", expr «expr = »(f, (Lp_meas_to_Lp_trim_lie F' exprℝ() 1 μ hm).symm g)] [],
  by simp [] [] ["only"] ["[", expr linear_isometry_equiv.symm_apply_apply, "]"] [] [],
  rw [expr hfg] [],
  refine [expr @Lp.induction α F' m _ _ _ _ 1 (μ.trim hm) _ ennreal.coe_ne_top (λ
    g : «expr →₁[ ] »(α, μ.trim hm, F'), «expr = »(condexp_L1_clm hm μ ((Lp_meas_to_Lp_trim_lie F' exprℝ() 1 μ hm).symm g : «expr →₁[ ] »(α, μ, F')), «expr↑ »((Lp_meas_to_Lp_trim_lie F' exprℝ() 1 μ hm).symm g))) _ _ _ g],
  { intros [ident c, ident s, ident hs, ident hμs],
    rw ["[", expr Lp.simple_func.coe_indicator_const, ",", expr Lp_meas_to_Lp_trim_lie_symm_indicator hs hμs.ne c, ",", expr condexp_L1_clm_indicator_const_Lp, "]"] [],
    exact [expr condexp_ind_of_measurable hs ((le_trim hm).trans_lt hμs).ne c] },
  { intros [ident f, ident g, ident hf, ident hg, ident hfg_disj, ident hf_eq, ident hg_eq],
    rw [expr linear_isometry_equiv.map_add] [],
    push_cast [] [],
    rw ["[", expr map_add, ",", expr hf_eq, ",", expr hg_eq, "]"] [] },
  { refine [expr is_closed_eq _ _],
    { refine [expr (condexp_L1_clm hm μ).continuous.comp (continuous_induced_dom.comp _)],
      exact [expr linear_isometry_equiv.continuous _] },
    { refine [expr continuous_induced_dom.comp _],
      exact [expr linear_isometry_equiv.continuous _] } }
end

theorem condexp_L1_clm_of_ae_measurable' (f : α →₁[μ] F') (hfm : ae_measurable' m f μ) : condexp_L1_clm hm μ f = f :=
  condexp_L1_clm_Lp_meas (⟨f, hfm⟩ : Lp_meas F' ℝ m 1 μ)

/-- Conditional expectation of a function, in L1. Its value is 0 if the function is not
integrable. The function-valued `condexp` should be used instead in most cases. -/
def condexp_L1 (hm : m ≤ m0) (μ : Measureₓ α) [sigma_finite (μ.trim hm)] (f : α → F') : α →₁[μ] F' :=
  set_to_fun (dominated_fin_meas_additive_condexp_ind F' hm μ) f

theorem condexp_L1_undef (hf : ¬integrable f μ) : condexp_L1 hm μ f = 0 :=
  set_to_fun_undef (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_eq (hf : integrable f μ) : condexp_L1 hm μ f = condexp_L1_clm hm μ (hf.to_L1 f) :=
  set_to_fun_eq (dominated_fin_meas_additive_condexp_ind F' hm μ) hf

theorem condexp_L1_zero : condexp_L1 hm μ (0 : α → F') = 0 :=
  by 
    refine' (condexp_L1_eq (integrable_zero _ _ _)).trans _ 
    change (condexp_L1_clm hm μ) (integrable.to_L1 0 _) = 0
    rw [integrable.to_L1_zero, ContinuousLinearMap.map_zero]

theorem ae_measurable'_condexp_L1 {f : α → F'} : ae_measurable' m (condexp_L1 hm μ f) μ :=
  by 
    byCases' hf : integrable f μ
    ·
      rw [condexp_L1_eq hf]
      exact ae_measurable'_condexp_L1_clm _
    ·
      rw [condexp_L1_undef hf]
      refine' ae_measurable'.congr _ (coe_fn_zero _ _ _).symm 
      exact measurable.ae_measurable' (@measurable_zero _ _ _ m _)

theorem integrable_condexp_L1 (f : α → F') : integrable (condexp_L1 hm μ f) μ :=
  L1.integrable_coe_fn _

/-- The integral of the conditional expectation `condexp_L1` over an `m`-measurable set is equal to
the integral of `f` on that set. See also `set_integral_condexp`, the similar statement for
`condexp`. -/
theorem set_integral_condexp_L1 (hf : integrable f μ) (hs : measurable_set[m] s) :
  (∫x in s, condexp_L1 hm μ f x ∂μ) = ∫x in s, f x ∂μ :=
  by 
    simpRw [condexp_L1_eq hf]
    rw [set_integral_condexp_L1_clm (hf.to_L1 f) hs]
    exact set_integral_congr_ae (hm s hs) (hf.coe_fn_to_L1.mono fun x hx hxs => hx)

theorem condexp_L1_add (hf : integrable f μ) (hg : integrable g μ) :
  condexp_L1 hm μ (f+g) = condexp_L1 hm μ f+condexp_L1 hm μ g :=
  calc condexp_L1 hm μ (f+g) = condexp_L1_clm hm μ ((hf.add hg).toL1 (f+g)) := condexp_L1_eq (hf.add hg)
    _ = condexp_L1_clm hm μ (hf.to_L1 f+hg.to_L1 g) :=
    by 
      rw [integrable.to_L1_add _ _ hf hg]
    _ = condexp_L1_clm hm μ (hf.to_L1 f)+condexp_L1_clm hm μ (hg.to_L1 g) := (condexp_L1_clm hm μ).map_add _ _ 
    _ = condexp_L1 hm μ f+condexp_L1 hm μ g :=
    by 
      rw [condexp_L1_eq hf, condexp_L1_eq hg]
    

theorem condexp_L1_neg (f : α → F') : condexp_L1 hm μ (-f) = -condexp_L1 hm μ f :=
  by 
    byCases' hf : integrable f μ
    ·
      calc condexp_L1 hm μ (-f) = condexp_L1_clm hm μ (hf.neg.to_L1 (-f)) :=
        condexp_L1_eq hf.neg _ = condexp_L1_clm hm μ (-hf.to_L1 f) :=
        by 
          rw [integrable.to_L1_neg _ hf]_ = -condexp_L1_clm hm μ (hf.to_L1 f) :=
        (condexp_L1_clm hm μ).map_neg _ _ = -condexp_L1 hm μ f :=
        by 
          rw [condexp_L1_eq hf]
    ·
      rw [condexp_L1_undef hf, condexp_L1_undef (mt integrable_neg_iff.mp hf), neg_zero]

theorem condexp_L1_smul (c : 𝕜) (f : α → F') : condexp_L1 hm μ (c • f) = c • condexp_L1 hm μ f :=
  by 
    byCases' hf : integrable f μ
    ·
      calc condexp_L1 hm μ (c • f) = condexp_L1_clm hm μ ((hf.smul c).toL1 (c • f)) :=
        condexp_L1_eq (hf.smul c)_ = condexp_L1_clm hm μ (c • hf.to_L1 f) :=
        by 
          rw [integrable.to_L1_smul' _ hf c]_ = c • condexp_L1_clm hm μ (hf.to_L1 f) :=
        condexp_L1_clm_smul c (hf.to_L1 f)_ = c • condexp_L1 hm μ f :=
        by 
          rw [condexp_L1_eq hf]
    ·
      byCases' hc : c = 0
      ·
        rw [hc, zero_smul, zero_smul, condexp_L1_zero]
      rw [condexp_L1_undef hf, condexp_L1_undef (mt (integrable_smul_iff hc f).mp hf), smul_zero]

theorem condexp_L1_sub (hf : integrable f μ) (hg : integrable g μ) :
  condexp_L1 hm μ (f - g) = condexp_L1 hm μ f - condexp_L1 hm μ g :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, condexp_L1_add hf hg.neg, condexp_L1_neg g]

theorem condexp_L1_of_ae_measurable' (hfm : ae_measurable' m f μ) (hfi : integrable f μ) : condexp_L1 hm μ f =ᵐ[μ] f :=
  by 
    rw [condexp_L1_eq hfi]
    refine' eventually_eq.trans _ (integrable.coe_fn_to_L1 hfi)
    rw [condexp_L1_clm_of_ae_measurable']
    exact ae_measurable'.congr hfm (integrable.coe_fn_to_L1 hfi).symm

end CondexpL1

section Condexp

/-! ### Conditional expectation of a function -/


open_locale Classical

attribute [local instance] fact_one_le_one_ennreal

variable{𝕜}{m m0 :
    MeasurableSpace
      α}{μ : Measureₓ α}[IsScalarTower ℝ 𝕜 F']{hm : m ≤ m0}[sigma_finite (μ.trim hm)]{f g : α → F'}{s : Set α}

/-- Conditional expectation of a function. Its value is 0 if the function is not integrable. -/
@[irreducible]
def condexp (hm : m ≤ m0) (μ : Measureₓ α) [sigma_finite (μ.trim hm)] (f : α → F') : α → F' :=
  if measurable[m] f ∧ integrable f μ then f else ae_measurable'_condexp_L1.mk (condexp_L1 hm μ f)

localized [MeasureTheory] notation μ "[" f "|" hm "]" => MeasureTheory.condexp hm μ f

theorem condexp_of_measurable {f : α → F'} (hf : measurable[m] f) (hfi : integrable f μ) : μ[f|hm] = f :=
  by 
    rw [condexp, if_pos (⟨hf, hfi⟩ : measurable[m] f ∧ integrable f μ)]

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem condexp_const (c : F') [is_finite_measure μ] : «expr = »(«expr [ | ]»(μ, λ x : α, c, hm), λ _, c) :=
condexp_of_measurable (@measurable_const _ _ _ m _) (integrable_const c)

theorem condexp_ae_eq_condexp_L1 (f : α → F') : μ[f|hm] =ᵐ[μ] condexp_L1 hm μ f :=
  by 
    unfold condexp 
    byCases' hfm : measurable[m] f
    ·
      byCases' hfi : integrable f μ
      ·
        rw [if_pos (⟨hfm, hfi⟩ : measurable[m] f ∧ integrable f μ)]
        exact (condexp_L1_of_ae_measurable' (measurable.ae_measurable' hfm) hfi).symm
      ·
        simp only [hfi, if_false, and_falseₓ]
        exact (ae_measurable'.ae_eq_mk ae_measurable'_condexp_L1).symm 
    simp only [hfm, if_false, false_andₓ]
    exact (ae_measurable'.ae_eq_mk ae_measurable'_condexp_L1).symm

theorem condexp_ae_eq_condexp_L1_clm (hf : integrable f μ) : μ[f|hm] =ᵐ[μ] condexp_L1_clm hm μ (hf.to_L1 f) :=
  by 
    refine' (condexp_ae_eq_condexp_L1 f).trans (eventually_of_forall fun x => _)
    rw [condexp_L1_eq hf]

theorem condexp_undef (hf : ¬integrable f μ) : μ[f|hm] =ᵐ[μ] 0 :=
  by 
    refine' (condexp_ae_eq_condexp_L1 f).trans (eventually_eq.trans _ (coe_fn_zero _ 1 _))
    rw [condexp_L1_undef hf]

@[simp]
theorem condexp_zero : μ[(0 : α → F')|hm] = 0 :=
  condexp_of_measurable (@measurable_zero _ _ _ m _) (integrable_zero _ _ _)

theorem measurable_condexp : measurable[m] (μ[f|hm]) :=
  by 
    unfold condexp 
    byCases' hfm : measurable[m] f
    ·
      byCases' hfi : integrable f μ
      ·
        rwa [if_pos (⟨hfm, hfi⟩ : measurable[m] f ∧ integrable f μ)]
      ·
        simp only [hfi, if_false, and_falseₓ]
        exact ae_measurable'.measurable_mk _ 
    simp only [hfm, if_false, false_andₓ]
    exact ae_measurable'.measurable_mk _

theorem integrable_condexp : integrable (μ[f|hm]) μ :=
  (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 f).symm

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s) :
  (∫x in s, (μ[f|hm]) x ∂μ) = ∫x in s, f x ∂μ :=
  by 
    rw [set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 f).mono fun x hx _ => hx)]
    exact set_integral_condexp_L1 hf hs

theorem integral_condexp (hf : integrable f μ) : (∫x, (μ[f|hm]) x ∂μ) = ∫x, f x ∂μ :=
  by 
    suffices  : (∫x in Set.Univ, (μ[f|hm]) x ∂μ) = ∫x in Set.Univ, f x ∂μ
    ·
      ·
        simpRw [integral_univ]  at this 
        exact this 
    exact set_integral_condexp hf (@MeasurableSet.univ _ m)

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [sigma_finite (μ.trim hm)] {f g : α → F'}
  (hf : integrable f μ) (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → integrable_on g s μ)
  (hg_eq : ∀ (s : Set α), measurable_set[m] s → μ s < ∞ → (∫x in s, g x ∂μ) = ∫x in s, f x ∂μ)
  (hgm : ae_measurable' m g μ) : g =ᵐ[μ] μ[f|hm] :=
  by 
    refine'
      ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite
        (fun s hs hμs => integrable_condexp.integrable_on) (fun s hs hμs => _) hgm
        (measurable.ae_measurable' measurable_condexp)
    rw [hg_eq s hs hμs, set_integral_condexp hf hs]

theorem condexp_add (hf : integrable f μ) (hg : integrable g μ) : μ[f+g|hm] =ᵐ[μ] μ[f|hm]+μ[g|hm] :=
  by 
    refine' (condexp_ae_eq_condexp_L1 _).trans _ 
    rw [condexp_L1_add hf hg]
    exact (coe_fn_add _ _).trans ((condexp_ae_eq_condexp_L1 _).symm.add (condexp_ae_eq_condexp_L1 _).symm)

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|hm] =ᵐ[μ] c • μ[f|hm] :=
  by 
    byCases' hf : integrable f μ
    ·
      refine' (condexp_ae_eq_condexp_L1 _).trans _ 
      rw [condexp_L1_smul c f]
      refine' (@condexp_ae_eq_condexp_L1 _ _ _ _ _ _ _ _ m _ _ hm _ f).mp _ 
      refine' (coe_fn_smul c (condexp_L1 hm μ f)).mono fun x hx1 hx2 => _ 
      rw [hx1, Pi.smul_apply, Pi.smul_apply, hx2]
    ·
      byCases' hc : c = 0
      ·
        rw [hc, zero_smul, zero_smul, condexp_zero]
      refine' (condexp_undef (mt (integrable_smul_iff hc f).mp hf)).trans _ 
      refine' (@condexp_undef _ _ _ _ _ _ _ _ _ _ _ hm _ _ hf).mono fun x hx => _ 
      rw [Pi.zero_apply, Pi.smul_apply, hx, Pi.zero_apply, smul_zero]

-- error in MeasureTheory.Function.ConditionalExpectation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem condexp_neg
(f : α → F') : «expr =ᵐ[ ] »(«expr [ | ]»(μ, «expr- »(f), hm), μ, «expr- »(«expr [ | ]»(μ, f, hm))) :=
by letI [] [":", expr module exprℝ() (α → F')] [":=", expr @pi.module α (λ
  _, F') exprℝ() _ _ (λ _, infer_instance)]; calc
  «expr = »(«expr [ | ]»(μ, «expr- »(f), hm), «expr [ | ]»(μ, «expr • »((«expr- »(1) : exprℝ()), f), hm)) : by rw [expr neg_one_smul exprℝ() f] []
  «expr =ᵐ[ ] »(..., μ, «expr • »((«expr- »(1) : exprℝ()), «expr [ | ]»(μ, f, hm))) : condexp_smul «expr- »(1) f
  «expr = »(..., «expr- »(«expr [ | ]»(μ, f, hm))) : neg_one_smul exprℝ() «expr [ | ]»(μ, f, hm)

theorem condexp_sub (hf : integrable f μ) (hg : integrable g μ) : μ[f - g|hm] =ᵐ[μ] μ[f|hm] - μ[g|hm] :=
  by 
    simpRw [sub_eq_add_neg]
    exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g))

section Real

theorem rn_deriv_ae_eq_condexp {f : α → ℝ} (hf : integrable f μ) :
  signed_measure.rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f|hm] :=
  by 
    refine' ae_eq_condexp_of_forall_set_integral_eq hm hf _ _ _
    ·
      exact
        fun _ _ _ =>
          (integrable_of_integrable_trim hm
              (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm))).IntegrableOn
    ·
      intro s hs hlt 
      convRHS =>
        rw [←hf.with_densityᵥ_trim_eq_integral hm hs,
          ←signed_measure.with_densityᵥ_rn_deriv_eq ((μ.with_densityᵥ f).trim hm) (μ.trim hm)
            (hf.with_densityᵥ_trim_absolutely_continuous hm)]
      rw [with_densityᵥ_apply (signed_measure.integrable_rn_deriv ((μ.with_densityᵥ f).trim hm) (μ.trim hm)) hs,
        ←set_integral_trim hm _ hs]
      exact signed_measure.measurable_rn_deriv _ _
    ·
      exact measurable.ae_measurable' (signed_measure.measurable_rn_deriv _ _)

end Real

end Condexp

end MeasureTheory

