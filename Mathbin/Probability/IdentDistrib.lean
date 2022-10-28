/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Probability.Variance
import Mathbin.MeasureTheory.Function.UniformIntegrable

/-!
# Identically distributed random variables

Two random variables defined on two (possibly different) probability spaces but taking value in
the same space are *identically distributed* if their distributions (i.e., the image probability
measures on the target space) coincide. We define this concept and establish its basic properties
in this file.

## Main definitions and results

* `ident_distrib f g μ ν` registers that the image of `μ` under `f` coincides with the image of `ν`
  under `g` (and that `f` and `g` are almost everywhere measurable, as otherwise the image measures
  don't make sense). The measures can be kept implicit as in `ident_distrib f g` if the spaces
  are registered as measure spaces.
* `ident_distrib.comp`: being identically distributed is stable under composition with measurable
  maps.

There are two main kind of lemmas, under the assumption that `f` and `g` are identically
distributed: lemmas saying that two quantities computed for `f` and `g` are the same, and lemmas
saying that if `f` has some property then `g` also has it. The first kind is registered as
`ident_distrib.foo_eq`, the second one as `ident_distrib.foo_snd` (in the latter case, to deduce
a property of `f` from one of `g`, use `h.symm.foo_snd` where `h : ident_distrib f g μ ν`). For
instance:

* `ident_distrib.measure_mem_eq`: if `f` and `g` are identically distributed, then the probabilities
  that they belong to a given measurable set are the same.
* `ident_distrib.integral_eq`: if `f` and `g` are identically distributed, then their integrals
  are the same.
* `ident_distrib.variance_eq`: if `f` and `g` are identically distributed, then their variances
  are the same.

* `ident_distrib.ae_strongly_measurable_snd`: if `f` and `g` are identically distributed and `f`
  is almost everywhere strongly measurable, then so is `g`.
* `ident_distrib.mem_ℒp_snd`: if `f` and `g` are identically distributed and `f`
  belongs to `ℒp`, then so does `g`.

We also register several dot notation shortcuts for convenience.
For instance, if `h : ident_distrib f g μ ν`, then `h.sq` states that `f^2` and `g^2` are
identically distributed, and `h.norm` states that `∥f∥` and `∥g∥` are identically distributed, and
so on.
-/


open MeasureTheory Filter Finset

noncomputable section

open TopologicalSpace BigOperators MeasureTheory Ennreal Nnreal

variable {α β γ δ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

namespace ProbabilityTheory

/-- Two functions defined on two (possibly different) measure spaces are identically distributed if
their image measures coincide. This only makes sense when the functions are ae measurable
(as otherwise the image measures are not defined), so we require this as well in the definition. -/
structure IdentDistrib (f : α → γ) (g : β → γ) (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume)
  (ν : Measure β := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  aeMeasurableFst : AeMeasurable f μ
  aeMeasurableSnd : AeMeasurable g ν
  map_eq : Measure.map f μ = Measure.map g ν

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

protected theorem refl (hf : AeMeasurable f μ) : IdentDistrib f f μ μ :=
  { aeMeasurableFst := hf, aeMeasurableSnd := hf, map_eq := rfl }

protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
  { aeMeasurableFst := h.aeMeasurableSnd, aeMeasurableSnd := h.aeMeasurableFst, map_eq := h.map_eq.symm }

protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν) (h₂ : IdentDistrib g h ν ρ) :
    IdentDistrib f h μ ρ :=
  { aeMeasurableFst := h₁.aeMeasurableFst, aeMeasurableSnd := h₂.aeMeasurableSnd, map_eq := h₁.map_eq.trans h₂.map_eq }

protected theorem compOfAeMeasurable {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : AeMeasurable u (Measure.map f μ)) :
    IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aeMeasurableFst := hu.compAeMeasurable h.aeMeasurableFst,
    aeMeasurableSnd := by
      rw [h.map_eq] at hu
      exact hu.comp_ae_measurable h.ae_measurable_snd,
    map_eq := by
      rw [← AeMeasurable.map_map_of_ae_measurable hu h.ae_measurable_fst, ←
        AeMeasurable.map_map_of_ae_measurable _ h.ae_measurable_snd, h.map_eq]
      rwa [← h.map_eq] }

protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  h.compOfAeMeasurable hu.AeMeasurable

protected theorem ofAeEq {g : α → γ} (hf : AeMeasurable f μ) (heq : f =ᵐ[μ] g) : IdentDistrib f g μ μ :=
  { aeMeasurableFst := hf, aeMeasurableSnd := hf.congr HEq, map_eq := Measure.map_congr HEq }

theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) : μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← measure.map_apply_of_ae_measurable h.ae_measurable_fst hs, ←
    measure.map_apply_of_ae_measurable h.ae_measurable_snd hs, h.map_eq]

alias measure_mem_eq ← measure_preimage_eq

theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ → Prop} (pmeas : MeasurableSet { x | p x }) (hp : ∀ᵐ x ∂μ, p (f x)) :
    ∀ᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.ae_measurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.ae_measurable_fst pmeas).2 hp

theorem ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t) (ht : ∀ᵐ x ∂μ, f x ∈ t) :
    ∀ᵐ x ∂ν, g x ∈ t :=
  h.ae_snd tmeas ht

/-- In a second countable topology, the first function in an identically distributed pair is a.e.
strongly measurable. So is the second function, but use `h.symm.ae_strongly_measurable_fst` as
`h.ae_strongly_measurable_snd` has a different meaning.-/
theorem aeStronglyMeasurableFst [TopologicalSpace γ] [MetrizableSpace γ] [OpensMeasurableSpace γ]
    [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) : AeStronglyMeasurable f μ :=
  h.aeMeasurableFst.AeStronglyMeasurable

/-- If `f` and `g` are identically distributed and `f` is a.e. strongly measurable, so is `g`. -/
theorem aeStronglyMeasurableSnd [TopologicalSpace γ] [MetrizableSpace γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : AeStronglyMeasurable f μ) : AeStronglyMeasurable g ν := by
  refine' ae_strongly_measurable_iff_ae_measurable_separable.2 ⟨h.ae_measurable_snd, _⟩
  rcases(ae_strongly_measurable_iff_ae_measurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine' ⟨Closure t, t_sep.closure, _⟩
  apply h.ae_mem_snd is_closed_closure.measurable_set
  filter_upwards [ht] with x hx using subset_closure hx

theorem ae_strongly_measurable_iff [TopologicalSpace γ] [MetrizableSpace γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    AeStronglyMeasurable f μ ↔ AeStronglyMeasurable g ν :=
  ⟨fun hf => h.aeStronglyMeasurableSnd hf, fun hg => h.symm.aeStronglyMeasurableSnd hg⟩

theorem ess_sup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : ∀ a, μ { x : α | a < f x } = ν { x : β | a < g x } := fun a => h.measure_mem_eq measurableSetIoi
  simp_rw [ess_sup_eq_Inf, I]

theorem lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : IdentDistrib f g μ ν) : (∫⁻ x, f x ∂μ) = ∫⁻ x, g x ∂ν := by
  change (∫⁻ x, id (f x) ∂μ) = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aeMeasurableId h.ae_measurable_fst, ← lintegral_map' aeMeasurableId h.ae_measurable_snd,
    h.map_eq]

theorem integral_eq [NormedAddCommGroup γ] [NormedSpace ℝ γ] [CompleteSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : (∫ x, f x ∂μ) = ∫ x, g x ∂ν := by
  by_cases hf:ae_strongly_measurable f μ
  · have A : ae_strongly_measurable id (measure.map f μ) := by
      rw [ae_strongly_measurable_iff_ae_measurable_separable]
      rcases(ae_strongly_measurable_iff_ae_measurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine' ⟨aeMeasurableId, ⟨Closure t, t_sep.closure, _⟩⟩
      rw [ae_map_iff h.ae_measurable_fst]
      · filter_upwards [ht] with x hx using subset_closure hx
        
      · exact is_closed_closure.measurable_set
        
    change (∫ x, id (f x) ∂μ) = ∫ x, id (g x) ∂ν
    rw [← integral_map h.ae_measurable_fst A]
    rw [h.map_eq] at A
    rw [← integral_map h.ae_measurable_snd A, h.map_eq]
    
  · rw [integral_non_ae_strongly_measurable hf]
    rw [h.ae_strongly_measurable_iff] at hf
    rw [integral_non_ae_strongly_measurable hf]
    

theorem snorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) (p : ℝ≥0∞) :
    snorm f p μ = snorm g p ν := by
  by_cases h0:p = 0
  · simp [h0]
    
  by_cases h_top:p = ∞
  · simp only [h_top, snorm, snorm_ess_sup, Ennreal.top_ne_zero, eq_self_iff_true, if_true, if_false]
    apply ess_sup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurableNnnorm)
    
  simp only [snorm_eq_snorm' h0 h_top, snorm', one_div]
  congr 1
  apply lintegral_eq
  exact h.comp (Measurable.powConst (measurable_coe_nnreal_ennreal.comp measurableNnnorm) p.to_real)

theorem memℒpSnd [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) (hf : Memℒp f p μ) :
    Memℒp g p ν := by
  refine' ⟨h.ae_strongly_measurable_snd hf.ae_strongly_measurable, _⟩
  rw [← h.snorm_eq]
  exact hf.2

theorem mem_ℒp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    Memℒp f p μ ↔ Memℒp g p ν :=
  ⟨fun hf => h.memℒpSnd hf, fun hg => h.symm.memℒpSnd hg⟩

theorem integrableSnd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) (hf : Integrable f μ) :
    Integrable g ν := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact h.mem_ℒp_snd hf

theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrableSnd hf, fun hg => h.symm.integrableSnd hg⟩

protected theorem norm [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ∥f x∥) (fun x => ∥g x∥) μ ν :=
  h.comp measurableNorm

protected theorem nnnorm [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ∥f x∥₊) (fun x => ∥g x∥₊) μ ν :=
  h.comp measurableNnnorm

protected theorem pow [Pow γ ℕ] [HasMeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) {n : ℕ} :
    IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν :=
  h.comp (measurableId.pow_const n)

protected theorem sq [Pow γ ℕ] [HasMeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν :=
  h.comp (measurableId.pow_const 2)

protected theorem coeNnrealEnnreal {f : α → ℝ≥0} {g : β → ℝ≥0} (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => (f x : ℝ≥0∞)) (fun x => (g x : ℝ≥0∞)) μ ν :=
  h.comp measurableCoeNnrealEnnreal

@[to_additive]
theorem mulConst [Mul γ] [HasMeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x * c) (fun x => g x * c) μ ν :=
  h.comp (measurableMulConst c)

@[to_additive]
theorem constMul [Mul γ] [HasMeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c * f x) (fun x => c * g x) μ ν :=
  h.comp (measurableConstMul c)

@[to_additive]
theorem divConst [Div γ] [HasMeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x / c) (fun x => g x / c) μ ν :=
  h.comp (HasMeasurableDiv.measurableDivConst c)

@[to_additive]
theorem constDiv [Div γ] [HasMeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c / f x) (fun x => c / g x) μ ν :=
  h.comp (HasMeasurableDiv.measurableConstDiv c)

theorem evariance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) : evariance f μ = evariance g ν := by
  convert (h.sub_const (∫ x, f x ∂μ)).nnnorm.coeNnrealEnnreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl

theorem variance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) : variance f μ = variance g ν := by
  rw [variance, h.evariance_eq]
  rfl

end IdentDistrib

section UniformIntegrable

open TopologicalSpace

variable {E : Type _} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- This lemma is superceded by `mem_ℒp.uniform_integrable_of_ident_distrib` which only require
`ae_strongly_measurable`. -/
theorem Memℒp.uniformIntegrableOfIdentDistribAux {ι : Type _} {f : ι → α → E} {j : ι} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hℒp : Memℒp (f j) p μ) (hfmeas : ∀ i, StronglyMeasurable (f i))
    (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  refine' uniform_integrable_of' hp hp' hfmeas fun ε hε => _
  by_cases hι:Nonempty ι
  swap
  · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
    
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.snorm_indicator_norm_ge_pos_le μ (hfmeas _) hε
  have hmeas : ∀ i, MeasurableSet { x | (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ∥f i x∥₊ } := fun i =>
    measurableSetLe measurableConst (hfmeas _).Measurable.nnnorm
  refine' ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq _) hC₂⟩
  have :
    { x : α | (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ∥f i x∥₊ }.indicator (f i) =
      (fun x : E => if (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ∥x∥₊ then x else 0) ∘ f i :=
    by
    ext x
    simp only [Set.indicator, Set.mem_set_of_eq]
  simp_rw [coe_nnnorm, this]
  rw [← snorm_map_measure _ (hf i).aeMeasurableFst, (hf i).map_eq, snorm_map_measure _ (hf j).aeMeasurableFst]
  · rfl
    
  all_goals exact ae_strongly_measurable_id.indicator (measurableSetLe measurableConst measurableNnnorm)

/-- A sequence of identically distributed Lᵖ functions is p-uniformly integrable. -/
theorem Memℒp.uniformIntegrableOfIdentDistrib {ι : Type _} {f : ι → α → E} {j : ι} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hℒp : Memℒp (f j) p μ) (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  have hfmeas : ∀ i, ae_strongly_measurable (f i) μ := fun i => (hf i).ae_strongly_measurable_iff.2 hℒp.1
  set g : ι → α → E := fun i => (hfmeas i).some
  have hgmeas : ∀ i, strongly_measurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hfmeas i).2.symm
  have hgℒp : mem_ℒp (g j) p μ := hℒp.ae_eq (hgeq j).symm
  exact
    uniform_integrable.ae_eq
      ((mem_ℒp.uniform_integrable_of_ident_distrib_aux hp hp' hgℒp hgmeas) fun i =>
        (ident_distrib.of_ae_eq (hgmeas i).AeMeasurable (hgeq i)).trans
          ((hf i).trans <| ident_distrib.of_ae_eq (hfmeas j).AeMeasurable (hgeq j).symm))
      hgeq

end UniformIntegrable

end ProbabilityTheory

