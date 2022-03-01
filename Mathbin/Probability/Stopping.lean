/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.MeasureTheory.Function.L1Space
import Mathbin.Topology.Instances.Discrete

/-!
# Filtration and stopping time

This file defines some standard definition from the theory of stochastic processes including
filtrations and stopping times. These definitions are used to model the amount of information
at a specific time and is the first step in formalizing stochastic processes.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space
* `measure_theory.adapted`: a sequence of functions `u` is said to be adapted to a
  filtration `f` if at each point in time `i`, `u i` is `f i`-measurable
* `measure_theory.filtration.natural`: the natural filtration with respect to a sequence of
  measurable functions is the smallest filtration to which it is adapted to
* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Tags

filtration, stopping time, stochastic process

-/


open TopologicalSpace Filter

open_locale Classical MeasureTheory Nnreal Ennreal TopologicalSpace BigOperators

namespace MeasureTheory

/-! ### Filtrations -/


/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure Filtration {α : Type _} (ι : Type _) [Preorderₓ ι] (m : MeasurableSpace α) where
  seq : ι → MeasurableSpace α
  mono' : Monotone seq
  le' : ∀ i : ι, seq i ≤ m

variable {α β ι : Type _} {m : MeasurableSpace α}

instance [Preorderₓ ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace α :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorderₓ ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace α) = g) : f = g := by
  cases f
  cases g
  simp only
  exact h

variable (ι)

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : MeasurableSpace α) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_const, fun _ => hm'⟩

variable {ι}

@[simp]
theorem const_apply {m' : MeasurableSpace α} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl

instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance : HasBot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

instance : HasTop (Filtration ι m) :=
  ⟨const ι m le_rfl⟩

instance : HasSup (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i⊔g i,
      mono' := fun i j hij => sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right),
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
theorem coe_fn_sup {f g : Filtration ι m} : ⇑(f⊔g) = f⊔g :=
  rfl

instance : HasInf (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i⊓g i,
      mono' := fun i j hij => le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij)),
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
theorem coe_fn_inf {f g : Filtration ι m} : ⇑(f⊓g) = f⊓g :=
  rfl

instance : HasSupₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sup ((fun f : Filtration ι m => f i) '' s),
      mono' := fun i j hij => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine' (f.mono hij).trans _
        have hfj_mem : f j ∈ (fun g : filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_Sup hfj_mem,
      le' := fun i => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

theorem Sup_def (s : Set (Filtration ι m)) (i : ι) : sup s i = sup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

noncomputable instance : HasInfₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m,
      mono' := fun i j hij => by
        by_cases' h_nonempty : Set.Nonempty s
        swap
        · simp only [h_nonempty, Set.nonempty_image_iff, if_false, le_reflₓ]
          
        simp only [h_nonempty, if_true, le_Inf_iff, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine' fun f hf_mem => le_transₓ _ (f.mono hij)
        have hfi_mem : f i ∈ (fun g : filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact Inf_le hfi_mem,
      le' := fun i => by
        by_cases' h_nonempty : Set.Nonempty s
        swap
        · simp only [h_nonempty, if_false, le_reflₓ]
          
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_transₓ (Inf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

theorem Inf_def (s : Set (Filtration ι m)) (i : ι) :
    inf s i = if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

noncomputable instance : CompleteLattice (Filtration ι m) where
  le := (· ≤ ·)
  le_refl := fun f i => le_rfl
  le_trans := fun f g h h_fg h_gh i => (h_fg i).trans (h_gh i)
  le_antisymm := fun f g h_fg h_gf => filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)
  sup := (·⊔·)
  le_sup_left := fun f g i => le_sup_left
  le_sup_right := fun f g i => le_sup_right
  sup_le := fun f g h h_fh h_gh i => sup_le (h_fh i) (h_gh _)
  inf := (·⊓·)
  inf_le_left := fun f g i => inf_le_left
  inf_le_right := fun f g i => inf_le_right
  le_inf := fun f g h h_fg h_fh i => le_inf (h_fg i) (h_fh i)
  sup := sup
  le_Sup := fun s f hf_mem i => le_Sup ⟨f, hf_mem, rfl⟩
  Sup_le := fun s f h_forall i =>
    Sup_le fun m' hm' => by
      obtain ⟨g, hg_mem, hfm'⟩ := hm'
      rw [← hfm']
      exact h_forall g hg_mem i
  inf := inf
  Inf_le := fun s f hf_mem i => by
    have hs : s.nonempty := ⟨f, hf_mem⟩
    simp only [Inf_def, hs, if_true]
    exact Inf_le ⟨f, hf_mem, rfl⟩
  le_Inf := fun s f h_forall i => by
    by_cases' hs : s.nonempty
    swap
    · simp only [Inf_def, hs, if_false]
      exact f.le i
      
    simp only [Inf_def, hs, if_true, le_Inf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun g hg_mem => h_forall g hg_mem i
  top := ⊤
  bot := ⊥
  le_top := fun f i => f.le' i
  bot_le := fun f i => bot_le

end Filtration

theorem measurable_set_of_filtration [Preorderₓ ι] {f : Filtration ι m} {s : Set α} {i : ι}
    (hs : measurable_set[f i] s) : measurable_set[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class SigmaFiniteFiltration [Preorderₓ ι] (μ : Measure α) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))

instance sigma_finite_of_sigma_finite_filtration [Preorderₓ ι] (μ : Measure α) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) := by
  apply hf.sigma_finite

-- can't exact here
section Adapted

variable [MeasurableSpace β] [Preorderₓ ι]

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`,
`u i` is `f i`-measurable. -/
def Adapted (f : Filtration ι m) (u : ι → α → β) : Prop :=
  ∀ i : ι, measurable[f i] (u i)

namespace Adapted

theorem add [Add β] [HasMeasurableAdd₂ β] {u v : ι → α → β} {f : Filtration ι m} (hu : Adapted f u) (hv : Adapted f v) :
    Adapted f (u + v) := fun i => @Measurable.add _ _ _ _ (f i) _ _ _ (hu i) (hv i)

theorem neg [Neg β] [HasMeasurableNeg β] {u : ι → α → β} {f : Filtration ι m} (hu : Adapted f u) : Adapted f (-u) :=
  fun i => @Measurable.neg _ α _ _ _ (f i) _ (hu i)

theorem smul [HasScalar ℝ β] [HasMeasurableSmul ℝ β] {u : ι → α → β} {f : Filtration ι m} (c : ℝ) (hu : Adapted f u) :
    Adapted f (c • u) := fun i => @Measurable.const_smul ℝ β α _ _ _ (f i) _ _ (hu i) c

end Adapted

variable (β)

theorem adapted_zero [Zero β] (f : Filtration ι m) : Adapted f (0 : ι → α → β) := fun i =>
  @measurable_zero β α (f i) _ _

end Adapted

namespace Filtration

variable {mβ : MeasurableSpace β} [Preorderₓ ι]

include mβ

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, Measurable (u i)) : Filtration ι m where
  seq := fun i => ⨆ j ≤ i, MeasurableSpace.comap (u j) inferInstance
  mono' := fun i j hij => bsupr_le_bsupr' fun k hk => le_transₓ hk hij
  le' := fun i =>
    bsupr_le fun j hj s hs =>
      let ⟨t, ht, ht'⟩ := hs
      ht' ▸ hum j ht

theorem adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) : Adapted (natural u hum) u := fun i =>
  Measurable.le (le_bsupr_of_le i (le_reflₓ i) le_rfl) fun s hs => ⟨s, hs, rfl⟩

end Filtration

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def IsStoppingTime [Preorderₓ ι] (f : Filtration ι m) (τ : α → ι) :=
  ∀ i : ι, measurable_set[f i] <| { x | τ x ≤ i }

theorem is_stopping_time_const [Preorderₓ ι] {f : Filtration ι m} (i : ι) : IsStoppingTime f fun x => i := fun j => by
  simp only [MeasurableSet.const]

section MeasurableSet

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m} {τ : α → ι}

theorem IsStoppingTime.measurable_set_le (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | τ x ≤ i } :=
  hτ i

theorem IsStoppingTime.measurable_set_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { x | τ x < i } := by
  by_cases' hi_min : IsMin i
  · suffices { x : α | τ x < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_empty_eq, iff_falseₓ]
    rw [is_min_iff_forall_not_lt] at hi_min
    exact hi_min (τ x)
    
  have : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := by
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_preimage, Set.mem_Iio]
  rw [this, PredOrder.Iio_eq_Iic_pred' hi_min]
  have : τ ⁻¹' Set.Iic (PredOrder.pred i) = { x : α | τ x ≤ PredOrder.pred i } := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_set_of_eq]
  rw [this]
  exact f.mono (PredOrder.pred_le i) _ (hτ.measurable_set_le (PredOrder.pred i))

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ ι] {f : Filtration ι m} {τ : α → ι}

theorem IsStoppingTime.measurable_set_gt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | i < τ x } := by
  have : { x | i < τ x } = { x | τ x ≤ i }ᶜ := by
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_compl_eq, not_leₓ]
  rw [this]
  exact (hτ.measurable_set_le i).Compl

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
theorem IsStoppingTime.measurable_set_lt_of_is_lub (hτ : IsStoppingTime f τ) (i : ι) (h_lub : IsLub (Set.Iio i) i) :
    measurable_set[f i] { x | τ x < i } := by
  by_cases' hi_min : IsMin i
  · suffices { x : α | τ x < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_empty_eq, iff_falseₓ]
    exact is_min_iff_forall_not_lt.mp hi_min (τ x)
    
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
    ∃ seq : ℕ → ι, Monotone seq ∧ (∀ j, seq j ≤ i) ∧ tendsto seq at_top (𝓝 i) ∧ ∀ j, seq j < i
  exact h_lub.exists_seq_monotone_tendsto (not_is_min_iff.mp hi_min)
  have h_Ioi_eq_Union : Set.Iio i = ⋃ j, { k | k ≤ seq j } := by
    ext1 k
    simp only [Set.mem_Iio, Set.mem_Union, Set.mem_set_of_eq]
    refine' ⟨fun hk_lt_i => _, fun h_exists_k_le_seq => _⟩
    · rw [tendsto_at_top'] at h_tendsto
      have h_nhds : Set.Ici k ∈ 𝓝 i := mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rfl, is_open_Ioi, hk_lt_i⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
      exact ⟨a, ha a le_rfl⟩
      
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (h_bound j)
      
  have h_lt_eq_preimage : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := by
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_preimage, Set.mem_Iio]
  rw [h_lt_eq_preimage, h_Ioi_eq_Union]
  simp only [Set.preimage_Union, Set.preimage_set_of_eq]
  exact MeasurableSet.Union fun n => f.mono (h_bound n).le _ (hτ.measurable_set_le (seq n))

theorem IsStoppingTime.measurable_set_lt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | τ x < i } := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLub (Set.Iio i) i'
  exact exists_lub_Iio i
  cases' lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub⊢
    exact hτ.measurable_set_lt_of_is_lub i' hi'_lub
    
  · have h_lt_eq_preimage : { x : α | τ x < i } = τ ⁻¹' Set.Iio i := rfl
    rw [h_lt_eq_preimage, h_Iio_eq_Iic]
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurable_set_le i')
    

theorem IsStoppingTime.measurable_set_ge (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | i ≤ τ x } := by
  have : { x | i ≤ τ x } = { x | τ x < i }ᶜ := by
    ext1 x
    simp only [Set.mem_set_of_eq, Set.mem_compl_eq, not_ltₓ]
  rw [this]
  exact (hτ.measurable_set_lt i).Compl

theorem IsStoppingTime.measurable_set_eq (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { x | τ x = i } := by
  have : { x | τ x = i } = { x | τ x ≤ i } ∩ { x | τ x ≥ i } := by
    ext1 x
    simp only [Set.mem_set_of_eq, ge_iff_le, Set.mem_inter_eq, le_antisymm_iffₓ]
  rw [this]
  exact (hτ.measurable_set_le i).inter (hτ.measurable_set_ge i)

theorem IsStoppingTime.measurable_set_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { x | τ x = i } :=
  f.mono hle _ <| hτ.measurable_set_eq i

theorem IsStoppingTime.measurable_set_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { x | τ x < i } :=
  f.mono hle _ <| hτ.measurable_set_lt i

end LinearOrderₓ

section Encodable

theorem is_stopping_time_of_measurable_set_eq [Preorderₓ ι] [Encodable ι] {f : Filtration ι m} {τ : α → ι}
    (hτ : ∀ i, measurable_set[f i] { x | τ x = i }) : IsStoppingTime f τ := by
  intro i
  rw
    [show { x | τ x ≤ i } = ⋃ k ≤ i, { x | τ x = k } by
      ext
      simp ]
  refine' MeasurableSet.bUnion (Set.countable_encodable _) fun k hk => _
  exact f.mono hk _ (hτ k)

end Encodable

end MeasurableSet

namespace IsStoppingTime

theorem max [LinearOrderₓ ι] {f : Filtration ι m} {τ π : α → ι} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun x => max (τ x) (π x) := by
  intro i
  simp_rw [max_le_iff, Set.set_of_and]
  exact (hτ i).inter (hπ i)

theorem min [LinearOrderₓ ι] {f : Filtration ι m} {τ π : α → ι} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f fun x => min (τ x) (π x) := by
  intro i
  simp_rw [min_le_iff, Set.set_of_or]
  exact (hτ i).union (hπ i)

theorem add_const [AddGroupₓ ι] [Preorderₓ ι] [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    [CovariantClass ι ι (· + ·) (· ≤ ·)] {f : Filtration ι m} {τ : α → ι} (hτ : IsStoppingTime f τ) {i : ι}
    (hi : 0 ≤ i) : IsStoppingTime f fun x => τ x + i := by
  intro j
  simp_rw [← le_sub_iff_add_le]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace {τ : α → ι} (hτ : IsStoppingTime f τ) : MeasurableSpace α where
  MeasurableSet' := fun s => ∀ i : ι, measurable_set[f i] (s ∩ { x | τ x ≤ i })
  measurable_set_empty := fun i => (Set.empty_inter { x | τ x ≤ i }).symm ▸ @MeasurableSet.empty _ (f i)
  measurable_set_compl := fun s hs i => by
    rw [(_ : sᶜ ∩ { x | τ x ≤ i } = (sᶜ ∪ { x | τ x ≤ i }ᶜ) ∩ { x | τ x ≤ i })]
    · refine' MeasurableSet.inter _ _
      · rw [← Set.compl_inter]
        exact (hs i).Compl
        
      · exact hτ i
        
      
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
      
  measurable_set_Union := fun s hs i => by
    rw [forall_swap] at hs
    rw [Set.Union_inter]
    exact MeasurableSet.Union (hs i)

@[protected]
theorem measurable_set {τ : α → ι} (hτ : IsStoppingTime f τ) (s : Set α) :
    measurable_set[hτ.MeasurableSpace] s ↔ ∀ i : ι, measurable_set[f i] (s ∩ { x | τ x ≤ i }) :=
  Iff.rfl

theorem measurable_space_mono {τ π : α → ι} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.MeasurableSpace ≤ hπ.MeasurableSpace := by
  intro s hs i
  rw [(_ : s ∩ { x | π x ≤ i } = s ∩ { x | τ x ≤ i } ∩ { x | π x ≤ i })]
  · exact (hs i).inter (hπ i)
    
  · ext
    simp only [Set.mem_inter_eq, iff_self_and, And.congr_left_iff, Set.mem_set_of_eq]
    intro hle' _
    exact le_transₓ (hle _) hle'
    

theorem measurable_space_le [Encodable ι] {τ : α → ι} (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { x | τ x ≤ i }) at hs
  rw [(_ : s = ⋃ i, s ∩ { x | τ x ≤ i })]
  · exact MeasurableSet.Union fun i => f.le i _ (hs i)
    
  · ext x
    constructor <;> rw [Set.mem_Union]
    · exact fun hx => ⟨τ x, hx, le_rfl⟩
      
    · rintro ⟨_, hx, _⟩
      exact hx
      
    

section Nat

theorem measurable_set_eq_const {f : Filtration ℕ m} {τ : α → ℕ} (hτ : IsStoppingTime f τ) (i : ℕ) :
    measurable_set[hτ.MeasurableSpace] { x | τ x = i } := by
  rw [hτ.measurable_set]
  intro j
  by_cases' i ≤ j
  · rw [(_ : { x | τ x = i } ∩ { x | τ x ≤ j } = { x | τ x = i })]
    · exact hτ.measurable_set_eq_le h
      
    · ext
      simp only [Set.mem_inter_eq, and_iff_left_iff_imp, Set.mem_set_of_eq]
      rintro rfl
      assumption
      
    
  · rw [(_ : { x | τ x = i } ∩ { x | τ x ≤ j } = ∅)]
    · exact @MeasurableSet.empty _ (f j)
      
    · ext
      simp only [Set.mem_empty_eq, Set.mem_inter_eq, not_and, not_leₓ, Set.mem_set_of_eq, iff_falseₓ]
      rintro rfl
      rwa [not_leₓ] at h
      
    

end Nat

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ ι]

theorem measurable [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    {f : Filtration ι m} {τ : α → ι} (hτ : IsStoppingTime f τ) : measurable[hτ.MeasurableSpace] τ := by
  refine' @measurable_of_Iic ι α _ _ _ hτ.measurable_space _ _ _ _ _
  simp_rw [hτ.measurable_set, Set.Preimage, Set.mem_Iic]
  intro i j
  rw [(_ : { x | τ x ≤ i } ∩ { x | τ x ≤ j } = { x | τ x ≤ LinearOrderₓ.min i j })]
  · exact f.mono (min_le_rightₓ i j) _ (hτ (LinearOrderₓ.min i j))
    
  · ext
    simp only [Set.mem_inter_eq, iff_selfₓ, le_min_iff, Set.mem_set_of_eq]
    

end LinearOrderₓ

end IsStoppingTime

section LinearOrderₓ

/-! ## Stopped value and stopped process -/


/-- Given a map `u : ι → α → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ x) x`. -/
def stoppedValue (u : ι → α → β) (τ : α → ι) : α → β := fun x => u (τ x) x

variable [LinearOrderₓ ι]

/-- Given a map `u : ι → α → E`, the stopped process with respect to `τ` is `u i x` if
`i ≤ τ x`, and `u (τ x) x` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stoppedProcess (u : ι → α → β) (τ : α → ι) : ι → α → β := fun i x => u (LinearOrderₓ.min i (τ x)) x

theorem stopped_process_eq_of_le {u : ι → α → β} {τ : α → ι} {i : ι} {x : α} (h : i ≤ τ x) :
    stoppedProcess u τ i x = u i x := by
  simp [stopped_process, min_eq_leftₓ h]

theorem stopped_process_eq_of_ge {u : ι → α → β} {τ : α → ι} {i : ι} {x : α} (h : τ x ≤ i) :
    stoppedProcess u τ i x = u (τ x) x := by
  simp [stopped_process, min_eq_rightₓ h]

-- We will need cadlag to generalize the following to continuous processes
section Nat

open Filtration

variable {f : Filtration ℕ m} {u : ℕ → α → β} {τ π : α → ℕ}

theorem stopped_value_sub_eq_sum [AddCommGroupₓ β] (hle : τ ≤ π) :
    stoppedValue u π - stoppedValue u τ = fun x => (∑ i in Finset.ico (τ x) (π x), u (i + 1) - u i) x := by
  ext x
  rw [Finset.sum_Ico_eq_sub _ (hle x), Finset.sum_range_sub, Finset.sum_range_sub]
  simp [stopped_value]

theorem stopped_value_sub_eq_sum' [AddCommGroupₓ β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun x =>
      (∑ i in Finset.range (N + 1), Set.indicator { x | τ x ≤ i ∧ i < π x } (u (i + 1) - u i)) x :=
  by
  rw [stopped_value_sub_eq_sum hle]
  ext x
  simp only [Finset.sum_apply, Finset.sum_indicator_eq_sum_filter]
  refine' Finset.sum_congr _ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Set.mem_set_of_eq, Finset.mem_range, Finset.mem_Ico]
  exact ⟨fun h => ⟨lt_transₓ h.2 (Nat.lt_succ_iffₓ.2 <| hbdd _), h⟩, fun h => h.2⟩

section AddCommMonoidₓ

variable [AddCommMonoidₓ β]

theorem stopped_value_eq {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
    stoppedValue u τ = fun x => (∑ i in Finset.range (N + 1), Set.indicator { x | τ x = i } (u i)) x := by
  ext y
  rw [stopped_value, Finset.sum_apply, Finset.sum_eq_single (τ y)]
  · rw [Set.indicator_of_mem]
    exact rfl
    
  · exact fun i hi hneq => Set.indicator_of_not_mem hneq.symm _
    
  · intro hy
    rw [Set.indicator_of_not_mem]
    exact fun _ => hy (Finset.mem_range.2 <| lt_of_le_of_ltₓ (hbdd _) (Nat.lt_succ_selfₓ _))
    

theorem stopped_process_eq (n : ℕ) :
    stoppedProcess u τ n =
      Set.indicator { a | n ≤ τ a } (u n) + ∑ i in Finset.range n, Set.indicator { a | τ a = i } (u i) :=
  by
  ext x
  rw [Pi.add_apply, Finset.sum_apply]
  cases le_or_ltₓ n (τ x)
  · rw [stopped_process_eq_of_le h, Set.indicator_of_mem, Finset.sum_eq_zero, add_zeroₓ]
    · intro m hm
      rw [Finset.mem_range] at hm
      exact Set.indicator_of_not_mem (lt_of_lt_of_leₓ hm h).Ne.symm _
      
    · exact h
      
    
  · rw [stopped_process_eq_of_ge (le_of_ltₓ h), Finset.sum_eq_single_of_mem (τ x)]
    · rw [Set.indicator_of_not_mem, zero_addₓ, Set.indicator_of_mem]
      · exact rfl
        
      -- refl does not work
      · exact not_leₓ.2 h
        
      
    · rwa [Finset.mem_range]
      
    · intro b hb hneq
      rw [Set.indicator_of_not_mem]
      exact hneq.symm
      
    

theorem Adapted.stopped_process [MeasurableSpace β] [HasMeasurableAdd₂ β] (hu : Adapted f u) (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) := by
  intro i
  rw [stopped_process_eq]
  refine' @Measurable.add _ _ _ _ (f i) _ _ _ _ _
  · refine' (hu i).indicator _
    convert MeasurableSet.union (hτ i).Compl (hτ.measurable_set_eq i)
    ext x
    change i ≤ τ x ↔ ¬τ x ≤ i ∨ τ x = i
    rw [not_leₓ, le_iff_lt_or_eqₓ, eq_comm]
    
  · refine' @Finset.measurable_sum' _ _ _ _ _ _ (f i) _ _ _
    refine' fun j hij => Measurable.indicator _ _
    · rw [Finset.mem_range] at hij
      exact Measurable.le (f.mono hij.le) (hu j)
      
    · rw [Finset.mem_range] at hij
      refine' f.mono hij.le _ _
      convert hτ.measurable_set_eq j
      
    

end AddCommMonoidₓ

section NormedGroup

variable [MeasurableSpace β] [NormedGroup β] [HasMeasurableAdd₂ β]

theorem measurable_stopped_process (hτ : IsStoppingTime f τ) (hu : Adapted f u) (n : ℕ) :
    Measurable (stoppedProcess u τ n) :=
  (hu.stoppedProcess hτ n).le (f.le _)

theorem mem_ℒp_stopped_process {p : ℝ≥0∞} [BorelSpace β] {μ : Measure α} (hτ : IsStoppingTime f τ)
    (hu : ∀ n, Memℒp (u n) p μ) (n : ℕ) : Memℒp (stoppedProcess u τ n) p μ := by
  rw [stopped_process_eq]
  refine' mem_ℒp.add _ _
  · exact mem_ℒp.indicator (f.le n { a : α | n ≤ τ a } (hτ.measurable_set_ge n)) (hu n)
    
  · suffices mem_ℒp (fun x => ∑ i : ℕ in Finset.range n, { a : α | τ a = i }.indicator (u i) x) p μ by
      convert this
      ext1 x
      simp only [Finset.sum_apply]
    refine' mem_ℒp_finset_sum _ fun i hi => mem_ℒp.indicator _ (hu i)
    exact f.le i { a : α | τ a = i } (hτ.measurable_set_eq i)
    

theorem integrable_stopped_process [BorelSpace β] {μ : Measure α} (hτ : IsStoppingTime f τ)
    (hu : ∀ n, Integrable (u n) μ) (n : ℕ) : Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]  at hu⊢
  exact mem_ℒp_stopped_process hτ hu n

theorem mem_ℒp_stopped_value {p : ℝ≥0∞} [BorelSpace β] {μ : Measure α} (hτ : IsStoppingTime f τ)
    (hu : ∀ n, Memℒp (u n) p μ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) : Memℒp (stoppedValue u τ) p μ := by
  rw [stopped_value_eq hbdd]
  suffices mem_ℒp (fun x => ∑ i : ℕ in Finset.range (N + 1), { a : α | τ a = i }.indicator (u i) x) p μ by
    convert this
    ext1 x
    simp only [Finset.sum_apply]
  refine' mem_ℒp_finset_sum _ fun i hi => mem_ℒp.indicator _ (hu i)
  exact f.le i { a : α | τ a = i } (hτ.measurable_set_eq i)

theorem integrable_stopped_value [BorelSpace β] {μ : Measure α} (hτ : IsStoppingTime f τ) (hu : ∀ n, Integrable (u n) μ)
    {N : ℕ} (hbdd : ∀ x, τ x ≤ N) : Integrable (stoppedValue u τ) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]  at hu⊢
  exact mem_ℒp_stopped_value hτ hu hbdd

end NormedGroup

end Nat

end LinearOrderₓ

end MeasureTheory

