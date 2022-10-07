/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathbin.Probability.Process.Adapted
import Mathbin.Topology.Instances.Discrete

/-!
# Stopping times, stopped processes and stopped values

Definition and properties of stopping times.

## Main definitions

* `measure_theory.is_stopping_time`: a stopping time with respect to some filtration `f` is a
  function `τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is
  `f i`-measurable
* `measure_theory.is_stopping_time.measurable_space`: the σ-algebra associated with a stopping time

## Main results

* `prog_measurable.stopped_process`: the stopped process of a progressively measurable process is
  progressively measurable.
* `mem_ℒp_stopped_process`: if a process belongs to `ℒp` at every time in `ℕ`, then its stopped
  process belongs to `ℒp` as well.

## Tags

stopping time, stochastic process

-/


open Filter Order TopologicalSpace

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace BigOperators

namespace MeasureTheory

variable {Ω β ι : Type _} {m : MeasurableSpace Ω}

/-! ### Stopping times -/


/-- A stopping time with respect to some filtration `f` is a function
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time
`i`, we may determine it with the information we have at time `i`. -/
def IsStoppingTime [Preorderₓ ι] (f : Filtration ι m) (τ : Ω → ι) :=
  ∀ i : ι, measurable_set[f i] <| { ω | τ ω ≤ i }

theorem is_stopping_time_const [Preorderₓ ι] (f : Filtration ι m) (i : ι) : IsStoppingTime f fun ω => i := fun j => by
  simp only [MeasurableSet.const]

section MeasurableSet

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m} {τ : Ω → ι}

protected theorem IsStoppingTime.measurable_set_le (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { ω | τ ω ≤ i } :=
  hτ i

theorem IsStoppingTime.measurable_set_lt_of_pred [PredOrder ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { ω | τ ω < i } := by
  by_cases hi_min:IsMin i
  · suffices { ω : Ω | τ ω < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_empty_iff_false, iff_falseₓ]
    rw [is_min_iff_forall_not_lt] at hi_min
    exact hi_min (τ ω)
    
  have : { ω : Ω | τ ω < i } = τ ⁻¹' Set.Iio i := rfl
  rw [this, ← Iic_pred_of_not_is_min hi_min]
  exact f.mono (pred_le i) _ (hτ.measurable_set_le <| pred i)

end Preorderₓ

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrderₓ ι] {τ : Ω → ι} {f : Filtration ι m}

protected theorem measurable_set_eq_of_countable_range (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[f i] { ω | τ ω = i } := by
  have : { ω | τ ω = i } = { ω | τ ω ≤ i } \ ⋃ (j ∈ Set.Range τ) (hj : j < i), { ω | τ ω ≤ j } := by
    ext1 a
    simp only [Set.mem_set_of_eq, Set.mem_range, Set.Union_exists, Set.Union_Union_eq', Set.mem_diff, Set.mem_Union,
      exists_propₓ, not_exists, not_and, not_leₓ]
    constructor <;> intro h
    · simp only [h, lt_iff_le_not_leₓ, le_reflₓ, and_imp, imp_self, implies_true_iff, and_selfₓ]
      
    · have h_lt_or_eq : τ a < i ∨ τ a = i := lt_or_eq_of_leₓ h.1
      rcases h_lt_or_eq with (h_lt | rfl)
      · exfalso
        exact h.2 a h_lt (le_reflₓ (τ a))
        
      · rfl
        
      
  rw [this]
  refine' (hτ.measurable_set_le i).diff _
  refine' MeasurableSet.bUnion h_countable fun j hj => _
  by_cases hji:j < i
  · simp only [hji, Set.Union_true]
    exact f.mono hji.le _ (hτ.measurable_set_le j)
    
  · simp only [hji, Set.Union_false]
    exact @MeasurableSet.empty _ (f i)
    

protected theorem measurable_set_eq_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { ω | τ ω = i } :=
  hτ.measurable_set_eq_of_countable_range (Set.to_countable _) i

protected theorem measurable_set_lt_of_countable_range (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable)
    (i : ι) : measurable_set[f i] { ω | τ ω < i } := by
  have : { ω | τ ω < i } = { ω | τ ω ≤ i } \ { ω | τ ω = i } := by
    ext1 ω
    simp [lt_iff_le_and_neₓ]
  rw [this]
  exact (hτ.measurable_set_le i).diff (hτ.measurable_set_eq_of_countable_range h_countable i)

protected theorem measurable_set_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[f i] { ω | τ ω < i } :=
  hτ.measurable_set_lt_of_countable_range (Set.to_countable _) i

protected theorem measurable_set_ge_of_countable_range {ι} [LinearOrderₓ ι] {τ : Ω → ι} {f : Filtration ι m}
    (hτ : IsStoppingTime f τ) (h_countable : (Set.Range τ).Countable) (i : ι) : measurable_set[f i] { ω | i ≤ τ ω } :=
  by
  have : { ω | i ≤ τ ω } = { ω | τ ω < i }ᶜ := by
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_compl_iff, not_ltₓ]
  rw [this]
  exact (hτ.measurable_set_lt_of_countable_range h_countable i).compl

protected theorem measurable_set_ge_of_countable {ι} [LinearOrderₓ ι] {τ : Ω → ι} {f : Filtration ι m} [Countable ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { ω | i ≤ τ ω } :=
  hτ.measurable_set_ge_of_countable_range (Set.to_countable _) i

end IsStoppingTime

end CountableStoppingTime

section LinearOrderₓ

variable [LinearOrderₓ ι] {f : Filtration ι m} {τ : Ω → ι}

theorem IsStoppingTime.measurable_set_gt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { ω | i < τ ω } := by
  have : { ω | i < τ ω } = { ω | τ ω ≤ i }ᶜ := by
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_compl_iff, not_leₓ]
  rw [this]
  exact (hτ.measurable_set_le i).compl

section TopologicalSpace

variable [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]

/-- Auxiliary lemma for `is_stopping_time.measurable_set_lt`. -/
theorem IsStoppingTime.measurable_set_lt_of_is_lub (hτ : IsStoppingTime f τ) (i : ι) (h_lub : IsLub (Set.Iio i) i) :
    measurable_set[f i] { ω | τ ω < i } := by
  by_cases hi_min:IsMin i
  · suffices { ω | τ ω < i } = ∅ by
      rw [this]
      exact @MeasurableSet.empty _ (f i)
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_empty_iff_false, iff_falseₓ]
    exact is_min_iff_forall_not_lt.mp hi_min (τ ω)
    
  obtain ⟨seq, -, -, h_tendsto, h_bound⟩ :
    ∃ seq : ℕ → ι, Monotoneₓ seq ∧ (∀ j, seq j ≤ i) ∧ tendsto seq at_top (𝓝 i) ∧ ∀ j, seq j < i
  exact h_lub.exists_seq_monotone_tendsto (not_is_min_iff.mp hi_min)
  have h_Ioi_eq_Union : Set.Iio i = ⋃ j, { k | k ≤ seq j } := by
    ext1 k
    simp only [Set.mem_Iio, Set.mem_Union, Set.mem_set_of_eq]
    refine' ⟨fun hk_lt_i => _, fun h_exists_k_le_seq => _⟩
    · rw [tendsto_at_top'] at h_tendsto
      have h_nhds : Set.Ici k ∈ 𝓝 i := mem_nhds_iff.mpr ⟨Set.Ioi k, Set.Ioi_subset_Ici le_rflₓ, is_open_Ioi, hk_lt_i⟩
      obtain ⟨a, ha⟩ : ∃ a : ℕ, ∀ b : ℕ, b ≥ a → k ≤ seq b := h_tendsto (Set.Ici k) h_nhds
      exact ⟨a, ha a le_rflₓ⟩
      
    · obtain ⟨j, hk_seq_j⟩ := h_exists_k_le_seq
      exact hk_seq_j.trans_lt (h_bound j)
      
  have h_lt_eq_preimage : { ω | τ ω < i } = τ ⁻¹' Set.Iio i := by
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_preimage, Set.mem_Iio]
  rw [h_lt_eq_preimage, h_Ioi_eq_Union]
  simp only [Set.preimage_Union, Set.preimage_set_of_eq]
  exact MeasurableSet.Union fun n => f.mono (h_bound n).le _ (hτ.measurable_set_le (seq n))

theorem IsStoppingTime.measurable_set_lt (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { ω | τ ω < i } := by
  obtain ⟨i', hi'_lub⟩ : ∃ i', IsLub (Set.Iio i) i'
  exact exists_lub_Iio i
  cases' lub_Iio_eq_self_or_Iio_eq_Iic i hi'_lub with hi'_eq_i h_Iio_eq_Iic
  · rw [← hi'_eq_i] at hi'_lub⊢
    exact hτ.measurable_set_lt_of_is_lub i' hi'_lub
    
  · have h_lt_eq_preimage : { ω : Ω | τ ω < i } = τ ⁻¹' Set.Iio i := rfl
    rw [h_lt_eq_preimage, h_Iio_eq_Iic]
    exact f.mono (lub_Iio_le i hi'_lub) _ (hτ.measurable_set_le i')
    

theorem IsStoppingTime.measurable_set_ge (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { ω | i ≤ τ ω } := by
  have : { ω | i ≤ τ ω } = { ω | τ ω < i }ᶜ := by
    ext1 ω
    simp only [Set.mem_set_of_eq, Set.mem_compl_iff, not_ltₓ]
  rw [this]
  exact (hτ.measurable_set_lt i).compl

theorem IsStoppingTime.measurable_set_eq (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[f i] { ω | τ ω = i } := by
  have : { ω | τ ω = i } = { ω | τ ω ≤ i } ∩ { ω | τ ω ≥ i } := by
    ext1 ω
    simp only [Set.mem_set_of_eq, ge_iff_leₓ, Set.mem_inter_iff, le_antisymm_iffₓ]
  rw [this]
  exact (hτ.measurable_set_le i).inter (hτ.measurable_set_ge i)

theorem IsStoppingTime.measurable_set_eq_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { ω | τ ω = i } :=
  f.mono hle _ <| hτ.measurable_set_eq i

theorem IsStoppingTime.measurable_set_lt_le (hτ : IsStoppingTime f τ) {i j : ι} (hle : i ≤ j) :
    measurable_set[f j] { ω | τ ω < i } :=
  f.mono hle _ <| hτ.measurable_set_lt i

end TopologicalSpace

end LinearOrderₓ

section Countable

theorem is_stopping_time_of_measurable_set_eq [Preorderₓ ι] [Countable ι] {f : Filtration ι m} {τ : Ω → ι}
    (hτ : ∀ i, measurable_set[f i] { ω | τ ω = i }) : IsStoppingTime f τ := by
  intro i
  rw [show { ω | τ ω ≤ i } = ⋃ k ≤ i, { ω | τ ω = k } by
      ext
      simp]
  refine' MeasurableSet.bUnion (Set.to_countable _) fun k hk => _
  exact f.mono hk _ (hτ k)

end Countable

end MeasurableSet

namespace IsStoppingTime

protected theorem max [LinearOrderₓ ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => max (τ ω) (π ω) := by
  intro i
  simp_rw [max_le_iff, Set.set_of_and]
  exact (hτ i).inter (hπ i)

protected theorem max_const [LinearOrderₓ ι] {f : Filtration ι m} {τ : Ω → ι} (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun ω => max (τ ω) i :=
  hτ.max (is_stopping_time_const f i)

protected theorem min [LinearOrderₓ ι] {f : Filtration ι m} {τ π : Ω → ι} (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : IsStoppingTime f fun ω => min (τ ω) (π ω) := by
  intro i
  simp_rw [min_le_iff, Set.set_of_or]
  exact (hτ i).union (hπ i)

protected theorem min_const [LinearOrderₓ ι] {f : Filtration ι m} {τ : Ω → ι} (hτ : IsStoppingTime f τ) (i : ι) :
    IsStoppingTime f fun ω => min (τ ω) i :=
  hτ.min (is_stopping_time_const f i)

theorem add_const [AddGroupₓ ι] [Preorderₓ ι] [CovariantClass ι ι (Function.swap (· + ·)) (· ≤ ·)]
    [CovariantClass ι ι (· + ·) (· ≤ ·)] {f : Filtration ι m} {τ : Ω → ι} (hτ : IsStoppingTime f τ) {i : ι}
    (hi : 0 ≤ i) : IsStoppingTime f fun ω => τ ω + i := by
  intro j
  simp_rw [← le_sub_iff_add_le]
  exact f.mono (sub_le_self j hi) _ (hτ (j - i))

theorem add_const_nat {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) {i : ℕ} :
    IsStoppingTime f fun ω => τ ω + i := by
  refine' is_stopping_time_of_measurable_set_eq fun j => _
  by_cases hij:i ≤ j
  · simp_rw [eq_comm, ← Nat.sub_eq_iff_eq_addₓ hij, eq_comm]
    exact f.mono (j.sub_le i) _ (hτ.measurable_set_eq (j - i))
    
  · rw [not_leₓ] at hij
    convert MeasurableSet.empty
    ext ω
    simp only [Set.mem_empty_iff_false, iff_falseₓ]
    rintro (hx : τ ω + i = j)
    linarith
    

-- generalize to certain countable type?
theorem add {f : Filtration ℕ m} {τ π : Ω → ℕ} (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    IsStoppingTime f (τ + π) := by
  intro i
  rw [(_ : { ω | (τ + π) ω ≤ i } = ⋃ k ≤ i, { ω | π ω = k } ∩ { ω | τ ω + k ≤ i })]
  · exact
      MeasurableSet.Union fun k => MeasurableSet.Union fun hk => (hπ.measurable_set_eq_le hk).inter (hτ.add_const_nat i)
    
  ext ω
  simp only [Pi.add_apply, Set.mem_set_of_eq, Set.mem_Union, Set.mem_inter_iff, exists_propₓ]
  refine' ⟨fun h => ⟨π ω, by linarith, rfl, h⟩, _⟩
  rintro ⟨j, hj, rfl, h⟩
  assumption

section Preorderₓ

variable [Preorderₓ ι] {f : Filtration ι m} {τ π : Ω → ι}

/-- The associated σ-algebra with a stopping time. -/
protected def measurableSpace (hτ : IsStoppingTime f τ) : MeasurableSpace Ω where
  MeasurableSet' := fun s => ∀ i : ι, measurable_set[f i] (s ∩ { ω | τ ω ≤ i })
  measurable_set_empty := fun i => (Set.empty_inter { ω | τ ω ≤ i }).symm ▸ @MeasurableSet.empty _ (f i)
  measurable_set_compl := fun s hs i => by
    rw [(_ : sᶜ ∩ { ω | τ ω ≤ i } = (sᶜ ∪ { ω | τ ω ≤ i }ᶜ) ∩ { ω | τ ω ≤ i })]
    · refine' MeasurableSet.inter _ _
      · rw [← Set.compl_inter]
        exact (hs i).compl
        
      · exact hτ i
        
      
    · rw [Set.union_inter_distrib_right]
      simp only [Set.compl_inter_self, Set.union_empty]
      
  measurable_set_Union := fun s hs i => by
    rw [forall_swap] at hs
    rw [Set.Union_inter]
    exact MeasurableSet.Union (hs i)

protected theorem measurable_set (hτ : IsStoppingTime f τ) (s : Set Ω) :
    measurable_set[hτ.MeasurableSpace] s ↔ ∀ i : ι, measurable_set[f i] (s ∩ { ω | τ ω ≤ i }) :=
  Iff.rfl

theorem measurable_space_mono (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (hle : τ ≤ π) :
    hτ.MeasurableSpace ≤ hπ.MeasurableSpace := by
  intro s hs i
  rw [(_ : s ∩ { ω | π ω ≤ i } = s ∩ { ω | τ ω ≤ i } ∩ { ω | π ω ≤ i })]
  · exact (hs i).inter (hπ i)
    
  · ext
    simp only [Set.mem_inter_iff, iff_self_and, And.congr_left_iffₓ, Set.mem_set_of_eq]
    intro hle' _
    exact le_transₓ (hle _) hle'
    

theorem measurable_space_le_of_countable [Countable ι] (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { ω | τ ω ≤ i }) at hs
  rw [(_ : s = ⋃ i, s ∩ { ω | τ ω ≤ i })]
  · exact MeasurableSet.Union fun i => f.le i _ (hs i)
    
  · ext ω
    constructor <;> rw [Set.mem_Union]
    · exact fun hx => ⟨τ ω, hx, le_rflₓ⟩
      
    · rintro ⟨_, hx, _⟩
      exact hx
      
    

theorem measurable_space_le' [IsCountablyGenerated (atTop : Filter ι)] [(atTop : Filter ι).ne_bot]
    (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { ω | τ ω ≤ i }) at hs
  obtain ⟨seq : ℕ → ι, h_seq_tendsto⟩ := at_top.exists_seq_tendsto
  rw [(_ : s = ⋃ n, s ∩ { ω | τ ω ≤ seq n })]
  · exact MeasurableSet.Union fun i => f.le (seq i) _ (hs (seq i))
    
  · ext ω
    constructor <;> rw [Set.mem_Union]
    · intro hx
      suffices : ∃ i, τ ω ≤ seq i
      exact ⟨this.some, hx, this.some_spec⟩
      rw [tendsto_at_top] at h_seq_tendsto
      exact (h_seq_tendsto (τ ω)).exists
      
    · rintro ⟨_, hx, _⟩
      exact hx
      
    
  all_goals infer_instance

theorem measurable_space_le {ι} [SemilatticeSup ι] {f : Filtration ι m} {τ : Ω → ι}
    [IsCountablyGenerated (atTop : Filter ι)] (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m := by
  cases is_empty_or_nonempty ι
  · haveI : IsEmpty Ω := ⟨fun ω => IsEmpty.false (τ ω)⟩
    intro s hsτ
    suffices hs : s = ∅
    · rw [hs]
      exact MeasurableSet.empty
      
    haveI : Unique (Set Ω) := Set.uniqueEmpty
    rw [Unique.eq_default s, Unique.eq_default ∅]
    
  exact measurable_space_le' hτ

example {f : Filtration ℕ m} {τ : Ω → ℕ} (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m :=
  hτ.measurable_space_le

example {f : Filtration ℝ m} {τ : Ω → ℝ} (hτ : IsStoppingTime f τ) : hτ.MeasurableSpace ≤ m :=
  hτ.measurable_space_le

@[simp]
theorem measurable_space_const (f : Filtration ι m) (i : ι) : (is_stopping_time_const f i).MeasurableSpace = f i := by
  ext1 s
  change measurable_set[(is_stopping_time_const f i).MeasurableSpace] s ↔ measurable_set[f i] s
  rw [is_stopping_time.measurable_set]
  constructor <;> intro h
  · specialize h i
    simpa only [le_reflₓ, Set.set_of_true, Set.inter_univ] using h
    
  · intro j
    by_cases hij:i ≤ j
    · simp only [hij, Set.set_of_true, Set.inter_univ]
      exact f.mono hij _ h
      
    · simp only [hij, Set.set_of_false, Set.inter_empty, MeasurableSet.empty]
      
    

theorem measurable_set_inter_eq_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    measurable_set[hτ.MeasurableSpace] (s ∩ { ω | τ ω = i }) ↔ measurable_set[f i] (s ∩ { ω | τ ω = i }) := by
  have : ∀ j, { ω : Ω | τ ω = i } ∩ { ω : Ω | τ ω ≤ j } = { ω : Ω | τ ω = i } ∩ { ω | i ≤ j } := by
    intro j
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_set_of_eq, And.congr_right_iff]
    intro hxi
    rw [hxi]
  constructor <;> intro h
  · specialize h i
    simpa only [Set.inter_assoc, this, le_reflₓ, Set.set_of_true, Set.inter_univ] using h
    
  · intro j
    rw [Set.inter_assoc, this]
    by_cases hij:i ≤ j
    · simp only [hij, Set.set_of_true, Set.inter_univ]
      exact f.mono hij _ h
      
    · simp [hij]
      
    

theorem measurable_space_le_of_le_const (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) :
    hτ.MeasurableSpace ≤ f i :=
  (measurable_space_mono hτ _ hτ_le).trans (measurable_space_const _ _).le

theorem measurable_space_le_of_le (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) : hτ.MeasurableSpace ≤ m :=
  (hτ.measurable_space_le_of_le_const hτ_le).trans (f.le n)

theorem le_measurable_space_of_const_le (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, i ≤ τ ω) :
    f i ≤ hτ.MeasurableSpace :=
  (measurable_space_const _ _).symm.le.trans (measurable_space_mono _ hτ hτ_le)

end Preorderₓ

instance sigma_finite_stopping_time {ι} [SemilatticeSup ι] [OrderBot ι] [(Filter.atTop : Filter ι).IsCountablyGenerated]
    {μ : Measure Ω} {f : Filtration ι m} {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) :
    SigmaFinite (μ.trim hτ.measurable_space_le) := by
  refine' sigma_finite_trim_mono hτ.measurable_space_le _
  · exact f ⊥
    
  · exact hτ.le_measurable_space_of_const_le fun _ => bot_le
    
  · infer_instance
    

instance sigma_finite_stopping_time_of_le {ι} [SemilatticeSup ι] [OrderBot ι] {μ : Measure Ω} {f : Filtration ι m}
    {τ : Ω → ι} [SigmaFiniteFiltration μ f] (hτ : IsStoppingTime f τ) {n : ι} (hτ_le : ∀ ω, τ ω ≤ n) :
    SigmaFinite (μ.trim (hτ.measurable_space_le_of_le hτ_le)) := by
  refine' sigma_finite_trim_mono (hτ.measurable_space_le_of_le hτ_le) _
  · exact f ⊥
    
  · exact hτ.le_measurable_space_of_const_le fun _ => bot_le
    
  · infer_instance
    

section LinearOrderₓ

variable [LinearOrderₓ ι] {f : Filtration ι m} {τ π : Ω → ι}

protected theorem measurable_set_le' (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { ω | τ ω ≤ i } := by
  intro j
  have : { ω : Ω | τ ω ≤ i } ∩ { ω : Ω | τ ω ≤ j } = { ω : Ω | τ ω ≤ min i j } := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_set_of_eq, le_min_iff]
  rw [this]
  exact f.mono (min_le_rightₓ i j) _ (hτ _)

protected theorem measurable_set_gt' (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { ω | i < τ ω } := by
  have : { ω : Ω | i < τ ω } = { ω : Ω | τ ω ≤ i }ᶜ := by
    ext1 ω
    simp
  rw [this]
  exact (hτ.measurable_set_le' i).compl

protected theorem measurable_set_eq' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | τ ω = i } := by
  rw [← Set.univ_inter { ω | τ ω = i }, measurable_set_inter_eq_iff, Set.univ_inter]
  exact hτ.measurable_set_eq i

protected theorem measurable_set_ge' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | i ≤ τ ω } := by
  have : { ω | i ≤ τ ω } = { ω | τ ω = i } ∪ { ω | i < τ ω } := by
    ext1 ω
    simp only [le_iff_lt_or_eqₓ, Set.mem_set_of_eq, Set.mem_union]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurable_set_eq' i).union (hτ.measurable_set_gt' i)

protected theorem measurable_set_lt' [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (hτ : IsStoppingTime f τ) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | τ ω < i } := by
  have : { ω | τ ω < i } = { ω | τ ω ≤ i } \ { ω | τ ω = i } := by
    ext1 ω
    simp only [lt_iff_le_and_neₓ, Set.mem_set_of_eq, Set.mem_diff]
  rw [this]
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq' i)

section Countable

protected theorem measurable_set_eq_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.Range τ).Countable) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | τ ω = i } := by
  rw [← Set.univ_inter { ω | τ ω = i }, measurable_set_inter_eq_iff, Set.univ_inter]
  exact hτ.measurable_set_eq_of_countable_range h_countable i

protected theorem measurable_set_eq_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { ω | τ ω = i } :=
  hτ.measurable_set_eq_of_countable_range' (Set.to_countable _) i

protected theorem measurable_set_ge_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.Range τ).Countable) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | i ≤ τ ω } := by
  have : { ω | i ≤ τ ω } = { ω | τ ω = i } ∪ { ω | i < τ ω } := by
    ext1 ω
    simp only [le_iff_lt_or_eqₓ, Set.mem_set_of_eq, Set.mem_union]
    rw [@eq_comm _ i, or_comm]
  rw [this]
  exact (hτ.measurable_set_eq_of_countable_range' h_countable i).union (hτ.measurable_set_gt' i)

protected theorem measurable_set_ge_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { ω | i ≤ τ ω } :=
  hτ.measurable_set_ge_of_countable_range' (Set.to_countable _) i

protected theorem measurable_set_lt_of_countable_range' (hτ : IsStoppingTime f τ)
    (h_countable : (Set.Range τ).Countable) (i : ι) : measurable_set[hτ.MeasurableSpace] { ω | τ ω < i } := by
  have : { ω | τ ω < i } = { ω | τ ω ≤ i } \ { ω | τ ω = i } := by
    ext1 ω
    simp only [lt_iff_le_and_neₓ, Set.mem_set_of_eq, Set.mem_diff]
  rw [this]
  exact (hτ.measurable_set_le' i).diff (hτ.measurable_set_eq_of_countable_range' h_countable i)

protected theorem measurable_set_lt_of_countable' [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    measurable_set[hτ.MeasurableSpace] { ω | τ ω < i } :=
  hτ.measurable_set_lt_of_countable_range' (Set.to_countable _) i

protected theorem measurable_space_le_of_countable_range (hτ : IsStoppingTime f τ)
    (h_countable : (Set.Range τ).Countable) : hτ.MeasurableSpace ≤ m := by
  intro s hs
  change ∀ i, measurable_set[f i] (s ∩ { ω | τ ω ≤ i }) at hs
  rw [(_ : s = ⋃ i ∈ Set.Range τ, s ∩ { ω | τ ω ≤ i })]
  · exact MeasurableSet.bUnion h_countable fun i _ => f.le i _ (hs i)
    
  · ext ω
    constructor <;> rw [Set.mem_Union]
    · exact fun hx => ⟨τ ω, by simpa using hx⟩
      
    · rintro ⟨i, hx⟩
      simp only [Set.mem_range, Set.Union_exists, Set.mem_Union, Set.mem_inter_iff, Set.mem_set_of_eq, exists_propₓ,
        exists_and_distrib_rightₓ] at hx
      exact hx.1.2
      
    

end Countable

protected theorem measurable [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) : measurable[hτ.MeasurableSpace] τ :=
  @measurable_of_Iic ι Ω _ _ _ hτ.MeasurableSpace _ _ _ _ fun i => hτ.measurable_set_le' i

protected theorem measurable_of_le [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] (hτ : IsStoppingTime f τ) {i : ι} (hτ_le : ∀ ω, τ ω ≤ i) : measurable[f i] τ :=
  hτ.Measurable.mono (measurable_space_le_of_le_const _ hτ_le) le_rflₓ

theorem measurable_space_min (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    (hτ.min hπ).MeasurableSpace = hτ.MeasurableSpace ⊓ hπ.MeasurableSpace := by
  refine' le_antisymmₓ _ _
  · exact
      le_inf (measurable_space_mono _ hτ fun _ => min_le_leftₓ _ _)
        (measurable_space_mono _ hπ fun _ => min_le_rightₓ _ _)
    
  · intro s
    change
      measurable_set[hτ.measurable_space] s ∧ measurable_set[hπ.measurable_space] s →
        measurable_set[(hτ.min hπ).MeasurableSpace] s
    simp_rw [is_stopping_time.measurable_set]
    have : ∀ i, { ω | min (τ ω) (π ω) ≤ i } = { ω | τ ω ≤ i } ∪ { ω | π ω ≤ i } := by
      intro i
      ext1 ω
      simp
    simp_rw [this, Set.inter_union_distrib_left]
    exact fun h i => (h.left i).union (h.right i)
    

theorem measurable_set_min_iff (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    measurable_set[(hτ.min hπ).MeasurableSpace] s ↔
      measurable_set[hτ.MeasurableSpace] s ∧ measurable_set[hπ.MeasurableSpace] s :=
  by
  rw [measurable_space_min]
  rfl

theorem measurable_space_min_const (hτ : IsStoppingTime f τ) {i : ι} :
    (hτ.min_const i).MeasurableSpace = hτ.MeasurableSpace ⊓ f i := by
  rw [hτ.measurable_space_min (is_stopping_time_const _ i), measurable_space_const]

theorem measurable_set_min_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) {i : ι} :
    measurable_set[(hτ.min_const i).MeasurableSpace] s ↔ measurable_set[hτ.MeasurableSpace] s ∧ measurable_set[f i] s :=
  by rw [measurable_space_min_const, MeasurableSpace.measurable_set_inf]

theorem measurable_set_inter_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω)
    (hs : measurable_set[hτ.MeasurableSpace] s) : measurable_set[(hτ.min hπ).MeasurableSpace] (s ∩ { ω | τ ω ≤ π ω }) :=
  by
  simp_rw [is_stopping_time.measurable_set] at hs⊢
  intro i
  have :
    s ∩ { ω | τ ω ≤ π ω } ∩ { ω | min (τ ω) (π ω) ≤ i } =
      s ∩ { ω | τ ω ≤ i } ∩ { ω | min (τ ω) (π ω) ≤ i } ∩ { ω | min (τ ω) i ≤ min (min (τ ω) (π ω)) i } :=
    by
    ext1 ω
    simp only [min_le_iff, Set.mem_inter_iff, Set.mem_set_of_eq, le_min_iff, le_reflₓ, true_andₓ, and_trueₓ, true_orₓ,
      or_trueₓ]
    by_cases hτi:τ ω ≤ i
    · simp only [hτi, true_orₓ, and_trueₓ, And.congr_right_iff]
      intro hx
      constructor <;> intro h
      · exact Or.inl h
        
      · cases h
        · exact h
          
        · exact hτi.trans h
          
        
      
    simp only [hτi, false_orₓ, and_falseₓ, false_andₓ, iff_falseₓ, not_and, not_leₓ, and_imp]
    refine' fun hx hτ_le_π => lt_of_lt_of_leₓ _ hτ_le_π
    rw [← not_leₓ]
    exact hτi
  rw [this]
  refine' ((hs i).inter ((hτ.min hπ) i)).inter _
  apply measurable_set_le
  · exact (hτ.min_const i).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact ((hτ.min hπ).min_const i).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_inter_le_iff [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) (s : Set Ω) :
    measurable_set[hτ.MeasurableSpace] (s ∩ { ω | τ ω ≤ π ω }) ↔
      measurable_set[(hτ.min hπ).MeasurableSpace] (s ∩ { ω | τ ω ≤ π ω }) :=
  by
  constructor <;> intro h
  · have : s ∩ { ω | τ ω ≤ π ω } = s ∩ { ω | τ ω ≤ π ω } ∩ { ω | τ ω ≤ π ω } := by rw [Set.inter_assoc, Set.inter_self]
    rw [this]
    exact measurable_set_inter_le _ _ _ h
    
  · rw [measurable_set_min_iff] at h
    exact h.1
    

theorem measurable_set_inter_le_const_iff (hτ : IsStoppingTime f τ) (s : Set Ω) (i : ι) :
    measurable_set[hτ.MeasurableSpace] (s ∩ { ω | τ ω ≤ i }) ↔
      measurable_set[(hτ.min_const i).MeasurableSpace] (s ∩ { ω | τ ω ≤ i }) :=
  by
  rw [is_stopping_time.measurable_set_min_iff hτ (is_stopping_time_const _ i), is_stopping_time.measurable_space_const,
    is_stopping_time.measurable_set]
  refine' ⟨fun h => ⟨h, _⟩, fun h j => h.1 j⟩
  specialize h i
  rwa [Set.inter_assoc, Set.inter_self] at h

theorem measurable_set_le_stopping_time [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    measurable_set[hτ.MeasurableSpace] { ω | τ ω ≤ π ω } := by
  rw [hτ.measurable_set]
  intro j
  have : { ω | τ ω ≤ π ω } ∩ { ω | τ ω ≤ j } = { ω | min (τ ω) j ≤ min (π ω) j } ∩ { ω | τ ω ≤ j } := by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_set_of_eq, min_le_iff, le_min_iff, le_reflₓ, and_trueₓ, And.congr_left_iffₓ]
    intro h
    simp only [h, or_selfₓ, and_trueₓ]
    by_cases hj:j ≤ π ω
    · simp only [hj, h.trans hj, or_selfₓ]
      
    · simp only [hj, or_falseₓ]
      
  rw [this]
  refine' MeasurableSet.inter _ (hτ.measurable_set_le j)
  apply measurable_set_le
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_stopping_time_le [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) :
    measurable_set[hπ.MeasurableSpace] { ω | τ ω ≤ π ω } := by
  suffices measurable_set[(hτ.min hπ).MeasurableSpace] { ω : Ω | τ ω ≤ π ω } by
    rw [measurable_set_min_iff hτ hπ] at this
    exact this.2
  rw [← Set.univ_inter { ω : Ω | τ ω ≤ π ω }, ← hτ.measurable_set_inter_le_iff hπ, Set.univ_inter]
  exact measurable_set_le_stopping_time hτ hπ

theorem measurable_set_eq_stopping_time [AddGroupₓ ι] [TopologicalSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι] [HasMeasurableSub₂ ι]
    (hτ : IsStoppingTime f τ) (hπ : IsStoppingTime f π) : measurable_set[hτ.MeasurableSpace] { ω | τ ω = π ω } := by
  rw [hτ.measurable_set]
  intro j
  have : { ω | τ ω = π ω } ∩ { ω | τ ω ≤ j } = { ω | min (τ ω) j = min (π ω) j } ∩ { ω | τ ω ≤ j } ∩ { ω | π ω ≤ j } :=
    by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_set_of_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
      
    · rw [← h.1]
      exact h.2
      
    · cases' h with h' hσ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_leftₓ hτ_le, min_eq_leftₓ hσ_le] at h_eq
      
  rw [this]
  refine' MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurable_set_le j)) (hπ.measurable_set_le j)
  apply measurable_set_eq_fun
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

theorem measurable_set_eq_stopping_time_of_countable [Countable ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [MeasurableSingletonClass ι] [SecondCountableTopology ι] (hτ : IsStoppingTime f τ)
    (hπ : IsStoppingTime f π) : measurable_set[hτ.MeasurableSpace] { ω | τ ω = π ω } := by
  rw [hτ.measurable_set]
  intro j
  have : { ω | τ ω = π ω } ∩ { ω | τ ω ≤ j } = { ω | min (τ ω) j = min (π ω) j } ∩ { ω | τ ω ≤ j } ∩ { ω | π ω ≤ j } :=
    by
    ext1 ω
    simp only [Set.mem_inter_iff, Set.mem_set_of_eq]
    refine' ⟨fun h => ⟨⟨_, h.2⟩, _⟩, fun h => ⟨_, h.1.2⟩⟩
    · rw [h.1]
      
    · rw [← h.1]
      exact h.2
      
    · cases' h with h' hπ_le
      cases' h' with h_eq hτ_le
      rwa [min_eq_leftₓ hτ_le, min_eq_leftₓ hπ_le] at h_eq
      
  rw [this]
  refine' MeasurableSet.inter (MeasurableSet.inter _ (hτ.measurable_set_le j)) (hπ.measurable_set_le j)
  apply measurable_set_eq_fun_of_countable
  · exact (hτ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    
  · exact (hπ.min_const j).measurable_of_le fun _ => min_le_rightₓ _ _
    

end LinearOrderₓ

end IsStoppingTime

section LinearOrderₓ

/-! ## Stopped value and stopped process -/


/-- Given a map `u : ι → Ω → E`, its stopped value with respect to the stopping
time `τ` is the map `x ↦ u (τ ω) ω`. -/
def stoppedValue (u : ι → Ω → β) (τ : Ω → ι) : Ω → β := fun ω => u (τ ω) ω

theorem stopped_value_const (u : ι → Ω → β) (i : ι) : (stoppedValue u fun ω => i) = u i :=
  rfl

variable [LinearOrderₓ ι]

/-- Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if
`i ≤ τ ω`, and `u (τ ω) ω` otherwise.

Intuitively, the stopped process stops evolving once the stopping time has occured. -/
def stoppedProcess (u : ι → Ω → β) (τ : Ω → ι) : ι → Ω → β := fun i ω => u (min i (τ ω)) ω

theorem stopped_process_eq_stopped_value {u : ι → Ω → β} {τ : Ω → ι} :
    stoppedProcess u τ = fun i => stoppedValue u fun ω => min i (τ ω) :=
  rfl

theorem stopped_value_stopped_process {u : ι → Ω → β} {τ σ : Ω → ι} :
    stoppedValue (stoppedProcess u τ) σ = stoppedValue u fun ω => min (σ ω) (τ ω) :=
  rfl

theorem stopped_process_eq_of_le {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : i ≤ τ ω) :
    stoppedProcess u τ i ω = u i ω := by simp [stopped_process, min_eq_leftₓ h]

theorem stopped_process_eq_of_ge {u : ι → Ω → β} {τ : Ω → ι} {i : ι} {ω : Ω} (h : τ ω ≤ i) :
    stoppedProcess u τ i ω = u (τ ω) ω := by simp [stopped_process, min_eq_rightₓ h]

section ProgMeasurable

variable [MeasurableSpace ι] [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [BorelSpace ι]
  [TopologicalSpace β] {u : ι → Ω → β} {τ : Ω → ι} {f : Filtration ι m}

theorem prog_measurable_min_stopping_time [MetrizableSpace ι] (hτ : IsStoppingTime f τ) :
    ProgMeasurable f fun i ω => min i (τ ω) := by
  intro i
  let m_prod : MeasurableSpace (Set.Iic i × Ω) := MeasurableSpace.prod _ (f i)
  let m_set : ∀ t : Set (Set.Iic i × Ω), MeasurableSpace t := fun _ => @Subtype.measurableSpace (Set.Iic i × Ω) _ m_prod
  let s := { p : Set.Iic i × Ω | τ p.2 ≤ i }
  have hs : measurable_set[m_prod] s := @measurable_snd (Set.Iic i) Ω _ (f i) _ (hτ i)
  have h_meas_fst : ∀ t : Set (Set.Iic i × Ω), measurable[m_set t] fun x : t => ((x : Set.Iic i × Ω).fst : ι) :=
    fun t => (@measurable_subtype_coe (Set.Iic i × Ω) m_prod _).fst.subtype_coe
  apply Measurable.strongly_measurable
  refine' measurable_of_restrict_of_restrict_compl hs _ _
  · refine' @Measurable.min _ _ _ _ _ (m_set s) _ _ _ _ _ (h_meas_fst s) _
    refine' @measurable_of_Iic ι s _ _ _ (m_set s) _ _ _ _ fun j => _
    have h_set_eq :
      (fun x : s => τ (x : Set.Iic i × Ω).snd) ⁻¹' Set.Iic j =
        (fun x : s => (x : Set.Iic i × Ω).snd) ⁻¹' { ω | τ ω ≤ min i j } :=
      by
      ext1 ω
      simp only [Set.mem_preimage, Set.mem_Iic, iff_and_self, le_min_iff, Set.mem_set_of_eq]
      exact fun _ => ω.prop
    rw [h_set_eq]
    suffices h_meas : @Measurable _ _ (m_set s) (f i) fun x : s => (x : Set.Iic i × Ω).snd
    exact h_meas (f.mono (min_le_leftₓ _ _) _ (hτ.measurable_set_le (min i j)))
    exact measurable_snd.comp (@measurable_subtype_coe _ m_prod _)
    
  · suffices h_min_eq_left :
      (fun x : sᶜ => min (↑(x : Set.Iic i × Ω).fst) (τ (x : Set.Iic i × Ω).snd)) = fun x : sᶜ =>
        ↑(x : Set.Iic i × Ω).fst
    · rw [Set.restrict, h_min_eq_left]
      exact h_meas_fst _
      
    ext1 ω
    rw [min_eq_leftₓ]
    have hx_fst_le : ↑(ω : Set.Iic i × Ω).fst ≤ i := (ω : Set.Iic i × Ω).fst.Prop
    refine' hx_fst_le.trans (le_of_ltₓ _)
    convert ω.prop
    simp only [not_leₓ, Set.mem_compl_iff, Set.mem_set_of_eq]
    

theorem ProgMeasurable.stopped_process [MetrizableSpace ι] (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    ProgMeasurable f (stoppedProcess u τ) :=
  h.comp (prog_measurable_min_stopping_time hτ) fun i x => min_le_leftₓ _ _

theorem ProgMeasurable.adapted_stopped_process [MetrizableSpace ι] (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) :=
  (h.stoppedProcess hτ).Adapted

theorem ProgMeasurable.strongly_measurable_stopped_process [MetrizableSpace ι] (hu : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) (i : ι) : StronglyMeasurable (stoppedProcess u τ i) :=
  (hu.adapted_stopped_process hτ i).mono (f.le _)

theorem strongly_measurable_stopped_value_of_le (h : ProgMeasurable f u) (hτ : IsStoppingTime f τ) {n : ι}
    (hτ_le : ∀ ω, τ ω ≤ n) : strongly_measurable[f n] (stoppedValue u τ) := by
  have : stopped_value u τ = (fun p : Set.Iic n × Ω => u (↑p.fst) p.snd) ∘ fun ω => (⟨τ ω, hτ_le ω⟩, ω) := by
    ext1 ω
    simp only [stopped_value, Function.comp_app, Subtype.coe_mk]
  rw [this]
  refine' strongly_measurable.comp_measurable (h n) _
  exact (hτ.measurable_of_le hτ_le).subtype_mk.prod_mk measurable_id

theorem measurable_stopped_value [MetrizableSpace β] [MeasurableSpace β] [BorelSpace β] (hf_prog : ProgMeasurable f u)
    (hτ : IsStoppingTime f τ) : measurable[hτ.MeasurableSpace] (stoppedValue u τ) := by
  have h_str_meas : ∀ i, strongly_measurable[f i] (stopped_value u fun ω => min (τ ω) i) := fun i =>
    strongly_measurable_stopped_value_of_le hf_prog (hτ.min_const i) fun _ => min_le_rightₓ _ _
  intro t ht i
  suffices
    stopped_value u τ ⁻¹' t ∩ { ω : Ω | τ ω ≤ i } = (stopped_value u fun ω => min (τ ω) i) ⁻¹' t ∩ { ω : Ω | τ ω ≤ i }
    by
    rw [this]
    exact ((h_str_meas i).Measurable ht).inter (hτ.measurable_set_le i)
  ext1 ω
  simp only [stopped_value, Set.mem_inter_iff, Set.mem_preimage, Set.mem_set_of_eq, And.congr_left_iffₓ]
  intro h
  rw [min_eq_leftₓ h]

end ProgMeasurable

end LinearOrderₓ

section StoppedValueOfMemFinset

variable {μ : Measure Ω} {τ σ : Ω → ι} {E : Type _} {p : ℝ≥0∞} {u : ι → Ω → E}

theorem stopped_value_eq_of_mem_finset [AddCommMonoidₓ E] {s : Finsetₓ ι} (hbdd : ∀ ω, τ ω ∈ s) :
    stoppedValue u τ = ∑ i in s, Set.indicatorₓ { ω | τ ω = i } (u i) := by
  ext y
  rw [stopped_value, Finsetₓ.sum_apply, Finsetₓ.sum_indicator_eq_sum_filter]
  suffices Finsetₓ.filter (fun i => y ∈ { ω : Ω | τ ω = i }) s = ({τ y} : Finsetₓ ι) by rw [this, Finsetₓ.sum_singleton]
  ext1 ω
  simp only [Set.mem_set_of_eq, Finsetₓ.mem_filter, Finsetₓ.mem_singleton]
  constructor <;> intro h
  · exact h.2.symm
    
  · refine' ⟨_, h.symm⟩
    rw [h]
    exact hbdd y
    

theorem stopped_value_eq' [Preorderₓ ι] [LocallyFiniteOrderBot ι] [AddCommMonoidₓ E] {N : ι} (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = ∑ i in Finsetₓ.iic N, Set.indicatorₓ { ω | τ ω = i } (u i) :=
  stopped_value_eq_of_mem_finset fun ω => Finsetₓ.mem_Iic.mpr (hbdd ω)

variable [PartialOrderₓ ι] {ℱ : Filtration ι m} [NormedAddCommGroup E]

theorem mem_ℒp_stopped_value_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Memℒp (u n) p μ) {s : Finsetₓ ι}
    (hbdd : ∀ ω, τ ω ∈ s) : Memℒp (stoppedValue u τ) p μ := by
  rw [stopped_value_eq_of_mem_finset hbdd]
  swap
  infer_instance
  refine' mem_ℒp_finset_sum' _ fun i hi => mem_ℒp.indicator _ (hu i)
  refine' ℱ.le i { a : Ω | τ a = i } (hτ.measurable_set_eq_of_countable_range _ i)
  refine' ((Finsetₓ.finite_to_set s).Subset fun ω hω => _).Countable
  obtain ⟨y, rfl⟩ := hω
  exact hbdd y

theorem mem_ℒp_stopped_value [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Memℒp (u n) p μ) {N : ι}
    (hbdd : ∀ ω, τ ω ≤ N) : Memℒp (stoppedValue u τ) p μ :=
  mem_ℒp_stopped_value_of_mem_finset hτ hu fun ω => Finsetₓ.mem_Iic.mpr (hbdd ω)

theorem integrable_stopped_value_of_mem_finset (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Integrable (u n) μ) {s : Finsetₓ ι}
    (hbdd : ∀ ω, τ ω ∈ s) : Integrable (stoppedValue u τ) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable] at hu⊢
  exact mem_ℒp_stopped_value_of_mem_finset hτ hu hbdd

variable (ι)

theorem integrable_stopped_value [LocallyFiniteOrderBot ι] (hτ : IsStoppingTime ℱ τ) (hu : ∀ n, Integrable (u n) μ)
    {N : ι} (hbdd : ∀ ω, τ ω ≤ N) : Integrable (stoppedValue u τ) μ :=
  integrable_stopped_value_of_mem_finset hτ hu fun ω => Finsetₓ.mem_Iic.mpr (hbdd ω)

end StoppedValueOfMemFinset

section Nat

/-! ### Filtrations indexed by `ℕ` -/


open Filtration

variable {f : Filtration ℕ m} {u : ℕ → Ω → β} {τ π : Ω → ℕ}

theorem stopped_value_sub_eq_sum [AddCommGroupₓ β] (hle : τ ≤ π) :
    stoppedValue u π - stoppedValue u τ = fun ω => (∑ i in Finsetₓ.ico (τ ω) (π ω), u (i + 1) - u i) ω := by
  ext ω
  rw [Finsetₓ.sum_Ico_eq_sub _ (hle ω), Finsetₓ.sum_range_sub, Finsetₓ.sum_range_sub]
  simp [stopped_value]

theorem stopped_value_sub_eq_sum' [AddCommGroupₓ β] (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ ω, π ω ≤ N) :
    stoppedValue u π - stoppedValue u τ = fun ω =>
      (∑ i in Finsetₓ.range (N + 1), Set.indicatorₓ { ω | τ ω ≤ i ∧ i < π ω } (u (i + 1) - u i)) ω :=
  by
  rw [stopped_value_sub_eq_sum hle]
  ext ω
  simp only [Finsetₓ.sum_apply, Finsetₓ.sum_indicator_eq_sum_filter]
  refine' Finsetₓ.sum_congr _ fun _ _ => rfl
  ext i
  simp only [Finsetₓ.mem_filter, Set.mem_set_of_eq, Finsetₓ.mem_range, Finsetₓ.mem_Ico]
  exact ⟨fun h => ⟨lt_transₓ h.2 (Nat.lt_succ_iff.2 <| hbdd _), h⟩, fun h => h.2⟩

section AddCommMonoidₓ

variable [AddCommMonoidₓ β]

/-- For filtrations indexed by `ℕ`, the stopped process obtained from an adapted process is
adapted. -/
theorem Adapted.stopped_process_of_nat [TopologicalSpace β] [HasContinuousAdd β] (hu : Adapted f u)
    (hτ : IsStoppingTime f τ) : Adapted f (stoppedProcess u τ) :=
  (hu.prog_measurable_of_nat.stoppedProcess hτ).Adapted

theorem Adapted.strongly_measurable_stopped_process_of_nat [TopologicalSpace β] [HasContinuousAdd β]
    (hτ : IsStoppingTime f τ) (hu : Adapted f u) (n : ℕ) : StronglyMeasurable (stoppedProcess u τ n) :=
  hu.prog_measurable_of_nat.strongly_measurable_stopped_process hτ n

theorem stopped_value_eq {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    stoppedValue u τ = fun x => (∑ i in Finsetₓ.range (N + 1), Set.indicatorₓ { ω | τ ω = i } (u i)) x :=
  stopped_value_eq_of_mem_finset fun ω => Finsetₓ.mem_range_succ_iff.mpr (hbdd ω)

theorem stopped_process_eq (n : ℕ) :
    stoppedProcess u τ n =
      Set.indicatorₓ { a | n ≤ τ a } (u n) + ∑ i in Finsetₓ.range n, Set.indicatorₓ { ω | τ ω = i } (u i) :=
  by
  ext ω
  rw [Pi.add_apply, Finsetₓ.sum_apply]
  cases le_or_ltₓ n (τ ω)
  · rw [stopped_process_eq_of_le h, Set.indicator_of_mem, Finsetₓ.sum_eq_zero, add_zeroₓ]
    · intro m hm
      rw [Finsetₓ.mem_range] at hm
      exact Set.indicator_of_not_mem (lt_of_lt_of_leₓ hm h).Ne.symm _
      
    · exact h
      
    
  · rw [stopped_process_eq_of_ge (le_of_ltₓ h), Finsetₓ.sum_eq_single_of_mem (τ ω)]
    · rw [Set.indicator_of_not_mem, zero_addₓ, Set.indicator_of_mem]
      · exact rfl
        
      -- refl does not work
      · exact not_leₓ.2 h
        
      
    · rwa [Finsetₓ.mem_range]
      
    · intro b hb hneq
      rw [Set.indicator_of_not_mem]
      exact hneq.symm
      
    

theorem stopped_process_eq' (n : ℕ) :
    stoppedProcess u τ n =
      Set.indicatorₓ { a | n + 1 ≤ τ a } (u n) + ∑ i in Finsetₓ.range (n + 1), Set.indicatorₓ { a | τ a = i } (u i) :=
  by
  have : { a | n ≤ τ a }.indicator (u n) = { a | n + 1 ≤ τ a }.indicator (u n) + { a | τ a = n }.indicator (u n) := by
    ext x
    rw [add_commₓ, Pi.add_apply, ← Set.indicator_union_of_not_mem_inter]
    · simp_rw [@eq_comm _ _ n, @le_iff_eq_or_ltₓ _ _ n, Nat.succ_le_iff]
      rfl
      
    · rintro ⟨h₁, h₂⟩
      exact (Nat.succ_le_iff.1 h₂).Ne h₁.symm
      
  rw [stopped_process_eq, this, Finsetₓ.sum_range_succ_comm, ← add_assocₓ]

end AddCommMonoidₓ

section NormedAddCommGroup

variable [NormedAddCommGroup β] {p : ℝ≥0∞} {μ : Measure Ω}

theorem mem_ℒp_stopped_process (hτ : IsStoppingTime f τ) (hu : ∀ n, Memℒp (u n) p μ) (n : ℕ) :
    Memℒp (stoppedProcess u τ n) p μ := by
  rw [stopped_process_eq]
  refine' mem_ℒp.add _ _
  · exact mem_ℒp.indicator (f.le n { a : Ω | n ≤ τ a } (hτ.measurable_set_ge n)) (hu n)
    
  · suffices mem_ℒp (fun ω => ∑ i : ℕ in Finsetₓ.range n, { a : Ω | τ a = i }.indicator (u i) ω) p μ by
      convert this
      ext1 ω
      simp only [Finsetₓ.sum_apply]
    refine' mem_ℒp_finset_sum _ fun i hi => mem_ℒp.indicator _ (hu i)
    exact f.le i { a : Ω | τ a = i } (hτ.measurable_set_eq i)
    

theorem integrable_stopped_process (hτ : IsStoppingTime f τ) (hu : ∀ n, Integrable (u n) μ) (n : ℕ) :
    Integrable (stoppedProcess u τ n) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable] at hu⊢
  exact mem_ℒp_stopped_process hτ hu n

end NormedAddCommGroup

end Nat

section PiecewiseConst

variable [Preorderₓ ι] {𝒢 : Filtration ι m} {τ η : Ω → ι} {i j : ι} {s : Set Ω} [DecidablePred (· ∈ s)]

/-- Given stopping times `τ` and `η` which are bounded below, `set.piecewise s τ η` is also
a stopping time with respect to the same filtration. -/
theorem IsStoppingTime.piecewise_of_le (hτ_st : IsStoppingTime 𝒢 τ) (hη_st : IsStoppingTime 𝒢 η) (hτ : ∀ ω, i ≤ τ ω)
    (hη : ∀ ω, i ≤ η ω) (hs : measurable_set[𝒢 i] s) : IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have : { ω | s.piecewise τ η ω ≤ n } = s ∩ { ω | τ ω ≤ n } ∪ sᶜ ∩ { ω | η ω ≤ n } := by
    ext1 ω
    simp only [Set.piecewise, Set.mem_inter_iff, Set.mem_set_of_eq, And.congr_right_iff]
    by_cases hx:ω ∈ s <;> simp [hx]
  rw [this]
  by_cases hin:i ≤ n
  · have hs_n : measurable_set[𝒢 n] s := 𝒢.mono hin _ hs
    exact (hs_n.inter (hτ_st n)).union (hs_n.compl.inter (hη_st n))
    
  · have hτn : ∀ ω, ¬τ ω ≤ n := fun ω hτn => hin ((hτ ω).trans hτn)
    have hηn : ∀ ω, ¬η ω ≤ n := fun ω hηn => hin ((hη ω).trans hηn)
    simp [hτn, hηn]
    

theorem is_stopping_time_piecewise_const (hij : i ≤ j) (hs : measurable_set[𝒢 i] s) :
    IsStoppingTime 𝒢 (s.piecewise (fun _ => i) fun _ => j) :=
  (is_stopping_time_const 𝒢 i).piecewise_of_le (is_stopping_time_const 𝒢 j) (fun x => le_rflₓ) (fun _ => hij) hs

theorem stopped_value_piecewise_const {ι' : Type _} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.piecewise (f i) (f j) := by
  ext ω
  rw [stopped_value]
  by_cases hx:ω ∈ s <;> simp [hx]

theorem stopped_value_piecewise_const' {ι' : Type _} {i j : ι'} {f : ι' → Ω → ℝ} :
    stoppedValue f (s.piecewise (fun _ => i) fun _ => j) = s.indicator (f i) + sᶜ.indicator (f j) := by
  ext ω
  rw [stopped_value]
  by_cases hx:ω ∈ s <;> simp [hx]

end PiecewiseConst

end MeasureTheory

