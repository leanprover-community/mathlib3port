/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ennreal.ae_measurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`measure_theory.ae_measurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/


open MeasureTheory Set TopologicalSpace

open_locale Classical Ennreal Nnreal

/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
theorem MeasureTheory.ae_measurable_of_exist_almost_disjoint_supersets {α : Type _} {m : MeasurableSpace α}
    (μ : Measureₓ α) {β : Type _} [CompleteLinearOrder β] [DenselyOrdered β] [TopologicalSpace β] [OrderTopology β]
    [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β] (s : Set β) (s_count : Countable s)
    (s_dense : Dense s) (f : α → β)
    (h :
      ∀,
        ∀ p ∈ s,
          ∀,
            ∀ q ∈ s,
              ∀,
                p < q →
                  ∃ u v,
                    MeasurableSet u ∧ MeasurableSet v ∧ { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AeMeasurable f μ := by
  have : Encodable s := s_count.to_encodable
  have h' :
    ∀ p q,
      ∃ u v,
        MeasurableSet u ∧
          MeasurableSet v ∧ { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ (p ∈ s → q ∈ s → p < q → μ (u ∩ v) = 0) :=
    by
    intro p q
    by_cases' H : p ∈ s ∧ q ∈ s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun ps qs pq => hμ⟩
      
    · refine' ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _, fun ps qs pq => _⟩
      simp only [not_and] at H
      exact (H ps qs pq).elim
      
  choose! u v huv using h'
  let u' : β → Set α := fun p => ⋂ q ∈ s ∩ Ioi p, u p q
  have u'_meas : ∀ i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.bInter (s_count.mono (inter_subset_left _ _)) fun b hb => (huv i b).1
  let f' : α → β := fun x => ⨅ i : s, piecewise (u' i) (fun x => (i : β)) (fun x => (⊤ : β)) x
  have f'_meas : Measurable f' := by
    apply measurable_infi
    exact fun i => Measurable.piecewise (u'_meas i) measurable_const measurable_const
  let t := ⋃ (p : s) (q : s ∩ Ioi p), u' p ∩ v p q
  have μt : μ t ≤ 0 :=
    calc
      μ t ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u' p ∩ v p q) := by
        refine' (measure_Union_le _).trans _
        apply Ennreal.tsum_le_tsum fun p => _
        apply measure_Union_le _
        exact (s_count.mono (inter_subset_left _ _)).toEncodable
      _ ≤ ∑' (p : s) (q : s ∩ Ioi p), μ (u p q ∩ v p q) := by
        apply Ennreal.tsum_le_tsum fun p => _
        refine' Ennreal.tsum_le_tsum fun q => measure_mono _
        exact inter_subset_inter_left _ (bInter_subset_of_mem q.2)
      _ = ∑' (p : s) (q : s ∩ Ioi p), (0 : ℝ≥0∞) := by
        congr
        ext1 p
        congr
        ext1 q
        exact (huv p q).2.2.2.2 p.2 q.2.1 q.2.2
      _ = 0 := by
        simp only [tsum_zero]
      
  have ff' : ∀ᵐ x ∂μ, f x = f' x := by
    have : ∀ᵐ x ∂μ, x ∉ t := by
      have : μ t = 0 := le_antisymmₓ μt bot_le
      change μ _ = 0
      convert this
      ext y
      simp only [not_exists, exists_prop, mem_set_of_eq, mem_compl_eq, not_not_mem]
    filter_upwards [this] with x hx
    apply (infi_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases' H : x ∈ u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_not_mem]
        
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (i : β) (f x) ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo i (f x)) is_open_Ioo (nonempty_Ioo.2 hx)
      have A : x ∈ v i r := (huv i r).2.2.2.1 rq
      apply mem_Union.2 ⟨i, _⟩
      refine' mem_Union.2 ⟨⟨r, ⟨rs, xr⟩⟩, _⟩
      exact ⟨H, A⟩
      
    · intro q hq
      obtain ⟨r, ⟨xr, rq⟩, rs⟩ : ∃ r, r ∈ Ioo (f x) q ∩ s :=
        dense_iff_inter_open.1 s_dense (Ioo (f x) q) is_open_Ioo (nonempty_Ioo.2 hq)
      refine' ⟨⟨r, rs⟩, _⟩
      have A : x ∈ u' r := mem_bInter fun i hi => (huv r i).2.2.1 xr
      simp only [A, rq, piecewise_eq_of_mem, Subtype.coe_mk]
      
  exact ⟨f', f'_meas, ff'⟩

/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
theorem Ennreal.ae_measurable_of_exist_almost_disjoint_supersets {α : Type _} {m : MeasurableSpace α} (μ : Measureₓ α)
    (f : α → ℝ≥0∞)
    (h :
      ∀ p : ℝ≥0 q : ℝ≥0 ,
        p < q →
          ∃ u v,
            MeasurableSet u ∧ MeasurableSet v ∧ { x | f x < p } ⊆ u ∧ { x | (q : ℝ≥0∞) < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AeMeasurable f μ := by
  obtain ⟨s, s_count, s_dense, s_zero, s_top⟩ : ∃ s : Set ℝ≥0∞, countable s ∧ Dense s ∧ (0 ∉ s) ∧ ∞ ∉ s :=
    Ennreal.exists_countable_dense_no_zero_top
  have I : ∀, ∀ x ∈ s, ∀, x ≠ ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.ae_measurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to ℝ≥0 using I p hp
  lift q to ℝ≥0 using I q hq
  exact h p q (Ennreal.coe_lt_coe.1 hpq)

