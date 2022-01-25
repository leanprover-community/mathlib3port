import Mathbin.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `measure_theory.ae_disjoint`) if their
intersection has measure zero. This assumption can be used instead of `disjoint` in most theorems in
measure theory.
-/


open Set Function

namespace MeasureTheory

variable {ι α : Type _} {m : MeasurableSpace α} (μ : Measureₓ α)

/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
def ae_disjoint (s t : Set α) :=
  μ (s ∩ t) = 0

variable {μ} {s t u v : Set α}

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (j «expr ≠ » i)
/-- If `s : ι → set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
theorem exists_null_pairwise_disjoint_diff [Encodable ι] {s : ι → Set α} (hd : Pairwise (ae_disjoint μ on s)) :
    ∃ t : ι → Set α, (∀ i, MeasurableSet (t i)) ∧ (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) := by
  refine'
    ⟨fun i => to_measurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i => measurable_set_to_measurable _ _, fun i => _,
      _⟩
  · simp only [measure_to_measurable, inter_Union, measure_bUnion_null_iff (countable_encodable _)]
    exact fun j hj => hd _ _ (Ne.symm hj)
    
  · simp only [Pairwise, disjoint_left, on_fun, mem_diff, not_and, and_imp, not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ ⋃ (j) (_ : j ≠ i), s j := fun h => hU (subset_to_measurable _ _ h)
    simp only [mem_inter_eq, mem_Union, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim
    

namespace AeDisjoint

protected theorem Eq (h : ae_disjoint μ s t) : μ (s ∩ t) = 0 :=
  h

@[symm]
protected theorem symm (h : ae_disjoint μ s t) : ae_disjoint μ t s := by
  rwa [ae_disjoint, inter_comm]

protected theorem Symmetric : Symmetric (ae_disjoint μ) := fun s t h => h.symm

protected theorem comm : ae_disjoint μ s t ↔ ae_disjoint μ t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩

theorem _root_.disjoint.ae_disjoint (h : Disjoint s t) : ae_disjoint μ s t := by
  rw [ae_disjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]

theorem mono_ae (h : ae_disjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : ae_disjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h

theorem mono (h : ae_disjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : ae_disjoint μ u v :=
  h.mono_ae hu.eventually_le hv.eventually_le

@[simp]
theorem Union_left_iff [Encodable ι] {s : ι → Set α} : ae_disjoint μ (⋃ i, s i) t ↔ ∀ i, ae_disjoint μ (s i) t := by
  simp only [ae_disjoint, Union_inter, measure_Union_null_iff]

@[simp]
theorem Union_right_iff [Encodable ι] {t : ι → Set α} : ae_disjoint μ s (⋃ i, t i) ↔ ∀ i, ae_disjoint μ s (t i) := by
  simp only [ae_disjoint, inter_Union, measure_Union_null_iff]

@[simp]
theorem union_left_iff : ae_disjoint μ (s ∪ t) u ↔ ae_disjoint μ s u ∧ ae_disjoint μ t u := by
  simp [union_eq_Union, And.comm]

@[simp]
theorem union_right_iff : ae_disjoint μ s (t ∪ u) ↔ ae_disjoint μ s t ∧ ae_disjoint μ s u := by
  simp [union_eq_Union, And.comm]

theorem union_left (hs : ae_disjoint μ s u) (ht : ae_disjoint μ t u) : ae_disjoint μ (s ∪ t) u :=
  union_left_iff.mpr ⟨hs, ht⟩

theorem union_right (ht : ae_disjoint μ s t) (hu : ae_disjoint μ s u) : ae_disjoint μ s (t ∪ u) :=
  union_right_iff.2 ⟨ht, hu⟩

theorem diff_ae_eq_left (h : ae_disjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @diff_self_inter _ s t ▸ diff_null_ae_eq_self h

theorem diff_ae_eq_right (h : ae_disjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
  h.symm.diff_ae_eq_left

theorem measure_diff_left (h : ae_disjoint μ s t) : μ (s \ t) = μ s :=
  measure_congr h.diff_ae_eq_left

theorem measure_diff_right (h : ae_disjoint μ s t) : μ (t \ s) = μ t :=
  measure_congr h.diff_ae_eq_right

/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
theorem exists_disjoint_diff (h : ae_disjoint μ s t) : ∃ u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨to_measurable μ (s ∩ t), measurable_set_to_measurable _ _, (measure_to_measurable _).trans h,
    disjoint_diff.symm.mono_left fun x hx => ⟨hx.1, fun hxt => hx.2 $ subset_to_measurable _ _ ⟨hx.1, hxt⟩⟩⟩

theorem of_null_right (h : μ t = 0) : ae_disjoint μ s t :=
  measure_mono_null (inter_subset_right _ _) h

theorem of_null_left (h : μ s = 0) : ae_disjoint μ s t :=
  (of_null_right h).symm

end AeDisjoint

theorem ae_disjoint_compl_left : ae_disjoint μ (sᶜ) s :=
  (@disjoint_compl_left _ s _).AeDisjoint

theorem ae_disjoint_compl_right : ae_disjoint μ s (sᶜ) :=
  (@disjoint_compl_right _ s _).AeDisjoint

end MeasureTheory

