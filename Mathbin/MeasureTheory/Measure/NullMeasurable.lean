import Mathbin.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Null measurable sets and complete measures

## Main definitions

### Null measurable sets and functions

A set `s : set α` is called *null measurable* (`measure_theory.null_measurable_set`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `measure_theory.to_measurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `measurable_space` instance on
`measure_theory.null_measurable_space α μ`. We also say that `f : α → β` is
`measure_theory.null_measurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`measure_theory.null_measurable_space α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `measurable_space α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `measure_theory.measure.completion μ` to be the same measure
interpreted as a measure on `measure_theory.null_measurable_space α μ` and prove that this is a
complete measure.

## Implementation notes

We define `measure_theory.null_measurable_set` as `@measurable_set (null_measurable_space α μ) _` so
that theorems about `measurable_set`s like `measurable_set.union` can be applied to
`null_measurable_set`s. However, these lemmas output terms of the same form
`@measurable_set (null_measurable_space α μ) _ _`. While this is definitionally equal to the
expected output `null_measurable_set s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `measure_theory.null_measurable_set` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/


open Filter Set Encodable

variable {ι α β γ : Type _}

namespace MeasureTheory

/-- A type tag for `α` with `measurable_set` given by `null_measurable_set`. -/
@[nolint unused_arguments]
def null_measurable_space (α : Type _) [MeasurableSpace α]
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Type _ :=
  α

section 

variable {m0 : MeasurableSpace α} {μ : Measureₓ α} {s t : Set α}

instance [h : Inhabited α] : Inhabited (null_measurable_space α μ) :=
  h

instance [h : Subsingleton α] : Subsingleton (null_measurable_space α μ) :=
  h

instance : MeasurableSpace (null_measurable_space α μ) :=
  { MeasurableSet' := fun s => ∃ t, MeasurableSet t ∧ s =ᵐ[μ] t,
    measurable_set_empty := ⟨∅, MeasurableSet.empty, ae_eq_refl _⟩,
    measurable_set_compl := fun s ⟨t, htm, hts⟩ => ⟨tᶜ, htm.compl, hts.compl⟩,
    measurable_set_Union :=
      fun s hs =>
        by 
          choose t htm hts using hs 
          exact ⟨⋃ i, t i, MeasurableSet.Union htm, EventuallyEq.countable_Union hts⟩ }

/-- A set is called `null_measurable_set` if it can be approximated by a measurable set up to
a set of null measure. -/
def null_measurable_set [MeasurableSpace α] (s : Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  @MeasurableSet (null_measurable_space α μ) _ s

@[simp]
theorem _root_.measurable_set.null_measurable_set (h : MeasurableSet s) : null_measurable_set s μ :=
  ⟨s, h, ae_eq_refl _⟩

@[simp]
theorem null_measurable_set_empty : null_measurable_set ∅ μ :=
  MeasurableSet.empty

@[simp]
theorem null_measurable_set_univ : null_measurable_set univ μ :=
  MeasurableSet.univ

namespace NullMeasurableSet

theorem of_null (h : μ s = 0) : null_measurable_set s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩

theorem compl (h : null_measurable_set s μ) : null_measurable_set (sᶜ) μ :=
  h.compl

theorem of_compl (h : null_measurable_set (sᶜ) μ) : null_measurable_set s μ :=
  h.of_compl

@[simp]
theorem compl_iff : null_measurable_set (sᶜ) μ ↔ null_measurable_set s μ :=
  MeasurableSet.compl_iff

@[nontriviality]
theorem of_subsingleton [Subsingleton α] : null_measurable_set s μ :=
  Subsingleton.measurable_set

protected theorem congr (hs : null_measurable_set s μ) (h : s =ᵐ[μ] t) : null_measurable_set t μ :=
  let ⟨s', hm, hs'⟩ := hs
  ⟨s', hm, h.symm.trans hs'⟩

protected theorem Union [Encodable ι] {s : ι → Set α} (h : ∀ i, null_measurable_set (s i) μ) :
  null_measurable_set (⋃ i, s i) μ :=
  MeasurableSet.Union h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » encodable.decode₂ ι n)
protected theorem bUnion_decode₂ [Encodable ι] ⦃f : ι → Set α⦄ (h : ∀ i, null_measurable_set (f i) μ) (n : ℕ) :
  null_measurable_set (⋃ (b : _)(_ : b ∈ Encodable.decode₂ ι n), f b) μ :=
  MeasurableSet.bUnion_decode₂ h n

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
protected theorem bUnion {f : ι → Set α} {s : Set ι} (hs : countable s)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋃ (b : _)(_ : b ∈ s), f b) μ :=
  MeasurableSet.bUnion hs h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » s)
protected theorem sUnion {s : Set (Set α)} (hs : countable s) (h : ∀ t _ : t ∈ s, null_measurable_set t μ) :
  null_measurable_set (⋃₀s) μ :=
  by 
    rw [sUnion_eq_bUnion]
    exact MeasurableSet.bUnion hs h

theorem Union_Prop {p : Prop} {f : p → Set α} (hf : ∀ i, null_measurable_set (f i) μ) :
  null_measurable_set (⋃ i, f i) μ :=
  MeasurableSet.Union_Prop hf

theorem Union_fintype [Fintype ι] {f : ι → Set α} (h : ∀ b, null_measurable_set (f b) μ) :
  null_measurable_set (⋃ b, f b) μ :=
  MeasurableSet.Union_fintype h

protected theorem Inter [Encodable ι] {f : ι → Set α} (h : ∀ i, null_measurable_set (f i) μ) :
  null_measurable_set (⋂ i, f i) μ :=
  MeasurableSet.Inter h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
protected theorem bInter {f : β → Set α} {s : Set β} (hs : countable s)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ (b : _)(_ : b ∈ s), f b) μ :=
  MeasurableSet.bInter hs h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » s)
protected theorem sInter {s : Set (Set α)} (hs : countable s) (h : ∀ t _ : t ∈ s, null_measurable_set t μ) :
  null_measurable_set (⋂₀s) μ :=
  MeasurableSet.sInter hs h

theorem Inter_Prop {p : Prop} {f : p → Set α} (hf : ∀ b, null_measurable_set (f b) μ) :
  null_measurable_set (⋂ b, f b) μ :=
  MeasurableSet.Inter_Prop hf

theorem Inter_fintype [Fintype ι] {f : ι → Set α} (h : ∀ b, null_measurable_set (f b) μ) :
  null_measurable_set (⋂ b, f b) μ :=
  MeasurableSet.Inter_fintype h

@[simp]
protected theorem union (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) : null_measurable_set (s ∪ t) μ :=
  hs.union ht

protected theorem union_null (hs : null_measurable_set s μ) (ht : μ t = 0) : null_measurable_set (s ∪ t) μ :=
  hs.union (of_null ht)

@[simp]
protected theorem inter (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) : null_measurable_set (s ∩ t) μ :=
  hs.inter ht

@[simp]
protected theorem diff (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) : null_measurable_set (s \ t) μ :=
  hs.diff ht

@[simp]
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, null_measurable_set (f i) μ) n :
  null_measurable_set (disjointed f n) μ :=
  MeasurableSet.disjointed h n

@[simp]
protected theorem const (p : Prop) : null_measurable_set { a : α | p } μ :=
  MeasurableSet.const p

instance [MeasurableSingletonClass α] : MeasurableSingletonClass (null_measurable_space α μ) :=
  ⟨fun x => (@measurable_set_singleton α _ _ x).NullMeasurableSet⟩

protected theorem insert [MeasurableSingletonClass (null_measurable_space α μ)] (hs : null_measurable_set s μ) (a : α) :
  null_measurable_set (insert a s) μ :=
  hs.insert a

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ⊇ » s)
theorem exists_measurable_superset_ae_eq (h : null_measurable_set s μ) :
  ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  by 
    rcases h with ⟨t, htm, hst⟩
    refine' ⟨t ∪ to_measurable μ (s \ t), _, htm.union (measurable_set_to_measurable _ _), _⟩
    ·
      exact diff_subset_iff.1 (subset_to_measurable _ _)
    ·
      have  : to_measurable μ (s \ t) =ᵐ[μ] (∅ : Set α)
      ·
        simp [ae_le_set.1 hst.le]
      simpa only [union_empty] using hst.symm.union this

theorem to_measurable_ae_eq (h : null_measurable_set s μ) : to_measurable μ s =ᵐ[μ] s :=
  by 
    rw [to_measurable, dif_pos]
    exact h.exists_measurable_superset_ae_eq.some_spec.snd.2

theorem compl_to_measurable_compl_ae_eq (h : null_measurable_set s μ) : to_measurable μ (sᶜ)ᶜ =ᵐ[μ] s :=
  by 
    simpa only [compl_compl] using h.compl.to_measurable_ae_eq.compl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem exists_measurable_subset_ae_eq (h : null_measurable_set s μ) :
  ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨to_measurable μ (sᶜ)ᶜ, compl_subset_comm.2$ subset_to_measurable _ _, (measurable_set_to_measurable _ _).Compl,
    h.compl_to_measurable_compl_ae_eq⟩

end NullMeasurableSet

theorem measure_Union {m0 : MeasurableSpace α} {μ : Measureₓ α} [Encodable ι] {f : ι → Set α}
  (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  by 
    rw [measure_eq_extend (MeasurableSet.Union h), extend_Union MeasurableSet.empty _ MeasurableSet.Union _ hn h]
    ·
      simp [measure_eq_extend, h]
    ·
      exact μ.empty
    ·
      exact μ.m_Union

theorem measure_Union₀ [Encodable ι] {f : ι → Set α} (hn : Pairwise (Disjoint on f))
  (h : ∀ i, null_measurable_set (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  by 
    refine' (measure_Union_le _).antisymm _ 
    choose s hsf hsm hs_eq using fun i => (h i).exists_measurable_subset_ae_eq 
    have hsd : Pairwise (Disjoint on s)
    exact hn.mono fun i j h => h.mono (hsf i) (hsf j)
    simp only [←measure_congr (hs_eq _), ←measure_Union hsd hsm]
    exact measure_mono (Union_subset_Union hsf)

theorem measure_union₀ (hs : null_measurable_set s μ) (ht : null_measurable_set t μ) (hd : Disjoint s t) :
  μ (s ∪ t) = μ s+μ t :=
  by 
    rw [union_eq_Union, measure_Union₀, tsum_fintype, Fintype.sum_bool, cond, cond]
    exacts[pairwise_disjoint_on_bool.2 hd, fun b => Bool.casesOn b ht hs]

section MeasurableSingletonClass

variable [MeasurableSingletonClass (null_measurable_space α μ)]

theorem null_measurable_set_singleton (x : α) : null_measurable_set {x} μ :=
  measurable_set_singleton x

@[simp]
theorem null_measurable_set_insert {a : α} {s : Set α} : null_measurable_set (insert a s) μ ↔ null_measurable_set s μ :=
  measurable_set_insert

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem null_measurable_set_eq { a : α } : null_measurable_set { x | x = a } μ := null_measurable_set_singleton a

protected theorem _root_.set.finite.null_measurable_set (hs : finite s) : null_measurable_set s μ :=
  finite.measurable_set hs

protected theorem _root_.finset.null_measurable_set (s : Finset α) : null_measurable_set (↑s) μ :=
  Finset.measurable_set s

end MeasurableSingletonClass

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
theorem _root_.set.finite.null_measurable_set_bUnion {f : ι → Set α} {s : Set ι} (hs : finite s)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋃ (b : _)(_ : b ∈ s), f b) μ :=
  finite.measurable_set_bUnion hs h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
theorem _root_.finset.null_measurable_set_bUnion {f : ι → Set α} (s : Finset ι)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋃ (b : _)(_ : b ∈ s), f b) μ :=
  Finset.measurable_set_bUnion s h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » s)
theorem _root_.set.finite.null_measurable_set_sUnion {s : Set (Set α)} (hs : finite s)
  (h : ∀ t _ : t ∈ s, null_measurable_set t μ) : null_measurable_set (⋃₀s) μ :=
  finite.measurable_set_sUnion hs h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
theorem _root_.set.finite.null_measurable_set_bInter {f : ι → Set α} {s : Set ι} (hs : finite s)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ (b : _)(_ : b ∈ s), f b) μ :=
  finite.measurable_set_bInter hs h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (b «expr ∈ » s)
theorem _root_.finset.null_measurable_set_bInter {f : ι → Set α} (s : Finset ι)
  (h : ∀ b _ : b ∈ s, null_measurable_set (f b) μ) : null_measurable_set (⋂ (b : _)(_ : b ∈ s), f b) μ :=
  s.finite_to_set.null_measurable_set_bInter h

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » s)
theorem _root_.set.finite.null_measurable_set_sInter {s : Set (Set α)} (hs : finite s)
  (h : ∀ t _ : t ∈ s, null_measurable_set t μ) : null_measurable_set (⋂₀s) μ :=
  null_measurable_set.sInter hs.countable h

theorem null_measurable_set_to_measurable : null_measurable_set (to_measurable μ s) μ :=
  (measurable_set_to_measurable _ _).NullMeasurableSet

end 

section NullMeasurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measureₓ α}

/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def null_measurable (f : α → β)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → null_measurable_set (f ⁻¹' s) μ

protected theorem _root_.measurable.null_measurable (h : Measurable f) : null_measurable f μ :=
  fun s hs => (h hs).NullMeasurableSet

protected theorem null_measurable.measurable' (h : null_measurable f μ) :
  @Measurable (null_measurable_space α μ) β _ _ f :=
  h

theorem measurable.comp_null_measurable {g : β → γ} (hg : Measurable g) (hf : null_measurable f μ) :
  null_measurable (g ∘ f) μ :=
  hg.comp hf

theorem null_measurable.congr {g : α → β} (hf : null_measurable f μ) (hg : f =ᵐ[μ] g) : null_measurable g μ :=
  fun s hs =>
    (hf hs).congr$
      eventually_eq_set.2$
        hg.mono$
          fun x hx =>
            by 
              rw [mem_preimage, mem_preimage, hx]

end NullMeasurable

section IsComplete

/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class measure.is_complete {_ : MeasurableSpace α} (μ : Measureₓ α) : Prop where 
  out' : ∀ s, μ s = 0 → MeasurableSet s

variable {m0 : MeasurableSpace α} {μ : Measureₓ α} {s t : Set α}

theorem measure.is_complete_iff : μ.is_complete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem measure.is_complete.out (h : μ.is_complete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1

theorem measurable_set_of_null [μ.is_complete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs

theorem null_measurable_set.measurable_of_complete (hs : null_measurable_set s μ) [μ.is_complete] : MeasurableSet s :=
  diff_diff_cancel_left (subset_to_measurable μ s) ▸
    (measurable_set_to_measurable _ _).diff (measurable_set_of_null (ae_le_set.1 hs.to_measurable_ae_eq.le))

theorem null_measurable.measurable_of_complete [μ.is_complete] {m1 : MeasurableSpace β} {f : α → β}
  (hf : null_measurable f μ) : Measurable f :=
  fun s hs => (hf hs).measurable_of_complete

theorem _root_.measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measureₓ α} [hμ : μ.is_complete]
  {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  (hf.null_measurable.congr hfg).measurable_of_complete

namespace Measureₓ

/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : MeasurableSpace α} (μ : Measureₓ α) : @MeasureTheory.Measure (null_measurable_space α μ) _ :=
  { toOuterMeasure := μ.to_outer_measure, m_Union := fun s hs hd => measure_Union₀ hd hs,
    trimmed :=
      by 
        refine' le_antisymmₓ (fun s => _) (outer_measure.le_trim _)
        rw [outer_measure.trim_eq_infi]
        simp only [to_outer_measure_apply]
        refine' (binfi_le_binfi _).trans_eq (measure_eq_infi _).symm 
        exact fun t ht => infi_le_infi2 fun h => ⟨h.null_measurable_set, le_rfl⟩ }

instance completion.is_complete {m : MeasurableSpace α} (μ : Measureₓ α) : μ.completion.is_complete :=
  ⟨fun z hz => null_measurable_set.of_null hz⟩

@[simp]
theorem coe_completion {_ : MeasurableSpace α} (μ : Measureₓ α) : ⇑μ.completion = μ :=
  rfl

theorem completion_apply {_ : MeasurableSpace α} (μ : Measureₓ α) (s : Set α) : μ.completion s = μ s :=
  rfl

end Measureₓ

end IsComplete

end MeasureTheory

