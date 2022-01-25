import Mathbin.MeasureTheory.ProbabilityMassFunction.Monad

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.
`of_multiset`, `uniform_of_finset`, and `uniform_of_fintype` construct probability mass functions
from the corresponding object, with proportional weighting for each element of the object.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `bool`

-/


namespace Pmf

noncomputable section

variable {α : Type _} {β : Type _} {γ : Type _}

open_locale Classical BigOperators Nnreal Ennreal

section Map

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : Pmf α) : Pmf β :=
  bind p (pure ∘ f)

variable (f : α → β) (p : Pmf α) (b : β)

@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by
  simp [map]

@[simp]
theorem support_map : (map f p).Support = f '' p.support :=
  Set.ext fun b => by
    simp [map, @eq_comm β b]

theorem mem_support_map_iff : b ∈ (map f p).Support ↔ ∃ a ∈ p.support, f a = b := by
  simp

theorem bind_pure_comp : bind p (pure ∘ f) = map f p :=
  rfl

theorem map_id : map id p = p := by
  simp [map]

theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by
  simp [map]

theorem pure_map (a : α) : (pure a).map f = pure (f a) := by
  simp [map]

end Map

section Seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (q : Pmf (α → β)) (p : Pmf α) : Pmf β :=
  q.bind fun m => p.bind $ fun a => pure (m a)

variable (q : Pmf (α → β)) (p : Pmf α) (b : β)

@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine' tsum_congr fun f => (Nnreal.tsum_mul_left (q f) _).symm.trans (tsum_congr fun a => _)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]
theorem support_seq : (seq q p).Support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by
    simp [-mem_support_iff, seq, @eq_comm β b]

theorem mem_support_seq_iff : b ∈ (seq q p).Support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by
  simp

end Seq

section OfFinset

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (a «expr ∉ » s)
/-- Given a finset `s` and a function `f : α → ℝ≥0` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `pmf` -/
def of_finset (f : α → ℝ≥0 ) (s : Finset α) (h : (∑ a in s, f a) = 1) (h' : ∀ a _ : a ∉ s, f a = 0) : Pmf α :=
  ⟨f, h ▸ has_sum_sum_of_ne_finset_zero h'⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (a «expr ∉ » s)
variable {f : α → ℝ≥0 } {s : Finset α} (h : (∑ a in s, f a) = 1) (h' : ∀ a _ : a ∉ s, f a = 0)

@[simp]
theorem of_finset_apply (a : α) : of_finset f s h h' a = f a :=
  rfl

@[simp]
theorem support_of_finset : (of_finset f s h h').Support = s ∩ Function.Support f :=
  Set.ext fun a => by
    simpa [mem_support_iff] using mt (h' a)

theorem mem_support_of_finset_iff (a : α) : a ∈ (of_finset f s h h').Support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem of_finset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_finset f s h h' a = 0 :=
  h' a ha

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [Fintype α] (f : α → ℝ≥0 ) (h : (∑ a, f a) = 1) : Pmf α :=
  of_finset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0 } (h : (∑ a, f a) = 1)

@[simp]
theorem of_fintype_apply (a : α) : of_fintype f h a = f a :=
  rfl

@[simp]
theorem support_of_fintype : (of_fintype f h).Support = Function.Support f :=
  rfl

theorem mem_support_of_fintype_iff (a : α) : a ∈ (of_fintype f h).Support ↔ f a ≠ 0 :=
  Iff.rfl

end OfFintype

section OfMultiset

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : Multiset α) (hs : s ≠ 0) : Pmf α :=
  ⟨fun a => s.count a / s.card, by
    have : (∑ a in s.to_finset, (s.count a : ℝ) / s.card) = 1 := by
      simp [div_eq_inv_mul, finset.mul_sum.symm, (Nat.cast_sum _ _).symm, hs]
    have : (∑ a in s.to_finset, (s.count a : ℝ≥0 ) / s.card) = 1 := by
      rw [← Nnreal.eq_iff, Nnreal.coe_one, ← this, Nnreal.coe_sum] <;> simp
    rw [← this]
    apply has_sum_sum_of_ne_finset_zero
    simp (config := { contextual := true })⟩

variable {s : Multiset α} (hs : s ≠ 0)

@[simp]
theorem of_multiset_apply (a : α) : of_multiset s hs a = s.count a / s.card :=
  rfl

@[simp]
theorem support_of_multiset : (of_multiset s hs).Support = s.to_finset :=
  Set.ext
    (by
      simp [mem_support_iff, hs])

theorem mem_support_of_multiset_iff (a : α) : a ∈ (of_multiset s hs).Support ↔ a ∈ s.to_finset := by
  simp

theorem of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
  div_eq_zero_iff.2 (Or.inl $ Nat.cast_eq_zero.2 $ Multiset.count_eq_zero_of_not_mem ha)

end OfMultiset

section Uniform

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : Finset α) (hs : s.nonempty) : Pmf α :=
  of_finset (fun a => if a ∈ s then (s.card : ℝ≥0 )⁻¹ else 0) s
    (Exists.rec_on hs fun x hx =>
      calc
        (∑ a : α in s, ite (a ∈ s) ((s.card : ℝ≥0 )⁻¹) 0) = ∑ a : α in s, (s.card : ℝ≥0 )⁻¹ :=
          Finset.sum_congr rfl fun x hx => by
            simp [hx]
        _ = s.card • (s.card : ℝ≥0 )⁻¹ := Finset.sum_const _
        _ = (s.card : ℝ≥0 ) * (s.card : ℝ≥0 )⁻¹ := by
          rw [nsmul_eq_mul]
        _ = 1 := div_self (Nat.cast_ne_zero.2 $ Finset.card_ne_zero_of_mem hx)
        )
    fun x hx => by
    simp only [hx, if_false]

variable {s : Finset α} (hs : s.nonempty) {a : α}

@[simp]
theorem uniform_of_finset_apply (a : α) : uniform_of_finset s hs a = if a ∈ s then (s.card : ℝ≥0 )⁻¹ else 0 :=
  rfl

theorem uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniform_of_finset s hs a = s.card⁻¹ := by
  simp [ha]

theorem uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniform_of_finset s hs a = 0 := by
  simp [ha]

@[simp]
theorem support_uniform_of_finset : (uniform_of_finset s hs).Support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff, Finset.ne_empty_of_mem ha])

theorem mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniform_of_finset s hs).Support ↔ a ∈ s := by
  simp

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type _) [Fintype α] [Nonempty α] : Pmf α :=
  uniform_of_finset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniform_of_fintype_apply (a : α) : uniform_of_fintype α a = Fintype.card α⁻¹ := by
  simpa only [uniform_of_fintype, Finset.mem_univ, if_true, uniform_of_finset_apply]

variable (α)

@[simp]
theorem support_uniform_of_fintype : (uniform_of_fintype α).Support = ⊤ :=
  Set.ext fun x => by
    simpa [mem_support_iff] using Fintype.card_ne_zero

variable {α}

theorem mem_support_uniform_of_fintype_iff (a : α) : a ∈ (uniform_of_fintype α).Support := by
  simp

end UniformOfFintype

end Uniform

section normalize

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by it's `tsum` -/
def normalize (f : α → ℝ≥0 ) (hf0 : tsum f ≠ 0) : Pmf α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    mul_inv_cancel hf0 ▸
      HasSum.mul_right ((∑' x, f x)⁻¹) (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬Summable f)).HasSum⟩

variable {f : α → ℝ≥0 } (hf0 : tsum f ≠ 0)

@[simp]
theorem normalize_apply (a : α) : (normalize f hf0) a = f a * (∑' x, f x)⁻¹ :=
  rfl

@[simp]
theorem support_normalize : (normalize f hf0).Support = Function.Support f :=
  Set.ext
    (by
      simp [mem_support_iff, hf0])

theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0).Support ↔ f a ≠ 0 := by
  simp

end normalize

section Filter

/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def Filter (p : Pmf α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : Pmf α :=
  Pmf.normalize (s.indicator p) $ Nnreal.tsum_indicator_ne_zero p.2.Summable h

variable {p : Pmf α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

@[simp]
theorem filter_apply (a : α) : (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [Filter, normalize_apply]

theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]

@[simp]
theorem support_filter : (p.filter s h).Support = s ∩ p.support := by
  refine' Set.ext fun a => _
  rw [mem_support_iff, filter_apply, mul_ne_zero_iff, Set.indicator_eq_zero_iff]
  exact ⟨fun ha => ha.1, fun ha => ⟨ha, inv_ne_zero (Nnreal.tsum_indicator_ne_zero p.2.Summable h)⟩⟩

theorem mem_support_filter_iff (a : α) : a ∈ (p.filter s h).Support ↔ a ∈ s ∧ a ∈ p.support := by
  simp

theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  erw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_distrib]

theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne.def, filter_apply_eq_zero_iff, not_or_distrib, not_not, not_not]

end Filter

section Bernoulli

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0 ) (h : p ≤ 1) : Pmf Bool :=
  of_fintype (fun b => cond b p (1 - p))
    (Nnreal.eq $ by
      simp [h])

variable {p : ℝ≥0 } (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) :=
  rfl

@[simp]
theorem support_bernoulli : (bernoulli p h).Support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_ff, Ne.def, tsub_eq_zero_iff_le, not_leₓ]
    exact ⟨ne_of_ltₓ, lt_of_le_of_neₓ h⟩
    
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_tt, Set.mem_set_of_eq]
    

theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).Support ↔ cond b (p ≠ 0) (p ≠ 1) := by
  simp

end Bernoulli

end Pmf

