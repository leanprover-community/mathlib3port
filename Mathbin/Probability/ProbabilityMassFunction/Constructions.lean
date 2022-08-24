/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathbin.Probability.ProbabilityMassFunction.Monad

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `bool`

-/


namespace Pmf

noncomputable section

variable {α β γ : Type _}

open Classical BigOperators Nnreal Ennreal

section Map

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : Pmf α) : Pmf β :=
  bind p (pure ∘ f)

variable (f : α → β) (p : Pmf α) (b : β)

theorem monad_map_eq_map {α β : Type _} (f : α → β) (p : Pmf α) : f <$> p = p.map f :=
  rfl

@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by
  simp [map]

@[simp]
theorem support_map : (map f p).Support = f '' p.Support :=
  Set.ext fun b => by
    simp [map, @eq_comm β b]

theorem mem_support_map_iff : b ∈ (map f p).Support ↔ ∃ a ∈ p.Support, f a = b := by
  simp

theorem bind_pure_comp : bind p (pure ∘ f) = map f p :=
  rfl

theorem map_id : map id p = p := by
  simp [map]

theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by
  simp [map]

theorem pure_map (a : α) : (pure a).map f = pure (f a) := by
  simp [map]

section Measureₓ

variable (s : Set β)

@[simp]
theorem to_outer_measure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicatorₓ, to_outer_measure_apply p (f ⁻¹' s)]

@[simp]
theorem to_measure_map_apply [MeasurableSpace α] [MeasurableSpace β] (hf : Measurable f) (hs : MeasurableSet s) :
    (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [to_measure_apply_eq_to_outer_measure_apply _ s hs,
    to_measure_apply_eq_to_outer_measure_apply _ (f ⁻¹' s) (measurable_set_preimage hf hs)]
  exact to_outer_measure_map_apply f p s

end Measureₓ

end Map

section Seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (q : Pmf (α → β)) (p : Pmf α) : Pmf β :=
  q.bind fun m => p.bind fun a => pure (m a)

variable (q : Pmf (α → β)) (p : Pmf α) (b : β)

theorem monad_seq_eq_seq {α β : Type _} (q : Pmf (α → β)) (p : Pmf α) : q <*> p = q.seq p :=
  rfl

@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine' tsum_congr fun f => (Nnreal.tsum_mul_left (q f) _).symm.trans (tsum_congr fun a => _)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]
theorem support_seq : (seq q p).Support = ⋃ f ∈ q.Support, f '' p.Support :=
  Set.ext fun b => by
    simp [-mem_support_iff, seq, @eq_comm β b]

theorem mem_support_seq_iff : b ∈ (seq q p).Support ↔ ∃ f ∈ q.Support, b ∈ f '' p.Support := by
  simp

end Seq

instance : IsLawfulFunctor Pmf where
  map_const_eq := fun α β => rfl
  id_map := fun α => bind_pure
  comp_map := fun α β γ g h x => (map_comp _ _ _).symm

instance : IsLawfulMonad Pmf where
  bind_pure_comp_eq_map := fun α β f x => rfl
  bind_map_eq_seq := fun α β f x => rfl
  pure_bind := fun α β => pure_bind
  bind_assoc := fun α β γ => bind_bind

section OfFinset

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (a «expr ∉ » s)
/-- Given a finset `s` and a function `f : α → ℝ≥0` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `pmf` -/
def ofFinset (f : α → ℝ≥0 ) (s : Finset α) (h : (∑ a in s, f a) = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0) : Pmf α :=
  ⟨f, h ▸ has_sum_sum_of_ne_finset_zero h'⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (a «expr ∉ » s)
variable {f : α → ℝ≥0 } {s : Finset α} (h : (∑ a in s, f a) = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem of_finset_apply (a : α) : ofFinset f s h h' a = f a :=
  rfl

@[simp]
theorem support_of_finset : (ofFinset f s h h').Support = s ∩ Function.Support f :=
  Set.ext fun a => by
    simpa [mem_support_iff] using mt (h' a)

theorem mem_support_of_finset_iff (a : α) : a ∈ (ofFinset f s h h').Support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem of_finset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

section Measureₓ

variable (t : Set α)

@[simp]
theorem to_outer_measure_of_finset_apply : (ofFinset f s h h').toOuterMeasure t = ↑(∑' x, t.indicator f x) :=
  to_outer_measure_apply' (ofFinset f s h h') t

@[simp]
theorem to_measure_of_finset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ↑(∑' x, t.indicator f x) :=
  (to_measure_apply_eq_to_outer_measure_apply _ t ht).trans (to_outer_measure_of_finset_apply h h' t)

end Measureₓ

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0 ) (h : (∑ a, f a) = 1) : Pmf α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0 } (h : (∑ a, f a) = 1)

@[simp]
theorem of_fintype_apply (a : α) : ofFintype f h a = f a :=
  rfl

@[simp]
theorem support_of_fintype : (ofFintype f h).Support = Function.Support f :=
  rfl

theorem mem_support_of_fintype_iff (a : α) : a ∈ (ofFintype f h).Support ↔ f a ≠ 0 :=
  Iff.rfl

section Measureₓ

variable (s : Set α)

@[simp]
theorem to_outer_measure_of_fintype_apply : (ofFintype f h).toOuterMeasure s = ↑(∑' x, s.indicator f x) :=
  to_outer_measure_apply' (ofFintype f h) s

@[simp]
theorem to_measure_of_fintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ↑(∑' x, s.indicator f x) :=
  (to_measure_apply_eq_to_outer_measure_apply _ s hs).trans (to_outer_measure_of_fintype_apply h s)

end Measureₓ

end OfFintype

section normalize

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by it's `tsum` -/
def normalize (f : α → ℝ≥0 ) (hf0 : tsum f ≠ 0) : Pmf α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    mul_inv_cancel hf0 ▸
      HasSum.mul_right (∑' x, f x)⁻¹ (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬Summable f)).HasSum⟩

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
def filter (p : Pmf α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.Support) : Pmf α :=
  Pmf.normalize (s.indicator p) <| Nnreal.tsum_indicator_ne_zero p.2.Summable h

variable {p : Pmf α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.Support)

@[simp]
theorem filter_apply (a : α) : (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [Filter, normalize_apply]

theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]

theorem mem_support_filter_iff {a : α} : a ∈ (p.filter s h).Support ↔ a ∈ s ∧ a ∈ p.Support :=
  (mem_support_normalize_iff _ _).trans Set.indicator_apply_ne_zero

@[simp]
theorem support_filter : (p.filter s h).Support = s ∩ p.Support :=
  Set.ext fun x => mem_support_filter_iff _

theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.Support := by
  erw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_distrib]

theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.Support := by
  rw [Ne.def, filter_apply_eq_zero_iff, not_or_distrib, not_not, not_not]

end Filter

section Bernoulli

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0 ) (h : p ≤ 1) : Pmf Bool :=
  ofFintype (fun b => cond b p (1 - p))
    (Nnreal.eq <| by
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

