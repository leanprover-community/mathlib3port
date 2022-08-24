/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathbin.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform Probability Mass Functions

This file defines a number of uniform `pmf` distributions from various inputs,
  uniformly drawing from the corresponding object.

`pmf.uniform_of_finset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`pmf.uniform_of_fintype` gives all elements equal probability,
  equal to the inverse of the size of the `fintype`.

`pmf.of_multiset` draws randomly from the given `multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `multiset`

-/


namespace Pmf

noncomputable section

variable {α β γ : Type _}

open Classical BigOperators Nnreal Ennreal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : Pmf α :=
  ofFinset (fun a => if a ∈ s then (s.card : ℝ≥0 )⁻¹ else 0) s
    (Exists.rec_on hs fun x hx =>
      calc
        (∑ a : α in s, ite (a ∈ s) (s.card : ℝ≥0 )⁻¹ 0) = ∑ a : α in s, (s.card : ℝ≥0 )⁻¹ :=
          Finset.sum_congr rfl fun x hx => by
            simp [hx]
        _ = s.card • (s.card : ℝ≥0 )⁻¹ := Finset.sum_const _
        _ = (s.card : ℝ≥0 ) * (s.card : ℝ≥0 )⁻¹ := by
          rw [nsmul_eq_mul]
        _ = 1 := div_self (Nat.cast_ne_zero.2 <| Finset.card_ne_zero_of_mem hx)
        )
    fun x hx => by
    simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

@[simp]
theorem uniform_of_finset_apply (a : α) : uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0 )⁻¹ else 0 :=
  rfl

theorem uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = s.card⁻¹ := by
  simp [ha]

theorem uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by
  simp [ha]

@[simp]
theorem support_uniform_of_finset : (uniformOfFinset s hs).Support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff, Finset.ne_empty_of_mem ha])

theorem mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniformOfFinset s hs).Support ↔ a ∈ s := by
  simp

section Measureₓ

variable (t : Set α)

@[simp]
theorem to_outer_measure_uniform_of_finset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = (s.filter (· ∈ t)).card / s.card :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ↑(∑' x, if x ∈ t then uniformOfFinset s hs x else 0) :=
      to_outer_measure_apply' (uniformOfFinset s hs) t
    _ = ↑(∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0 )⁻¹ else 0) := by
      refine' Ennreal.coe_eq_coe.2 <| tsum_congr fun x => _
      by_cases' hxt : x ∈ t
      · by_cases' hxs : x ∈ s <;> simp [hxt, hxs]
        
      · simp [hxt]
        
    _ = ↑(∑ x in s.filter (· ∈ t), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0 )⁻¹ else 0) := by
      refine' Ennreal.coe_eq_coe.2 (tsum_eq_sum fun x hx => _)
      have : ¬(x ∈ s ∧ x ∈ t) := fun h => hx (Finset.mem_filter.2 h)
      simp [this]
    _ = ↑(∑ x in s.filter (· ∈ t), (s.card : ℝ≥0 )⁻¹) :=
      Ennreal.coe_eq_coe.2
        ((Finset.sum_congr rfl) fun x hx => by
          let this : x ∈ s ∧ x ∈ t := by
            simpa using hx
          simp [this])
    _ = (s.filter (· ∈ t)).card / s.card := by
      let this : (s.card : ℝ≥0 ) ≠ 0 := Nat.cast_ne_zero.2 (hs.recOn fun _ => Finset.card_ne_zero_of_mem)
      simp [div_eq_mul_inv, Ennreal.coe_inv this]
    

@[simp]
theorem to_measure_uniform_of_finset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = (s.filter (· ∈ t)).card / s.card :=
  (to_measure_apply_eq_to_outer_measure_apply _ t ht).trans (to_outer_measure_uniform_of_finset_apply hs t)

end Measureₓ

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniformOfFintype (α : Type _) [Fintype α] [Nonempty α] : Pmf α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniform_of_fintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α)⁻¹ := by
  simpa only [uniform_of_fintype, Finset.mem_univ, if_true, uniform_of_finset_apply]

@[simp]
theorem support_uniform_of_fintype (α : Type _) [Fintype α] [Nonempty α] : (uniformOfFintype α).Support = ⊤ :=
  Set.ext fun x => by
    simpa [mem_support_iff] using Fintype.card_ne_zero

theorem mem_support_uniform_of_fintype (a : α) : a ∈ (uniformOfFintype α).Support := by
  simp

section Measureₓ

variable (s : Set α)

theorem to_outer_measure_uniform_of_fintype_apply :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  simpa [uniform_of_fintype]

theorem to_measure_uniform_of_fintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  simpa [uniform_of_fintype, hs]

end Measureₓ

end UniformOfFintype

section OfMultiset

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : Pmf α :=
  ⟨fun a => s.count a / s.card, by
    have : (∑ a in s.toFinset, (s.count a : ℝ) / s.card) = 1 := by
      simp only [div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum, Multiset.to_finset_sum_count_eq]
      rw [inv_mul_cancel]
      simp [hs]
    have : (∑ a in s.toFinset, (s.count a : ℝ≥0 ) / s.card) = 1 := by
      rw [← Nnreal.eq_iff, Nnreal.coe_one, ← this, Nnreal.coe_sum] <;> simp
    rw [← this]
    apply has_sum_sum_of_ne_finset_zero
    simp (config := { contextual := true })⟩

variable {s : Multiset α} (hs : s ≠ 0)

@[simp]
theorem of_multiset_apply (a : α) : ofMultiset s hs a = s.count a / s.card :=
  rfl

@[simp]
theorem support_of_multiset : (ofMultiset s hs).Support = s.toFinset :=
  Set.ext
    (by
      simp [mem_support_iff, hs])

theorem mem_support_of_multiset_iff (a : α) : a ∈ (ofMultiset s hs).Support ↔ a ∈ s.toFinset := by
  simp

theorem of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 :=
  div_eq_zero_iff.2 (Or.inl <| Nat.cast_eq_zero.2 <| Multiset.count_eq_zero_of_not_mem ha)

section Measureₓ

variable (t : Set α)

@[simp]
theorem to_outer_measure_of_multiset_apply :
    (ofMultiset s hs).toOuterMeasure t = (∑' x, (s.filter (· ∈ t)).count x) / s.card := by
  rw [div_eq_mul_inv, ← Ennreal.tsum_mul_right, to_outer_measure_apply]
  refine' tsum_congr fun x => _
  by_cases' hx : x ∈ t
  · have : (Multiset.card s : ℝ≥0 ) ≠ 0 := by
      simp [hs]
    simp [Set.indicatorₓ, hx, div_eq_mul_inv, Ennreal.coe_inv this]
    
  · simp [hx]
    

@[simp]
theorem to_measure_of_multiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· ∈ t)).count x) / s.card :=
  (to_measure_apply_eq_to_outer_measure_apply _ t ht).trans (to_outer_measure_of_multiset_apply hs t)

end Measureₓ

end OfMultiset

end Pmf

