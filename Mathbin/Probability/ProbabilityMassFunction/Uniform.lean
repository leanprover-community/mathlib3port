/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma

! This file was ported from Lean 3 source module probability.probability_mass_function.uniform
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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
  ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s
    (Exists.rec_on hs fun x hx =>
      calc
        (∑ a : α in s, ite (a ∈ s) (s.card : ℝ≥0∞)⁻¹ 0) = ∑ a : α in s, (s.card : ℝ≥0∞)⁻¹ :=
          Finset.sum_congr rfl fun x hx => by simp [hx]
        _ = (s.card : ℝ≥0∞) * (s.card : ℝ≥0∞)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 :=
          Ennreal.mul_inv_cancel
            (by
              simpa only [Ne.def, Nat.cast_eq_zero, Finset.card_eq_zero] using
                Finset.nonempty_iff_ne_empty.1 hs)
            (Ennreal.nat_ne_top s.card)
        )
    fun x hx => by simp only [hx, if_false]
#align pmf.uniform_of_finset Pmf.uniformOfFinset

variable {s : Finset α} (hs : s.Nonempty) {a : α}

@[simp]
theorem uniform_of_finset_apply (a : α) : uniformOfFinset s hs a = if a ∈ s then s.card⁻¹ else 0 :=
  rfl
#align pmf.uniform_of_finset_apply Pmf.uniform_of_finset_apply

theorem uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = s.card⁻¹ := by
  simp [ha]
#align pmf.uniform_of_finset_apply_of_mem Pmf.uniform_of_finset_apply_of_mem

theorem uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]
#align pmf.uniform_of_finset_apply_of_not_mem Pmf.uniform_of_finset_apply_of_not_mem

@[simp]
theorem support_uniform_of_finset : (uniformOfFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff, Finset.ne_empty_of_mem ha])
#align pmf.support_uniform_of_finset Pmf.support_uniform_of_finset

theorem mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp
#align pmf.mem_support_uniform_of_finset_iff Pmf.mem_support_uniform_of_finset_iff

section Measure

variable (t : Set α)

@[simp]
theorem to_outer_measure_uniform_of_finset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = (s.filter (· ∈ t)).card / s.card :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      to_outer_measure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by
        simp only [uniform_of_finset_apply, and_comm' (x ∈ s), ite_and, Ennreal.coe_nat]
    _ = ∑ x in s.filter (· ∈ t), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun x hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x in s.filter (· ∈ t), (s.card : ℝ≥0∞)⁻¹ :=
      (Finset.sum_congr rfl) fun x hx =>
        by
        let this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = (s.filter (· ∈ t)).card / s.card :=
      by
      have : (s.card : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.2 (hs.recOn fun _ => Finset.card_ne_zero_of_mem)
      simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
    
#align pmf.to_outer_measure_uniform_of_finset_apply Pmf.to_outer_measure_uniform_of_finset_apply

@[simp]
theorem to_measure_uniform_of_finset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = (s.filter (· ∈ t)).card / s.card :=
  (to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
    (to_outer_measure_uniform_of_finset_apply hs t)
#align pmf.to_measure_uniform_of_finset_apply Pmf.to_measure_uniform_of_finset_apply

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniformOfFintype (α : Type _) [Fintype α] [Nonempty α] : Pmf α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty
#align pmf.uniform_of_fintype Pmf.uniformOfFintype

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniform_of_fintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α)⁻¹ := by
  simpa only [uniform_of_fintype, Finset.mem_univ, if_true, uniform_of_finset_apply]
#align pmf.uniform_of_fintype_apply Pmf.uniform_of_fintype_apply

@[simp]
theorem support_uniform_of_fintype (α : Type _) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]
#align pmf.support_uniform_of_fintype Pmf.support_uniform_of_fintype

theorem mem_support_uniform_of_fintype (a : α) : a ∈ (uniformOfFintype α).support := by simp
#align pmf.mem_support_uniform_of_fintype Pmf.mem_support_uniform_of_fintype

section Measure

variable (s : Set α)

theorem to_outer_measure_uniform_of_fintype_apply :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  simpa [uniform_of_fintype]
#align pmf.to_outer_measure_uniform_of_fintype_apply Pmf.to_outer_measure_uniform_of_fintype_apply

theorem to_measure_uniform_of_fintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  simpa [uniform_of_fintype, hs]
#align pmf.to_measure_uniform_of_fintype_apply Pmf.to_measure_uniform_of_fintype_apply

end Measure

end UniformOfFintype

section OfMultiset

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : Pmf α :=
  ⟨fun a => s.count a / s.card,
    Ennreal.summable.has_sum_iff.2
      (calc
        (∑' b : α, (s.count b : ℝ≥0∞) / s.card) = s.card⁻¹ * ∑' b, s.count b := by
          simp_rw [Ennreal.div_eq_inv_mul, Ennreal.tsum_mul_left]
        _ = s.card⁻¹ * ∑ b in s.toFinset, (s.count b : ℝ≥0∞) :=
          congr_arg (fun x => s.card⁻¹ * x)
            (tsum_eq_sum fun a ha =>
              Nat.cast_eq_zero.2 <| by rwa [Multiset.count_eq_zero, ← Multiset.mem_to_finset])
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.to_finset_sum_count_eq s,
            Ennreal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (Ennreal.nat_ne_top _)]
        )⟩
#align pmf.of_multiset Pmf.ofMultiset

variable {s : Multiset α} (hs : s ≠ 0)

@[simp]
theorem of_multiset_apply (a : α) : ofMultiset s hs a = s.count a / s.card :=
  rfl
#align pmf.of_multiset_apply Pmf.of_multiset_apply

@[simp]
theorem support_of_multiset : (ofMultiset s hs).support = s.toFinset :=
  Set.ext (by simp [mem_support_iff, hs])
#align pmf.support_of_multiset Pmf.support_of_multiset

theorem mem_support_of_multiset_iff (a : α) : a ∈ (ofMultiset s hs).support ↔ a ∈ s.toFinset := by
  simp
#align pmf.mem_support_of_multiset_iff Pmf.mem_support_of_multiset_iff

theorem of_multiset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 := by
  simpa only [of_multiset_apply, Ennreal.div_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    Ennreal.nat_ne_top, or_false_iff] using ha
#align pmf.of_multiset_apply_of_not_mem Pmf.of_multiset_apply_of_not_mem

section Measure

variable (t : Set α)

@[simp]
theorem to_outer_measure_of_multiset_apply :
    (ofMultiset s hs).toOuterMeasure t = (∑' x, (s.filter (· ∈ t)).count x) / s.card :=
  by
  rw [div_eq_mul_inv, ← Ennreal.tsum_mul_right, to_outer_measure_apply]
  refine' tsum_congr fun x => _
  by_cases hx : x ∈ t <;> simp [Set.indicator, hx, div_eq_mul_inv]
#align pmf.to_outer_measure_of_multiset_apply Pmf.to_outer_measure_of_multiset_apply

@[simp]
theorem to_measure_of_multiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· ∈ t)).count x) / s.card :=
  (to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
    (to_outer_measure_of_multiset_apply hs t)
#align pmf.to_measure_of_multiset_apply Pmf.to_measure_of_multiset_apply

end Measure

end OfMultiset

end Pmf

