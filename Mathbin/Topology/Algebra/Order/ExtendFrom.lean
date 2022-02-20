/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathbin.Topology.Algebra.Order.Basic
import Mathbin.Topology.ExtendFrom

/-!
# Lemmas about `extend_from` in an order topology.
-/


open Filter Set TopologicalSpace

open_locale TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v}

theorem continuous_on_Icc_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
    [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β} (hab : a ≠ b)
    (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) := by
  apply continuous_on_extend_from
  · rw [closure_Ioo hab]
    
  · intro x x_in
    rcases mem_Ioo_or_eq_endpoints_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhds_within_mono _ Ioo_subset_Ioi_self⟩
      
    · exact ⟨lb, hb.mono_left <| nhds_within_mono _ Ioo_subset_Iio_self⟩
      
    · use f x, hf x h
      
    

theorem eq_lim_at_left_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
    [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    extendFrom (Ioo a b) f a = la := by
  apply extend_from_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_ltₓ hab, left_mem_Icc, right_mem_Icc]
    
  · simpa [hab]
    

theorem eq_lim_at_right_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
    [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    extendFrom (Ioo a b) f b = lb := by
  apply extend_from_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_ltₓ hab, left_mem_Icc, right_mem_Icc]
    
  · simpa [hab]
    

theorem continuous_on_Ico_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
    [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) := by
  apply continuous_on_extend_from
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
    
  · intro x x_in
    rcases mem_Ioo_or_eq_left_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
      
    · use f x, hf x h
      
    

theorem continuous_on_Ioc_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
    [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) := by
  have := @continuous_on_Ico_extend_from_Ioo (OrderDual α) _ _ _ _ _ _ _ f _ _ _ hab
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this
  exact this hf hb

