import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Topology.ExtendFrom

/-!
# Lemmas about `extend_from` in an order topology.
-/


open Filter Set TopologicalSpace

open_locale TopologicalSpace Classical

universe u v

variable{α : Type u}{β : Type v}

theorem continuous_on_Icc_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
  (ha : tendsto f (𝓝[Ioi a] a) (𝓝 la)) (hb : tendsto f (𝓝[Iio b] b) (𝓝 lb)) :
  ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) :=
  by 
    apply continuous_on_extend_from
    ·
      rw [closure_Ioo hab]
    ·
      intro x x_in 
      rcases mem_Ioo_or_eq_endpoints_of_mem_Icc x_in with (rfl | rfl | h)
      ·
        use la 
        simpa [hab]
      ·
        use lb 
        simpa [hab]
      ·
        use f x, hf x h

theorem eq_lim_at_left_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b) (ha : tendsto f (𝓝[Ioi a] a) (𝓝 la)) :
  extendFrom (Ioo a b) f a = la :=
  by 
    apply extend_from_eq
    ·
      rw [closure_Ioo hab]
      simp only [le_of_ltₓ hab, left_mem_Icc, right_mem_Icc]
    ·
      simpa [hab]

theorem eq_lim_at_right_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b) (hb : tendsto f (𝓝[Iio b] b) (𝓝 lb)) :
  extendFrom (Ioo a b) f b = lb :=
  by 
    apply extend_from_eq
    ·
      rw [closure_Ioo hab]
      simp only [le_of_ltₓ hab, left_mem_Icc, right_mem_Icc]
    ·
      simpa [hab]

theorem continuous_on_Ico_extend_from_Ioo [TopologicalSpace α] [LinearOrderₓ α] [DenselyOrdered α] [OrderTopology α]
  [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β} (hab : a < b) (hf : ContinuousOn f (Ioo a b))
  (ha : tendsto f (𝓝[Ioi a] a) (𝓝 la)) : ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) :=
  by 
    apply continuous_on_extend_from
    ·
      rw [closure_Ioo hab]
      exact Ico_subset_Icc_self
    ·
      intro x x_in 
      rcases mem_Ioo_or_eq_left_of_mem_Ico x_in with (rfl | h)
      ·
        use la 
        simpa [hab]
      ·
        use f x, hf x h

-- error in Topology.Algebra.Ordered.ExtendFrom: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_on_Ioc_extend_from_Ioo
[topological_space α]
[linear_order α]
[densely_ordered α]
[order_topology α]
[topological_space β]
[regular_space β]
{f : α → β}
{a b : α}
{lb : β}
(hab : «expr < »(a, b))
(hf : continuous_on f (Ioo a b))
(hb : tendsto f «expr𝓝[ ] »(Iio b, b) (expr𝓝() lb)) : continuous_on (extend_from (Ioo a b) f) (Ioc a b) :=
begin
  have [] [] [":=", expr @continuous_on_Ico_extend_from_Ioo (order_dual α) _ _ _ _ _ _ _ f _ _ _ hab],
  erw ["[", expr dual_Ico, ",", expr dual_Ioi, ",", expr dual_Ioo, "]"] ["at", ident this],
  exact [expr this hf hb]
end

