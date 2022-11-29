/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Topology.ContinuousOn

/-!
# Left and right continuity

In this file we prove a few lemmas about left and right continuous functions:

* `continuous_within_at_Ioi_iff_Ici`: two definitions of right continuity
  (with `(a, ∞)` and with `[a, ∞)`) are equivalent;
* `continuous_within_at_Iio_iff_Iic`: two definitions of left continuity
  (with `(-∞, a)` and with `(-∞, a]`) are equivalent;
* `continuous_at_iff_continuous_left_right`, `continuous_at_iff_continuous_left'_right'` :
  a function is continuous at `a` if and only if it is left and right continuous at `a`.

## Tags

left continuous, right continuous
-/


open Set Filter

open TopologicalSpace

section PartialOrder

variable {α β : Type _} [TopologicalSpace α] [PartialOrder α] [TopologicalSpace β]

theorem continuous_within_at_Ioi_iff_Ici {a : α} {f : α → β} :
    ContinuousWithinAt f (ioi a) a ↔ ContinuousWithinAt f (ici a) a := by
  simp only [← Ici_diff_left, continuous_within_at_diff_self]
#align continuous_within_at_Ioi_iff_Ici continuous_within_at_Ioi_iff_Ici

theorem continuous_within_at_Iio_iff_Iic {a : α} {f : α → β} :
    ContinuousWithinAt f (iio a) a ↔ ContinuousWithinAt f (iic a) a :=
  @continuous_within_at_Ioi_iff_Ici αᵒᵈ _ ‹TopologicalSpace α› _ _ _ f
#align continuous_within_at_Iio_iff_Iic continuous_within_at_Iio_iff_Iic

theorem nhds_left'_le_nhds_ne (a : α) : 𝓝[<] a ≤ 𝓝[≠] a :=
  nhds_within_mono a fun y hy => ne_of_lt hy
#align nhds_left'_le_nhds_ne nhds_left'_le_nhds_ne

theorem nhds_right'_le_nhds_ne (a : α) : 𝓝[>] a ≤ 𝓝[≠] a :=
  nhds_within_mono a fun y hy => ne_of_gt hy
#align nhds_right'_le_nhds_ne nhds_right'_le_nhds_ne

end PartialOrder

section TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]

theorem nhds_left_sup_nhds_right (a : α) : 𝓝[≤] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhds_within_union, Iic_union_Ici, nhds_within_univ]
#align nhds_left_sup_nhds_right nhds_left_sup_nhds_right

theorem nhds_left'_sup_nhds_right (a : α) : 𝓝[<] a ⊔ 𝓝[≥] a = 𝓝 a := by
  rw [← nhds_within_union, Iio_union_Ici, nhds_within_univ]
#align nhds_left'_sup_nhds_right nhds_left'_sup_nhds_right

theorem nhds_left_sup_nhds_right' (a : α) : 𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a := by
  rw [← nhds_within_union, Iic_union_Ioi, nhds_within_univ]
#align nhds_left_sup_nhds_right' nhds_left_sup_nhds_right'

theorem nhds_left'_sup_nhds_right' (a : α) : 𝓝[<] a ⊔ 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhds_within_union, Iio_union_Ioi]
#align nhds_left'_sup_nhds_right' nhds_left'_sup_nhds_right'

theorem continuous_at_iff_continuous_left_right {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (iic a) a ∧ ContinuousWithinAt f (ici a) a := by
  simp only [ContinuousWithinAt, ContinuousAt, ← tendsto_sup, nhds_left_sup_nhds_right]
#align continuous_at_iff_continuous_left_right continuous_at_iff_continuous_left_right

theorem continuous_at_iff_continuous_left'_right' {a : α} {f : α → β} :
    ContinuousAt f a ↔ ContinuousWithinAt f (iio a) a ∧ ContinuousWithinAt f (ioi a) a := by
  rw [continuous_within_at_Ioi_iff_Ici, continuous_within_at_Iio_iff_Iic,
    continuous_at_iff_continuous_left_right]
#align continuous_at_iff_continuous_left'_right' continuous_at_iff_continuous_left'_right'

end TopologicalSpace

