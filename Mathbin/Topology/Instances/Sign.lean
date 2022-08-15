/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Data.Sign
import Mathbin.Topology.Algebra.Order.Basic

/-!
# Topology on `sign_type`

This file gives `sign_type` the discrete topology, and proves continuity results for `sign` in
an `order_topology`.

-/


instance : TopologicalSpace SignType :=
  ⊥

instance : DiscreteTopology SignType :=
  ⟨rfl⟩

variable {α : Type _} [Zero α] [TopologicalSpace α]

section PartialOrderₓ

variable [PartialOrderₓ α] [DecidableRel ((· < ·) : α → α → Prop)] [OrderTopology α]

theorem continuous_at_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt sign a := by
  refine' (continuous_at_const : ContinuousAt (fun x => (1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, is_open_lt' 0, h⟩

theorem continuous_at_sign_of_neg {a : α} (h : a < 0) : ContinuousAt sign a := by
  refine' (continuous_at_const : ContinuousAt (fun x => (-1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, is_open_gt' 0, h⟩

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] [OrderTopology α]

theorem continuous_at_sign_of_ne_zero {a : α} (h : a ≠ 0) : ContinuousAt sign a := by
  rcases h.lt_or_lt with (h_neg | h_pos)
  · exact continuous_at_sign_of_neg h_neg
    
  · exact continuous_at_sign_of_pos h_pos
    

end LinearOrderₓ

