/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module topology.instances.sign
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sign
import Mathbin.Topology.Order.Basic

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

section PartialOrder

variable [PartialOrder α] [DecidableRel ((· < ·) : α → α → Prop)] [OrderTopology α]

theorem continuous_at_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt sign a := by
  refine' (continuous_at_const : ContinuousAt (fun x => (1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, is_open_lt' 0, h⟩
#align continuous_at_sign_of_pos continuous_at_sign_of_pos

theorem continuous_at_sign_of_neg {a : α} (h : a < 0) : ContinuousAt sign a := by
  refine' (continuous_at_const : ContinuousAt (fun x => (-1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, is_open_gt' 0, h⟩
#align continuous_at_sign_of_neg continuous_at_sign_of_neg

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

theorem continuous_at_sign_of_ne_zero {a : α} (h : a ≠ 0) : ContinuousAt sign a := by
  rcases h.lt_or_lt with (h_neg | h_pos)
  · exact continuous_at_sign_of_neg h_neg
  · exact continuous_at_sign_of_pos h_pos
#align continuous_at_sign_of_ne_zero continuous_at_sign_of_ne_zero

end LinearOrder

