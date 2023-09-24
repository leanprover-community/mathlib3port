/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Data.Sign
import Topology.Order.Basic

#align_import topology.instances.sign from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Topology on `sign_type`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print continuousAt_sign_of_pos /-
theorem continuousAt_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt SignType.sign a :=
  by
  refine' (continuousAt_const : ContinuousAt (fun x => (1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{x | 0 < x}, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩
#align continuous_at_sign_of_pos continuousAt_sign_of_pos
-/

#print continuousAt_sign_of_neg /-
theorem continuousAt_sign_of_neg {a : α} (h : a < 0) : ContinuousAt SignType.sign a :=
  by
  refine' (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{x | x < 0}, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩
#align continuous_at_sign_of_neg continuousAt_sign_of_neg
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

#print continuousAt_sign_of_ne_zero /-
theorem continuousAt_sign_of_ne_zero {a : α} (h : a ≠ 0) : ContinuousAt SignType.sign a :=
  by
  rcases h.lt_or_lt with (h_neg | h_pos)
  · exact continuousAt_sign_of_neg h_neg
  · exact continuousAt_sign_of_pos h_pos
#align continuous_at_sign_of_ne_zero continuousAt_sign_of_ne_zero
-/

end LinearOrder

