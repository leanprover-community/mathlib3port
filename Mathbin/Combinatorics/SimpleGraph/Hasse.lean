/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Combinatorics.SimpleGraph.Prod
import Data.Fin.SuccPred
import Order.SuccPred.Relation

#align_import combinatorics.simple_graph.hasse from "leanprover-community/mathlib"@"f47581155c818e6361af4e4fda60d27d020c226b"

/-!
# The Hasse diagram as a graph

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the Hasse diagram of an order (graph of `covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `simple_graph.hasse`: Hasse diagram of an order.
* `simple_graph.path_graph`: Path graph on `n` vertices.
-/


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type _)

section Preorder

variable [Preorder α] [Preorder β]

#print SimpleGraph.hasse /-
/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm a b := Or.symm
  loopless a h := h.elim (irrefl _) (irrefl _)
#align simple_graph.hasse SimpleGraph.hasse
-/

variable {α β} {a b : α}

#print SimpleGraph.hasse_adj /-
@[simp]
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl
#align simple_graph.hasse_adj SimpleGraph.hasse_adj
-/

#print SimpleGraph.hasseDualIso /-
/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := fun a b => by simp [or_comm'] }
#align simple_graph.hasse_dual_iso SimpleGraph.hasseDualIso
-/

#print SimpleGraph.hasseDualIso_apply /-
@[simp]
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl
#align simple_graph.hasse_dual_iso_apply SimpleGraph.hasseDualIso_apply
-/

#print SimpleGraph.hasseDualIso_symm_apply /-
@[simp]
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl
#align simple_graph.hasse_dual_iso_symm_apply SimpleGraph.hasseDualIso_symm_apply
-/

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

#print SimpleGraph.hasse_prod /-
@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by ext x y;
  simp_rw [box_prod_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]
#align simple_graph.hasse_prod SimpleGraph.hasse_prod
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α]

#print SimpleGraph.hasse_preconnected_of_succ /-
theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_refl_trans_gen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covby_succ_of_not_is_max hc.2.not_isMax)
      fun c hc => Or.inr <| covby_succ_of_not_is_max hc.2.not_isMax
#align simple_graph.hasse_preconnected_of_succ SimpleGraph.hasse_preconnected_of_succ
-/

#print SimpleGraph.hasse_preconnected_of_pred /-
theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_refl_trans_gen, ← refl_trans_gen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covby_of_not_is_min hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covby_of_not_is_min hc.1.not_isMin
#align simple_graph.hasse_preconnected_of_pred SimpleGraph.hasse_preconnected_of_pred
-/

end LinearOrder

#print SimpleGraph.pathGraph /-
/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _
#align simple_graph.path_graph SimpleGraph.pathGraph
-/

#print SimpleGraph.pathGraph_preconnected /-
theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _
#align simple_graph.path_graph_preconnected SimpleGraph.pathGraph_preconnected
-/

#print SimpleGraph.pathGraph_connected /-
theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩
#align simple_graph.path_graph_connected SimpleGraph.pathGraph_connected
-/

end SimpleGraph

