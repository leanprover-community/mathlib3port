/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.simple_graph.hasse
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Prod
import Mathbin.Data.Fin.SuccPred
import Mathbin.Order.SuccPred.Relation

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

/- warning: simple_graph.hasse_dual_iso_apply -> SimpleGraph.hasseDualIso_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : OrderDual.{u1} α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (SimpleGraph.Iso.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)) (SimpleGraph.hasse.{u1} α _inst_1)) (fun (_x : RelIso.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1))) => (OrderDual.{u1} α) -> α) (RelIso.hasCoeToFun.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1))) (SimpleGraph.hasseDualIso.{u1} α _inst_1) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : OrderDual.{u1} α), Eq.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (RelIso.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1))) (OrderDual.{u1} α) (fun (_x : OrderDual.{u1} α) => α) (RelHomClass.toFunLike.{u1, u1, u1} (RelIso.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1))) (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (RelIso.instRelHomClassRelIso.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)))) (SimpleGraph.hasseDualIso.{u1} α _inst_1) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.{u1} α) (fun (_x : OrderDual.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : OrderDual.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align simple_graph.hasse_dual_iso_apply SimpleGraph.hasseDualIso_applyₓ'. -/
@[simp]
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl
#align simple_graph.hasse_dual_iso_apply SimpleGraph.hasseDualIso_apply

/- warning: simple_graph.hasse_dual_iso_symm_apply -> SimpleGraph.hasseDualIso_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (SimpleGraph.Iso.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} α _inst_1) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (fun (_x : RelIso.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)))) => α -> (OrderDual.{u1} α)) (RelIso.hasCoeToFun.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)))) (SimpleGraph.Iso.symm.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)) (SimpleGraph.hasse.{u1} α _inst_1) (SimpleGraph.hasseDualIso.{u1} α _inst_1)) a) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (OrderDual.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (RelIso.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)))) α (fun (_x : α) => OrderDual.{u1} α) (RelHomClass.toFunLike.{u1, u1, u1} (RelIso.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)))) α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (RelIso.instRelHomClassRelIso.{u1, u1} α (OrderDual.{u1} α) (SimpleGraph.Adj.{u1} α (SimpleGraph.hasse.{u1} α _inst_1)) (SimpleGraph.Adj.{u1} (OrderDual.{u1} α) (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))))) (SimpleGraph.Iso.symm.{u1, u1} (OrderDual.{u1} α) α (SimpleGraph.hasse.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1)) (SimpleGraph.hasse.{u1} α _inst_1) (SimpleGraph.hasseDualIso.{u1} α _inst_1)) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => OrderDual.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align simple_graph.hasse_dual_iso_symm_apply SimpleGraph.hasseDualIso_symm_applyₓ'. -/
@[simp]
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl
#align simple_graph.hasse_dual_iso_symm_apply SimpleGraph.hasseDualIso_symm_apply

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

/- warning: simple_graph.hasse_prod -> SimpleGraph.hasse_prod is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β], Eq.{succ (max u1 u2)} (SimpleGraph.{max u1 u2} (Prod.{u1, u2} α β)) (SimpleGraph.hasse.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2))) (SimpleGraph.boxProd.{u1, u2} α β (SimpleGraph.hasse.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (SimpleGraph.hasse.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β], Eq.{max (succ u2) (succ u1)} (SimpleGraph.{max u1 u2} (Prod.{u2, u1} α β)) (SimpleGraph.hasse.{max u1 u2} (Prod.{u2, u1} α β) (Prod.instPreorderProd.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2))) (SimpleGraph.boxProd.{u2, u1} α β (SimpleGraph.hasse.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) (SimpleGraph.hasse.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align simple_graph.hasse_prod SimpleGraph.hasse_prodₓ'. -/
@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β :=
  by
  ext (x y)
  simp_rw [box_prod_adj, hasse_adj, Prod.covby_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]
#align simple_graph.hasse_prod SimpleGraph.hasse_prod

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

