/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module topology.instances.sign
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sign
import Mathbin.Topology.Order.Basic

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

/- warning: continuous_at_sign_of_pos -> continuousAt_sign_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)))] [_inst_5 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_3)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) a) -> (ContinuousAt.{u1, 0} α SignType _inst_2 SignType.topologicalSpace (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α _inst_3) (fun (a : α) (b : α) => _inst_4 a b))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Topology.Instances.Sign._hyg.105 : α) (x._@.Mathlib.Topology.Instances.Sign._hyg.107 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x._@.Mathlib.Topology.Instances.Sign._hyg.105 x._@.Mathlib.Topology.Instances.Sign._hyg.107)] [_inst_5 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_3)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1)) a) -> (ContinuousAt.{u1, 0} α SignType _inst_2 instTopologicalSpaceSignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α _inst_3) (fun (a : α) (b : α) => _inst_4 a b))) a)
Case conversion may be inaccurate. Consider using '#align continuous_at_sign_of_pos continuousAt_sign_of_posₓ'. -/
theorem continuousAt_sign_of_pos {a : α} (h : 0 < a) : ContinuousAt SignType.sign a :=
  by
  refine' (continuousAt_const : ContinuousAt (fun x => (1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | 0 < x }, fun x hx => (sign_pos hx).symm, isOpen_lt' 0, h⟩
#align continuous_at_sign_of_pos continuousAt_sign_of_pos

/- warning: continuous_at_sign_of_neg -> continuousAt_sign_of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : DecidableRel.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)))] [_inst_5 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_3)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))) -> (ContinuousAt.{u1, 0} α SignType _inst_2 SignType.topologicalSpace (coeFn.{succ u1, succ u1} (OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => α -> SignType) (OrderHom.hasCoeToFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α _inst_3) (fun (a : α) (b : α) => _inst_4 a b))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Topology.Instances.Sign._hyg.234 : α) (x._@.Mathlib.Topology.Instances.Sign._hyg.236 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) x._@.Mathlib.Topology.Instances.Sign._hyg.234 x._@.Mathlib.Topology.Instances.Sign._hyg.236)] [_inst_5 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_3)] {a : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_1))) -> (ContinuousAt.{u1, 0} α SignType _inst_2 instTopologicalSpaceSignType (OrderHom.toFun.{u1, 0} α SignType (PartialOrder.toPreorder.{u1} α _inst_3) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α _inst_3) (fun (a : α) (b : α) => _inst_4 a b))) a)
Case conversion may be inaccurate. Consider using '#align continuous_at_sign_of_neg continuousAt_sign_of_negₓ'. -/
theorem continuousAt_sign_of_neg {a : α} (h : a < 0) : ContinuousAt SignType.sign a :=
  by
  refine' (continuousAt_const : ContinuousAt (fun x => (-1 : SignType)) a).congr _
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  exact ⟨{ x | x < 0 }, fun x hx => (sign_neg hx).symm, isOpen_gt' 0, h⟩
#align continuous_at_sign_of_neg continuousAt_sign_of_neg

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

