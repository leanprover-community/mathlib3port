/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.order.proj_Icc
! leanprover-community/mathlib commit 50832daea47b195a48b5b33b1c8b2162c48c3afc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.ProjIcc
import Mathbin.Topology.Order.Basic

/-!
# Projection onto a closed interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/


open Set Filter

open Filter Topology

variable {α β γ : Type _} [LinearOrder α] [TopologicalSpace γ] {a b c : α} {h : a ≤ b}

/- warning: filter.tendsto.Icc_extend -> Filter.Tendsto.IccExtend' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.tendsto.Icc_extend Filter.Tendsto.IccExtend'ₓ'. -/
theorem Filter.Tendsto.IccExtend' (f : γ → Icc a b → β) {z : γ} {l : Filter α} {l' : Filter β}
    (hf : Tendsto (↿f) (𝓝 z ×ᶠ l.map (projIcc a b h)) l') :
    Tendsto (↿(IccExtend h ∘ f)) (𝓝 z ×ᶠ l) l' :=
  show Tendsto (↿f ∘ Prod.map id (projIcc a b h)) (𝓝 z ×ᶠ l) l' from
    hf.comp <| tendsto_id.Prod_map tendsto_map
#align filter.tendsto.Icc_extend Filter.Tendsto.IccExtend'

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

/- warning: continuous_proj_Icc -> continuous_projIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))], Continuous.{u1, u1} α (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3 (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3) (Set.projIcc.{u1} α _inst_1 a b h)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))], Continuous.{u1, u1} α (Set.Elem.{u1} α (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b)) _inst_3 (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b)) _inst_3) (Set.projIcc.{u1} α _inst_1 a b h)
Case conversion may be inaccurate. Consider using '#align continuous_proj_Icc continuous_projIccₓ'. -/
@[continuity]
theorem continuous_projIcc : Continuous (projIcc a b h) :=
  (continuous_const.max <| continuous_const.min continuous_id).subtype_mk _
#align continuous_proj_Icc continuous_projIcc

/- warning: quotient_map_proj_Icc -> quotientMap_projIcc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))], QuotientMap.{u1, u1} α (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3 (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3) (Set.projIcc.{u1} α _inst_1 a b h)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))], QuotientMap.{u1, u1} α (Set.Elem.{u1} α (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b)) _inst_3 (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) a b)) _inst_3) (Set.projIcc.{u1} α _inst_1 a b h)
Case conversion may be inaccurate. Consider using '#align quotient_map_proj_Icc quotientMap_projIccₓ'. -/
theorem quotientMap_projIcc : QuotientMap (projIcc a b h) :=
  quotientMap_iff.2
    ⟨projIcc_surjective h, fun s =>
      ⟨fun hs => hs.Preimage continuous_projIcc, fun hs =>
        ⟨_, hs, by
          ext
          simp⟩⟩⟩
#align quotient_map_proj_Icc quotientMap_projIcc

/- warning: continuous_Icc_extend_iff -> continuous_IccExtend_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] [_inst_5 : TopologicalSpace.{u2} β] {f : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) -> β}, Iff (Continuous.{u1, u2} α β _inst_3 _inst_5 (Set.IccExtend.{u1, u2} α β _inst_1 a b h f)) (Continuous.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3) _inst_5 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {a : α} {b : α} {h : LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a b} [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : OrderTopology.{u2} α _inst_3 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))] [_inst_5 : TopologicalSpace.{u1} β] {f : (Set.Elem.{u2} α (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) -> β}, Iff (Continuous.{u2, u1} α β _inst_3 _inst_5 (Set.IccExtend.{u2, u1} α β _inst_1 a b h f)) (Continuous.{u2, u1} (Set.Elem.{u2} α (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) _inst_3) _inst_5 f)
Case conversion may be inaccurate. Consider using '#align continuous_Icc_extend_iff continuous_IccExtend_iffₓ'. -/
@[simp]
theorem continuous_IccExtend_iff {f : Icc a b → β} : Continuous (IccExtend h f) ↔ Continuous f :=
  quotientMap_projIcc.continuous_iff.symm
#align continuous_Icc_extend_iff continuous_IccExtend_iff

/- warning: continuous.Icc_extend -> Continuous.IccExtend is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous.Icc_extend Continuous.IccExtendₓ'. -/
/-- See Note [continuity lemma statement]. -/
theorem Continuous.IccExtend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  hf.comp <| continuous_id.prod_mk <| continuous_projIcc.comp hg
#align continuous.Icc_extend Continuous.IccExtend

/- warning: continuous.Icc_extend' -> Continuous.Icc_extend' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {a : α} {b : α} {h : LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderTopology.{u1} α _inst_3 (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))] [_inst_5 : TopologicalSpace.{u2} β] {f : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) -> β}, (Continuous.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) β (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Set.Icc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) a b)) _inst_3) _inst_5 f) -> (Continuous.{u1, u2} α β _inst_3 _inst_5 (Set.IccExtend.{u1, u2} α β _inst_1 a b h f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] {a : α} {b : α} {h : LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) a b} [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : OrderTopology.{u2} α _inst_3 (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))] [_inst_5 : TopologicalSpace.{u1} β] {f : (Set.Elem.{u2} α (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) -> β}, (Continuous.{u2, u1} (Set.Elem.{u2} α (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) β (instTopologicalSpaceSubtype.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Set.Icc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))) a b)) _inst_3) _inst_5 f) -> (Continuous.{u2, u1} α β _inst_3 _inst_5 (Set.IccExtend.{u2, u1} α β _inst_1 a b h f))
Case conversion may be inaccurate. Consider using '#align continuous.Icc_extend' Continuous.Icc_extend'ₓ'. -/
/-- A useful special case of `continuous.Icc_extend`. -/
@[continuity]
theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) : Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc
#align continuous.Icc_extend' Continuous.Icc_extend'

/- warning: continuous_at.Icc_extend -> ContinuousAt.IccExtend is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_at.Icc_extend ContinuousAt.IccExtendₓ'. -/
theorem ContinuousAt.IccExtend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
    (hf : ContinuousAt (↿f) (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
    ContinuousAt.comp hf <| continuousAt_id.Prod <| continuous_projIcc.ContinuousAt.comp hg
#align continuous_at.Icc_extend ContinuousAt.IccExtend

