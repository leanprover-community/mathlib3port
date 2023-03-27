/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison

! This file was ported from Lean 3 source module topology.algebra.field
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.Algebra.GroupWithZero
import Mathbin.Topology.LocalExtr
import Mathbin.FieldTheory.Subfield

/-!
# Topological fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


variable {K : Type _} [DivisionRing K] [TopologicalSpace K]

/- warning: filter.tendsto_cocompact_mul_left₀ -> Filter.tendsto_cocompact_mul_left₀ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : TopologicalSpace.{u1} K] [_inst_3 : ContinuousMul.{u1} K _inst_2 (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))] {a : K}, (Ne.{succ u1} K a (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))) -> (Filter.Tendsto.{u1, u1} K K (fun (x : K) => HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) a x) (Filter.cocompact.{u1} K _inst_2) (Filter.cocompact.{u1} K _inst_2))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : TopologicalSpace.{u1} K] [_inst_3 : ContinuousMul.{u1} K _inst_2 (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))] {a : K}, (Ne.{succ u1} K a (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))))) -> (Filter.Tendsto.{u1, u1} K K (fun (x : K) => HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) a x) (Filter.cocompact.{u1} K _inst_2) (Filter.cocompact.{u1} K _inst_2))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_cocompact_mul_left₀ Filter.tendsto_cocompact_mul_left₀ₓ'. -/
/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel ha)
#align filter.tendsto_cocompact_mul_left₀ Filter.tendsto_cocompact_mul_left₀

/- warning: filter.tendsto_cocompact_mul_right₀ -> Filter.tendsto_cocompact_mul_right₀ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : TopologicalSpace.{u1} K] [_inst_3 : ContinuousMul.{u1} K _inst_2 (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))] {a : K}, (Ne.{succ u1} K a (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))) -> (Filter.Tendsto.{u1, u1} K K (fun (x : K) => HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) x a) (Filter.cocompact.{u1} K _inst_2) (Filter.cocompact.{u1} K _inst_2))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : TopologicalSpace.{u1} K] [_inst_3 : ContinuousMul.{u1} K _inst_2 (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))] {a : K}, (Ne.{succ u1} K a (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))))) -> (Filter.Tendsto.{u1, u1} K K (fun (x : K) => HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) x a) (Filter.cocompact.{u1} K _inst_2) (Filter.cocompact.{u1} K _inst_2))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_cocompact_mul_right₀ Filter.tendsto_cocompact_mul_right₀ₓ'. -/
/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)
#align filter.tendsto_cocompact_mul_right₀ Filter.tendsto_cocompact_mul_right₀

variable (K)

#print TopologicalDivisionRing /-
/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class TopologicalDivisionRing extends TopologicalRing K, HasContinuousInv₀ K : Prop
#align topological_division_ring TopologicalDivisionRing
-/

section Subfield

variable {α : Type _} [Field α] [TopologicalSpace α] [TopologicalDivisionRing α]

#print Subfield.topologicalClosure /-
/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  {
    K.toSubring.topologicalClosure with
    carrier := closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv]
        exact mem_closure_image (continuous_at_inv₀ h) hx }
#align subfield.topological_closure Subfield.topologicalClosure
-/

/- warning: subfield.le_topological_closure -> Subfield.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3), LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (SetLike.partialOrder.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.setLike.{u1} α _inst_3)))) s (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3), LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subfield.{u1} α _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subfield.{u1} α _inst_3) (Subfield.instCompleteLatticeSubfield.{u1} α _inst_3))))) s (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s)
Case conversion may be inaccurate. Consider using '#align subfield.le_topological_closure Subfield.le_topologicalClosureₓ'. -/
theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subfield.le_topological_closure Subfield.le_topologicalClosure

/- warning: subfield.is_closed_topological_closure -> Subfield.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3), IsClosed.{u1} α _inst_4 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subfield.{u1} α _inst_3) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subfield.{u1} α _inst_3) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subfield.{u1} α _inst_3) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.setLike.{u1} α _inst_3)))) (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3), IsClosed.{u1} α _inst_4 (SetLike.coe.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.instSetLikeSubfield.{u1} α _inst_3) (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s))
Case conversion may be inaccurate. Consider using '#align subfield.is_closed_topological_closure Subfield.isClosed_topologicalClosureₓ'. -/
theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure
#align subfield.is_closed_topological_closure Subfield.isClosed_topologicalClosure

/- warning: subfield.topological_closure_minimal -> Subfield.topologicalClosure_minimal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3) {t : Subfield.{u1} α _inst_3}, (LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (SetLike.partialOrder.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.setLike.{u1} α _inst_3)))) s t) -> (IsClosed.{u1} α _inst_4 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subfield.{u1} α _inst_3) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subfield.{u1} α _inst_3) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subfield.{u1} α _inst_3) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.setLike.{u1} α _inst_3)))) t)) -> (LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (SetLike.partialOrder.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.setLike.{u1} α _inst_3)))) (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : Field.{u1} α] [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : TopologicalDivisionRing.{u1} α (Field.toDivisionRing.{u1} α _inst_3) _inst_4] (s : Subfield.{u1} α _inst_3) {t : Subfield.{u1} α _inst_3}, (LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subfield.{u1} α _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subfield.{u1} α _inst_3) (Subfield.instCompleteLatticeSubfield.{u1} α _inst_3))))) s t) -> (IsClosed.{u1} α _inst_4 (SetLike.coe.{u1, u1} (Subfield.{u1} α _inst_3) α (Subfield.instSetLikeSubfield.{u1} α _inst_3) t)) -> (LE.le.{u1} (Subfield.{u1} α _inst_3) (Preorder.toLE.{u1} (Subfield.{u1} α _inst_3) (PartialOrder.toPreorder.{u1} (Subfield.{u1} α _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subfield.{u1} α _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subfield.{u1} α _inst_3) (Subfield.instCompleteLatticeSubfield.{u1} α _inst_3))))) (Subfield.topologicalClosure.{u1} α _inst_3 _inst_4 _inst_5 s) t)
Case conversion may be inaccurate. Consider using '#align subfield.topological_closure_minimal Subfield.topologicalClosure_minimalₓ'. -/
theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subfield.topological_closure_minimal Subfield.topologicalClosure_minimal

end Subfield

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type _} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]

/- warning: affine_homeomorph -> affineHomeomorph is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_3 : Field.{u1} 𝕜] [_inst_4 : TopologicalSpace.{u1} 𝕜] [_inst_5 : TopologicalRing.{u1} 𝕜 _inst_4 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 _inst_3))))] (a : 𝕜), 𝕜 -> (Ne.{succ u1} 𝕜 a (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 _inst_3))))))))))) -> (Homeomorph.{u1, u1} 𝕜 𝕜 _inst_4 _inst_4)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_3 : Field.{u1} 𝕜] [_inst_4 : TopologicalSpace.{u1} 𝕜] [_inst_5 : TopologicalRing.{u1} 𝕜 _inst_4 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 _inst_3))))] (a : 𝕜), 𝕜 -> (Ne.{succ u1} 𝕜 a (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 _inst_3))))))) -> (Homeomorph.{u1, u1} 𝕜 𝕜 _inst_4 _inst_4)
Case conversion may be inaccurate. Consider using '#align affine_homeomorph affineHomeomorphₓ'. -/
/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜
    where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel]
    exact mul_div_cancel_left x h
  right_inv y := by simp [mul_div_cancel' _ h]
#align affine_homeomorph affineHomeomorph

end affineHomeomorph

section LocalExtr

variable {α β : Type _} [TopologicalSpace α] [LinearOrderedSemifield β] {a : α}

open Topology

/- warning: is_local_min.inv -> IsLocalMin.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : LinearOrderedSemifield.{u2} β] {f : α -> β} {a : α}, (IsLocalMin.{u1, u2} α β _inst_3 (PartialOrder.toPreorder.{u2} β (OrderedCancelAddCommMonoid.toPartialOrder.{u2} β (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} β _inst_4)))))) f a) -> (Filter.Eventually.{u1} α (fun (z : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCancelAddCommMonoid.toPartialOrder.{u2} β (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} β _inst_4))))))) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β (DivisionSemiring.toSemiring.{u2} β (Semifield.toDivisionSemiring.{u2} β (LinearOrderedSemifield.toSemifield.{u2} β _inst_4)))))))))) (f z)) (nhds.{u1} α _inst_3 a)) -> (IsLocalMax.{u1, u2} α β _inst_3 (PartialOrder.toPreorder.{u2} β (OrderedCancelAddCommMonoid.toPartialOrder.{u2} β (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} β _inst_4)))))) (Inv.inv.{max u1 u2} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasInv.{u2} β (GroupWithZero.toDivInvMonoid.{u2} β (DivisionSemiring.toGroupWithZero.{u2} β (Semifield.toDivisionSemiring.{u2} β (LinearOrderedSemifield.toSemifield.{u2} β _inst_4)))))) f) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : LinearOrderedSemifield.{u1} β] {f : α -> β} {a : α}, (IsLocalMin.{u2, u1} α β _inst_3 (PartialOrder.toPreorder.{u1} β (StrictOrderedSemiring.toPartialOrder.{u1} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} β _inst_4))))) f a) -> (Filter.Eventually.{u2} α (fun (z : α) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (StrictOrderedSemiring.toPartialOrder.{u1} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} β _inst_4)))))) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β (Semifield.toCommGroupWithZero.{u1} β (LinearOrderedSemifield.toSemifield.{u1} β _inst_4)))))) (f z)) (nhds.{u2} α _inst_3 a)) -> (IsLocalMax.{u2, u1} α β _inst_3 (PartialOrder.toPreorder.{u1} β (StrictOrderedSemiring.toPartialOrder.{u1} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} β (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} β (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} β _inst_4))))) (Inv.inv.{max u1 u2} (α -> β) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => LinearOrderedSemifield.toInv.{u1} β _inst_4)) f) a)
Case conversion may be inaccurate. Consider using '#align is_local_min.inv IsLocalMin.invₓ'. -/
theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2]with z h3 h4 using(inv_le_inv h4 h2.self_of_nhds).mpr h3
#align is_local_min.inv IsLocalMin.inv

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/


open Set

variable {α 𝕜 : Type _} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/- warning: is_preconnected.eq_one_or_eq_neg_one_of_sq_eq -> IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Ring.{u2} 𝕜] [_inst_7 : NoZeroDivisors.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 _inst_6)) (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 _inst_6)))))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 _inst_6)))) f (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{max u1 u2} (α -> 𝕜) 1 (OfNat.mk.{max u1 u2} (α -> 𝕜) 1 (One.one.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => AddMonoidWithOne.toOne.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 _inst_6)))))))) S) -> (Or (Set.EqOn.{u1, u2} α 𝕜 f (OfNat.ofNat.{max u1 u2} (α -> 𝕜) 1 (OfNat.mk.{max u1 u2} (α -> 𝕜) 1 (One.one.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => AddMonoidWithOne.toOne.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 _inst_6)))))))) S) (Set.EqOn.{u1, u2} α 𝕜 f (Neg.neg.{max u1 u2} (α -> 𝕜) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 _inst_6)))))) (OfNat.ofNat.{max u1 u2} (α -> 𝕜) 1 (OfNat.mk.{max u1 u2} (α -> 𝕜) 1 (One.one.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => AddMonoidWithOne.toOne.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 _inst_6))))))))) S))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Ring.{u2} 𝕜] [_inst_7 : NoZeroDivisors.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 _inst_6))) (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 _inst_6)))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u2 u1} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Monoid.Pow.{max u1 u2} (α -> 𝕜) (Pi.monoid.{u1, u2} α (fun (a._@.Mathlib.Topology.Algebra.Field._hyg.738 : α) => 𝕜) (fun (i : α) => MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 _inst_6)))))) f (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{max u2 u1} (α -> 𝕜) 1 (One.toOfNat1.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : α) => 𝕜) (fun (i : α) => NonAssocRing.toOne.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 _inst_6))))) S) -> (Or (Set.EqOn.{u1, u2} α 𝕜 f (OfNat.ofNat.{max u1 u2} (α -> 𝕜) 1 (One.toOfNat1.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : α) => 𝕜) (fun (i : α) => NonAssocRing.toOne.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 _inst_6))))) S) (Set.EqOn.{u1, u2} α 𝕜 f (Neg.neg.{max u1 u2} (α -> 𝕜) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Ring.toNeg.{u2} 𝕜 _inst_6)) (OfNat.ofNat.{max u1 u2} (α -> 𝕜) 1 (One.toOfNat1.{max u1 u2} (α -> 𝕜) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Data.Set.Function._hyg.1349 : α) => 𝕜) (fun (i : α) => NonAssocRing.toOne.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 _inst_6)))))) S))
Case conversion may be inaccurate. Consider using '#align is_preconnected.eq_one_or_eq_neg_one_of_sq_eq IsPreconnected.eq_one_or_eq_neg_one_of_sq_eqₓ'. -/
/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S :=
  by
  simp_rw [eq_on, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] at hsq
  -- First deal with crazy case where `S` is empty.
  by_cases hSe : ∀ x : α, x ∉ S
  · left
    intro x hx
    exfalso
    exact hSe x hx
  push_neg  at hSe
  choose y hy using hSe
  suffices ∀ x : α, x ∈ S → f x = f y by
    rcases hsq hy with ⟨⟩
    · left
      intro z hz
      rw [Pi.one_apply z, ← h]
      exact this z hz
    · right
      intro z hz
      rw [Pi.neg_apply, Pi.one_apply, ← h]
      exact this z hz
  refine' fun x hx => hS.constant_of_maps_to hf (fun z hz => _) hx hy
  show f z ∈ ({-1, 1} : Set 𝕜)
  · exact mem_insert_iff.mpr (hsq hz).symm
  exact discrete_of_t1_of_finite
#align is_preconnected.eq_one_or_eq_neg_one_of_sq_eq IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq

/- warning: is_preconnected.eq_or_eq_neg_of_sq_eq -> IsPreconnected.eq_or_eq_neg_of_sq_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {g : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Field.{u2} 𝕜] [_inst_7 : HasContinuousInv₀.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))))))) (DivInvMonoid.toHasInv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))) _inst_4] [_inst_8 : ContinuousMul.{u2} 𝕜 _inst_4 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 g S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))) f (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))) g (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) S) -> (forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) -> (Ne.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))))))))) -> (Or (Set.EqOn.{u1, u2} α 𝕜 f g S) (Set.EqOn.{u1, u2} α 𝕜 f (Neg.neg.{max u1 u2} (α -> 𝕜) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))))) g) S))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {g : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Field.{u2} 𝕜] [_inst_7 : HasContinuousInv₀.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))) (Field.toInv.{u2} 𝕜 _inst_6) _inst_4] [_inst_8 : ContinuousMul.{u2} 𝕜 _inst_4 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 g S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u2 u1} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Monoid.Pow.{max u1 u2} (α -> 𝕜) (Pi.monoid.{u1, u2} α (fun (a._@.Mathlib.Topology.Algebra.Field._hyg.872 : α) => 𝕜) (fun (i : α) => MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) f (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{max u1 u2, 0, max u2 u1} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Monoid.Pow.{max u1 u2} (α -> 𝕜) (Pi.monoid.{u1, u2} α (fun (a._@.Mathlib.Topology.Algebra.Field._hyg.872 : α) => 𝕜) (fun (i : α) => MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) g (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) S) -> (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) -> (Ne.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) -> (Or (Set.EqOn.{u1, u2} α 𝕜 f g S) (Set.EqOn.{u1, u2} α 𝕜 f (Neg.neg.{max u1 u2} (α -> 𝕜) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => 𝕜) (fun (i : α) => Ring.toNeg.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))) g) S))
Case conversion may be inaccurate. Consider using '#align is_preconnected.eq_or_eq_neg_of_sq_eq IsPreconnected.eq_or_eq_neg_of_sq_eqₓ'. -/
/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) :
    EqOn f g S ∨ EqOn f (-g) S :=
  by
  rcases hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z hz => hg_ne hz) fun x hx => _ with
    (h | h)
  · refine' Or.inl fun x hx => _
    rw [← div_eq_one_iff_eq (hg_ne hx)]
    exact h hx
  · refine' Or.inr fun x hx => _
    specialize h hx
    rwa [Pi.div_apply, Pi.neg_apply, Pi.one_apply, div_eq_iff (hg_ne hx), neg_one_mul] at h
  · rw [Pi.one_apply, div_pow, Pi.div_apply, hsq hx, div_self]
    exact pow_ne_zero _ (hg_ne hx)
#align is_preconnected.eq_or_eq_neg_of_sq_eq IsPreconnected.eq_or_eq_neg_of_sq_eq

/- warning: is_preconnected.eq_of_sq_eq -> IsPreconnected.eq_of_sq_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {g : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Field.{u2} 𝕜] [_inst_7 : HasContinuousInv₀.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))))))) (DivInvMonoid.toHasInv.{u2} 𝕜 (DivisionRing.toDivInvMonoid.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))) _inst_4] [_inst_8 : ContinuousMul.{u2} 𝕜 _inst_4 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6))))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 g S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))) f (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => 𝕜) (fun (i : α) => Monoid.Pow.{u2} 𝕜 (Ring.toMonoid.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))) g (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) S) -> (forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x S) -> (Ne.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))))))))) -> (forall {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y S) -> (Eq.{succ u2} 𝕜 (f y) (g y)) -> (Set.EqOn.{u1, u2} α 𝕜 f g S))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} {f : α -> 𝕜} {g : α -> 𝕜} {S : Set.{u1} α} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : TopologicalSpace.{u2} 𝕜] [_inst_5 : T1Space.{u2} 𝕜 _inst_4] [_inst_6 : Field.{u2} 𝕜] [_inst_7 : HasContinuousInv₀.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))) (Field.toInv.{u2} 𝕜 _inst_6) _inst_4] [_inst_8 : ContinuousMul.{u2} 𝕜 _inst_4 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 _inst_6)))))], (IsPreconnected.{u1} α _inst_3 S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 f S) -> (ContinuousOn.{u1, u2} α 𝕜 _inst_3 _inst_4 g S) -> (Set.EqOn.{u1, u2} α 𝕜 (HPow.hPow.{max u1 u2, 0, max u2 u1} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Monoid.Pow.{max u1 u2} (α -> 𝕜) (Pi.monoid.{u1, u2} α (fun (a._@.Mathlib.Topology.Algebra.Field._hyg.1060 : α) => 𝕜) (fun (i : α) => MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) f (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{max u1 u2, 0, max u2 u1} (α -> 𝕜) Nat (α -> 𝕜) (instHPow.{max u1 u2, 0} (α -> 𝕜) Nat (Monoid.Pow.{max u1 u2} (α -> 𝕜) (Pi.monoid.{u1, u2} α (fun (a._@.Mathlib.Topology.Algebra.Field._hyg.1060 : α) => 𝕜) (fun (i : α) => MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) g (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) S) -> (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x S) -> (Ne.{succ u2} 𝕜 (g x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 _inst_6)))))))) -> (forall {y : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y S) -> (Eq.{succ u2} 𝕜 (f y) (g y)) -> (Set.EqOn.{u1, u2} α 𝕜 f g S))
Case conversion may be inaccurate. Consider using '#align is_preconnected.eq_of_sq_eq IsPreconnected.eq_of_sq_eqₓ'. -/
/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) {y : α} (hy : y ∈ S)
    (hy' : f y = g y) : EqOn f g S := fun x hx =>
  by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h hy, eq_comm, ← sub_eq_zero, sub_eq_add_neg, Pi.neg_apply, neg_neg, ← mul_two,
      mul_eq_zero] at hy'
    cases hy'
    -- need to handle case of `char 𝕜 = 2` separately
    · exfalso
      exact hg_ne hy hy'
    ·
      rw [h hx, Pi.neg_apply, eq_comm, ← sub_eq_zero, sub_eq_add_neg, neg_neg, ← mul_two, hy',
        MulZeroClass.mul_zero]
#align is_preconnected.eq_of_sq_eq IsPreconnected.eq_of_sq_eq

end Preconnected

