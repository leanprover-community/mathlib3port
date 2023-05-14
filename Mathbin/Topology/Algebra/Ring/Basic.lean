/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.ring.basic
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Prod
import Mathbin.RingTheory.Subring.Basic
import Mathbin.Topology.Algebra.Group.Basic

/-!

# Topological (semi)rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `subring.topological_closure`/`subsemiring.topological_closure`: the topological closure of a
  `subring`/`subsemiring` is itself a `sub(semi)ring`.
- `prod.topological_semiring`/`prod.topological_ring`: The product of two topological
  (semi)rings.
- `pi.topological_semiring`/`pi.topological_ring`: The arbitrary product of topological
  (semi)rings.

-/


open Classical Set Filter TopologicalSpace Function

open Classical Topology Filter

section TopologicalSemiring

variable (α : Type _)

#print TopologicalSemiring /-
/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `topological_semiring` class should *only* be instantiated in the presence of a
`non_unital_non_assoc_semiring` instance; if there is an instance of `non_unital_non_assoc_ring`,
then `topological_ring` should be used. Note: in the presence of `non_assoc_ring`, these classes are
mathematically equivalent (see `topological_semiring.has_continuous_neg_of_mul` or
`topological_semiring.to_topological_ring`).  -/
class TopologicalSemiring [TopologicalSpace α] [NonUnitalNonAssocSemiring α] extends
  ContinuousAdd α, ContinuousMul α : Prop
#align topological_semiring TopologicalSemiring
-/

#print TopologicalRing /-
/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`topological_semiring.has_continuous_neg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class TopologicalRing [TopologicalSpace α] [NonUnitalNonAssocRing α] extends TopologicalSemiring α,
  ContinuousNeg α : Prop
#align topological_ring TopologicalRing
-/

variable {α}

/- warning: topological_semiring.has_continuous_neg_of_mul -> TopologicalSemiring.continuousNeg_of_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonAssocRing.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_2))))], ContinuousNeg.{u1} α _inst_1 (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (NonAssocRing.toAddCommGroupWithOne.{u1} α _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonAssocRing.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α _inst_2))], ContinuousNeg.{u1} α _inst_1 (AddGroupWithOne.toNeg.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (NonAssocRing.toAddCommGroupWithOne.{u1} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align topological_semiring.has_continuous_neg_of_mul TopologicalSemiring.continuousNeg_of_mulₓ'. -/
/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
theorem TopologicalSemiring.continuousNeg_of_mul [TopologicalSpace α] [NonAssocRing α]
    [ContinuousMul α] : ContinuousNeg α :=
  {
    continuous_neg := by
      simpa using (continuous_const.mul continuous_id : Continuous fun x : α => -1 * x) }
#align topological_semiring.has_continuous_neg_of_mul TopologicalSemiring.continuousNeg_of_mul

#print TopologicalSemiring.toTopologicalRing /-
/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
theorem TopologicalSemiring.toTopologicalRing [TopologicalSpace α] [NonAssocRing α]
    (h : TopologicalSemiring α) : TopologicalRing α :=
  { h,
    (haveI := h.to_has_continuous_mul
      TopologicalSemiring.continuousNeg_of_mul :
      ContinuousNeg α) with }
#align topological_semiring.to_topological_ring TopologicalSemiring.toTopologicalRing
-/

#print TopologicalRing.to_topologicalAddGroup /-
-- See note [lower instance priority]
instance (priority := 100) TopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing α]
    [TopologicalSpace α] [TopologicalRing α] : TopologicalAddGroup α :=
  { TopologicalRing.to_topologicalSemiring.to_continuousAdd, TopologicalRing.to_continuousNeg with }
#align topological_ring.to_topological_add_group TopologicalRing.to_topologicalAddGroup
-/

#print DiscreteTopology.topologicalSemiring /-
instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace α]
    [NonUnitalNonAssocSemiring α] [DiscreteTopology α] : TopologicalSemiring α :=
  ⟨⟩
#align discrete_topology.topological_semiring DiscreteTopology.topologicalSemiring
-/

#print DiscreteTopology.topologicalRing /-
instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace α]
    [NonUnitalNonAssocRing α] [DiscreteTopology α] : TopologicalRing α :=
  ⟨⟩
#align discrete_topology.topological_ring DiscreteTopology.topologicalRing
-/

section

variable [TopologicalSpace α] [Semiring α] [TopologicalSemiring α]

namespace Subsemiring

instance (S : Subsemiring α) : TopologicalSemiring S :=
  { S.toSubmonoid.ContinuousMul, S.toAddSubmonoid.ContinuousAdd with }

end Subsemiring

#print Subsemiring.topologicalClosure /-
/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := closure (s : Set α) }
#align subsemiring.topological_closure Subsemiring.topologicalClosure
-/

/- warning: subsemiring.topological_closure_coe -> Subsemiring.topologicalClosure_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)) (closure.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)) (closure.{u1} α _inst_1 (SetLike.coe.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align subsemiring.topological_closure_coe Subsemiring.topologicalClosure_coeₓ'. -/
@[simp]
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring α) :
    (s.topologicalClosure : Set α) = closure (s : Set α) :=
  rfl
#align subsemiring.topological_closure_coe Subsemiring.topologicalClosure_coe

/- warning: subsemiring.le_topological_closure -> Subsemiring.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.partialOrder.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) s (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.instCompleteLatticeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))))) s (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)
Case conversion may be inaccurate. Consider using '#align subsemiring.le_topological_closure Subsemiring.le_topologicalClosureₓ'. -/
theorem Subsemiring.le_topologicalClosure (s : Subsemiring α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subsemiring.le_topological_closure Subsemiring.le_topologicalClosure

/- warning: subsemiring.is_closed_topological_closure -> Subsemiring.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), IsClosed.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), IsClosed.{u1} α _inst_1 (SetLike.coe.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))
Case conversion may be inaccurate. Consider using '#align subsemiring.is_closed_topological_closure Subsemiring.isClosed_topologicalClosureₓ'. -/
theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := by convert isClosed_closure
#align subsemiring.is_closed_topological_closure Subsemiring.isClosed_topologicalClosure

/- warning: subsemiring.topological_closure_minimal -> Subsemiring.topologicalClosure_minimal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) {t : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)}, (LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.partialOrder.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) s t) -> (IsClosed.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) t)) -> (LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.partialOrder.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))))) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) {t : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)}, (LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.instCompleteLatticeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))))) s t) -> (IsClosed.{u1} α _inst_1 (SetLike.coe.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) t)) -> (LE.le.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Preorder.toLE.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.instCompleteLatticeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))))) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s) t)
Case conversion may be inaccurate. Consider using '#align subsemiring.topological_closure_minimal Subsemiring.topologicalClosure_minimalₓ'. -/
theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subsemiring.topological_closure_minimal Subsemiring.topologicalClosure_minimal

/- warning: subsemiring.comm_semiring_topological_closure -> Subsemiring.commSemiringTopologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] [_inst_4 : T2Space.{u1} α _inst_1] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), (forall (x : coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (y : coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (MulMemClass.mul.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.commSemiringTopologicalClosure._proof_1.{u1} α _inst_2) s)) x y) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) s) (MulMemClass.mul.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)))) (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (Subsemiring.commSemiringTopologicalClosure._proof_1.{u1} α _inst_2) s)) y x)) -> (CommSemiring.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.setLike.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Semiring.{u1} α] [_inst_3 : TopologicalSemiring.{u1} α _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))] [_inst_4 : T2Space.{u1} α _inst_1] (s : Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)), (forall (x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (y : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)), Eq.{succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (instHMul.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Submonoid.mul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) (Subsemiring.toSubmonoid.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2) s))) x y) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (instHMul.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x s)) (Submonoid.mul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) (Subsemiring.toSubmonoid.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2) s))) y x)) -> (CommSemiring.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) (SetLike.instMembership.{u1, u1} (Subsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2)) α (Subsemiring.instSetLikeSubsemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_2))) x (Subsemiring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))))
Case conversion may be inaccurate. Consider using '#align subsemiring.comm_semiring_topological_closure Subsemiring.commSemiringTopologicalClosureₓ'. -/
/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure. -/
def Subsemiring.commSemiringTopologicalClosure [T2Space α] (s : Subsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subsemiring.comm_semiring_topological_closure Subsemiring.commSemiringTopologicalClosure

end

section

variable {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [TopologicalSemiring α]
    [TopologicalSemiring β] : TopologicalSemiring (α × β) where

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [NonUnitalNonAssocRing α] [NonUnitalNonAssocRing β] [TopologicalRing α]
    [TopologicalRing β] : TopologicalRing (α × β) where

end

instance {β : Type _} {C : β → Type _} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    TopologicalSemiring (∀ b, C b) where

instance {β : Type _} {C : β → Type _} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocRing (C b)] [∀ b, TopologicalRing (C b)] : TopologicalRing (∀ b, C b)
    where

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousAdd α] : ContinuousAdd αᵐᵒᵖ
    where continuous_add :=
    continuous_induced_rng.2 <|
      (@continuous_add α _ _ _).comp (continuous_unop.Prod_map continuous_unop)

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵐᵒᵖ where

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [ContinuousNeg α] : ContinuousNeg αᵐᵒᵖ
    where continuous_neg :=
    continuous_induced_rng.2 <| (@continuous_neg α _ _ _).comp continuous_unop

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] : TopologicalRing αᵐᵒᵖ
    where

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousMul α] : ContinuousMul αᵃᵒᵖ
    where continuous_mul := by
    convert continuous_op.comp <|
        (@continuous_mul α _ _ _).comp <| continuous_unop.prod_map continuous_unop

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵃᵒᵖ where

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] : TopologicalRing αᵃᵒᵖ
    where

end AddOpposite

section

variable {R : Type _} [NonUnitalNonAssocRing R] [TopologicalSpace R]

/- warning: topological_ring.of_add_group_of_nhds_zero -> TopologicalRing.of_addGroup_of_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalAddGroup.{u1} R _inst_2 (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x x₀) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (TopologicalRing.{u1} R _inst_2 _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalAddGroup.{u1} R _inst_2 (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (fun (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.806 : R) (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.808 : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.806 x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.808)) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x x₀) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (TopologicalRing.{u1} R _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_ring.of_add_group_of_nhds_zero TopologicalRing.of_addGroup_of_nhds_zeroₓ'. -/
theorem TopologicalRing.of_addGroup_of_nhds_zero [TopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : TopologicalRing R :=
  by
  refine' { ‹TopologicalAddGroup R› with .. }
  have hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0) := by simp
  have hadd : tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) (𝓝 0) :=
    by
    rw [← nhds_prod_eq]
    convert continuous_add.tendsto ((0 : R), (0 : R))
    rw [zero_add]
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, y₀⟩
  rw [ContinuousAt, nhds_prod_eq, hleft x₀, hleft y₀, hleft (x₀ * y₀), Filter.prod_map_map_eq,
    tendsto_map'_iff]
  suffices
    tendsto
      ((fun x : R => x + x₀ * y₀) ∘
        (fun p : R × R => p.1 + p.2) ∘ fun p : R × R => (p.1 * y₀ + x₀ * p.2, p.1 * p.2))
      (𝓝 0 ×ᶠ 𝓝 0) ((map fun x : R => x + x₀ * y₀) <| 𝓝 0)
    by
    convert this using 1
    · ext
      simp only [comp_app, mul_add, add_mul]
      abel
    · simp only [add_comm]
  refine' tendsto_map.comp (hadd.comp (tendsto.prod_mk _ hmul))
  exact hadd.comp (((hmul_right y₀).comp tendsto_fst).prod_mk ((hmul_left x₀).comp tendsto_snd))
#align topological_ring.of_add_group_of_nhds_zero TopologicalRing.of_addGroup_of_nhds_zero

/- warning: topological_ring.of_nhds_zero -> TopologicalRing.of_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (Filter.Tendsto.{u1, u1} R R (fun (x : R) => Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1)))) x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x x₀) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (forall (x₀ : R), Eq.{succ u1} (Filter.{u1} R) (nhds.{u1} R _inst_2 x₀) (Filter.map.{u1, u1} R R (fun (x : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))))) -> (TopologicalRing.{u1} R _inst_2 _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (fun (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.975 : R) (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.977 : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.975 x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.977)) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (Filter.Tendsto.{u1, u1} R R (fun (x : R) => Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1)))))) x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} R R) R (Function.uncurry.{u1, u1, u1} R R R (fun (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.1059 : R) (x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.1061 : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.1059 x._@.Mathlib.Topology.Algebra.Ring.Basic._hyg.1061)) (Filter.prod.{u1, u1} R R (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (forall (x₀ : R), Filter.Tendsto.{u1, u1} R R (fun (x : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) x x₀) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))))))) -> (forall (x₀ : R), Eq.{succ u1} (Filter.{u1} R) (nhds.{u1} R _inst_2 x₀) (Filter.map.{u1, u1} R R (fun (x : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) x₀ x) (nhds.{u1} R _inst_2 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))))))) -> (TopologicalRing.{u1} R _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align topological_ring.of_nhds_zero TopologicalRing.of_nhds_zeroₓ'. -/
theorem TopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ᶠ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : TopologicalRing R :=
  haveI := TopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  TopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right
#align topological_ring.of_nhds_zero TopologicalRing.of_nhds_zero

end

variable {α} [TopologicalSpace α]

section

variable [NonUnitalNonAssocRing α] [TopologicalRing α]

/- warning: mul_left_continuous -> mulLeft_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 _inst_2] (x : α), Continuous.{u1, u1} α α _inst_1 _inst_1 (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (fun (_x : AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) => α -> α) (AddMonoidHom.hasCoeToFun.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddMonoidHom.mulLeft.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 _inst_2] (x : α), Continuous.{u1, u1} α α _inst_1 _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoidHom.addMonoidHomClass.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))))) (AddMonoidHom.mulLeft.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2) x))
Case conversion may be inaccurate. Consider using '#align mul_left_continuous mulLeft_continuousₓ'. -/
/-- In a topological semiring, the left-multiplication `add_monoid_hom` is continuous. -/
theorem mulLeft_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id
#align mul_left_continuous mulLeft_continuous

/- warning: mul_right_continuous -> mulRight_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 _inst_2] (x : α), Continuous.{u1, u1} α α _inst_1 _inst_1 (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (fun (_x : AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) => α -> α) (AddMonoidHom.hasCoeToFun.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddMonoidHom.mulRight.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocRing.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 _inst_2] (x : α), Continuous.{u1, u1} α α _inst_1 _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))) α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoidHom.addMonoidHomClass.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2)))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2))))))) (AddMonoidHom.mulRight.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α _inst_2) x))
Case conversion may be inaccurate. Consider using '#align mul_right_continuous mulRight_continuousₓ'. -/
/-- In a topological semiring, the right-multiplication `add_monoid_hom` is continuous. -/
theorem mulRight_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const
#align mul_right_continuous mulRight_continuous

end

variable [Ring α] [TopologicalRing α]

namespace Subring

instance (S : Subring α) : TopologicalRing S :=
  TopologicalSemiring.toTopologicalRing S.toSubsemiring.TopologicalSemiring

end Subring

#print Subring.topologicalClosure /-
/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := closure (S : Set α) }
#align subring.topological_closure Subring.topologicalClosure
-/

/- warning: subring.le_topological_closure -> Subring.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2), LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (SetLike.partialOrder.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)))) s (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2), LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} α _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} α _inst_2) (Subring.instCompleteLatticeSubring.{u1} α _inst_2))))) s (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)
Case conversion may be inaccurate. Consider using '#align subring.le_topological_closure Subring.le_topologicalClosureₓ'. -/
theorem Subring.le_topologicalClosure (s : Subring α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subring.le_topological_closure Subring.le_topologicalClosure

/- warning: subring.is_closed_topological_closure -> Subring.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2), IsClosed.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} α _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} α _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} α _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)))) (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2), IsClosed.{u1} α _inst_1 (SetLike.coe.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2) (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))
Case conversion may be inaccurate. Consider using '#align subring.is_closed_topological_closure Subring.isClosed_topologicalClosureₓ'. -/
theorem Subring.isClosed_topologicalClosure (s : Subring α) :
    IsClosed (s.topologicalClosure : Set α) := by convert isClosed_closure
#align subring.is_closed_topological_closure Subring.isClosed_topologicalClosure

/- warning: subring.topological_closure_minimal -> Subring.topologicalClosure_minimal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2) {t : Subring.{u1} α _inst_2}, (LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (SetLike.partialOrder.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)))) s t) -> (IsClosed.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subring.{u1} α _inst_2) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Subring.{u1} α _inst_2) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Subring.{u1} α _inst_2) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)))) t)) -> (LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (SetLike.partialOrder.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)))) (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] (s : Subring.{u1} α _inst_2) {t : Subring.{u1} α _inst_2}, (LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} α _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} α _inst_2) (Subring.instCompleteLatticeSubring.{u1} α _inst_2))))) s t) -> (IsClosed.{u1} α _inst_1 (SetLike.coe.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2) t)) -> (LE.le.{u1} (Subring.{u1} α _inst_2) (Preorder.toLE.{u1} (Subring.{u1} α _inst_2) (PartialOrder.toPreorder.{u1} (Subring.{u1} α _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subring.{u1} α _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subring.{u1} α _inst_2) (Subring.instCompleteLatticeSubring.{u1} α _inst_2))))) (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s) t)
Case conversion may be inaccurate. Consider using '#align subring.topological_closure_minimal Subring.topologicalClosure_minimalₓ'. -/
theorem Subring.topologicalClosure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subring.topological_closure_minimal Subring.topologicalClosure_minimal

/- warning: subring.comm_ring_topological_closure -> Subring.commRingTopologicalClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] [_inst_4 : T2Space.{u1} α _inst_1] (s : Subring.{u1} α _inst_2), (forall (x : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (y : coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (MulMemClass.mul.{u1, u1} α (Subring.{u1} α _inst_2) (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (Subring.setLike.{u1} α _inst_2) (Subring.commRingTopologicalClosure._proof_1.{u1} α _inst_2) s)) x y) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) s) (MulMemClass.mul.{u1, u1} α (Subring.{u1} α _inst_2) (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))))) (Subring.setLike.{u1} α _inst_2) (Subring.commRingTopologicalClosure._proof_1.{u1} α _inst_2) s)) y x)) -> (CommRing.{u1} (coeSort.{succ u1, succ (succ u1)} (Subring.{u1} α _inst_2) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.setLike.{u1} α _inst_2)) (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u1} α] [_inst_3 : TopologicalRing.{u1} α _inst_1 (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_2))] [_inst_4 : T2Space.{u1} α _inst_1] (s : Subring.{u1} α _inst_2), (forall (x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (y : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)), Eq.{succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (instHMul.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Submonoid.mul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_2)))) (Subsemiring.toSubmonoid.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_2)) (Subring.toSubsemiring.{u1} α _inst_2 s)))) x y) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (instHMul.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x s)) (Submonoid.mul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_2)))) (Subsemiring.toSubmonoid.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_2)) (Subring.toSubsemiring.{u1} α _inst_2 s)))) y x)) -> (CommRing.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Subring.{u1} α _inst_2) (SetLike.instMembership.{u1, u1} (Subring.{u1} α _inst_2) α (Subring.instSetLikeSubring.{u1} α _inst_2)) x (Subring.topologicalClosure.{u1} α _inst_1 _inst_2 _inst_3 s))))
Case conversion may be inaccurate. Consider using '#align subring.comm_ring_topological_closure Subring.commRingTopologicalClosureₓ'. -/
/-- If a subring of a topological ring is commutative, then so is its topological closure. -/
def Subring.commRingTopologicalClosure [T2Space α] (s : Subring α) (hs : ∀ x y : s, x * y = y * x) :
    CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }
#align subring.comm_ring_topological_closure Subring.commRingTopologicalClosure

end TopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `ring_topology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → ring_topology β`. -/


universe u v

#print RingTopology /-
/-- A ring topology on a ring `α` is a topology for which addition, negation and multiplication
are continuous. -/
@[ext]
structure RingTopology (α : Type u) [Ring α] extends TopologicalSpace α, TopologicalRing α : Type u
#align ring_topology RingTopology
-/

namespace RingTopology

variable {α : Type _} [Ring α]

#print RingTopology.inhabited /-
instance inhabited {α : Type u} [Ring α] : Inhabited (RingTopology α) :=
  ⟨{  toTopologicalSpace := ⊤
      continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩
#align ring_topology.inhabited RingTopology.inhabited
-/

#print RingTopology.ext /-
@[ext]
theorem ext {f g : RingTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  by
  ext : 2
  exact h
#align ring_topology.ext' RingTopology.ext
-/

/-- The ordering on ring topologies on the ring `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : PartialOrder (RingTopology α) :=
  PartialOrder.lift RingTopology.toTopologicalSpace <| ext

-- mathport name: exprcont
local notation "cont" => @Continuous _ _

private def def_Inf (S : Set (RingTopology α)) : RingTopology α :=
  let Inf_S' := sInf (toTopologicalSpace '' S)
  { toTopologicalSpace := Inf_S'
    continuous_add := by
      apply continuous_sInf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_sInf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      have h_continuous_id := @Continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_add h_continuous_id
    continuous_mul := by
      apply continuous_sInf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_sInf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      have h_continuous_id := @Continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_mul h_continuous_id
    continuous_neg := by
      apply continuous_sInf_rng.2
      rintro _ ⟨⟨t, tr⟩, haS, rfl⟩; skip
      have h := continuous_sInf_dom (Set.mem_image_of_mem to_topological_space haS) continuous_id
      exact @Continuous.comp _ _ _ (id _) (id _) t _ _ continuous_neg h }
#align ring_topology.def_Inf ring_topology.def_Inf

/-- Ring topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance : CompleteSemilatticeInf (RingTopology α) :=
  { RingTopology.partialOrder with
    sInf := defInf
    inf_le := fun S a haS =>
      by
      apply topological_space.complete_lattice.Inf_le
      use a, ⟨haS, rfl⟩
    le_inf := by
      intro S a hab
      apply topological_space.complete_lattice.le_Inf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

instance : CompleteLattice (RingTopology α) :=
  completeLatticeOfCompleteSemilatticeInf _

#print RingTopology.coinduced /-
/-- Given `f : α → β` and a topology on `α`, the coinduced ring topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological ring. -/
def coinduced {α β : Type _} [t : TopologicalSpace α] [Ring β] (f : α → β) : RingTopology β :=
  sInf { b : RingTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }
#align ring_topology.coinduced RingTopology.coinduced
-/

/- warning: ring_topology.coinduced_continuous -> RingTopology.coinduced_continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [t : TopologicalSpace.{u1} α] [_inst_2 : Ring.{u2} β] (f : α -> β), Continuous.{u1, u2} α β t (RingTopology.toTopologicalSpace.{u2} β _inst_2 (RingTopology.coinduced.{u1, u2} α β t _inst_2 f)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [t : TopologicalSpace.{u2} α] [_inst_2 : Ring.{u1} β] (f : α -> β), Continuous.{u2, u1} α β t (RingTopology.toTopologicalSpace.{u1} β _inst_2 (RingTopology.coinduced.{u2, u1} α β t _inst_2 f)) f
Case conversion may be inaccurate. Consider using '#align ring_topology.coinduced_continuous RingTopology.coinduced_continuousₓ'. -/
theorem coinduced_continuous {α β : Type _} [t : TopologicalSpace α] [Ring β] (f : α → β) :
    cont t (coinduced f).toTopologicalSpace f :=
  by
  rw [continuous_iff_coinduced_le]
  refine' le_sInf _
  rintro _ ⟨t', ht', rfl⟩
  exact ht'
#align ring_topology.coinduced_continuous RingTopology.coinduced_continuous

/- warning: ring_topology.to_add_group_topology -> RingTopology.toAddGroupTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], (RingTopology.{u1} α _inst_1) -> (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], (RingTopology.{u1} α _inst_1) -> (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ring_topology.to_add_group_topology RingTopology.toAddGroupTopologyₓ'. -/
/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology (t : RingTopology α) : AddGroupTopology α
    where
  toTopologicalSpace := t.toTopologicalSpace
  to_topologicalAddGroup :=
    @TopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toTopologicalRing
#align ring_topology.to_add_group_topology RingTopology.toAddGroupTopology

/- warning: ring_topology.to_add_group_topology.order_embedding -> RingTopology.toAddGroupTopology.orderEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], OrderEmbedding.{u1, u1} (RingTopology.{u1} α _inst_1) (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))) (Preorder.toLE.{u1} (RingTopology.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (RingTopology.{u1} α _inst_1) (RingTopology.partialOrder.{u1} α _inst_1))) (Preorder.toLE.{u1} (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u1} (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))) (AddGroupTopology.partialOrder.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α], OrderEmbedding.{u1, u1} (RingTopology.{u1} α _inst_1) (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1))) (Preorder.toLE.{u1} (RingTopology.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (RingTopology.{u1} α _inst_1) (RingTopology.instPartialOrderRingTopology.{u1} α _inst_1))) (Preorder.toLE.{u1} (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (AddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1))) (AddGroupTopology.instPartialOrderAddGroupTopology.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (Ring.toAddGroupWithOne.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring_topology.to_add_group_topology.order_embedding RingTopology.toAddGroupTopology.orderEmbeddingₓ'. -/
/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology α) (AddGroupTopology α) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl
#align ring_topology.to_add_group_topology.order_embedding RingTopology.toAddGroupTopology.orderEmbedding

end RingTopology

section AbsoluteValue

/- warning: absolute_value.comp -> AbsoluteValue.comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_1 : Semiring.{u3} T] [_inst_2 : Semiring.{u1} R] [_inst_3 : OrderedSemiring.{u2} S], (AbsoluteValue.{u1, u2} R S _inst_2 _inst_3) -> (forall {f : RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)}, (Function.Injective.{succ u3, succ u1} T R (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) (fun (_x : RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) => T -> R) (RingHom.hasCoeToFun.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) f)) -> (AbsoluteValue.{u3, u2} T S _inst_1 _inst_3))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} {T : Type.{u3}} [_inst_1 : Semiring.{u3} T] [_inst_2 : Semiring.{u1} R] [_inst_3 : OrderedSemiring.{u2} S], (AbsoluteValue.{u1, u2} R S _inst_2 _inst_3) -> (forall {f : RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)}, (Function.Injective.{succ u3, succ u1} T R (FunLike.coe.{max (succ u1) (succ u3), succ u3, succ u1} (RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) T (fun (_x : T) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : T) => R) _x) (MulHomClass.toFunLike.{max u1 u3, u3, u1} (RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) T R (NonUnitalNonAssocSemiring.toMul.{u3} T (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} T (Semiring.toNonAssocSemiring.{u3} T _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u3, u1} (RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) T R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} T (Semiring.toNonAssocSemiring.{u3} T _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u3, u1} (RingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2)) T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2) (RingHom.instRingHomClassRingHom.{u3, u1} T R (Semiring.toNonAssocSemiring.{u3} T _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_2))))) f)) -> (AbsoluteValue.{u3, u2} T S _inst_1 _inst_3))
Case conversion may be inaccurate. Consider using '#align absolute_value.comp AbsoluteValue.compₓ'. -/
/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
def AbsoluteValue.comp {R S T : Type _} [Semiring T] [Semiring R] [OrderedSemiring S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S
    where
  toFun := v ∘ f
  map_mul' := by simp only [Function.comp_apply, map_mul, eq_self_iff_true, forall_const]
  nonneg' := by simp only [v.nonneg, forall_const]
  eq_zero' := by simp only [map_eq_zero_iff f hf, v.eq_zero, forall_const, iff_self_iff]
  add_le' := by simp only [Function.comp_apply, map_add, v.add_le, forall_const]
#align absolute_value.comp AbsoluteValue.comp

end AbsoluteValue

