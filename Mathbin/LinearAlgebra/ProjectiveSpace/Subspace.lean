/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth

! This file was ported from Lean 3 source module linear_algebra.projective_space.subspace
! leanprover-community/mathlib commit a2706b55e8d7f7e9b1f93143f0b88f2e34a11eea
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.ProjectiveSpace.Basic

/-!
# Subspaces of Projective Space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.

# Future Work
- Show that there is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/


variable (K V : Type _) [Field K] [AddCommGroup V] [Module K V]

namespace Projectivization

#print Projectivization.Subspace /-
/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
structure Subspace where
  carrier : Set (ℙ K V)
  mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) hvw ∈ carrier
#align projectivization.subspace Projectivization.Subspace
-/

namespace Subspace

variable {K V}

instance : SetLike (Subspace K V) (ℙ K V)
    where
  coe := carrier
  coe_injective' A B := by
    cases A
    cases B
    simp

/- warning: projectivization.subspace.mem_carrier_iff -> Projectivization.Subspace.mem_carrier_iff is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (A : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (x : Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3), Iff (Membership.Mem.{u2, u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasMem.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) x (Projectivization.Subspace.carrier.{u1, u2} K V _inst_1 _inst_2 _inst_3 A)) (Membership.Mem.{u2, u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)) x A)
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (A : Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (x : Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3), Iff (Membership.mem.{u1, u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Set.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)) (Set.instMembershipSet.{u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3)) x (Projectivization.Subspace.carrier.{u2, u1} K V _inst_1 _inst_2 _inst_3 A)) (Membership.mem.{u1, u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u2, u1} K V _inst_1 _inst_2 _inst_3)) x A)
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.mem_carrier_iff Projectivization.Subspace.mem_carrier_iffₓ'. -/
@[simp]
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A :=
  Iff.refl _
#align projectivization.subspace.mem_carrier_iff Projectivization.Subspace.mem_carrier_iff

/- warning: projectivization.subspace.mem_add -> Projectivization.Subspace.mem_add is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (T : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (v : V) (w : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) (hw : Ne.{succ u2} V w (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) (hvw : Ne.{succ u2} V (HAdd.hAdd.{u2, u2, u2} V V V (instHAdd.{u2} V (AddZeroClass.toHasAdd.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))) v w) (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), (Membership.Mem.{u2, u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3 v hv) T) -> (Membership.Mem.{u2, u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3 w hw) T) -> (Membership.Mem.{u2, u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3 (HAdd.hAdd.{u2, u2, u2} V V V (instHAdd.{u2} V (AddZeroClass.toHasAdd.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))) v w) hvw) T)
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (T : Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (v : V) (w : V) (hv : Ne.{succ u1} V v (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V _inst_2)))))))) (hw : Ne.{succ u1} V w (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V _inst_2)))))))) (hvw : Ne.{succ u1} V (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2)))))) v w) (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V _inst_2)))))))), (Membership.mem.{u1, u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u2, u1} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3 v hv) T) -> (Membership.mem.{u1, u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u2, u1} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3 w hw) T) -> (Membership.mem.{u1, u1} (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u2, u1} K V _inst_1 _inst_2 _inst_3)) (Projectivization.mk.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3 (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2)))))) v w) hvw) T)
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.mem_add Projectivization.Subspace.mem_addₓ'. -/
theorem mem_add (T : Subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    Projectivization.mk K v hv ∈ T →
      Projectivization.mk K w hw ∈ T → Projectivization.mk K (v + w) hvw ∈ T :=
  T.mem_add' v w hv hw hvw
#align projectivization.subspace.mem_add Projectivization.Subspace.mem_add

#print Projectivization.Subspace.spanCarrier /-
/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive spanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
  |
  mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (Projectivization.mk K v hv) →
      span_carrier (Projectivization.mk K w hw) → span_carrier (Projectivization.mk K (v + w) hvw)
#align projectivization.subspace.span_carrier Projectivization.Subspace.spanCarrier
-/

#print Projectivization.Subspace.span /-
/-- The span of a set of points in projective space is a subspace. -/
def span (S : Set (ℙ K V)) : Subspace K V
    where
  carrier := spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw
#align projectivization.subspace.span Projectivization.Subspace.span
-/

#print Projectivization.Subspace.subset_span /-
/-- The span of a set of points contains the set of points. -/
theorem subset_span (S : Set (ℙ K V)) : S ⊆ span S := fun x hx => spanCarrier.of _ hx
#align projectivization.subspace.subset_span Projectivization.Subspace.subset_span
-/

/- warning: projectivization.subspace.gi -> Projectivization.Subspace.gi is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], GaloisInsertion.{u2, u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.completeBooleanAlgebra.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))))))) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.partialOrder.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], GaloisInsertion.{u2, u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instCompleteBooleanAlgebraSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))))))) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.instPartialOrder.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SetLike.coe.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.gi Projectivization.Subspace.giₓ'. -/
/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : GaloisInsertion (span : Set (ℙ K V) → Subspace K V) coe
    where
  choice S hS := span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx
      · apply h
        assumption
      · apply B.mem_add
        assumption'⟩
  le_l_u S := subset_span _
  choice_eq _ _ := rfl
#align projectivization.subspace.gi Projectivization.Subspace.gi

/- warning: projectivization.subspace.span_coe -> Projectivization.Subspace.span_coe is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) W)) W
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : Field.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (W : Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3), Eq.{succ u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u2, u1} K V _inst_1 _inst_2 _inst_3 (SetLike.coe.{u1, u1} (Projectivization.Subspace.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u2, u1} K V (Field.toDivisionRing.{u2} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u2, u1} K V _inst_1 _inst_2 _inst_3) W)) W
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_coe Projectivization.Subspace.span_coeₓ'. -/
/-- The span of a subspace is the subspace. -/
@[simp]
theorem span_coe (W : Subspace K V) : span ↑W = W :=
  GaloisInsertion.l_u_eq gi W
#align projectivization.subspace.span_coe Projectivization.Subspace.span_coe

#print Projectivization.Subspace.instInf /-
/-- The infimum of two subspaces exists. -/
instance instInf : Inf (Subspace K V) :=
  ⟨fun A B =>
    ⟨A ⊓ B, fun v w hv hw hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩
#align projectivization.subspace.has_inf Projectivization.Subspace.instInf
-/

#print Projectivization.Subspace.instInfSet /-
/-- Infimums of arbitrary collections of subspaces exist. -/
instance instInfSet : InfSet (Subspace K V) :=
  ⟨fun A =>
    ⟨sInf (coe '' A), fun v w hv hw hvw h1 h2 t =>
      by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩
#align projectivization.subspace.has_Inf Projectivization.Subspace.instInfSet
-/

/-- The subspaces of a projective space form a complete lattice. -/
instance : CompleteLattice (Subspace K V) :=
  { (inferInstance : Inf _),
    completeLatticeOfInf (Subspace K V)
      (by
        refine' fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => _⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx) with
    inf_le_left := fun A B x hx => hx.1
    inf_le_right := fun A B x hx => hx.2
    le_inf := fun A B C h1 h2 x hx => ⟨h1 hx, h2 hx⟩ }

#print Projectivization.Subspace.subspaceInhabited /-
instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤
#align projectivization.subspace.subspace_inhabited Projectivization.Subspace.subspaceInhabited
-/

/- warning: projectivization.subspace.span_empty -> Projectivization.Subspace.span_empty is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (EmptyCollection.emptyCollection.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasEmptyc.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))) (Bot.bot.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toHasBot.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (EmptyCollection.emptyCollection.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instEmptyCollectionSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))) (Bot.bot.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toBot.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_empty Projectivization.Subspace.span_emptyₓ'. -/
/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp]
theorem span_empty : span (∅ : Set (ℙ K V)) = ⊥ :=
  gi.gc.l_bot
#align projectivization.subspace.span_empty Projectivization.Subspace.span_empty

/- warning: projectivization.subspace.span_univ -> Projectivization.Subspace.span_univ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Set.univ.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))) (Top.top.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toHasTop.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Set.univ.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))) (Top.top.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toTop.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_univ Projectivization.Subspace.span_univₓ'. -/
/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp]
theorem span_univ : span (Set.univ : Set (ℙ K V)) = ⊤ :=
  by
  rw [eq_top_iff, SetLike.le_def]
  intro x hx
  exact subset_span _ (Set.mem_univ x)
#align projectivization.subspace.span_univ Projectivization.Subspace.span_univ

/- warning: projectivization.subspace.span_le_subspace_iff -> Projectivization.Subspace.span_le_subspace_iff is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Iff (LE.le.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W) (HasSubset.Subset.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasSubset.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) W))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Iff (LE.le.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W) (HasSubset.Subset.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instHasSubsetSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S (SetLike.coe.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3) W))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_le_subspace_iff Projectivization.Subspace.span_le_subspace_iffₓ'. -/
/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
theorem span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S ≤ W ↔ S ⊆ W :=
  gi.gc S W
#align projectivization.subspace.span_le_subspace_iff Projectivization.Subspace.span_le_subspace_iff

/- warning: projectivization.subspace.monotone_span -> Projectivization.Subspace.monotone_span is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Monotone.{u2, u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.completeBooleanAlgebra.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))))))) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Monotone.{u2, u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instCompleteBooleanAlgebraSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)))))))) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.monotone_span Projectivization.Subspace.monotone_spanₓ'. -/
/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[mono]
theorem monotone_span : Monotone (span : Set (ℙ K V) → Subspace K V) :=
  gi.gc.monotone_l
#align projectivization.subspace.monotone_span Projectivization.Subspace.monotone_span

#print Projectivization.Subspace.subset_span_trans /-
theorem subset_span_trans {S T U : Set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
    S ⊆ span U :=
  gi.gc.le_u_l_trans hST hTU
#align projectivization.subspace.subset_span_trans Projectivization.Subspace.subset_span_trans
-/

/- warning: projectivization.subspace.span_union -> Projectivization.Subspace.span_union is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (T : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)), Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasUnion.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S T)) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toHasSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 T))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (T : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)), Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instUnionSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S T)) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 T))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_union Projectivization.Subspace.span_unionₓ'. -/
/-- The supremum of two subspaces is equal to the span of their union. -/
theorem span_union (S T : Set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T :=
  (@gi K V _ _ _).gc.l_sup
#align projectivization.subspace.span_union Projectivization.Subspace.span_union

/- warning: projectivization.subspace.span_Union -> Projectivization.Subspace.span_iUnion is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {ι : Sort.{u3}} (s : ι -> (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))), Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Set.iUnion.{u2, u3} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) ι (fun (i : ι) => s i))) (iSup.{u2, u3} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toHasSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))) ι (fun (i : ι) => Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (s i)))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {ι : Sort.{u3}} (s : ι -> (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3))), Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Set.iUnion.{u2, u3} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) ι (fun (i : ι) => s i))) (iSup.{u2, u3} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toSupSet.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))) ι (fun (i : ι) => Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (s i)))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_Union Projectivization.Subspace.span_iUnionₓ'. -/
/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
theorem span_iUnion {ι} (s : ι → Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_iSup
#align projectivization.subspace.span_Union Projectivization.Subspace.span_iUnion

/- warning: projectivization.subspace.sup_span -> Projectivization.Subspace.sup_span is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toHasSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) W (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S)) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasUnion.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) W) S))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) W (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S)) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instUnionSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.coe.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3) W) S))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.sup_span Projectivization.Subspace.sup_spanₓ'. -/
/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
theorem sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W ∪ S) := by
  rw [span_union, span_coe]
#align projectivization.subspace.sup_span Projectivization.Subspace.sup_span

/- warning: projectivization.subspace.span_sup -> Projectivization.Subspace.span_sup is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toHasSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasUnion.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) W)))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Sup.sup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (SemilatticeSup.toSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Lattice.toSemilatticeSup.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (ConditionallyCompleteLattice.toLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Union.union.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instUnionSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S (SetLike.coe.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3) W)))
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_sup Projectivization.Subspace.span_supₓ'. -/
theorem span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S ∪ W) := by
  rw [span_union, span_coe]
#align projectivization.subspace.span_sup Projectivization.Subspace.span_sup

#print Projectivization.Subspace.mem_span /-
/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
theorem mem_span {S : Set (ℙ K V)} (u : ℙ K V) : u ∈ span S ↔ ∀ W : Subspace K V, S ⊆ W → u ∈ W :=
  by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩
#align projectivization.subspace.mem_span Projectivization.Subspace.mem_span
-/

#print Projectivization.Subspace.span_eq_sInf /-
/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
theorem span_eq_sInf {S : Set (ℙ K V)} : span S = sInf { W | S ⊆ W } :=
  by
  ext
  simp_rw [mem_carrier_iff, mem_span x]
  refine' ⟨fun hx => _, fun hx W hW => _⟩
  · rintro W ⟨T, ⟨hT, rfl⟩⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S ⊆ ↑W } W hW) x hx
#align projectivization.subspace.span_eq_Inf Projectivization.Subspace.span_eq_sInf
-/

/- warning: projectivization.subspace.span_eq_of_le -> Projectivization.Subspace.span_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, (HasSubset.Subset.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.hasSubset.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (HasLiftT.mk.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (CoeTCₓ.coe.{succ u2, succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (SetLike.Set.hasCoeT.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.Projectivization.setLike.{u1, u2} K V _inst_1 _inst_2 _inst_3)))) W)) -> (LE.le.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteSemilatticeInf.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.completeLattice.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) W (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S)) -> (Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W)
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : Field.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {S : Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)} {W : Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3}, (HasSubset.Subset.{u2} (Set.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) (Set.instHasSubsetSet.{u2} (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3)) S (SetLike.coe.{u2, u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u1, u2} K V (Field.toDivisionRing.{u1} K _inst_1) _inst_2 _inst_3) (Projectivization.Subspace.instSetLikeSubspaceProjectivizationToDivisionRing.{u1, u2} K V _inst_1 _inst_2 _inst_3) W)) -> (LE.le.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.instCompleteLatticeSubspace.{u1, u2} K V _inst_1 _inst_2 _inst_3))))) W (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S)) -> (Eq.{succ u2} (Projectivization.Subspace.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.Subspace.span.{u1, u2} K V _inst_1 _inst_2 _inst_3 S) W)
Case conversion may be inaccurate. Consider using '#align projectivization.subspace.span_eq_of_le Projectivization.Subspace.span_eq_of_leₓ'. -/
/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
theorem span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
    span S = W :=
  le_antisymm (span_le_subspace_iff.mpr hS) hW
#align projectivization.subspace.span_eq_of_le Projectivization.Subspace.span_eq_of_le

#print Projectivization.Subspace.span_eq_span_iff /-
/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
theorem span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
  ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩
#align projectivization.subspace.span_eq_span_iff Projectivization.Subspace.span_eq_span_iff
-/

end Subspace

end Projectivization

