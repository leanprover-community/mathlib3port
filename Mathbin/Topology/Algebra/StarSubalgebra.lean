/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module topology.algebra.star_subalgebra
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Subalgebra
import Mathbin.Topology.Algebra.Algebra
import Mathbin.Topology.Algebra.Star

/-!
# Topological star (sub)algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `has_continuous_smul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/


open Classical Set TopologicalSpace

open Classical

namespace StarSubalgebra

section TopologicalStarAlgebra

variable {R A B : Type _} [CommSemiring R] [StarRing R]

variable [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

instance [TopologicalSpace R] [ContinuousSMul R A] (s : StarSubalgebra R A) : ContinuousSMul R s :=
  s.toSubalgebra.ContinuousSMul

instance [TopologicalSemiring A] (s : StarSubalgebra R A) : TopologicalSemiring s :=
  s.toSubalgebra.TopologicalSemiring

/- warning: star_subalgebra.embedding_inclusion -> StarSubalgebra.embedding_inclusion is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_subalgebra.embedding_inclusion StarSubalgebra.embedding_inclusionₓ'. -/
/-- The `star_subalgebra.inclusion` of a star subalgebra is an `embedding`. -/
theorem embedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) : Embedding (inclusion h) :=
  { induced := Eq.symm induced_compose
    inj := Subtype.map_injective h Function.injective_id }
#align star_subalgebra.embedding_inclusion StarSubalgebra.embedding_inclusion

/- warning: star_subalgebra.closed_embedding_inclusion -> StarSubalgebra.closedEmbedding_inclusion is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_subalgebra.closed_embedding_inclusion StarSubalgebra.closedEmbedding_inclusionₓ'. -/
/-- The `star_subalgebra.inclusion` of a closed star subalgebra is a `closed_embedding`. -/
theorem closedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂)
    (hS₁ : IsClosed (S₁ : Set A)) : ClosedEmbedding (inclusion h) :=
  { embedding_inclusion h with
    closed_range :=
      isClosed_induced_iff.2
        ⟨S₁, hS₁, by
          convert(Set.range_subtype_map id _).symm
          rw [Set.image_id]
          rfl⟩ }
#align star_subalgebra.closed_embedding_inclusion StarSubalgebra.closedEmbedding_inclusion

variable [TopologicalSemiring A] [ContinuousStar A]

variable [TopologicalSpace B] [Semiring B] [Algebra R B] [StarRing B]

#print StarSubalgebra.topologicalClosure /-
/-- The closure of a star subalgebra in a topological star algebra as a star subalgebra. -/
def topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A :=
  {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun a ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x ∈ s → star x ∈ s) }
#align star_subalgebra.topological_closure StarSubalgebra.topologicalClosure
-/

/- warning: star_subalgebra.topological_closure_coe -> StarSubalgebra.topologicalClosure_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)] [_inst_7 : StarModule.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1)) _inst_2))) (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6))) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_4 _inst_5)))))] [_inst_8 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))] [_inst_9 : ContinuousStar.{u2} A _inst_3 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), Eq.{succ u2} (Set.{u2} A) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7)))) (StarSubalgebra.topologicalClosure.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s)) (closure.{u2} A _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7)))) s))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : StarRing.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1))] [_inst_3 : TopologicalSpace.{u1} A] [_inst_4 : Semiring.{u1} A] [_inst_5 : Algebra.{u2, u1} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4)] [_inst_7 : StarModule.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (StarRing.toStarAddMonoid.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1)) _inst_2))) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6))) (Algebra.toSMul.{u2, u1} R A _inst_1 _inst_4 _inst_5)] [_inst_8 : TopologicalSemiring.{u1} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4))] [_inst_9 : ContinuousStar.{u1} A _inst_3 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), Eq.{succ u1} (Set.{u1} A) (SetLike.coe.{u1, u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (StarSubalgebra.topologicalClosure.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s)) (closure.{u1} A _inst_3 (SetLike.coe.{u1, u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) s))
Case conversion may be inaccurate. Consider using '#align star_subalgebra.topological_closure_coe StarSubalgebra.topologicalClosure_coeₓ'. -/
@[simp]
theorem topologicalClosure_coe (s : StarSubalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl
#align star_subalgebra.topological_closure_coe StarSubalgebra.topologicalClosure_coe

/- warning: star_subalgebra.le_topological_closure -> StarSubalgebra.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)] [_inst_7 : StarModule.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1)) _inst_2))) (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6))) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_4 _inst_5)))))] [_inst_8 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))] [_inst_9 : ContinuousStar.{u2} A _inst_3 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), LE.le.{u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Preorder.toHasLe.{u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (PartialOrder.toPreorder.{u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (CompleteSemilatticeInf.toPartialOrder.{u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (CompleteLattice.toCompleteSemilatticeInf.{u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (StarSubalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_5 _inst_6 _inst_7))))) s (StarSubalgebra.topologicalClosure.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : StarRing.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1))] [_inst_3 : TopologicalSpace.{u1} A] [_inst_4 : Semiring.{u1} A] [_inst_5 : Algebra.{u2, u1} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4)] [_inst_7 : StarModule.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (StarRing.toStarAddMonoid.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1)) _inst_2))) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6))) (Algebra.toSMul.{u2, u1} R A _inst_1 _inst_4 _inst_5)] [_inst_8 : TopologicalSemiring.{u1} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4))] [_inst_9 : ContinuousStar.{u1} A _inst_3 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), LE.le.{u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Preorder.toLE.{u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (PartialOrder.toPreorder.{u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (OmegaCompletePartialOrder.toPartialOrder.{u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (StarSubalgebra.completeLattice.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_5 _inst_6 _inst_7))))) s (StarSubalgebra.topologicalClosure.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s)
Case conversion may be inaccurate. Consider using '#align star_subalgebra.le_topological_closure StarSubalgebra.le_topologicalClosureₓ'. -/
theorem le_topologicalClosure (s : StarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
#align star_subalgebra.le_topological_closure StarSubalgebra.le_topologicalClosure

/- warning: star_subalgebra.is_closed_topological_closure -> StarSubalgebra.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : StarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))] [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)] [_inst_7 : StarModule.{u1, u2} R A (InvolutiveStar.toHasStar.{u1} R (StarAddMonoid.toHasInvolutiveStar.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (StarRing.toStarAddMonoid.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1)) _inst_2))) (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6))) (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4)))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_4 _inst_5)))))] [_inst_8 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))] [_inst_9 : ContinuousStar.{u2} A _inst_3 (InvolutiveStar.toHasStar.{u2} A (StarAddMonoid.toHasInvolutiveStar.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), IsClosed.{u2} A _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (StarSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7)))) (StarSubalgebra.topologicalClosure.{u1, u2} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : StarRing.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1))] [_inst_3 : TopologicalSpace.{u1} A] [_inst_4 : Semiring.{u1} A] [_inst_5 : Algebra.{u2, u1} R A _inst_1 _inst_4] [_inst_6 : StarRing.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4)] [_inst_7 : StarModule.{u2, u1} R A (InvolutiveStar.toStar.{u2} R (StarAddMonoid.toInvolutiveStar.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (StarRing.toStarAddMonoid.{u2} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u2} R (CommSemiring.toNonUnitalCommSemiring.{u2} R _inst_1)) _inst_2))) (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6))) (Algebra.toSMul.{u2, u1} R A _inst_1 _inst_4 _inst_5)] [_inst_8 : TopologicalSemiring.{u1} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4))] [_inst_9 : ContinuousStar.{u1} A _inst_3 (InvolutiveStar.toStar.{u1} A (StarAddMonoid.toInvolutiveStar.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_4)))) (StarRing.toStarAddMonoid.{u1} A (Semiring.toNonUnitalSemiring.{u1} A _inst_4) _inst_6)))] (s : StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7), IsClosed.{u1} A _inst_3 (SetLike.coe.{u1, u1} (StarSubalgebra.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) A (StarSubalgebra.setLike.{u2, u1} R A _inst_1 _inst_2 _inst_4 _inst_6 _inst_5 _inst_7) (StarSubalgebra.topologicalClosure.{u2, u1} R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 s))
Case conversion may be inaccurate. Consider using '#align star_subalgebra.is_closed_topological_closure StarSubalgebra.isClosed_topologicalClosureₓ'. -/
theorem isClosed_topologicalClosure (s : StarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) :=
  isClosed_closure
#align star_subalgebra.is_closed_topological_closure StarSubalgebra.isClosed_topologicalClosure

instance {A : Type _} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [TopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A]
    {S : StarSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe

/- warning: star_subalgebra.topological_closure_minimal -> StarSubalgebra.topologicalClosure_minimal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_subalgebra.topological_closure_minimal StarSubalgebra.topologicalClosure_minimalₓ'. -/
theorem topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align star_subalgebra.topological_closure_minimal StarSubalgebra.topologicalClosure_minimal

#print StarSubalgebra.topologicalClosure_mono /-
theorem topologicalClosure_mono : Monotone (topologicalClosure : _ → StarSubalgebra R A) :=
  fun S₁ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)
#align star_subalgebra.topological_closure_mono StarSubalgebra.topologicalClosure_mono
-/

/- warning: star_subalgebra.comm_semiring_topological_closure -> StarSubalgebra.commSemiringTopologicalClosure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_subalgebra.comm_semiring_topological_closure StarSubalgebra.commSemiringTopologicalClosureₓ'. -/
/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  s.toSubalgebra.commSemiringTopologicalClosure hs
#align star_subalgebra.comm_semiring_topological_closure StarSubalgebra.commSemiringTopologicalClosure

/- warning: star_subalgebra.comm_ring_topological_closure -> StarSubalgebra.commRingTopologicalClosure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_subalgebra.comm_ring_topological_closure StarSubalgebra.commRingTopologicalClosureₓ'. -/
/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] [TopologicalRing A] [ContinuousStar A] [T2Space A]
    (s : StarSubalgebra R A) (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  s.toSubalgebra.commRingTopologicalClosure hs
#align star_subalgebra.comm_ring_topological_closure StarSubalgebra.commRingTopologicalClosure

/- warning: star_alg_hom.ext_topological_closure -> StarAlgHom.ext_topologicalClosure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_alg_hom.ext_topological_closure StarAlgHom.ext_topologicalClosureₓ'. -/
/-- Continuous `star_alg_hom`s from the the topological closure of a `star_subalgebra` whose
compositions with the `star_subalgebra.inclusion` map agree are, in fact, equal. -/
theorem StarAlgHom.ext_topologicalClosure [T2Space B] {S : StarSubalgebra R A}
    {φ ψ : S.topologicalClosure →⋆ₐ[R] B} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      φ.comp (inclusion (le_topologicalClosure S)) = ψ.comp (inclusion (le_topologicalClosure S))) :
    φ = ψ := by
  rw [FunLike.ext'_iff]
  have : Dense (Set.range <| inclusion (le_topological_closure S)) :=
    by
    refine' embedding_subtype_coe.to_inducing.dense_iff.2 fun x => _
    convert show ↑x ∈ closure (S : Set A) from x.prop
    rw [← Set.range_comp]
    exact
      Set.ext fun y =>
        ⟨by
          rintro ⟨y, rfl⟩
          exact y.prop, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  refine' Continuous.ext_on this hφ hψ _
  rintro _ ⟨x, rfl⟩
  simpa only using FunLike.congr_fun h x
#align star_alg_hom.ext_topological_closure StarAlgHom.ext_topologicalClosure

/- warning: star_alg_hom_class.ext_topological_closure -> StarAlgHomClass.ext_topologicalClosure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align star_alg_hom_class.ext_topological_closure StarAlgHomClass.ext_topologicalClosureₓ'. -/
theorem StarAlgHomClass.ext_topologicalClosure [T2Space B] {F : Type _} {S : StarSubalgebra R A}
    [StarAlgHomClass F R S.topologicalClosure B] {φ ψ : F} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      ∀ x : S,
        φ (inclusion (le_topologicalClosure S) x) = ψ ((inclusion (le_topologicalClosure S)) x)) :
    φ = ψ :=
  by
  have : (φ : S.topological_closure →⋆ₐ[R] B) = (ψ : S.topological_closure →⋆ₐ[R] B) := by
    refine' StarAlgHom.ext_topologicalClosure hφ hψ (StarAlgHom.ext _) <;>
      simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using h
  simpa only [FunLike.ext'_iff, StarAlgHom.coe_coe]
#align star_alg_hom_class.ext_topological_closure StarAlgHomClass.ext_topologicalClosure

end TopologicalStarAlgebra

end StarSubalgebra

section Elemental

open StarSubalgebra

variable (R : Type _) {A B : Type _} [CommSemiring R] [StarRing R]

variable [TopologicalSpace A] [Semiring A] [StarRing A] [TopologicalSemiring A]

variable [ContinuousStar A] [Algebra R A] [StarModule R A]

variable [TopologicalSpace B] [Semiring B] [StarRing B] [Algebra R B]

#print elementalStarAlgebra /-
/-- The topological closure of the subalgebra generated by a single element. -/
def elementalStarAlgebra (x : A) : StarSubalgebra R A :=
  (adjoin R ({x} : Set A)).topologicalClosure
#align elemental_star_algebra elementalStarAlgebra
-/

namespace elementalStarAlgebra

#print elementalStarAlgebra.self_mem /-
theorem self_mem (x : A) : x ∈ elementalStarAlgebra R x :=
  SetLike.le_def.mp (le_topologicalClosure _) (self_mem_adjoin_singleton R x)
#align elemental_star_algebra.self_mem elementalStarAlgebra.self_mem
-/

#print elementalStarAlgebra.star_self_mem /-
theorem star_self_mem (x : A) : star x ∈ elementalStarAlgebra R x :=
  star_mem <| self_mem R x
#align elemental_star_algebra.star_self_mem elementalStarAlgebra.star_self_mem
-/

/-- The `elemental_star_algebra` generated by a normal element is commutative. -/
instance [T2Space A] {x : A} [IsStarNormal x] : CommSemiring (elementalStarAlgebra R x) :=
  StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

/-- The `elemental_star_algebra` generated by a normal element is commutative. -/
instance {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A] [Algebra R A] [StarRing A]
    [StarModule R A] [TopologicalRing A] [ContinuousStar A] [T2Space A] {x : A} [IsStarNormal x] :
    CommRing (elementalStarAlgebra R x) :=
  StarSubalgebra.commRingTopologicalClosure _ mul_comm

#print elementalStarAlgebra.isClosed /-
protected theorem isClosed (x : A) : IsClosed (elementalStarAlgebra R x : Set A) :=
  isClosed_closure
#align elemental_star_algebra.is_closed elementalStarAlgebra.isClosed
-/

instance {A : Type _} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [TopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A] (x : A) :
    CompleteSpace (elementalStarAlgebra R x) :=
  isClosed_closure.completeSpace_coe

/- warning: elemental_star_algebra.le_of_is_closed_of_mem -> elementalStarAlgebra.le_of_isClosed_of_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align elemental_star_algebra.le_of_is_closed_of_mem elementalStarAlgebra.le_of_isClosed_of_memₓ'. -/
theorem le_of_isClosed_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
    (hx : x ∈ S) : elementalStarAlgebra R x ≤ S :=
  topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS
#align elemental_star_algebra.le_of_is_closed_of_mem elementalStarAlgebra.le_of_isClosed_of_mem

#print elementalStarAlgebra.closedEmbedding_coe /-
/-- The coercion from an elemental algebra to the full algebra as a `closed_embedding`. -/
theorem closedEmbedding_coe (x : A) : ClosedEmbedding (coe : elementalStarAlgebra R x → A) :=
  { induced := rfl
    inj := Subtype.coe_injective
    closed_range := by
      convert elementalStarAlgebra.isClosed R x
      exact
        Set.ext fun y =>
          ⟨by
            rintro ⟨y, rfl⟩
            exact y.prop, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩ }
#align elemental_star_algebra.closed_embedding_coe elementalStarAlgebra.closedEmbedding_coe
-/

/- warning: elemental_star_algebra.star_alg_hom_class_ext -> elementalStarAlgebra.starAlgHomClass_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align elemental_star_algebra.star_alg_hom_class_ext elementalStarAlgebra.starAlgHomClass_extₓ'. -/
theorem starAlgHomClass_ext [T2Space B] {F : Type _} {a : A}
    [StarAlgHomClass F R (elementalStarAlgebra R a) B] {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ :=
  by
  refine' StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => adjoin_induction' x _ _ _ _ _
  exacts[fun y hy => by simpa only [set.mem_singleton_iff.mp hy] using h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]
#align elemental_star_algebra.star_alg_hom_class_ext elementalStarAlgebra.starAlgHomClass_ext

end elementalStarAlgebra

end Elemental

