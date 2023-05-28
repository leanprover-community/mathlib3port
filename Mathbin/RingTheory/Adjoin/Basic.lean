/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.adjoin.basic
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Tower
import Mathbin.LinearAlgebra.Prod
import Mathbin.LinearAlgebra.Finsupp

/-!
# Adjoining elements to form subalgebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up.

## Tags

adjoin, algebra

-/


universe u v w

open Pointwise

open Submodule Subsemiring

variable {R : Type u} {A : Type v} {B : Type w}

namespace Algebra

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra R B] {s t : Set A}

/- warning: algebra.subset_adjoin -> Algebra.subset_adjoin is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))
Case conversion may be inaccurate. Consider using '#align algebra.subset_adjoin Algebra.subset_adjoinₓ'. -/
theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s
#align algebra.subset_adjoin Algebra.subset_adjoin

/- warning: algebra.adjoin_le -> Algebra.adjoin_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4}, (HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)))) S)) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toHasLe.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4}, (HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) S)) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S)
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_le Algebra.adjoin_leₓ'. -/
theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H
#align algebra.adjoin_le Algebra.adjoin_le

/- warning: algebra.adjoin_eq_Inf -> Algebra.adjoin_eq_sInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (InfSet.sInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toHasInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))) (setOf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (fun (p : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) => HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)))) p))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (InfSet.sInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toInfSet.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4))) (setOf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (fun (p : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) => HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) p))))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_eq_Inf Algebra.adjoin_eq_sInfₓ'. -/
theorem adjoin_eq_sInf : adjoin R s = sInf { p | s ⊆ p } :=
  le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)
#align algebra.adjoin_eq_Inf Algebra.adjoin_eq_sInf

/- warning: algebra.adjoin_le_iff -> Algebra.adjoin_le_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4}, Iff (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toHasLe.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S) (HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)))) S))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4}, Iff (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S) (HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) S))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_le_iff Algebra.adjoin_le_iffₓ'. -/
theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _
#align algebra.adjoin_le_iff Algebra.adjoin_le_iff

/- warning: algebra.adjoin_mono -> Algebra.adjoin_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {t : Set.{u2} A}, (HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s t) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toHasLe.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 t))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {t : Set.{u2} A}, (HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s t) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 t))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_mono Algebra.adjoin_monoₓ'. -/
theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H
#align algebra.adjoin_mono Algebra.adjoin_mono

/- warning: algebra.adjoin_eq_of_le -> Algebra.adjoin_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} (S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4), (HasSubset.Subset.{u2} (Set.{u2} A) (Set.hasSubset.{u2} A) s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Set.{u2} A) (SetLike.Set.hasCoeT.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)))) S)) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toHasLe.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) S (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) -> (Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} (S : Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4), (HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) s (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) S)) -> (LE.le.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Preorder.toLE.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (PartialOrder.toPreorder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4))))) S (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) -> (Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) S)
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_eq_of_le Algebra.adjoin_eq_of_leₓ'. -/
theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymm (adjoin_le h₁) h₂
#align algebra.adjoin_eq_of_le Algebra.adjoin_eq_of_le

#print Algebra.adjoin_eq /-
theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin
#align algebra.adjoin_eq Algebra.adjoin_eq
-/

/- warning: algebra.adjoin_Union -> Algebra.adjoin_iUnion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {α : Type.{u3}} (s : α -> (Set.{u2} A)), Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Set.iUnion.{u2, succ u3} A α s)) (iSup.{u2, succ u3} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toHasSup.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))) α (fun (i : α) => Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (s i)))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_4 : Algebra.{u2, u3} R A _inst_1 _inst_2] {α : Type.{u1}} (s : α -> (Set.{u3} A)), Eq.{succ u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u2, u3} R A _inst_1 _inst_2 _inst_4 (Set.iUnion.{u3, succ u1} A α s)) (iSup.{u3, succ u1} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toSupSet.{u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4))) α (fun (i : α) => Algebra.adjoin.{u2, u3} R A _inst_1 _inst_2 _inst_4 (s i)))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_Union Algebra.adjoin_iUnionₓ'. -/
theorem adjoin_iUnion {α : Type _} (s : α → Set A) :
    adjoin R (Set.iUnion s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_iSup
#align algebra.adjoin_Union Algebra.adjoin_iUnion

/- warning: algebra.adjoin_attach_bUnion -> Algebra.adjoin_attach_biUnion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_6 : DecidableEq.{succ u2} A] {α : Type.{u3}} {s : Finset.{u3} α} (f : (coeSort.{succ u3, succ (succ u3)} (Finset.{u3} α) Type.{u3} (Finset.hasCoeToSort.{u3} α) s) -> (Finset.{u2} A)), Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} A) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} A) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} A) (Set.{u2} A) (Finset.Set.hasCoeT.{u2} A))) (Finset.biUnion.{u3, u2} (Subtype.{succ u3} α (fun (x : α) => Membership.Mem.{u3, u3} α (Finset.{u3} α) (Finset.hasMem.{u3} α) x s)) A (fun (a : A) (b : A) => _inst_6 a b) (Finset.attach.{u3} α s) f))) (iSup.{u2, succ u3} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toHasSup.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4))) (coeSort.{succ u3, succ (succ u3)} (Finset.{u3} α) Type.{u3} (Finset.hasCoeToSort.{u3} α) s) (fun (x : coeSort.{succ u3, succ (succ u3)} (Finset.{u3} α) Type.{u3} (Finset.hasCoeToSort.{u3} α) s) => Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} A) (Set.{u2} A) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} A) (Set.{u2} A) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} A) (Set.{u2} A) (Finset.Set.hasCoeT.{u2} A))) (f x))))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Semiring.{u3} A] [_inst_4 : Algebra.{u2, u3} R A _inst_1 _inst_2] [_inst_6 : DecidableEq.{succ u3} A] {α : Type.{u1}} {s : Finset.{u1} α} (f : (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) -> (Finset.{u3} A)), Eq.{succ u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u2, u3} R A _inst_1 _inst_2 _inst_4 (Finset.toSet.{u3} A (Finset.biUnion.{u1, u3} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) A (fun (a : A) (b : A) => _inst_6 a b) (Finset.attach.{u1} α s) f))) (iSup.{u3, succ u1} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (ConditionallyCompleteLattice.toSupSet.{u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Subalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u2, u3} R A _inst_1 _inst_2 _inst_4))) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) => Algebra.adjoin.{u2, u3} R A _inst_1 _inst_2 _inst_4 (Finset.toSet.{u3} A (f x))))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_attach_bUnion Algebra.adjoin_attach_biUnionₓ'. -/
theorem adjoin_attach_biUnion [DecidableEq A] {α : Type _} {s : Finset α} (f : s → Finset A) :
    adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x) := by simpa [adjoin_Union]
#align algebra.adjoin_attach_bUnion Algebra.adjoin_attach_biUnion

/- warning: algebra.adjoin_induction -> Algebra.adjoin_induction is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {p : A -> Prop} {x : A}, (Membership.Mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.hasMem.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) -> (forall (x : A), (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) x s) -> (p x)) -> (forall (r : R), p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_4) r)) -> (forall (x : A) (y : A), (p x) -> (p y) -> (p (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (Distrib.toHasAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) x y))) -> (forall (x : A) (y : A), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) x y))) -> (p x)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A} {p : A -> Prop} {x : A}, (Membership.mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) -> (forall (x : A), (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x s) -> (p x)) -> (forall (r : R), p (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2)) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) (algebraMap.{u1, u2} R A _inst_1 _inst_2 _inst_4) r)) -> (forall (x : A) (y : A), (p x) -> (p y) -> (p (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (Distrib.toAdd.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) x y))) -> (forall (x : A) (y : A), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) x y))) -> (p x)
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_induction Algebra.adjoin_inductionₓ'. -/
@[elab_as_elim]
theorem adjoin_induction {p : A → Prop} {x : A} (h : x ∈ adjoin R s) (Hs : ∀ x ∈ s, p x)
    (Halg : ∀ r, p (algebraMap R A r)) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  let S : Subalgebra R A :=
    { carrier := p
      mul_mem' := Hmul
      add_mem' := Hadd
      algebraMap_mem' := Halg }
  adjoin_le (show s ≤ S from Hs) h
#align algebra.adjoin_induction Algebra.adjoin_induction

/- warning: algebra.adjoin_induction₂ -> Algebra.adjoin_induction₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_induction₂ Algebra.adjoin_induction₂ₓ'. -/
/-- Induction principle for the algebra generated by a set `s`: show that `p x y` holds for any
`x y ∈ adjoin R s` given that that it holds for `x y ∈ s` and that it satisfies a number of
natural properties. -/
@[elab_as_elim]
theorem adjoin_induction₂ {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s) (hb : b ∈ adjoin R s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (Halg : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂))
    (Halg_left : ∀ (r), ∀ x ∈ s, p (algebraMap R A r) x)
    (Halg_right : ∀ (r), ∀ x ∈ s, p x (algebraMap R A r))
    (Hadd_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ + x₂) y)
    (Hadd_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ + y₂))
    (Hmul_left : ∀ x₁ x₂ y, p x₁ y → p x₂ y → p (x₁ * x₂) y)
    (Hmul_right : ∀ x y₁ y₂, p x y₁ → p x y₂ → p x (y₁ * y₂)) : p a b :=
  by
  refine' adjoin_induction hb _ (fun r => _) (Hadd_right a) (Hmul_right a)
  ·
    exact
      adjoin_induction ha Hs Halg_left (fun x y Hx Hy z hz => Hadd_left x y z (Hx z hz) (Hy z hz))
        fun x y Hx Hy z hz => Hmul_left x y z (Hx z hz) (Hy z hz)
  ·
    exact
      adjoin_induction ha (Halg_right r) (fun r' => Halg r' r)
        (fun x y => Hadd_left x y ((algebraMap R A) r)) fun x y =>
        Hmul_left x y ((algebraMap R A) r)
#align algebra.adjoin_induction₂ Algebra.adjoin_induction₂

/- warning: algebra.adjoin_induction' -> Algebra.adjoin_induction' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_induction' Algebra.adjoin_induction'ₓ'. -/
/-- The difference with `algebra.adjoin_induction` is that this acts on the subtype. -/
theorem adjoin_induction' {p : adjoin R s → Prop} (Hs : ∀ (x) (h : x ∈ s), p ⟨x, subset_adjoin h⟩)
    (Halg : ∀ r, p (algebraMap R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y))
    (Hmul : ∀ x y, p x → p y → p (x * y)) (x : adjoin R s) : p x :=
  Subtype.recOn x fun x hx =>
    by
    refine' Exists.elim _ fun (hx : x ∈ adjoin R s) (hc : p ⟨x, hx⟩) => hc
    exact
      adjoin_induction hx (fun x hx => ⟨subset_adjoin hx, Hs x hx⟩)
        (fun r => ⟨Subalgebra.algebraMap_mem _ r, Halg r⟩)
        (fun x y hx hy =>
          Exists.elim hx fun hx' hx =>
            Exists.elim hy fun hy' hy => ⟨Subalgebra.add_mem _ hx' hy', Hadd _ _ hx hy⟩)
        fun x y hx hy =>
        Exists.elim hx fun hx' hx =>
          Exists.elim hy fun hy' hy => ⟨Subalgebra.mul_mem _ hx' hy', Hmul _ _ hx hy⟩
#align algebra.adjoin_induction' Algebra.adjoin_induction'

/- warning: algebra.adjoin_adjoin_coe_preimage -> Algebra.adjoin_adjoin_coe_preimage is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, Eq.{succ u2} (Subalgebra.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (Algebra.adjoin.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Set.preimage.{u2, u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) A ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) A (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) A (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) A (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) A (coeSubtype.{succ u2} A (fun (x : A) => Membership.Mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.hasMem.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))))))) s)) (Top.top.{u2} (Subalgebra.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (CompleteLattice.toHasTop.{u2} (Subalgebra.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (Algebra.Subalgebra.completeLattice.{u1, u2} R (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, Eq.{succ u2} (Subalgebra.{u1, u2} R (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (Algebra.adjoin.{u1, u2} R (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Set.preimage.{u2, u2} (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) A (Subtype.val.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) s)) (Top.top.{u2} (Subalgebra.{u1, u2} R (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (CompleteLattice.toTop.{u2} (Subalgebra.{u1, u2} R (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) x (SetLike.coe.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))) _inst_1 (Subalgebra.toSemiring.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)) (Subalgebra.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_adjoin_coe_preimage Algebra.adjoin_adjoin_coe_preimageₓ'. -/
@[simp]
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R ((coe : adjoin R s → A) ⁻¹' s) = ⊤ :=
  by
  refine'
    eq_top_iff.2 fun x =>
      adjoin_induction' (fun a ha => _) (fun r => _) (fun _ _ => _) (fun _ _ => _) x
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _
#align algebra.adjoin_adjoin_coe_preimage Algebra.adjoin_adjoin_coe_preimage

#print Algebra.adjoin_union /-
theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (Algebra.gc : GaloisConnection _ (coe : Subalgebra R A → Set A)).l_sup
#align algebra.adjoin_union Algebra.adjoin_union
-/

variable (R A)

/- warning: algebra.adjoin_empty -> Algebra.adjoin_empty is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (EmptyCollection.emptyCollection.{u2} (Set.{u2} A) (Set.hasEmptyc.{u2} A))) (Bot.bot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toHasBot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (EmptyCollection.emptyCollection.{u2} (Set.{u2} A) (Set.instEmptyCollectionSet.{u2} A))) (Bot.bot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toBot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_empty Algebra.adjoin_emptyₓ'. -/
@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥ by
    apply GaloisConnection.l_bot
    exact Algebra.gc
#align algebra.adjoin_empty Algebra.adjoin_empty

/- warning: algebra.adjoin_univ -> Algebra.adjoin_univ is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Set.univ.{u2} A)) (Top.top.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toHasTop.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
but is expected to have type
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Set.univ.{u2} A)) (Top.top.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toTop.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_univ Algebra.adjoin_univₓ'. -/
@[simp]
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ :=
  eq_top_iff.2 fun x => subset_adjoin <| Set.mem_univ _
#align algebra.adjoin_univ Algebra.adjoin_univ

variable (R) {A} (s)

/- warning: algebra.adjoin_eq_span -> Algebra.adjoin_eq_span is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_eq_span Algebra.adjoin_eq_spanₓ'. -/
theorem adjoin_eq_span : (adjoin R s).toSubmodule = span R (Submonoid.closure s) :=
  by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction' L with hd tl ih
    · exact zero_mem _
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons, List.sum_cons]
    refine' Submodule.add_mem _ _ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _)(hr : r ∈ Submonoid.closure s), SMul.smul z r = List.prod hd
      by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction' hd with hd tl ih
    · exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine' ⟨hd * z, r, hr, _⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
    ·
      exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine' span_le.2 _
  change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin
#align algebra.adjoin_eq_span Algebra.adjoin_eq_span

/- warning: algebra.span_le_adjoin -> Algebra.span_le_adjoin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.span_le_adjoin Algebra.span_le_adjoinₓ'. -/
theorem span_le_adjoin (s : Set A) : span R s ≤ (adjoin R s).toSubmodule :=
  span_le.mpr subset_adjoin
#align algebra.span_le_adjoin Algebra.span_le_adjoin

/- warning: algebra.adjoin_to_submodule_le -> Algebra.adjoin_toSubmodule_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_to_submodule_le Algebra.adjoin_toSubmodule_leₓ'. -/
theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    (adjoin R s).toSubmodule ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [adjoin_eq_span, span_le]
#align algebra.adjoin_to_submodule_le Algebra.adjoin_toSubmodule_le

/- warning: algebra.adjoin_eq_span_of_subset -> Algebra.adjoin_eq_span_of_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_eq_span_of_subset Algebra.adjoin_eq_span_of_subsetₓ'. -/
theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    (adjoin R s).toSubmodule = span R s :=
  le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)
#align algebra.adjoin_eq_span_of_subset Algebra.adjoin_eq_span_of_subset

#print Algebra.adjoin_span /-
@[simp]
theorem adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R s :=
  le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)
#align algebra.adjoin_span Algebra.adjoin_span
-/

#print Algebra.adjoin_image /-
theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  le_antisymm (adjoin_le <| Set.image_subset _ subset_adjoin) <|
    Subalgebra.map_le.2 <| adjoin_le <| Set.image_subset_iff.1 subset_adjoin
#align algebra.adjoin_image Algebra.adjoin_image
-/

#print Algebra.adjoin_insert_adjoin /-
@[simp]
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  le_antisymm
    (adjoin_le
      (Set.insert_subset.mpr
        ⟨subset_adjoin (Set.mem_insert _ _), adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))
#align algebra.adjoin_insert_adjoin Algebra.adjoin_insert_adjoin
-/

/- warning: algebra.adjoin_prod_le -> Algebra.adjoin_prod_le is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_3] (s : Set.{u2} A) (t : Set.{u3} B), LE.le.{max u2 u3} (Subalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (Preorder.toHasLe.{max u2 u3} (Subalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (PartialOrder.toPreorder.{max u2 u3} (Subalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u3} (Subalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u3} (Subalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (Algebra.Subalgebra.completeLattice.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)))))) (Algebra.adjoin.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.semiring.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (Set.prod.{u2, u3} A B s t)) (Subalgebra.prod.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (Algebra.adjoin.{u1, u3} R B _inst_1 _inst_3 _inst_5 t))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Semiring.{u3} B] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_5 : Algebra.{u1, u3} R B _inst_1 _inst_3] (s : Set.{u2} A) (t : Set.{u3} B), LE.le.{max u2 u3} (Subalgebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (Preorder.toLE.{max u2 u3} (Subalgebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (PartialOrder.toPreorder.{max u2 u3} (Subalgebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (OmegaCompletePartialOrder.toPartialOrder.{max u2 u3} (Subalgebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (CompleteLattice.instOmegaCompletePartialOrder.{max u2 u3} (Subalgebra.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)) (Algebra.instCompleteLatticeSubalgebra.{u1, max u2 u3} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5)))))) (Algebra.adjoin.{u1, max u3 u2} R (Prod.{u2, u3} A B) _inst_1 (Prod.instSemiringProd.{u2, u3} A B _inst_2 _inst_3) (Prod.algebra.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5) (Set.prod.{u2, u3} A B s t)) (Subalgebra.prod.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_4 _inst_3 _inst_5 (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s) (Algebra.adjoin.{u1, u3} R B _inst_1 _inst_3 _inst_5 t))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_prod_le Algebra.adjoin_prod_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) ≤ (adjoin R s).Prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin
#align algebra.adjoin_prod_le Algebra.adjoin_prod_le

/- warning: algebra.mem_adjoin_of_map_mul -> Algebra.mem_adjoin_of_map_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.mem_adjoin_of_map_mul Algebra.mem_adjoin_of_map_mulₓ'. -/
theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) :=
  by
  refine'
    @adjoin_induction R A _ _ _ _ (fun a => f a ∈ adjoin R (f '' (s ∪ {1}))) x h
      (fun a ha => subset_adjoin ⟨a, ⟨Set.subset_union_left _ _ ha, rfl⟩⟩) (fun r => _)
      (fun y z hy hz => by simpa [hy, hz] using Subalgebra.add_mem _ hy hz) fun y z hy hz => by
      simpa [hy, hz, hf y z] using Subalgebra.mul_mem _ hy hz
  have : f 1 ∈ adjoin R (f '' (s ∪ {1})) :=
    subset_adjoin ⟨1, ⟨Set.subset_union_right _ _ <| Set.mem_singleton 1, rfl⟩⟩
  replace this := Subalgebra.smul_mem (adjoin R (f '' (s ∪ {1}))) this r
  convert this
  rw [algebra_map_eq_smul_one]
  exact f.map_smul _ _
#align algebra.mem_adjoin_of_map_mul Algebra.mem_adjoin_of_map_mul

/- warning: algebra.adjoin_inl_union_inr_eq_prod -> Algebra.adjoin_inl_union_inr_eq_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_inl_union_inr_eq_prod Algebra.adjoin_inl_union_inr_eq_prodₓ'. -/
theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) =
      (adjoin R s).Prod (adjoin R t) :=
  by
  apply le_antisymm
  ·
    simp only [adjoin_le_iff, Set.insert_subset, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin,-- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono (Set.subset_union_left _ _) Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono (Set.subset_union_right _ _) Hb
    simpa using Subalgebra.add_mem _ Ha Hb
#align algebra.adjoin_inl_union_inr_eq_prod Algebra.adjoin_inl_union_inr_eq_prod

/- warning: algebra.adjoin_comm_semiring_of_comm -> Algebra.adjoinCommSemiringOfComm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, (forall (a : A), (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) a s) -> (forall (b : A), (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) b s) -> (Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) a b) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))) b a)))) -> (CommSemiring.{u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s)))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] {s : Set.{u2} A}, (forall (a : A), (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) a s) -> (forall (b : A), (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) b s) -> (Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) a b) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) b a)))) -> (CommSemiring.{u2} (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 s))))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_comm_semiring_of_comm Algebra.adjoinCommSemiringOfCommₓ'. -/
/-- If all elements of `s : set A` commute pairwise, then `adjoin R s` is a commutative
semiring.  -/
def adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  { (adjoin R s).toSemiring with
    mul_comm := fun x y => by
      ext
      simp only [Subalgebra.coe_mul]
      exact
        adjoin_induction₂ x.prop y.prop hcomm (fun _ _ => by rw [commutes])
          (fun r x hx => commutes r x) (fun r x hx => (commutes r x).symm)
          (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun _ _ _ h₁ h₂ => by simp only [add_mul, mul_add, h₁, h₂])
          (fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc y₁, ← h₁, mul_assoc x₁])
          fun x₁ x₂ y₁ h₁ h₂ => by rw [mul_assoc x₂, ← h₂, ← mul_assoc x₂, ← h₁, ← mul_assoc] }
#align algebra.adjoin_comm_semiring_of_comm Algebra.adjoinCommSemiringOfComm

/- warning: algebra.adjoin_singleton_one -> Algebra.adjoin_singleton_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Singleton.singleton.{u2, u2} A (Set.{u2} A) (Set.hasSingleton.{u2} A) (OfNat.ofNat.{u2} A 1 (OfNat.mk.{u2} A 1 (One.one.{u2} A (AddMonoidWithOne.toOne.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))))))) (Bot.bot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toHasBot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2], Eq.{succ u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Singleton.singleton.{u2, u2} A (Set.{u2} A) (Set.instSingletonSet.{u2} A) (OfNat.ofNat.{u2} A 1 (One.toOfNat1.{u2} A (Semiring.toOne.{u2} A _inst_2))))) (Bot.bot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (CompleteLattice.toBot.{u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_singleton_one Algebra.adjoin_singleton_oneₓ'. -/
theorem adjoin_singleton_one : adjoin R ({1} : Set A) = ⊥ :=
  eq_bot_iff.2 <| adjoin_le <| Set.singleton_subset_iff.2 <| SetLike.mem_coe.2 <| one_mem _
#align algebra.adjoin_singleton_one Algebra.adjoin_singleton_one

/- warning: algebra.self_mem_adjoin_singleton -> Algebra.self_mem_adjoin_singleton is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] (x : A), Membership.Mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.hasMem.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.setLike.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Singleton.singleton.{u2, u2} A (Set.{u2} A) (Set.hasSingleton.{u2} A) x))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A _inst_1 _inst_2] (x : A), Membership.mem.{u2, u2} A (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A _inst_1 _inst_2 _inst_4)) x (Algebra.adjoin.{u1, u2} R A _inst_1 _inst_2 _inst_4 (Singleton.singleton.{u2, u2} A (Set.{u2} A) (Set.instSingletonSet.{u2} A) x))
Case conversion may be inaccurate. Consider using '#align algebra.self_mem_adjoin_singleton Algebra.self_mem_adjoin_singletonₓ'. -/
theorem self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : Set A) :=
  Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)
#align algebra.self_mem_adjoin_singleton Algebra.self_mem_adjoin_singleton

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]

variable [Algebra R A] {s t : Set A}

variable (R s t)

#print Algebra.adjoin_union_eq_adjoin_adjoin /-
theorem adjoin_union_eq_adjoin_adjoin :
    adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r, rfl⟩)
        (Set.union_subset_union_left _ fun x hxs => ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono (Set.subset_union_left _ _) x.2)
        (Set.Subset.trans (Set.subset_union_right _ _) subset_adjoin))
#align algebra.adjoin_union_eq_adjoin_adjoin Algebra.adjoin_union_eq_adjoin_adjoin
-/

/- warning: algebra.adjoin_union_coe_submodule -> Algebra.adjoin_union_coe_submodule is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_union_coe_submodule Algebra.adjoin_union_coe_submoduleₓ'. -/
theorem adjoin_union_coe_submodule :
    (adjoin R (s ∪ t)).toSubmodule = (adjoin R s).toSubmodule * (adjoin R t).toSubmodule :=
  by
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]
#align algebra.adjoin_union_coe_submodule Algebra.adjoin_union_coe_submodule

#print Algebra.adjoin_adjoin_of_tower /-
theorem adjoin_adjoin_of_tower [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (s : Set B) : adjoin A (adjoin R s : Set B) = adjoin A s :=
  by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · change adjoin R s ≤ (adjoin A s).restrictScalars R
    refine' adjoin_le _
    exact subset_adjoin
#align algebra.adjoin_adjoin_of_tower Algebra.adjoin_adjoin_of_tower
-/

variable {R}

/- warning: algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin -> Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoinₓ'. -/
theorem pow_smul_mem_of_smul_subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (r : A) (s : Set B) (B' : Subalgebra R B) (hs : r • s ⊆ B') {x : B}
    (hx : x ∈ adjoin R s) (hr : algebraMap A B r ∈ B') : ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ B' :=
  by
  change x ∈ (adjoin R s).toSubmodule at hx
  rw [adjoin_eq_span, Finsupp.mem_span_iff_total] at hx
  rcases hx with ⟨l, rfl : (l.sum fun (i : Submonoid.closure s) (c : R) => c • ↑i) = x⟩
  choose n₁ n₂ using fun x : Submonoid.closure s => Submonoid.pow_smul_mem_closure_smul r s x.Prop
  use l.support.sup n₁
  intro n hn
  rw [Finsupp.smul_sum]
  refine' B'.to_submodule.sum_mem _
  intro a ha
  have : n ≥ n₁ a := le_trans (Finset.le_sup ha) hn
  dsimp only
  rw [← tsub_add_cancel_of_le this, pow_add, ← smul_smul, ←
    IsScalarTower.algebraMap_smul A (l a) (a : B), smul_smul (r ^ n₁ a), mul_comm, ← smul_smul,
    smul_def, map_pow, IsScalarTower.algebraMap_smul]
  apply Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hr _) _
  refine' Subalgebra.smul_mem _ _ _
  change _ ∈ B'.to_submonoid
  rw [← Submonoid.closure_eq B'.to_submonoid]
  apply Submonoid.closure_mono hs (n₂ a)
#align algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin

/- warning: algebra.pow_smul_mem_adjoin_smul -> Algebra.pow_smul_mem_adjoin_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.pow_smul_mem_adjoin_smul Algebra.pow_smul_mem_adjoin_smulₓ'. -/
theorem pow_smul_mem_adjoin_smul (r : R) (s : Set A) {x : A} (hx : x ∈ adjoin R s) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ adjoin R (r • s) :=
  pow_smul_mem_of_smul_subset_of_mem_adjoin r s _ subset_adjoin hx (Subalgebra.algebraMap_mem _ _)
#align algebra.pow_smul_mem_adjoin_smul Algebra.pow_smul_mem_adjoin_smul

end CommSemiring

section Ring

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

variable {R s t}

/- warning: algebra.adjoin_int -> Algebra.adjoin_int is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Set.{u1} R), Eq.{succ u1} (Subalgebra.{0, u1} Int R Int.commSemiring (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (algebraInt.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Algebra.adjoin.{0, u1} Int R Int.commSemiring (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (algebraInt.{u1} R (CommRing.toRing.{u1} R _inst_1)) s) (subalgebraOfSubring.{u1} R (CommRing.toRing.{u1} R _inst_1) (Subring.closure.{u1} R (CommRing.toRing.{u1} R _inst_1) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Set.{u1} R), Eq.{succ u1} (Subalgebra.{0, u1} Int R Int.instCommSemiringInt (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (algebraInt.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Algebra.adjoin.{0, u1} Int R Int.instCommSemiringInt (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (algebraInt.{u1} R (CommRing.toRing.{u1} R _inst_1)) s) (subalgebraOfSubring.{u1} R (CommRing.toRing.{u1} R _inst_1) (Subring.closure.{u1} R (CommRing.toRing.{u1} R _inst_1) s))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_int Algebra.adjoin_intₓ'. -/
theorem adjoin_int (s : Set R) : adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)
#align algebra.adjoin_int Algebra.adjoin_int

/- warning: algebra.mem_adjoin_iff -> Algebra.mem_adjoin_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {s : Set.{u2} A} {x : A}, Iff (Membership.Mem.{u2, u2} A (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) A (Subalgebra.setLike.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3)) x (Algebra.adjoin.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3 s)) (Membership.Mem.{u2, u2} A (Subring.{u2} A _inst_2) (SetLike.hasMem.{u2, u2} (Subring.{u2} A _inst_2) A (Subring.setLike.{u2} A _inst_2)) x (Subring.closure.{u2} A _inst_2 (Union.union.{u2} (Set.{u2} A) (Set.hasUnion.{u2} A) (Set.range.{u2, succ u1} A R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) (fun (_x : RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) => R -> A) (RingHom.hasCoeToFun.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3))) s)))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {s : Set.{u2} A} {x : A}, Iff (Membership.mem.{u2, u2} A (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3)) x (Algebra.adjoin.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3 s)) (Membership.mem.{u2, u2} A (Subring.{u2} A _inst_2) (SetLike.instMembership.{u2, u2} (Subring.{u2} A _inst_2) A (Subring.instSetLikeSubring.{u2} A _inst_2)) x (Subring.closure.{u2} A _inst_2 (Union.union.{u2} (Set.{u2} A) (Set.instUnionSet.{u2} A) (Set.range.{u2, succ u1} A R (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => A) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) R A (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) R A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))) R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3))) s)))
Case conversion may be inaccurate. Consider using '#align algebra.mem_adjoin_iff Algebra.mem_adjoin_iffₓ'. -/
theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  ⟨fun hx =>
    Subsemiring.closure_induction hx Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ => Subring.add_mem _) fun _ _ => Subring.mul_mem _,
    suffices Subring.closure (Set.range ⇑(algebraMap R A) ∪ s) ≤ (adjoin R s).toSubring from @this x
    Subring.closure_le.2 Subsemiring.subset_closure⟩
#align algebra.mem_adjoin_iff Algebra.mem_adjoin_iff

#print Algebra.adjoin_eq_ring_closure /-
theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  Subring.ext fun x => mem_adjoin_iff
#align algebra.adjoin_eq_ring_closure Algebra.adjoin_eq_ring_closure
-/

variable (R)

/- warning: algebra.adjoin_comm_ring_of_comm -> Algebra.adjoinCommRingOfComm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {s : Set.{u2} A}, (forall (a : A), (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) a s) -> (forall (b : A), (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) b s) -> (Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) a b) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) b a)))) -> (CommRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) A (Subalgebra.setLike.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3)) (Algebra.adjoin.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3 s)))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {s : Set.{u2} A}, (forall (a : A), (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) a s) -> (forall (b : A), (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) b s) -> (Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) a b) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) b a)))) -> (CommRing.{u2} (Subtype.{succ u2} A (fun (x : A) => Membership.mem.{u2, u2} A (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3) A (Subalgebra.instSetLikeSubalgebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3)) x (Algebra.adjoin.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_3 s))))
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_comm_ring_of_comm Algebra.adjoinCommRingOfCommₓ'. -/
/-- If all elements of `s : set A` commute pairwise, then `adjoin R s` is a commutative
ring.  -/
def adjoinCommRingOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (adjoin R s) :=
  { (adjoin R s).toRing, adjoinCommSemiringOfComm R hcomm with }
#align algebra.adjoin_comm_ring_of_comm Algebra.adjoinCommRingOfComm

end Ring

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

#print AlgHom.map_adjoin /-
theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm
#align alg_hom.map_adjoin AlgHom.map_adjoin
-/

#print AlgHom.adjoin_le_equalizer /-
theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    adjoin R s ≤ φ₁.equalizer φ₂ :=
  adjoin_le h
#align alg_hom.adjoin_le_equalizer AlgHom.adjoin_le_equalizer
-/

/- warning: alg_hom.ext_of_adjoin_eq_top -> AlgHom.ext_of_adjoin_eq_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align alg_hom.ext_of_adjoin_eq_top AlgHom.ext_of_adjoin_eq_topₓ'. -/
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
  ext fun x => adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivial
#align alg_hom.ext_of_adjoin_eq_top AlgHom.ext_of_adjoin_eq_top

end AlgHom

