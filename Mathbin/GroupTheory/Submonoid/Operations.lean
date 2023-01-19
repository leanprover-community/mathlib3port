/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.submonoid.operations
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.Cancel.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.Submonoid.Basic
import Mathbin.GroupTheory.Subsemigroup.Operations

/-!
# Operations on `submonoid`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define various operations on `submonoid`s and `monoid_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `submonoid.to_add_submonoid`, `submonoid.to_add_submonoid'`, `add_submonoid.to_submonoid`,
  `add_submonoid.to_submonoid'`: convert between multiplicative and additive submonoids of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) monoid structure on a submonoid

* `submonoid.to_monoid`, `submonoid.to_comm_monoid`: a submonoid inherits a (commutative) monoid
  structure.

### Group actions by submonoids

* `submonoid.mul_action`, `submonoid.distrib_mul_action`: a submonoid inherits (distributive)
  multiplicative actions.

### Operations on submonoids

* `submonoid.comap`: preimage of a submonoid under a monoid homomorphism as a submonoid of the
  domain;
* `submonoid.map`: image of a submonoid under a monoid homomorphism as a submonoid of the codomain;
* `submonoid.prod`: product of two submonoids `s : submonoid M` and `t : submonoid N` as a submonoid
  of `M × N`;

### Monoid homomorphisms between submonoid

* `submonoid.subtype`: embedding of a submonoid into the ambient monoid.
* `submonoid.inclusion`: given two submonoids `S`, `T` such that `S ≤ T`, `S.inclusion T` is the
  inclusion of `S` into `T` as a monoid homomorphism;
* `mul_equiv.submonoid_congr`: converts a proof of `S = T` into a monoid isomorphism between `S`
  and `T`.
* `submonoid.prod_equiv`: monoid isomorphism between `s.prod t` and `s × t`;

### Operations on `monoid_hom`s

* `monoid_hom.mrange`: range of a monoid homomorphism as a submonoid of the codomain;
* `monoid_hom.mker`: kernel of a monoid homomorphism as a submonoid of the domain;
* `monoid_hom.restrict`: restrict a monoid homomorphism to a submonoid;
* `monoid_hom.cod_restrict`: restrict the codomain of a monoid homomorphism to a submonoid;
* `monoid_hom.mrange_restrict`: restrict a monoid homomorphism to its range;

## Tags

submonoid, range, product, map, comap
-/


variable {M N P : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

/- warning: submonoid.to_add_submonoid -> Submonoid.toAddSubmonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], OrderIso.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], OrderIso.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align submonoid.to_add_submonoid Submonoid.toAddSubmonoidₓ'. -/
/-- Submonoids of monoid `M` are isomorphic to additive submonoids of `additive M`. -/
@[simps]
def Submonoid.toAddSubmonoid : Submonoid M ≃o AddSubmonoid (Additive M)
    where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun _ _ => S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun _ _ => S.add_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align submonoid.to_add_submonoid Submonoid.toAddSubmonoid

/- warning: add_submonoid.to_submonoid' -> AddSubmonoid.toSubmonoid' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], OrderIso.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))))) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], OrderIso.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align add_submonoid.to_submonoid' AddSubmonoid.toSubmonoid'ₓ'. -/
/-- Additive submonoids of an additive monoid `additive M` are isomorphic to submonoids of `M`. -/
abbrev AddSubmonoid.toSubmonoid' : AddSubmonoid (Additive M) ≃o Submonoid M :=
  Submonoid.toAddSubmonoid.symm
#align add_submonoid.to_submonoid' AddSubmonoid.toSubmonoid'

/- warning: submonoid.to_add_submonoid_closure -> Submonoid.toAddSubmonoid_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} M), Eq.{succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) (fun (_x : RelIso.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) (LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))))))) => (Submonoid.{u1} M _inst_1) -> (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))) (RelIso.hasCoeToFun.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) (LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))))))) (Submonoid.toAddSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 S)) (AddSubmonoid.closure.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1) (Set.preimage.{u1, u1} (Additive.{u1} M) M (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} M) M) => (Additive.{u1} M) -> M) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.toMul.{u1} M)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Submonoid.{u1} M _inst_1) => AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))) (Submonoid.{u1} M _inst_1) (fun (_x : Submonoid.{u1} M _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Submonoid.{u1} M _inst_1) => AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))) (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))) (RelEmbedding.toEmbedding.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (Submonoid.{u1} M _inst_1) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (Submonoid.toAddSubmonoid.{u1} M _inst_1))) (Submonoid.closure.{u1} M _inst_1 S)) (AddSubmonoid.closure.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1) (Set.preimage.{u1, u1} (Additive.{u1} M) M (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) (fun (_x : Additive.{u1} M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u1} M) => M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) M (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) M (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Additive.{u1} M) M))) (Additive.toMul.{u1} M)) S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_add_submonoid_closure Submonoid.toAddSubmonoid_closureₓ'. -/
theorem Submonoid.toAddSubmonoid_closure (S : Set M) :
    (Submonoid.closure S).toAddSubmonoid = AddSubmonoid.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid.le_symm_apply.1 <| Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)
#align submonoid.to_add_submonoid_closure Submonoid.toAddSubmonoid_closure

/- warning: add_submonoid.to_submonoid'_closure -> AddSubmonoid.toSubmonoid'_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} (Additive.{u1} M)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1))))) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) (fun (_x : RelIso.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))))) => (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) -> (Submonoid.{u1} M _inst_1)) (RelIso.hasCoeToFun.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))))) (AddSubmonoid.toSubmonoid'.{u1} M _inst_1) (AddSubmonoid.closure.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1) S)) (Submonoid.closure.{u1} M _inst_1 (Set.preimage.{u1, u1} M (Multiplicative.{u1} M) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) (fun (_x : Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) => M -> (Multiplicative.{u1} M)) (Equiv.hasCoeToFun.{succ u1, succ u1} M (Multiplicative.{u1} M)) (Multiplicative.ofAdd.{u1} M)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} (Additive.{u1} M)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => Submonoid.{u1} M _inst_1) (AddSubmonoid.closure.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1) S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1)) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (fun (_x : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => Submonoid.{u1} M _inst_1) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1)) (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1))) (RelEmbedding.toEmbedding.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Submonoid.{u1} M _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) => LE.le.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (AddSubmonoid.toSubmonoid'.{u1} M _inst_1))) (AddSubmonoid.closure.{u1} (Additive.{u1} M) (Additive.addZeroClass.{u1} M _inst_1) S)) (Submonoid.closure.{u1} M _inst_1 (Set.preimage.{u1, u1} M (Multiplicative.{u1} M) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Multiplicative.{u1} M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (Multiplicative.{u1} M) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (Multiplicative.{u1} M) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} M (Multiplicative.{u1} M)))) (Multiplicative.ofAdd.{u1} M)) S))
Case conversion may be inaccurate. Consider using '#align add_submonoid.to_submonoid'_closure AddSubmonoid.toSubmonoid'_closureₓ'. -/
theorem AddSubmonoid.toSubmonoid'_closure (S : Set (Additive M)) :
    (AddSubmonoid.closure S).toSubmonoid' = Submonoid.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid'.le_symm_apply.1 <|
      AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)
#align add_submonoid.to_submonoid'_closure AddSubmonoid.toSubmonoid'_closure

end

section

variable {A : Type _} [AddZeroClass A]

/- warning: add_submonoid.to_submonoid -> AddSubmonoid.toSubmonoid is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A], OrderIso.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4)))) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A], OrderIso.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4))))) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))))))
Case conversion may be inaccurate. Consider using '#align add_submonoid.to_submonoid AddSubmonoid.toSubmonoidₓ'. -/
/-- Additive submonoids of an additive monoid `A` are isomorphic to
multiplicative submonoids of `multiplicative A`. -/
@[simps]
def AddSubmonoid.toSubmonoid : AddSubmonoid A ≃o Submonoid (Multiplicative A)
    where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      one_mem' := S.zero_mem'
      mul_mem' := fun _ _ => S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      zero_mem' := S.one_mem'
      add_mem' := fun _ _ => S.mul_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align add_submonoid.to_submonoid AddSubmonoid.toSubmonoid

/- warning: submonoid.to_add_submonoid' -> Submonoid.toAddSubmonoid' is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A], OrderIso.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A], OrderIso.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4)))))
Case conversion may be inaccurate. Consider using '#align submonoid.to_add_submonoid' Submonoid.toAddSubmonoid'ₓ'. -/
/-- Submonoids of a monoid `multiplicative A` are isomorphic to additive submonoids of `A`. -/
abbrev Submonoid.toAddSubmonoid' : Submonoid (Multiplicative A) ≃o AddSubmonoid A :=
  AddSubmonoid.toSubmonoid.symm
#align submonoid.to_add_submonoid' Submonoid.toAddSubmonoid'

/- warning: add_submonoid.to_submonoid_closure -> AddSubmonoid.toSubmonoid_closure is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A] (S : Set.{u1} A), Eq.{succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4)))) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) (fun (_x : RelIso.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4))))) (LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))))))) => (AddSubmonoid.{u1} A _inst_4) -> (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))) (RelIso.hasCoeToFun.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4))))) (LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))))))) (AddSubmonoid.toSubmonoid.{u1} A _inst_4) (AddSubmonoid.closure.{u1} A _inst_4 S)) (Submonoid.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4) (Set.preimage.{u1, u1} (Multiplicative.{u1} A) A (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) => (Multiplicative.{u1} A) -> A) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.toAdd.{u1} A)) S))
but is expected to have type
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A] (S : Set.{u1} A), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubmonoid.{u1} A _inst_4) => Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.closure.{u1} A _inst_4 S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))) (AddSubmonoid.{u1} A _inst_4) (fun (_x : AddSubmonoid.{u1} A _inst_4) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubmonoid.{u1} A _inst_4) => Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))) (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))) (RelEmbedding.toEmbedding.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubmonoid.{u1} A _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubmonoid.{u1} A _inst_4) => LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (AddSubmonoid.{u1} A _inst_4) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubmonoid.{u1} A _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubmonoid.{u1} A _inst_4) => LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (AddSubmonoid.toSubmonoid.{u1} A _inst_4))) (AddSubmonoid.closure.{u1} A _inst_4 S)) (Submonoid.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4) (Set.preimage.{u1, u1} (Multiplicative.{u1} A) A (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) (fun (_x : Multiplicative.{u1} A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u1} A) => A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) A (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) A (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} A) A))) (Multiplicative.toAdd.{u1} A)) S))
Case conversion may be inaccurate. Consider using '#align add_submonoid.to_submonoid_closure AddSubmonoid.toSubmonoid_closureₓ'. -/
theorem AddSubmonoid.toSubmonoid_closure (S : Set A) :
    (AddSubmonoid.closure S).toSubmonoid = Submonoid.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubmonoid.toSubmonoid.to_galois_connection.l_le <|
      AddSubmonoid.closure_le.2 Submonoid.subset_closure)
    (Submonoid.closure_le.2 AddSubmonoid.subset_closure)
#align add_submonoid.to_submonoid_closure AddSubmonoid.toSubmonoid_closure

/- warning: submonoid.to_add_submonoid'_closure -> Submonoid.toAddSubmonoid'_closure is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A] (S : Set.{u1} (Multiplicative.{u1} A)), Eq.{succ u1} (AddSubmonoid.{u1} A _inst_4) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4))))) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4))))) (fun (_x : RelIso.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) (LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4)))))) => (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) -> (AddSubmonoid.{u1} A _inst_4)) (RelIso.hasCoeToFun.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) (LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (SetLike.partialOrder.{u1, u1} (AddSubmonoid.{u1} A _inst_4) A (AddSubmonoid.setLike.{u1} A _inst_4)))))) (Submonoid.toAddSubmonoid'.{u1} A _inst_4) (Submonoid.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4) S)) (AddSubmonoid.closure.{u1} A _inst_4 (Set.preimage.{u1, u1} A (Additive.{u1} A) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) (fun (_x : Equiv.{succ u1, succ u1} A (Additive.{u1} A)) => A -> (Additive.{u1} A)) (Equiv.hasCoeToFun.{succ u1, succ u1} A (Additive.{u1} A)) (Additive.ofMul.{u1} A)) S))
but is expected to have type
  forall {A : Type.{u1}} [_inst_4 : AddZeroClass.{u1} A] (S : Set.{u1} (Multiplicative.{u1} A)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => AddSubmonoid.{u1} A _inst_4) (Submonoid.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4) S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4)) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (fun (_x : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => AddSubmonoid.{u1} A _inst_4) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4)) (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4))) (RelEmbedding.toEmbedding.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubmonoid.{u1} A _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubmonoid.{u1} A _inst_4) => LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (AddSubmonoid.{u1} A _inst_4) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) => LE.le.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Preorder.toLE.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)) (Submonoid.instCompleteLatticeSubmonoid.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubmonoid.{u1} A _inst_4) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubmonoid.{u1} A _inst_4) => LE.le.{u1} (AddSubmonoid.{u1} A _inst_4) (Preorder.toLE.{u1} (AddSubmonoid.{u1} A _inst_4) (PartialOrder.toPreorder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubmonoid.{u1} A _inst_4) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubmonoid.{u1} A _inst_4) (AddSubmonoid.instCompleteLatticeAddSubmonoid.{u1} A _inst_4))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (Submonoid.toAddSubmonoid'.{u1} A _inst_4))) (Submonoid.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mulOneClass.{u1} A _inst_4) S)) (AddSubmonoid.closure.{u1} A _inst_4 (Set.preimage.{u1, u1} A (Additive.{u1} A) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (fun (_x : A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Additive.{u1} A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (Additive.{u1} A) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (Additive.{u1} A) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} A (Additive.{u1} A)))) (Additive.ofMul.{u1} A)) S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_add_submonoid'_closure Submonoid.toAddSubmonoid'_closureₓ'. -/
theorem Submonoid.toAddSubmonoid'_closure (S : Set (Multiplicative A)) :
    (Submonoid.closure S).toAddSubmonoid' = AddSubmonoid.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (Submonoid.toAddSubmonoid'.to_galois_connection.l_le <|
      Submonoid.closure_le.2 AddSubmonoid.subset_closure)
    (AddSubmonoid.closure_le.2 Submonoid.subset_closure)
#align submonoid.to_add_submonoid'_closure Submonoid.toAddSubmonoid'_closure

end

namespace Submonoid

variable {F : Type _} [mc : MonoidHomClass F M N]

open Set

/-!
### `comap` and `map`
-/


include mc

#print Submonoid.comap /-
/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive
      "The preimage of an `add_submonoid` along an `add_monoid` homomorphism is an\n`add_submonoid`."]
def comap (f : F) (S : Submonoid N) : Submonoid M
    where
  carrier := f ⁻¹' S
  one_mem' := show f 1 ∈ S by rw [map_one] <;> exact S.one_mem
  mul_mem' a b ha hb := show f (a * b) ∈ S by rw [map_mul] <;> exact S.mul_mem ha hb
#align submonoid.comap Submonoid.comap
#align add_submonoid.comap AddSubmonoid.comap
-/

/- warning: submonoid.coe_comap -> Submonoid.coe_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (S : Submonoid.{u2} N _inst_2) (f : F), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) (Set.preimage.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submonoid.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (S : Submonoid.{u3} N _inst_2) (f : F), Eq.{succ u2} (Set.{u2} M) (SetLike.coe.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)) (Set.preimage.{u2, u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f) (SetLike.coe.{u3, u3} (Submonoid.{u3} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u3} N _inst_2) S))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_comap Submonoid.coe_comapₓ'. -/
@[simp, to_additive]
theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl
#align submonoid.coe_comap Submonoid.coe_comap
#align add_submonoid.coe_comap AddSubmonoid.coe_comap

/- warning: submonoid.mem_comap -> Submonoid.mem_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {S : Submonoid.{u2} N _inst_2} {f : F} {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {S : Submonoid.{u3} N _inst_2} {f : F} {x : M}, Iff (Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)) (Membership.mem.{u3, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Submonoid.{u3} N _inst_2) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u3} N _inst_2)) (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f x) S)
Case conversion may be inaccurate. Consider using '#align submonoid.mem_comap Submonoid.mem_comapₓ'. -/
@[simp, to_additive]
theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align submonoid.mem_comap Submonoid.mem_comap
#align add_submonoid.mem_comap AddSubmonoid.mem_comap

omit mc

#print Submonoid.comap_comap /-
@[to_additive]
theorem comap_comap (S : Submonoid P) (g : N →* P) (f : M →* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align submonoid.comap_comap Submonoid.comap_comap
#align add_submonoid.comap_comap AddSubmonoid.comap_comap
-/

#print Submonoid.comap_id /-
@[simp, to_additive]
theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S :=
  ext (by simp)
#align submonoid.comap_id Submonoid.comap_id
#align add_submonoid.comap_id AddSubmonoid.comap_id
-/

include mc

#print Submonoid.map /-
/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive
      "The image of an `add_submonoid` along an `add_monoid` homomorphism is\nan `add_submonoid`."]
def map (f : F) (S : Submonoid M) : Submonoid N
    where
  carrier := f '' S
  one_mem' := ⟨1, S.one_mem, map_one f⟩
  mul_mem' := by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩;
    exact ⟨x * y, S.mul_mem hx hy, by rw [map_mul] <;> rfl⟩
#align submonoid.map Submonoid.map
#align add_submonoid.map AddSubmonoid.map
-/

/- warning: submonoid.coe_map -> Submonoid.coe_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) (S : Submonoid.{u1} M _inst_1), Eq.{succ u2} (Set.{u2} N) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submonoid.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) (Set.image.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F) (S : Submonoid.{u3} M _inst_1), Eq.{succ u2} (Set.{u2} N) (SetLike.coe.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S)) (Set.image.{u3, u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f) (SetLike.coe.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1) S))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_map Submonoid.coe_mapₓ'. -/
@[simp, to_additive]
theorem coe_map (f : F) (S : Submonoid M) : (S.map f : Set N) = f '' S :=
  rfl
#align submonoid.coe_map Submonoid.coe_map
#align add_submonoid.coe_map AddSubmonoid.coe_map

/- warning: submonoid.mem_map -> Submonoid.mem_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F} {S : Submonoid.{u1} M _inst_1} {y : N}, Iff (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) y (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) (Exists.{succ u1} M (fun (x : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (fun (H : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) => Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) y)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F} {S : Submonoid.{u3} M _inst_1} {y : N}, Iff (Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) y (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S)) (Exists.{succ u3} M (fun (x : M) => And (Membership.mem.{u3, u3} M (Submonoid.{u3} M _inst_1) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1)) x S) (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) a) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f x) y)))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_map Submonoid.mem_mapₓ'. -/
@[simp, to_additive]
theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex
#align submonoid.mem_map Submonoid.mem_map
#align add_submonoid.mem_map AddSubmonoid.mem_map

/- warning: submonoid.mem_map_of_mem -> Submonoid.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) {S : Submonoid.{u1} M _inst_1} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) -> (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F) {S : Submonoid.{u3} M _inst_1} {x : M}, (Membership.mem.{u3, u3} M (Submonoid.{u3} M _inst_1) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1)) x S) -> (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f x) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_map_of_mem Submonoid.mem_map_of_memₓ'. -/
@[to_additive]
theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align submonoid.mem_map_of_mem Submonoid.mem_map_of_mem
#align add_submonoid.mem_map_of_mem AddSubmonoid.mem_map_of_mem

/- warning: submonoid.apply_coe_mem_map -> Submonoid.apply_coe_mem_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) (S : Submonoid.{u1} M _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S), Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) x)) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F) (S : Submonoid.{u3} M _inst_1) (x : Subtype.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Submonoid.{u3} M _inst_1) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1)) x S)), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) (Subtype.val.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Set.{u3} M) (Set.instMembershipSet.{u3} M) x (SetLike.coe.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1) S)) x)) (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f (Subtype.val.{succ u3} M (fun (x : M) => Membership.mem.{u3, u3} M (Set.{u3} M) (Set.instMembershipSet.{u3} M) x (SetLike.coe.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1) S)) x)) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S)
Case conversion may be inaccurate. Consider using '#align submonoid.apply_coe_mem_map Submonoid.apply_coe_mem_mapₓ'. -/
@[to_additive]
theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop
#align submonoid.apply_coe_mem_map Submonoid.apply_coe_mem_map
#align add_submonoid.apply_coe_mem_map AddSubmonoid.apply_coe_mem_map

omit mc

/- warning: submonoid.map_map -> Submonoid.map_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (S : Submonoid.{u1} M _inst_1) (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u3} (Submonoid.{u3} P _inst_3) (Submonoid.map.{u2, u3, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u2, u3} N P _inst_2 _inst_3) g (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) (Submonoid.map.{u1, u3, max u3 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) S)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : MulOneClass.{u2} P] (S : Submonoid.{u1} M _inst_1) (g : MonoidHom.{u3, u2} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u3} M N _inst_1 _inst_2), Eq.{succ u2} (Submonoid.{u2} P _inst_3) (Submonoid.map.{u3, u2, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u3, u2} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u3, u2} N P _inst_2 _inst_3) g (Submonoid.map.{u1, u3, max u1 u3} M N _inst_1 _inst_2 (MonoidHom.{u1, u3} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u3} M N _inst_1 _inst_2) f S)) (Submonoid.map.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 g f) S)
Case conversion may be inaccurate. Consider using '#align submonoid.map_map Submonoid.map_mapₓ'. -/
@[to_additive]
theorem map_map (g : N →* P) (f : M →* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align submonoid.map_map Submonoid.map_map
#align add_submonoid.map_map AddSubmonoid.map_map

include mc

/- warning: submonoid.mem_map_iff_mem -> Submonoid.mem_map_iff_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall {S : Submonoid.{u1} M _inst_1} {x : M}, Iff (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (forall {S : Submonoid.{u3} M _inst_1} {x : M}, Iff (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f x) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S)) (Membership.mem.{u3, u3} M (Submonoid.{u3} M _inst_1) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_map_iff_mem Submonoid.mem_map_iff_memₓ'. -/
@[to_additive]
theorem mem_map_iff_mem {f : F} (hf : Function.Injective f) {S : Submonoid M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image
#align submonoid.mem_map_iff_mem Submonoid.mem_map_iff_mem
#align add_submonoid.mem_map_iff_mem AddSubmonoid.mem_map_iff_mem

/- warning: submonoid.map_le_iff_le_comap -> Submonoid.map_le_iff_le_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F} {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u2} N _inst_2}, Iff (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) T) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F} {S : Submonoid.{u3} M _inst_1} {T : Submonoid.{u2} N _inst_2}, Iff (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2))))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S) T) (LE.le.{u3} (Submonoid.{u3} M _inst_1) (Preorder.toLE.{u3} (Submonoid.{u3} M _inst_1) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1))))) S (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f T))
Case conversion may be inaccurate. Consider using '#align submonoid.map_le_iff_le_comap Submonoid.map_le_iff_le_comapₓ'. -/
@[to_additive]
theorem map_le_iff_le_comap {f : F} {S : Submonoid M} {T : Submonoid N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align submonoid.map_le_iff_le_comap Submonoid.map_le_iff_le_comap
#align add_submonoid.map_le_iff_le_comap AddSubmonoid.map_le_iff_le_comap

/- warning: submonoid.gc_map_comap -> Submonoid.gc_map_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), GaloisConnection.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F), GaloisConnection.{u3, u2} (Submonoid.{u3} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f)
Case conversion may be inaccurate. Consider using '#align submonoid.gc_map_comap Submonoid.gc_map_comapₓ'. -/
@[to_additive]
theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap
#align submonoid.gc_map_comap Submonoid.gc_map_comap
#align add_submonoid.gc_map_comap AddSubmonoid.gc_map_comap

/- warning: submonoid.map_le_of_le_comap -> Submonoid.map_le_of_le_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {T : Submonoid.{u2} N _inst_2} {f : F}, (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T)) -> (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) T)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] (S : Submonoid.{u2} M _inst_1) {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {T : Submonoid.{u3} N _inst_2} {f : F}, (LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) S (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T)) -> (LE.le.{u3} (Submonoid.{u3} N _inst_2) (Preorder.toLE.{u3} (Submonoid.{u3} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2))))) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) T)
Case conversion may be inaccurate. Consider using '#align submonoid.map_le_of_le_comap Submonoid.map_le_of_le_comapₓ'. -/
@[to_additive]
theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align submonoid.map_le_of_le_comap Submonoid.map_le_of_le_comap
#align add_submonoid.map_le_of_le_comap AddSubmonoid.map_le_of_le_comap

/- warning: submonoid.le_comap_of_map_le -> Submonoid.le_comap_of_map_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {T : Submonoid.{u2} N _inst_2} {f : F}, (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) T) -> (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] (S : Submonoid.{u2} M _inst_1) {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {T : Submonoid.{u3} N _inst_2} {f : F}, (LE.le.{u3} (Submonoid.{u3} N _inst_2) (Preorder.toLE.{u3} (Submonoid.{u3} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2))))) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) T) -> (LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) S (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T))
Case conversion may be inaccurate. Consider using '#align submonoid.le_comap_of_map_le Submonoid.le_comap_of_map_leₓ'. -/
@[to_additive]
theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align submonoid.le_comap_of_map_le Submonoid.le_comap_of_map_le
#align add_submonoid.le_comap_of_map_le AddSubmonoid.le_comap_of_map_le

/- warning: submonoid.le_comap_map -> Submonoid.le_comap_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u3} M _inst_1) {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, LE.le.{u3} (Submonoid.{u3} M _inst_1) (Preorder.toLE.{u3} (Submonoid.{u3} M _inst_1) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1))))) S (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S))
Case conversion may be inaccurate. Consider using '#align submonoid.le_comap_map Submonoid.le_comap_mapₓ'. -/
@[to_additive]
theorem le_comap_map {f : F} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align submonoid.le_comap_map Submonoid.le_comap_map
#align add_submonoid.le_comap_map AddSubmonoid.le_comap_map

/- warning: submonoid.map_comap_le -> Submonoid.map_comap_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {S : Submonoid.{u2} N _inst_2} {f : F}, LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) S
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {S : Submonoid.{u3} N _inst_2} {f : F}, LE.le.{u3} (Submonoid.{u3} N _inst_2) (Preorder.toLE.{u3} (Submonoid.{u3} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2))))) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)) S
Case conversion may be inaccurate. Consider using '#align submonoid.map_comap_le Submonoid.map_comap_leₓ'. -/
@[to_additive]
theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align submonoid.map_comap_le Submonoid.map_comap_le
#align add_submonoid.map_comap_le AddSubmonoid.map_comap_le

/- warning: submonoid.monotone_map -> Submonoid.monotone_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, Monotone.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, Monotone.{u3, u2} (Submonoid.{u3} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f)
Case conversion may be inaccurate. Consider using '#align submonoid.monotone_map Submonoid.monotone_mapₓ'. -/
@[to_additive]
theorem monotone_map {f : F} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align submonoid.monotone_map Submonoid.monotone_map
#align add_submonoid.monotone_map AddSubmonoid.monotone_map

/- warning: submonoid.monotone_comap -> Submonoid.monotone_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, Monotone.{u2, u1} (Submonoid.{u2} N _inst_2) (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, Monotone.{u3, u2} (Submonoid.{u3} N _inst_2) (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1)))) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f)
Case conversion may be inaccurate. Consider using '#align submonoid.monotone_comap Submonoid.monotone_comapₓ'. -/
@[to_additive]
theorem monotone_comap {f : F} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align submonoid.monotone_comap Submonoid.monotone_comap
#align add_submonoid.monotone_comap AddSubmonoid.monotone_comap

/- warning: submonoid.map_comap_map -> Submonoid.map_comap_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] (S : Submonoid.{u2} M _inst_1) {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, Eq.{succ u3} (Submonoid.{u3} N _inst_2) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S))) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)
Case conversion may be inaccurate. Consider using '#align submonoid.map_comap_map Submonoid.map_comap_mapₓ'. -/
@[simp, to_additive]
theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align submonoid.map_comap_map Submonoid.map_comap_map
#align add_submonoid.map_comap_map AddSubmonoid.map_comap_map

/- warning: submonoid.comap_map_comap -> Submonoid.comap_map_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {S : Submonoid.{u2} N _inst_2} {f : F}, Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {S : Submonoid.{u3} N _inst_2} {f : F}, Eq.{succ u2} (Submonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S))) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)
Case conversion may be inaccurate. Consider using '#align submonoid.comap_map_comap Submonoid.comap_map_comapₓ'. -/
@[simp, to_additive]
theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align submonoid.comap_map_comap Submonoid.comap_map_comap
#align add_submonoid.comap_map_comap AddSubmonoid.comap_map_comap

/- warning: submonoid.map_sup -> Submonoid.map_sup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (S : Submonoid.{u1} M _inst_1) (T : Submonoid.{u1} M _inst_1) (f : F), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) S T)) (HasSup.sup.{u2} (Submonoid.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (S : Submonoid.{u3} M _inst_1) (T : Submonoid.{u3} M _inst_1) (f : F), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u3} (Submonoid.{u3} M _inst_1) (SemilatticeSup.toHasSup.{u3} (Submonoid.{u3} M _inst_1) (Lattice.toSemilatticeSup.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toLattice.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)))) S T)) (HasSup.sup.{u2} (Submonoid.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f T))
Case conversion may be inaccurate. Consider using '#align submonoid.map_sup Submonoid.map_supₓ'. -/
@[to_additive]
theorem map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align submonoid.map_sup Submonoid.map_sup
#align add_submonoid.map_sup AddSubmonoid.map_sup

/- warning: submonoid.map_supr -> Submonoid.map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Sort.{u4}} (f : F) (s : ι -> (Submonoid.{u1} M _inst_1)), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (supᵢ.{u1, u4} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι s)) (supᵢ.{u2, u4} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2))) ι (fun (i : ι) => Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (s i)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {ι : Sort.{u4}} (f : F) (s : ι -> (Submonoid.{u3} M _inst_1)), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (supᵢ.{u3, u4} (Submonoid.{u3} M _inst_1) (CompleteLattice.toSupSet.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)) ι s)) (supᵢ.{u2, u4} (Submonoid.{u2} N _inst_2) (CompleteLattice.toSupSet.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)) ι (fun (i : ι) => Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (s i)))
Case conversion may be inaccurate. Consider using '#align submonoid.map_supr Submonoid.map_supᵢₓ'. -/
@[to_additive]
theorem map_supᵢ {ι : Sort _} (f : F) (s : ι → Submonoid M) : (supᵢ s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_supr
#align submonoid.map_supr Submonoid.map_supᵢ
#align add_submonoid.map_supr AddSubmonoid.map_supᵢ

/- warning: submonoid.comap_inf -> Submonoid.comap_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (S : Submonoid.{u2} N _inst_2) (T : Submonoid.{u2} N _inst_2) (f : F), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) S T)) (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (S : Submonoid.{u3} N _inst_2) (T : Submonoid.{u3} N _inst_2) (f : F), Eq.{succ u2} (Submonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instHasInfSubmonoid.{u3} N _inst_2) S T)) (HasInf.inf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instHasInfSubmonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_inf Submonoid.comap_infₓ'. -/
@[to_additive]
theorem comap_inf (S T : Submonoid N) (f : F) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_inf
#align submonoid.comap_inf Submonoid.comap_inf
#align add_submonoid.comap_inf AddSubmonoid.comap_inf

/- warning: submonoid.comap_infi -> Submonoid.comap_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Sort.{u4}} (f : F) (s : ι -> (Submonoid.{u2} N _inst_2)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (infᵢ.{u2, u4} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) ι s)) (infᵢ.{u1, u4} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) ι (fun (i : ι) => Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (s i)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {ι : Sort.{u4}} (f : F) (s : ι -> (Submonoid.{u3} N _inst_2)), Eq.{succ u2} (Submonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (infᵢ.{u3, u4} (Submonoid.{u3} N _inst_2) (Submonoid.instInfSetSubmonoid.{u3} N _inst_2) ι s)) (infᵢ.{u2, u4} (Submonoid.{u2} M _inst_1) (Submonoid.instInfSetSubmonoid.{u2} M _inst_1) ι (fun (i : ι) => Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (s i)))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_infi Submonoid.comap_infᵢₓ'. -/
@[to_additive]
theorem comap_infᵢ {ι : Sort _} (f : F) (s : ι → Submonoid N) :
    (infᵢ s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_infi
#align submonoid.comap_infi Submonoid.comap_infᵢ
#align add_submonoid.comap_infi AddSubmonoid.comap_infᵢ

/- warning: submonoid.map_bot -> Submonoid.map_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Submonoid.{u3} N _inst_2) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1))) (Bot.bot.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instBotSubmonoid.{u3} N _inst_2))
Case conversion may be inaccurate. Consider using '#align submonoid.map_bot Submonoid.map_botₓ'. -/
@[simp, to_additive]
theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align submonoid.map_bot Submonoid.map_bot
#align add_submonoid.map_bot AddSubmonoid.map_bot

/- warning: submonoid.comap_top -> Submonoid.comap_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Submonoid.{u3} M _inst_1) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instTopSubmonoid.{u2} N _inst_2))) (Top.top.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instTopSubmonoid.{u3} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_top Submonoid.comap_topₓ'. -/
@[simp, to_additive]
theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align submonoid.comap_top Submonoid.comap_top
#align add_submonoid.comap_top AddSubmonoid.comap_top

omit mc

#print Submonoid.map_id /-
@[simp, to_additive]
theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align submonoid.map_id Submonoid.map_id
#align add_submonoid.map_id AddSubmonoid.map_id
-/

section GaloisCoinsertion

variable {ι : Type _} {f : F} (hf : Function.Injective f)

include hf

/- warning: submonoid.gci_map_comap -> Submonoid.gciMapComap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (GaloisCoinsertion.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (FunLike.coe.{succ u3, succ u1, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc)) f)) -> (GaloisCoinsertion.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.gci_map_comap Submonoid.gciMapComapₓ'. -/
/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align submonoid.gci_map_comap Submonoid.gciMapComap
#align add_submonoid.gci_map_comap AddSubmonoid.gciMapComap

/- warning: submonoid.comap_map_eq_of_injective -> Submonoid.comap_map_eq_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) S)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} M _inst_1), Eq.{succ u3} (Submonoid.{u3} M _inst_1) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S)) S)
Case conversion may be inaccurate. Consider using '#align submonoid.comap_map_eq_of_injective Submonoid.comap_map_eq_of_injectiveₓ'. -/
@[to_additive]
theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align submonoid.comap_map_eq_of_injective Submonoid.comap_map_eq_of_injective
#align add_submonoid.comap_map_eq_of_injective AddSubmonoid.comap_map_eq_of_injective

/- warning: submonoid.comap_surjective_of_injective -> Submonoid.comap_surjective_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (Function.Surjective.{succ u2, succ u1} (Submonoid.{u2} N _inst_2) (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (Function.Surjective.{succ u3, succ u2} (Submonoid.{u3} N _inst_2) (Submonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_surjective_of_injective Submonoid.comap_surjective_of_injectiveₓ'. -/
@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align submonoid.comap_surjective_of_injective Submonoid.comap_surjective_of_injective
#align add_submonoid.comap_surjective_of_injective AddSubmonoid.comap_surjective_of_injective

/- warning: submonoid.map_injective_of_injective -> Submonoid.map_injective_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (Function.Injective.{succ u1, succ u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (Function.Injective.{succ u3, succ u2} (Submonoid.{u3} M _inst_1) (Submonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.map_injective_of_injective Submonoid.map_injective_of_injectiveₓ'. -/
@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align submonoid.map_injective_of_injective Submonoid.map_injective_of_injective
#align add_submonoid.map_injective_of_injective AddSubmonoid.map_injective_of_injective

/- warning: submonoid.comap_inf_map_of_injective -> Submonoid.comap_inf_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u1} M _inst_1) (T : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))) (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) S T))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} M _inst_1) (T : Submonoid.{u3} M _inst_1), Eq.{succ u3} (Submonoid.{u3} M _inst_1) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instHasInfSubmonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f T))) (HasInf.inf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instHasInfSubmonoid.{u3} M _inst_1) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_inf_map_of_injective Submonoid.comap_inf_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_inf_map_of_injective (S T : Submonoid M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align submonoid.comap_inf_map_of_injective Submonoid.comap_inf_map_of_injective
#align add_submonoid.comap_inf_map_of_injective AddSubmonoid.comap_inf_map_of_injective

/- warning: submonoid.comap_infi_map_of_injective -> Submonoid.comap_infᵢ_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Type.{u4}} {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : ι -> (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (infᵢ.{u2, succ u4} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) ι (fun (i : ι) => Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (S i)))) (infᵢ.{u1, succ u4} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) ι S))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u4} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u2}} [mc : MonoidHomClass.{u2, u4, u3} F M N _inst_1 _inst_2] {ι : Type.{u1}} {f : F}, (Function.Injective.{succ u4, succ u3} M N (FunLike.coe.{succ u2, succ u4, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u4, u3} F M N (MulOneClass.toMul.{u4} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u2, u4, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : ι -> (Submonoid.{u4} M _inst_1)), Eq.{succ u4} (Submonoid.{u4} M _inst_1) (Submonoid.comap.{u4, u3, u2} M N _inst_1 _inst_2 F mc f (infᵢ.{u3, succ u1} (Submonoid.{u3} N _inst_2) (Submonoid.instInfSetSubmonoid.{u3} N _inst_2) ι (fun (i : ι) => Submonoid.map.{u4, u3, u2} M N _inst_1 _inst_2 F mc f (S i)))) (infᵢ.{u4, succ u1} (Submonoid.{u4} M _inst_1) (Submonoid.instInfSetSubmonoid.{u4} M _inst_1) ι S))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_infi_map_of_injective Submonoid.comap_infᵢ_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_infᵢ_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = infᵢ S :=
  (gciMapComap hf).u_infi_l _
#align submonoid.comap_infi_map_of_injective Submonoid.comap_infᵢ_map_of_injective
#align add_submonoid.comap_infi_map_of_injective AddSubmonoid.comap_infᵢ_map_of_injective

/- warning: submonoid.comap_sup_map_of_injective -> Submonoid.comap_sup_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u1} M _inst_1) (T : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u2} (Submonoid.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))) (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} M _inst_1) (T : Submonoid.{u3} M _inst_1), Eq.{succ u3} (Submonoid.{u3} M _inst_1) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u2} (Submonoid.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f T))) (HasSup.sup.{u3} (Submonoid.{u3} M _inst_1) (SemilatticeSup.toHasSup.{u3} (Submonoid.{u3} M _inst_1) (Lattice.toSemilatticeSup.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toLattice.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_sup_map_of_injective Submonoid.comap_sup_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_sup_map_of_injective (S T : Submonoid M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align submonoid.comap_sup_map_of_injective Submonoid.comap_sup_map_of_injective
#align add_submonoid.comap_sup_map_of_injective AddSubmonoid.comap_sup_map_of_injective

/- warning: submonoid.comap_supr_map_of_injective -> Submonoid.comap_supᵢ_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Type.{u4}} {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : ι -> (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (supᵢ.{u2, succ u4} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2))) ι (fun (i : ι) => Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (S i)))) (supᵢ.{u1, succ u4} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι S))
but is expected to have type
  forall {M : Type.{u4}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u4} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u2}} [mc : MonoidHomClass.{u2, u4, u3} F M N _inst_1 _inst_2] {ι : Type.{u1}} {f : F}, (Function.Injective.{succ u4, succ u3} M N (FunLike.coe.{succ u2, succ u4, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u4, u3} F M N (MulOneClass.toMul.{u4} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u2, u4, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : ι -> (Submonoid.{u4} M _inst_1)), Eq.{succ u4} (Submonoid.{u4} M _inst_1) (Submonoid.comap.{u4, u3, u2} M N _inst_1 _inst_2 F mc f (supᵢ.{u3, succ u1} (Submonoid.{u3} N _inst_2) (CompleteLattice.toSupSet.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2)) ι (fun (i : ι) => Submonoid.map.{u4, u3, u2} M N _inst_1 _inst_2 F mc f (S i)))) (supᵢ.{u4, succ u1} (Submonoid.{u4} M _inst_1) (CompleteLattice.toSupSet.{u4} (Submonoid.{u4} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u4} M _inst_1)) ι S))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_supr_map_of_injective Submonoid.comap_supᵢ_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_supᵢ_map_of_injective (S : ι → Submonoid M) : (⨆ i, (S i).map f).comap f = supᵢ S :=
  (gciMapComap hf).u_supr_l _
#align submonoid.comap_supr_map_of_injective Submonoid.comap_supᵢ_map_of_injective
#align add_submonoid.comap_supr_map_of_injective AddSubmonoid.comap_supᵢ_map_of_injective

/- warning: submonoid.map_le_map_iff_of_injective -> Submonoid.map_le_map_iff_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, Iff (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T)) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (forall {S : Submonoid.{u3} M _inst_1} {T : Submonoid.{u3} M _inst_1}, Iff (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2))))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f T)) (LE.le.{u3} (Submonoid.{u3} M _inst_1) (Preorder.toLE.{u3} (Submonoid.{u3} M _inst_1) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1))))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.map_le_map_iff_of_injective Submonoid.map_le_map_iff_of_injectiveₓ'. -/
@[to_additive]
theorem map_le_map_iff_of_injective {S T : Submonoid M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align submonoid.map_le_map_iff_of_injective Submonoid.map_le_map_iff_of_injective
#align add_submonoid.map_le_map_iff_of_injective AddSubmonoid.map_le_map_iff_of_injective

/- warning: submonoid.map_strict_mono_of_injective -> Submonoid.map_strict_mono_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (StrictMono.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (StrictMono.{u3, u2} (Submonoid.{u3} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.map_strict_mono_of_injective Submonoid.map_strict_mono_of_injectiveₓ'. -/
@[to_additive]
theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l
#align submonoid.map_strict_mono_of_injective Submonoid.map_strict_mono_of_injective
#align add_submonoid.map_strict_mono_of_injective AddSubmonoid.map_strict_mono_of_injective

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : F} (hf : Function.Surjective f)

include hf

/- warning: submonoid.gi_map_comap -> Submonoid.giMapComap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (GaloisInsertion.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{succ u3, succ u1, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc)) f)) -> (GaloisInsertion.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u2} N _inst_2)))) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.gi_map_comap Submonoid.giMapComapₓ'. -/
/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align submonoid.gi_map_comap Submonoid.giMapComap
#align add_submonoid.gi_map_comap AddSubmonoid.giMapComap

/- warning: submonoid.map_comap_eq_of_surjective -> Submonoid.map_comap_eq_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u2} N _inst_2), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S)) S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} N _inst_2), Eq.{succ u3} (Submonoid.{u3} N _inst_2) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S)) S)
Case conversion may be inaccurate. Consider using '#align submonoid.map_comap_eq_of_surjective Submonoid.map_comap_eq_of_surjectiveₓ'. -/
@[to_additive]
theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align submonoid.map_comap_eq_of_surjective Submonoid.map_comap_eq_of_surjective
#align add_submonoid.map_comap_eq_of_surjective AddSubmonoid.map_comap_eq_of_surjective

/- warning: submonoid.map_surjective_of_surjective -> Submonoid.map_surjective_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (Function.Surjective.{succ u1, succ u2} (Submonoid.{u1} M _inst_1) (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (Function.Surjective.{succ u3, succ u2} (Submonoid.{u3} M _inst_1) (Submonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.map_surjective_of_surjective Submonoid.map_surjective_of_surjectiveₓ'. -/
@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align submonoid.map_surjective_of_surjective Submonoid.map_surjective_of_surjective
#align add_submonoid.map_surjective_of_surjective AddSubmonoid.map_surjective_of_surjective

/- warning: submonoid.comap_injective_of_surjective -> Submonoid.comap_injective_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (Function.Injective.{succ u2, succ u1} (Submonoid.{u2} N _inst_2) (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (Function.Injective.{succ u3, succ u2} (Submonoid.{u3} N _inst_2) (Submonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_injective_of_surjective Submonoid.comap_injective_of_surjectiveₓ'. -/
@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align submonoid.comap_injective_of_surjective Submonoid.comap_injective_of_surjective
#align add_submonoid.comap_injective_of_surjective AddSubmonoid.comap_injective_of_surjective

/- warning: submonoid.map_inf_comap_of_surjective -> Submonoid.map_inf_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u2} N _inst_2) (T : Submonoid.{u2} N _inst_2), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))) (HasInf.inf.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} N _inst_2) (T : Submonoid.{u3} N _inst_2), Eq.{succ u3} (Submonoid.{u3} N _inst_2) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (HasInf.inf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instHasInfSubmonoid.{u2} M _inst_1) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T))) (HasInf.inf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instHasInfSubmonoid.{u3} N _inst_2) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.map_inf_comap_of_surjective Submonoid.map_inf_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_inf_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align submonoid.map_inf_comap_of_surjective Submonoid.map_inf_comap_of_surjective
#align add_submonoid.map_inf_comap_of_surjective AddSubmonoid.map_inf_comap_of_surjective

/- warning: submonoid.map_infi_comap_of_surjective -> Submonoid.map_infᵢ_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Type.{u4}} {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : ι -> (Submonoid.{u2} N _inst_2)), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (infᵢ.{u1, succ u4} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) ι (fun (i : ι) => Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (S i)))) (infᵢ.{u2, succ u4} (Submonoid.{u2} N _inst_2) (Submonoid.hasInf.{u2} N _inst_2) ι S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u4} N] {F : Type.{u2}} [mc : MonoidHomClass.{u2, u3, u4} F M N _inst_1 _inst_2] {ι : Type.{u1}} {f : F}, (Function.Surjective.{succ u3, succ u4} M N (FunLike.coe.{succ u2, succ u3, succ u4} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u3, u4} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u4} N _inst_2) (MonoidHomClass.toMulHomClass.{u2, u3, u4} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : ι -> (Submonoid.{u4} N _inst_2)), Eq.{succ u4} (Submonoid.{u4} N _inst_2) (Submonoid.map.{u3, u4, u2} M N _inst_1 _inst_2 F mc f (infᵢ.{u3, succ u1} (Submonoid.{u3} M _inst_1) (Submonoid.instInfSetSubmonoid.{u3} M _inst_1) ι (fun (i : ι) => Submonoid.comap.{u3, u4, u2} M N _inst_1 _inst_2 F mc f (S i)))) (infᵢ.{u4, succ u1} (Submonoid.{u4} N _inst_2) (Submonoid.instInfSetSubmonoid.{u4} N _inst_2) ι S))
Case conversion may be inaccurate. Consider using '#align submonoid.map_infi_comap_of_surjective Submonoid.map_infᵢ_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_infᵢ_comap_of_surjective (S : ι → Submonoid N) : (⨅ i, (S i).comap f).map f = infᵢ S :=
  (giMapComap hf).l_infi_u _
#align submonoid.map_infi_comap_of_surjective Submonoid.map_infᵢ_comap_of_surjective
#align add_submonoid.map_infi_comap_of_surjective AddSubmonoid.map_infᵢ_comap_of_surjective

/- warning: submonoid.map_sup_comap_of_surjective -> Submonoid.map_sup_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : Submonoid.{u2} N _inst_2) (T : Submonoid.{u2} N _inst_2), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T))) (HasSup.sup.{u2} (Submonoid.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2)))) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : Submonoid.{u3} N _inst_2) (T : Submonoid.{u3} N _inst_2), Eq.{succ u3} (Submonoid.{u3} N _inst_2) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (HasSup.sup.{u2} (Submonoid.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Submonoid.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1)))) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T))) (HasSup.sup.{u3} (Submonoid.{u3} N _inst_2) (SemilatticeSup.toHasSup.{u3} (Submonoid.{u3} N _inst_2) (Lattice.toSemilatticeSup.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toLattice.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2)))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.map_sup_comap_of_surjective Submonoid.map_sup_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_sup_comap_of_surjective (S T : Submonoid N) : (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align submonoid.map_sup_comap_of_surjective Submonoid.map_sup_comap_of_surjective
#align add_submonoid.map_sup_comap_of_surjective AddSubmonoid.map_sup_comap_of_surjective

/- warning: submonoid.map_supr_comap_of_surjective -> Submonoid.map_supᵢ_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {ι : Type.{u4}} {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall (S : ι -> (Submonoid.{u2} N _inst_2)), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (supᵢ.{u1, succ u4} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (S i)))) (supᵢ.{u2, succ u4} (Submonoid.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Submonoid.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.completeLattice.{u2} N _inst_2))) ι S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u4} N] {F : Type.{u2}} [mc : MonoidHomClass.{u2, u3, u4} F M N _inst_1 _inst_2] {ι : Type.{u1}} {f : F}, (Function.Surjective.{succ u3, succ u4} M N (FunLike.coe.{succ u2, succ u3, succ u4} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u2, u3, u4} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u4} N _inst_2) (MonoidHomClass.toMulHomClass.{u2, u3, u4} F M N _inst_1 _inst_2 mc)) f)) -> (forall (S : ι -> (Submonoid.{u4} N _inst_2)), Eq.{succ u4} (Submonoid.{u4} N _inst_2) (Submonoid.map.{u3, u4, u2} M N _inst_1 _inst_2 F mc f (supᵢ.{u3, succ u1} (Submonoid.{u3} M _inst_1) (CompleteLattice.toSupSet.{u3} (Submonoid.{u3} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u3} M _inst_1)) ι (fun (i : ι) => Submonoid.comap.{u3, u4, u2} M N _inst_1 _inst_2 F mc f (S i)))) (supᵢ.{u4, succ u1} (Submonoid.{u4} N _inst_2) (CompleteLattice.toSupSet.{u4} (Submonoid.{u4} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u4} N _inst_2)) ι S))
Case conversion may be inaccurate. Consider using '#align submonoid.map_supr_comap_of_surjective Submonoid.map_supᵢ_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_supᵢ_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = supᵢ S :=
  (giMapComap hf).l_supr_u _
#align submonoid.map_supr_comap_of_surjective Submonoid.map_supᵢ_comap_of_surjective
#align add_submonoid.map_supr_comap_of_surjective AddSubmonoid.map_supᵢ_comap_of_surjective

/- warning: submonoid.comap_le_comap_iff_of_surjective -> Submonoid.comap_le_comap_iff_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (forall {S : Submonoid.{u2} N _inst_2} {T : Submonoid.{u2} N _inst_2}, Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f T)) (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (forall {S : Submonoid.{u3} N _inst_2} {T : Submonoid.{u3} N _inst_2}, Iff (LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f S) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f T)) (LE.le.{u3} (Submonoid.{u3} N _inst_2) (Preorder.toLE.{u3} (Submonoid.{u3} N _inst_2) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2))))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_le_comap_iff_of_surjective Submonoid.comap_le_comap_iff_of_surjectiveₓ'. -/
@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Submonoid N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align submonoid.comap_le_comap_iff_of_surjective Submonoid.comap_le_comap_iff_of_surjective
#align add_submonoid.comap_le_comap_iff_of_surjective AddSubmonoid.comap_le_comap_iff_of_surjective

/- warning: submonoid.comap_strict_mono_of_surjective -> Submonoid.comap_strict_mono_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (StrictMono.{u2, u1} (Submonoid.{u2} N _inst_2) (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f)) -> (StrictMono.{u3, u2} (Submonoid.{u3} N _inst_2) (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u3} (Submonoid.{u3} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u3} (Submonoid.{u3} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u3} N _inst_2)))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1)))) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align submonoid.comap_strict_mono_of_surjective Submonoid.comap_strict_mono_of_surjectiveₓ'. -/
@[to_additive]
theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u
#align submonoid.comap_strict_mono_of_surjective Submonoid.comap_strict_mono_of_surjective
#align add_submonoid.comap_strict_mono_of_surjective AddSubmonoid.comap_strict_mono_of_surjective

end GaloisInsertion

end Submonoid

namespace OneMemClass

variable {A M₁ : Type _} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

include hA

#print OneMemClass.one /-
/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance one : One S' :=
  ⟨⟨1, OneMemClass.one_mem S'⟩⟩
#align one_mem_class.has_one OneMemClass.one
#align zero_mem_class.has_zero ZeroMemClass.zero
-/

#print OneMemClass.coe_one /-
@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : S') : M₁) = 1 :=
  rfl
#align one_mem_class.coe_one OneMemClass.coe_one
#align zero_mem_class.coe_zero ZeroMemClass.coe_zero
-/

variable {S'}

#print OneMemClass.coe_eq_one /-
@[simp, norm_cast, to_additive]
theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 :=
  (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)
#align one_mem_class.coe_eq_one OneMemClass.coe_eq_one
#align zero_mem_class.coe_eq_zero ZeroMemClass.coe_eq_zero
-/

variable (S')

#print OneMemClass.one_def /-
@[to_additive]
theorem one_def : (1 : S') = ⟨1, OneMemClass.one_mem S'⟩ :=
  rfl
#align one_mem_class.one_def OneMemClass.one_def
#align zero_mem_class.zero_def ZeroMemClass.zero_def
-/

end OneMemClass

namespace SubmonoidClass

variable {A : Type _} [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

#print AddSubmonoidClass.nSMul /-
/-- An `add_submonoid` of an `add_monoid` inherits a scalar multiplication. -/
instance AddSubmonoidClass.nSMul {M} [AddMonoid M] {A : Type _} [SetLike A M]
    [AddSubmonoidClass A M] (S : A) : SMul ℕ S :=
  ⟨fun n a => ⟨n • a.1, nsmul_mem a.2 n⟩⟩
#align add_submonoid_class.has_nsmul AddSubmonoidClass.nSMul
-/

#print SubmonoidClass.nPow /-
/-- A submonoid of a monoid inherits a power operator. -/
instance nPow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : Pow S ℕ :=
  ⟨fun a n => ⟨a.1 ^ n, pow_mem a.2 n⟩⟩
#align submonoid_class.has_pow SubmonoidClass.nPow
-/

attribute [to_additive] SubmonoidClass.nPow

/- warning: submonoid_class.coe_pow -> SubmonoidClass.coe_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Monoid.{u1} M] {A : Type.{u2}} [_inst_6 : SetLike.{u2, u1} A M] [_inst_7 : SubmonoidClass.{u2, u1} A M (Monoid.toMulOneClass.{u1} M _inst_5) _inst_6] {S : A} (x : coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) (n : Nat), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S))))) (HPow.hPow.{u1, 0, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) Nat (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) (instHPow.{u1, 0} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) Nat (SubmonoidClass.nPow.{u1, u2} M _inst_5 A _inst_6 _inst_7 S)) x n)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_5)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_6) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S))))) x) n)
but is expected to have type
  forall {M : Type.{u2}} [_inst_5 : Monoid.{u2} M] {A : Type.{u1}} [_inst_6 : SetLike.{u1, u2} A M] [_inst_7 : SubmonoidClass.{u1, u2} A M (Monoid.toMulOneClass.{u2} M _inst_5) _inst_6] {S : A} (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) (n : Nat), Eq.{succ u2} M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_6 S)) (HPow.hPow.{u2, 0, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) Nat (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) (instHPow.{u2, 0} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) Nat (SubmonoidClass.nPow.{u2, u1} M _inst_5 A _inst_6 _inst_7 S)) x n)) (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_5)) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_6 S)) x) n)
Case conversion may be inaccurate. Consider using '#align submonoid_class.coe_pow SubmonoidClass.coe_powₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_pow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : (↑(x ^ n) : M) = ↑x ^ n :=
  rfl
#align submonoid_class.coe_pow SubmonoidClass.coe_pow
#align add_submonoid_class.coe_smul AddSubmonoidClass.coe_smul

/- warning: submonoid_class.mk_pow -> SubmonoidClass.mk_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Monoid.{u1} M] {A : Type.{u2}} [_inst_6 : SetLike.{u2, u1} A M] [_inst_7 : SubmonoidClass.{u2, u1} A M (Monoid.toMulOneClass.{u1} M _inst_5) _inst_6] {S : A} (x : M) (hx : Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S) (n : Nat), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S)) (HPow.hPow.{u1, 0, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S)) Nat (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S)) (instHPow.{u1, 0} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S)) Nat (SubmonoidClass.nPow.{u1, u2} M _inst_5 A _inst_6 _inst_7 S)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S) x hx) n) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_6) x S) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_5)) x n) (pow_mem.{u1, u2} M _inst_5 A _inst_6 _inst_7 S x hx n))
but is expected to have type
  forall {M : Type.{u2}} [_inst_5 : Monoid.{u2} M] {A : Type.{u1}} [_inst_6 : SetLike.{u1, u2} A M] [_inst_7 : SubmonoidClass.{u1, u2} A M (Monoid.toMulOneClass.{u2} M _inst_5) _inst_6] {S : A} (x : M) (hx : Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S) (n : Nat), Eq.{succ u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) (HPow.hPow.{u2, 0, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) Nat (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) (instHPow.{u2, 0} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S)) Nat (SubmonoidClass.nPow.{u2, u1} M _inst_5 A _inst_6 _inst_7 S)) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S) x hx) n) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_6) x S) (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_5)) x n) (pow_mem.{u1, u2} M A _inst_5 _inst_6 _inst_7 S x hx n))
Case conversion may be inaccurate. Consider using '#align submonoid_class.mk_pow SubmonoidClass.mk_powₓ'. -/
@[simp, to_additive]
theorem mk_pow {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} (x : M)
    (hx : x ∈ S) (n : ℕ) : (⟨x, hx⟩ : S) ^ n = ⟨x ^ n, pow_mem hx n⟩ :=
  rfl
#align submonoid_class.mk_pow SubmonoidClass.mk_pow
#align add_submonoid_class.mk_smul AddSubmonoidClass.mk_smul

#print SubmonoidClass.toMulOneClass /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `add_submonoid` of an unital additive magma inherits an unital additive magma\nstructure."]
instance (priority := 75) toMulOneClass {M : Type _} [MulOneClass M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : MulOneClass S :=
  Subtype.coe_injective.MulOneClass _ rfl fun _ _ => rfl
#align submonoid_class.to_mul_one_class SubmonoidClass.toMulOneClass
#align add_submonoid_class.to_add_zero_class AddSubmonoidClass.toAddZeroClass
-/

#print SubmonoidClass.toMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance (priority := 75) toMonoid {M : Type _} [Monoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : Monoid S :=
  Subtype.coe_injective.Monoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_monoid SubmonoidClass.toMonoid
#align add_submonoid_class.to_add_monoid AddSubmonoidClass.toAddMonoid
-/

#print SubmonoidClass.toCommMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance (priority := 75) toCommMonoid {M} [CommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : CommMonoid S :=
  Subtype.coe_injective.CommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_comm_monoid SubmonoidClass.toCommMonoid
#align add_submonoid_class.to_add_comm_monoid AddSubmonoidClass.toAddCommMonoid
-/

#print SubmonoidClass.toOrderedCommMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance (priority := 75) toOrderedCommMonoid {M} [OrderedCommMonoid M] {A : Type _} [SetLike A M]
    [SubmonoidClass A M] (S : A) : OrderedCommMonoid S :=
  Subtype.coe_injective.OrderedCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_ordered_comm_monoid SubmonoidClass.toOrderedCommMonoid
#align add_submonoid_class.to_ordered_add_comm_monoid AddSubmonoidClass.toOrderedAddCommMonoid
-/

#print SubmonoidClass.toLinearOrderedCommMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is\na `linear_ordered_add_comm_monoid`."]
instance (priority := 75) toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] {A : Type _}
    [SetLike A M] [SubmonoidClass A M] (S : A) : LinearOrderedCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_linear_ordered_comm_monoid SubmonoidClass.toLinearOrderedCommMonoid
#align add_submonoid_class.to_linear_ordered_add_comm_monoid AddSubmonoidClass.toLinearOrderedAddCommMonoid
-/

#print SubmonoidClass.toOrderedCancelCommMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is\nan `ordered_cancel_add_comm_monoid`."]
instance (priority := 75) toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] {A : Type _}
    [SetLike A M] [SubmonoidClass A M] (S : A) : OrderedCancelCommMonoid S :=
  Subtype.coe_injective.OrderedCancelCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_ordered_cancel_comm_monoid SubmonoidClass.toOrderedCancelCommMonoid
#align add_submonoid_class.to_ordered_cancel_add_comm_monoid AddSubmonoidClass.toOrderedCancelAddCommMonoid
-/

#print SubmonoidClass.toLinearOrderedCancelCommMonoid /-
-- Prefer subclasses of `monoid` over subclasses of `submonoid_class`.
/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
@[to_additive
      "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is\na `linear_ordered_cancel_add_comm_monoid`."]
instance (priority := 75) toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M]
    {A : Type _} [SetLike A M] [SubmonoidClass A M] (S : A) : LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid_class.to_linear_ordered_cancel_comm_monoid SubmonoidClass.toLinearOrderedCancelCommMonoid
#align add_submonoid_class.to_linear_ordered_cancel_add_comm_monoid AddSubmonoidClass.toLinearOrderedCancelAddCommMonoid
-/

include hA

#print SubmonoidClass.Subtype /-
/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def Subtype : S' →* M :=
  ⟨coe, rfl, fun _ _ => rfl⟩
#align submonoid_class.subtype SubmonoidClass.Subtype
#align add_submonoid_class.subtype AddSubmonoidClass.Subtype
-/

/- warning: submonoid_class.coe_subtype -> SubmonoidClass.coe_subtype is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [hA : SubmonoidClass.{u2, u1} A M _inst_1 _inst_4] (S' : A), Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 A _inst_4 hA S') _inst_1) => (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') -> M) (SubmonoidClass.Subtype.{u1, u2} M _inst_1 A _inst_4 hA S')) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 A _inst_4 hA S') _inst_1) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 A _inst_4 hA S') _inst_1) => (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') -> M) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 A _inst_4 hA S') _inst_1) (SubmonoidClass.Subtype.{u1, u2} M _inst_1 A _inst_4 hA S')) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_4) x S'))))))
but is expected to have type
  forall {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {A : Type.{u1}} [_inst_4 : SetLike.{u1, u2} A M] [hA : SubmonoidClass.{u1, u2} A M _inst_1 _inst_4] (S' : A), Eq.{succ u2} (forall (a : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) => M) a) (FunLike.coe.{succ u2, succ u2, succ u2} (MonoidHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S') _inst_1) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) => M) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MonoidHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S') _inst_1) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (MulOneClass.toMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S')) (MulOneClass.toMul.{u2} M _inst_1) (MonoidHomClass.toMulHomClass.{u2, u2, u2} (MonoidHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S') _inst_1) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S') _inst_1 (MonoidHom.monoidHomClass.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S')) M (SubmonoidClass.toMulOneClass.{u2, u1} M _inst_1 A _inst_4 hA S') _inst_1))) (SubmonoidClass.Subtype.{u2, u1} M _inst_1 A _inst_4 hA S')) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_4) x S'))
Case conversion may be inaccurate. Consider using '#align submonoid_class.coe_subtype SubmonoidClass.coe_subtypeₓ'. -/
@[simp, to_additive]
theorem coe_subtype : (SubmonoidClass.Subtype S' : S' → M) = coe :=
  rfl
#align submonoid_class.coe_subtype SubmonoidClass.coe_subtype
#align add_submonoid_class.coe_subtype AddSubmonoidClass.coe_subtype

end SubmonoidClass

namespace Submonoid

/- warning: submonoid.has_mul -> Submonoid.mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Mul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Mul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.has_mul Submonoid.mulₓ'. -/
/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an addition."]
instance mul : Mul S :=
  ⟨fun a b => ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩
#align submonoid.has_mul Submonoid.mul
#align add_submonoid.has_add AddSubmonoid.add

/- warning: submonoid.has_one -> Submonoid.one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), One.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), One.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.has_one Submonoid.oneₓ'. -/
/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits a zero."]
instance one : One S :=
  ⟨⟨_, S.one_mem⟩⟩
#align submonoid.has_one Submonoid.one
#align add_submonoid.has_zero AddSubmonoid.zero

/- warning: submonoid.coe_mul -> Submonoid.coe_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (Submonoid.mul.{u1} M _inst_1 S)) x y)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) y))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (y : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)), Eq.{succ u1} M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.mul.{u1} M _inst_1 S)) x y)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) x) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) y))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_mul Submonoid.coe_mulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y :=
  rfl
#align submonoid.coe_mul Submonoid.coe_mul
#align add_submonoid.coe_add AddSubmonoid.coe_add

/- warning: submonoid.coe_one -> Submonoid.coe_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (Submonoid.one.{u1} M _inst_1 S))))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) (OfNat.ofNat.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.one.{u1} M _inst_1 S)))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_one Submonoid.coe_oneₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : S) : M) = 1 :=
  rfl
#align submonoid.coe_one Submonoid.coe_one
#align add_submonoid.coe_zero AddSubmonoid.coe_zero

/- warning: submonoid.mk_mul_mk -> Submonoid.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : M) (y : M) (hx : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (hy : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y S), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)) (Submonoid.mul.{u1} M _inst_1 S)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) x hx) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) y hy)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) (Submonoid.mul_mem.{u1} M _inst_1 S x y hx hy))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : M) (y : M) (hx : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (hy : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y S), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.mul.{u1} M _inst_1 S)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) x hx) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) y hy)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) (Submonoid.mul_mem.{u1} M _inst_1 S x y hx hy))
Case conversion may be inaccurate. Consider using '#align submonoid.mk_mul_mk Submonoid.mk_mul_mkₓ'. -/
@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S) (hy : y ∈ S) :
    (⟨x, hx⟩ : S) * ⟨y, hy⟩ = ⟨x * y, S.mul_mem hx hy⟩ :=
  rfl
#align submonoid.mk_mul_mk Submonoid.mk_mul_mk
#align add_submonoid.mk_add_mk AddSubmonoid.mk_add_mk

/- warning: submonoid.mul_def -> Submonoid.mul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (Submonoid.mul.{u1} M _inst_1 S)) x y) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) y)) (Submonoid.mul_mem.{u1} M _inst_1 S ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) y) (Subtype.property.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) x) (Subtype.property.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) y)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (y : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.mul.{u1} M _inst_1 S)) x y) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) x) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) y)) (Submonoid.mul_mem.{u1} M _inst_1 S (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) x) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) y) (Subtype.property.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) x) (Subtype.property.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) y)))
Case conversion may be inaccurate. Consider using '#align submonoid.mul_def Submonoid.mul_defₓ'. -/
@[to_additive]
theorem mul_def (x y : S) : x * y = ⟨x * y, S.mul_mem x.2 y.2⟩ :=
  rfl
#align submonoid.mul_def Submonoid.mul_def
#align add_submonoid.add_def AddSubmonoid.add_def

/- warning: submonoid.one_def -> Submonoid.one_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (Submonoid.one.{u1} M _inst_1 S)))) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (Submonoid.one_mem.{u1} M _inst_1 S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (OfNat.ofNat.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.one.{u1} M _inst_1 S))) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (Submonoid.one_mem.{u1} M _inst_1 S))
Case conversion may be inaccurate. Consider using '#align submonoid.one_def Submonoid.one_defₓ'. -/
@[to_additive]
theorem one_def : (1 : S) = ⟨1, S.one_mem⟩ :=
  rfl
#align submonoid.one_def Submonoid.one_def
#align add_submonoid.zero_def AddSubmonoid.zero_def

/- warning: submonoid.to_mul_one_class -> Submonoid.toMulOneClass is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_4), MulOneClass.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_4) M (Submonoid.setLike.{u1} M _inst_4)) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_4), MulOneClass.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_4) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_4) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_4)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_mul_one_class Submonoid.toMulOneClassₓ'. -/
/-- A submonoid of a unital magma inherits a unital magma structure. -/
@[to_additive
      "An `add_submonoid` of an unital additive magma inherits an unital additive magma\nstructure."]
instance toMulOneClass {M : Type _} [MulOneClass M] (S : Submonoid M) : MulOneClass S :=
  Subtype.coe_injective.MulOneClass coe rfl fun _ _ => rfl
#align submonoid.to_mul_one_class Submonoid.toMulOneClass
#align add_submonoid.to_add_zero_class AddSubmonoid.toAddZeroClass

/- warning: submonoid.pow_mem -> Submonoid.pow_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) x S) -> (forall (n : Nat), Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_4)) x n) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) x S) -> (forall (n : Nat), Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_4)) x n) S)
Case conversion may be inaccurate. Consider using '#align submonoid.pow_mem Submonoid.pow_memₓ'. -/
@[to_additive]
protected theorem pow_mem {M : Type _} [Monoid M] (S : Submonoid M) {x : M} (hx : x ∈ S) (n : ℕ) :
    x ^ n ∈ S :=
  pow_mem hx n
#align submonoid.pow_mem Submonoid.pow_mem
#align add_submonoid.smul_mem AddSubmonoid.smul_mem

/- warning: submonoid.coe_pow clashes with [anonymous] -> [anonymous]
warning: submonoid.coe_pow -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_4 : Monoid.{u_1} M] {S : Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)} (x : coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) (n : Nat), Eq.{succ u_1} M ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (HasLiftT.mk.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (CoeTCₓ.coe.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (coeBase.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (coeSubtype.{succ u_1} M (fun (x : M) => Membership.Mem.{u_1, u_1} M (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) (SetLike.hasMem.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) x S))))) (HPow.hPow.{u_1, 0, u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) Nat (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) (instHPow.{u_1, 0} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) Nat (SubmonoidClass.nPow.{u_1, u_1} M _inst_4 (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) (Submonoid.submonoid_class.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) S)) x n)) (HPow.hPow.{u_1, 0, u_1} M Nat M (instHPow.{u_1, 0} M Nat (Monoid.Pow.{u_1} M _inst_4)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (HasLiftT.mk.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (CoeTCₓ.coe.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (coeBase.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) Type.{u_1} (SetLike.hasCoeToSort.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) S) M (coeSubtype.{succ u_1} M (fun (x : M) => Membership.Mem.{u_1, u_1} M (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) (SetLike.hasMem.{u_1, u_1} (Submonoid.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4)) M (Submonoid.setLike.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_4))) x S))))) x) n)
but is expected to have type
  forall {M : Type.{u}} {_inst_4 : Type.{v}}, (Nat -> M -> _inst_4) -> Nat -> (List.{u} M) -> (List.{v} _inst_4)
Case conversion may be inaccurate. Consider using '#align submonoid.coe_pow [anonymous]ₓ'. -/
@[simp, norm_cast, to_additive]
theorem [anonymous] {M : Type _} [Monoid M] {S : Submonoid M} (x : S) (n : ℕ) :
    ↑(x ^ n) = (x ^ n : M) :=
  rfl
#align submonoid.coe_pow [anonymous]

/- warning: submonoid.to_monoid -> Submonoid.toMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)), Monoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)), Monoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_monoid Submonoid.toMonoidₓ'. -/
/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive "An `add_submonoid` of an `add_monoid` inherits an `add_monoid`\nstructure."]
instance toMonoid {M : Type _} [Monoid M] (S : Submonoid M) : Monoid S :=
  Subtype.coe_injective.Monoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_monoid Submonoid.toMonoid
#align add_submonoid.to_add_monoid AddSubmonoid.toAddMonoid

/- warning: submonoid.to_comm_monoid -> Submonoid.toCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))), CommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))), CommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_comm_monoid Submonoid.toCommMonoidₓ'. -/
/-- A submonoid of a `comm_monoid` is a `comm_monoid`. -/
@[to_additive "An `add_submonoid` of an `add_comm_monoid` is\nan `add_comm_monoid`."]
instance toCommMonoid {M} [CommMonoid M] (S : Submonoid M) : CommMonoid S :=
  Subtype.coe_injective.CommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_comm_monoid Submonoid.toCommMonoid
#align add_submonoid.to_add_comm_monoid AddSubmonoid.toAddCommMonoid

/- warning: submonoid.to_ordered_comm_monoid -> Submonoid.toOrderedCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : OrderedCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))), OrderedCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4))))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : OrderedCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))), OrderedCommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M _inst_4))))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_ordered_comm_monoid Submonoid.toOrderedCommMonoidₓ'. -/
/-- A submonoid of an `ordered_comm_monoid` is an `ordered_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of an `ordered_add_comm_monoid` is\nan `ordered_add_comm_monoid`."]
instance toOrderedCommMonoid {M} [OrderedCommMonoid M] (S : Submonoid M) : OrderedCommMonoid S :=
  Subtype.coe_injective.OrderedCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_ordered_comm_monoid Submonoid.toOrderedCommMonoid
#align add_submonoid.to_ordered_add_comm_monoid AddSubmonoid.toOrderedAddCommMonoid

/- warning: submonoid.to_linear_ordered_comm_monoid -> Submonoid.toLinearOrderedCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : LinearOrderedCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} M _inst_4))))), LinearOrderedCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} M _inst_4))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} M _inst_4))))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} M _inst_4)))))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : LinearOrderedCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (LinearOrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))), LinearOrderedCommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (LinearOrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (LinearOrderedCommMonoid.toCommMonoid.{u1} M _inst_4)))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (LinearOrderedCommMonoid.toCommMonoid.{u1} M _inst_4))))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_linear_ordered_comm_monoid Submonoid.toLinearOrderedCommMonoidₓ'. -/
/-- A submonoid of a `linear_ordered_comm_monoid` is a `linear_ordered_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of a `linear_ordered_add_comm_monoid` is\na `linear_ordered_add_comm_monoid`."]
instance toLinearOrderedCommMonoid {M} [LinearOrderedCommMonoid M] (S : Submonoid M) :
    LinearOrderedCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_linear_ordered_comm_monoid Submonoid.toLinearOrderedCommMonoid
#align add_submonoid.to_linear_ordered_add_comm_monoid AddSubmonoid.toLinearOrderedAddCommMonoid

/- warning: submonoid.to_ordered_cancel_comm_monoid -> Submonoid.toOrderedCancelCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : OrderedCancelCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))), OrderedCancelCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4))))))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : OrderedCancelCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))), OrderedCancelCommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4)))))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_4))))))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_ordered_cancel_comm_monoid Submonoid.toOrderedCancelCommMonoidₓ'. -/
/-- A submonoid of an `ordered_cancel_comm_monoid` is an `ordered_cancel_comm_monoid`. -/
@[to_additive
      "An `add_submonoid` of an `ordered_cancel_add_comm_monoid` is\nan `ordered_cancel_add_comm_monoid`."]
instance toOrderedCancelCommMonoid {M} [OrderedCancelCommMonoid M] (S : Submonoid M) :
    OrderedCancelCommMonoid S :=
  Subtype.coe_injective.OrderedCancelCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_ordered_cancel_comm_monoid Submonoid.toOrderedCancelCommMonoid
#align add_submonoid.to_ordered_cancel_add_comm_monoid AddSubmonoid.toOrderedCancelAddCommMonoid

/- warning: submonoid.to_linear_ordered_cancel_comm_monoid -> Submonoid.toLinearOrderedCancelCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : LinearOrderedCancelCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))), LinearOrderedCancelCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4)))))))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : LinearOrderedCancelCommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))), LinearOrderedCancelCommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4))))))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_4)))))))) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.to_linear_ordered_cancel_comm_monoid Submonoid.toLinearOrderedCancelCommMonoidₓ'. -/
/-- A submonoid of a `linear_ordered_cancel_comm_monoid` is a `linear_ordered_cancel_comm_monoid`.
-/
@[to_additive
      "An `add_submonoid` of a `linear_ordered_cancel_add_comm_monoid` is\na `linear_ordered_cancel_add_comm_monoid`."]
instance toLinearOrderedCancelCommMonoid {M} [LinearOrderedCancelCommMonoid M] (S : Submonoid M) :
    LinearOrderedCancelCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submonoid.to_linear_ordered_cancel_comm_monoid Submonoid.toLinearOrderedCancelCommMonoid
#align add_submonoid.to_linear_ordered_cancel_add_comm_monoid AddSubmonoid.toLinearOrderedCancelAddCommMonoid

/- warning: submonoid.subtype -> Submonoid.subtype is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1
Case conversion may be inaccurate. Consider using '#align submonoid.subtype Submonoid.subtypeₓ'. -/
/-- The natural monoid hom from a submonoid of monoid `M` to `M`. -/
@[to_additive "The natural monoid hom from an `add_submonoid` of `add_monoid` `M` to `M`."]
def subtype : S →* M :=
  ⟨coe, rfl, fun _ _ => rfl⟩
#align submonoid.subtype Submonoid.subtype
#align add_submonoid.subtype AddSubmonoid.subtype

/- warning: submonoid.coe_subtype -> Submonoid.coe_subtype is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} ((coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) -> M) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (fun (_x : MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) => (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) -> M) (MonoidHom.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (Submonoid.subtype.{u1} M _inst_1 S)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (forall (ᾰ : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) => M) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (fun (_x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) => M) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (MulOneClass.toMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Submonoid.toMulOneClass.{u1} M _inst_1 S)) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1 (MonoidHom.monoidHomClass.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1))) (Submonoid.subtype.{u1} M _inst_1 S)) (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_subtype Submonoid.coe_subtypeₓ'. -/
@[simp, to_additive]
theorem coe_subtype : ⇑S.Subtype = coe :=
  rfl
#align submonoid.coe_subtype Submonoid.coe_subtype
#align add_submonoid.coe_subtype AddSubmonoid.coe_subtype

/- warning: submonoid.top_equiv -> Submonoid.topEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], MulEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) M (Submonoid.mul.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) (MulOneClass.toHasMul.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], MulEquiv.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1)))) M (Submonoid.mul.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) (MulOneClass.toMul.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align submonoid.top_equiv Submonoid.topEquivₓ'. -/
/-- The top submonoid is isomorphic to the monoid. -/
@[to_additive "The top additive submonoid is isomorphic to the additive monoid.", simps]
def topEquiv : (⊤ : Submonoid M) ≃* M where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align submonoid.top_equiv Submonoid.topEquiv
#align add_submonoid.top_equiv AddSubmonoid.topEquiv

/- warning: submonoid.top_equiv_to_monoid_hom -> Submonoid.top_equiv_toMonoidHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) M (Submonoid.toMulOneClass.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) _inst_1) (MulEquiv.toMonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) M (Submonoid.toMulOneClass.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) _inst_1 (Submonoid.topEquiv.{u1} M _inst_1)) (Submonoid.subtype.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1)))) M (Submonoid.toMulOneClass.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) _inst_1) (MulEquiv.toMonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1)))) M (Submonoid.toMulOneClass.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) _inst_1 (Submonoid.topEquiv.{u1} M _inst_1)) (Submonoid.subtype.{u1} M _inst_1 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.top_equiv_to_monoid_hom Submonoid.top_equiv_toMonoidHomₓ'. -/
@[simp, to_additive]
theorem top_equiv_toMonoidHom : (topEquiv : _ ≃* M).toMonoidHom = (⊤ : Submonoid M).Subtype :=
  rfl
#align submonoid.top_equiv_to_monoid_hom Submonoid.top_equiv_toMonoidHom
#align add_submonoid.top_equiv_to_add_monoid_hom AddSubmonoid.top_equiv_toAddMonoidHom

/- warning: submonoid.equiv_map_of_injective -> Submonoid.equivMapOfInjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), (Function.Injective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2))) f)) -> (MulEquiv.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)))
Case conversion may be inaccurate. Consider using '#align submonoid.equiv_map_of_injective Submonoid.equivMapOfInjectiveₓ'. -/
/-- A subgroup is isomorphic to its image under an injective function. If you have an isomorphism,
use `mul_equiv.submonoid_map` for better definitional equalities. -/
@[to_additive
      "An additive subgroup is isomorphic to its image under an injective function. If you\nhave an isomorphism, use `add_equiv.add_submonoid_map` for better definitional equalities."]
noncomputable def equivMapOfInjective (f : M →* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _) }
#align submonoid.equiv_map_of_injective Submonoid.equivMapOfInjective
#align add_submonoid.equiv_map_of_injective AddSubmonoid.equivMapOfInjective

/- warning: submonoid.coe_equiv_map_of_injective_apply -> Submonoid.coe_equiv_map_of_injective_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (hf : Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S), Eq.{succ u2} N ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) N (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) N (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) N (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) N (coeSubtype.{succ u2} N (fun (x : N) => Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) x (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S))) (fun (_x : MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S))) => (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) -> (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S))) (MulEquiv.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S))) (Submonoid.equivMapOfInjective.{u1, u2} M N _inst_1 _inst_2 S f hf) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))))) x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (S : Submonoid.{u2} M _inst_1) (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (hf : Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f)) (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)), Eq.{succ u1} N (Subtype.val.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Set.{u1} N) (Set.instMembershipSet.{u1} N) x (SetLike.coe.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2) (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u2} M _inst_1 S) (Submonoid.mul.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u2} M _inst_1 S) (Submonoid.mul.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (MulOneClass.toMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Submonoid.toMulOneClass.{u2} M _inst_1 S)) (MulOneClass.toMul.{u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u2} M _inst_1 S) (Submonoid.mul.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.toMulOneClass.{u2} M _inst_1 S) (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S)) (MulEquivClass.instMonoidHomClass.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u2} M _inst_1 S) (Submonoid.mul.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.toMulOneClass.{u2} M _inst_1 S) (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S)) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S))) (Submonoid.mul.{u2} M _inst_1 S) (Submonoid.mul.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S)))))) (Submonoid.equivMapOfInjective.{u2, u1} M N _inst_1 _inst_2 S f hf) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) S)) x))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_equiv_map_of_injective_apply Submonoid.coe_equiv_map_of_injective_applyₓ'. -/
@[simp, to_additive]
theorem coe_equiv_map_of_injective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl
#align submonoid.coe_equiv_map_of_injective_apply Submonoid.coe_equiv_map_of_injective_apply
#align add_submonoid.coe_equiv_map_of_injective_apply AddSubmonoid.coe_equiv_map_of_injective_apply

/- warning: submonoid.closure_closure_coe_preimage -> Submonoid.closure_closure_coe_preimage is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M}, Eq.{succ u1} (Submonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))) (Submonoid.closure.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s)) (Set.preimage.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s))))))) s)) (Top.top.{u1} (Submonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))) (Submonoid.hasTop.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s)) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M}, Eq.{succ u1} (Submonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))) (Submonoid.closure.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s)) (Set.preimage.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) s)) (Top.top.{u1} (Submonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))) (Submonoid.instTopSubmonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s)))) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.closure.{u1} M _inst_1 s))))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_closure_coe_preimage Submonoid.closure_closure_coe_preimageₓ'. -/
@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    Subtype.recOn x fun x hx _ =>
      by
      refine' closure_induction' _ (fun g hg => _) _ (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact subset_closure hg
      · exact Submonoid.one_mem _
      · exact Submonoid.mul_mem _
#align submonoid.closure_closure_coe_preimage Submonoid.closure_closure_coe_preimage
#align add_submonoid.closure_closure_coe_preimage AddSubmonoid.closure_closure_coe_preimage

/- warning: submonoid.prod -> Submonoid.prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], (Submonoid.{u1} M _inst_1) -> (Submonoid.{u2} N _inst_2) -> (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], (Submonoid.{u1} M _inst_1) -> (Submonoid.{u2} N _inst_2) -> (Submonoid.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align submonoid.prod Submonoid.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given `submonoid`s `s`, `t` of monoids `M`, `N` respectively, `s × t` as a submonoid
of `M × N`. -/
@[to_additive Prod
      "Given `add_submonoid`s `s`, `t` of `add_monoid`s `A`, `B` respectively, `s × t`\nas an `add_submonoid` of `A × B`."]
def prod (s : Submonoid M) (t : Submonoid N) : Submonoid (M × N)
    where
  carrier := s ×ˢ t
  one_mem' := ⟨s.one_mem, t.one_mem⟩
  mul_mem' p q hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align submonoid.prod Submonoid.prod
#align add_submonoid.prod AddSubmonoid.prod

/- warning: submonoid.coe_prod -> Submonoid.coe_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1) (t : Submonoid.{u2} N _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} M N)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (Set.prod.{u1, u2} M N ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submonoid.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (s : Submonoid.{u2} M _inst_1) (t : Submonoid.{u1} N _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} M N)) (SetLike.coe.{max u2 u1, max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Prod.{u2, u1} M N) (Submonoid.instSetLikeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (Set.prod.{u2, u1} M N (SetLike.coe.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) s) (SetLike.coe.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2) t))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_prod Submonoid.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive coe_prod]
theorem coe_prod (s : Submonoid M) (t : Submonoid N) : (s.Prod t : Set (M × N)) = s ×ˢ t :=
  rfl
#align submonoid.coe_prod Submonoid.coe_prod
#align add_submonoid.coe_prod AddSubmonoid.coe_prod

/- warning: submonoid.mem_prod -> Submonoid.mem_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s : Submonoid.{u1} M _inst_1} {t : Submonoid.{u2} N _inst_2} {p : Prod.{u1, u2} M N}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.hasMem.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))) p (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (And (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Prod.fst.{u1, u2} M N p) s) (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Prod.snd.{u1, u2} M N p) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s : Submonoid.{u2} M _inst_1} {t : Submonoid.{u1} N _inst_2} {p : Prod.{u2, u1} M N}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (SetLike.instMembership.{max u2 u1, max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Prod.{u2, u1} M N) (Submonoid.instSetLikeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2))) p (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (And (Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) (Prod.fst.{u2, u1} M N p) s) (Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) (Prod.snd.{u2, u1} M N p) t))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_prod Submonoid.mem_prodₓ'. -/
@[to_additive mem_prod]
theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align submonoid.mem_prod Submonoid.mem_prod
#align add_submonoid.mem_prod AddSubmonoid.mem_prod

/- warning: submonoid.prod_mono -> Submonoid.prod_mono is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s₁ : Submonoid.{u1} M _inst_1} {s₂ : Submonoid.{u1} M _inst_1} {t₁ : Submonoid.{u2} N _inst_2} {t₂ : Submonoid.{u2} N _inst_2}, (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) s₁ s₂) -> (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) t₁ t₂) -> (LE.le.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s₁ t₁) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s₂ t₂))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s₁ : Submonoid.{u2} M _inst_1} {s₂ : Submonoid.{u2} M _inst_1} {t₁ : Submonoid.{u1} N _inst_2} {t₂ : Submonoid.{u1} N _inst_2}, (LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) s₁ s₂) -> (LE.le.{u1} (Submonoid.{u1} N _inst_2) (Preorder.toLE.{u1} (Submonoid.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u1} N _inst_2))))) t₁ t₂) -> (LE.le.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))))) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s₁ t₁) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s₂ t₂))
Case conversion may be inaccurate. Consider using '#align submonoid.prod_mono Submonoid.prod_monoₓ'. -/
@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Submonoid M} {t₁ t₂ : Submonoid N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht
#align submonoid.prod_mono Submonoid.prod_mono
#align add_submonoid.prod_mono AddSubmonoid.prod_mono

/- warning: submonoid.prod_top -> Submonoid.prod_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1), Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))) (Submonoid.comap.{max u1 u2, u1, max u1 u2} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2) s)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (s : Submonoid.{u2} M _inst_1), Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s (Top.top.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instTopSubmonoid.{u1} N _inst_2))) (Submonoid.comap.{max u2 u1, u2, max u2 u1} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2) s)
Case conversion may be inaccurate. Consider using '#align submonoid.prod_top Submonoid.prod_topₓ'. -/
@[to_additive prod_top]
theorem prod_top (s : Submonoid M) : s.Prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]
#align submonoid.prod_top Submonoid.prod_top
#align add_submonoid.prod_top AddSubmonoid.prod_top

/- warning: submonoid.top_prod -> Submonoid.top_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u2} N _inst_2), Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)) s) (Submonoid.comap.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2) s)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u2} N _inst_2), Eq.{max (succ u1) (succ u2)} (Submonoid.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1)) s) (Submonoid.comap.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u2 u1, u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2) s)
Case conversion may be inaccurate. Consider using '#align submonoid.top_prod Submonoid.top_prodₓ'. -/
@[to_additive top_prod]
theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).Prod s = s.comap (MonoidHom.snd M N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]
#align submonoid.top_prod Submonoid.top_prod
#align add_submonoid.top_prod AddSubmonoid.top_prod

/- warning: submonoid.top_prod_top -> Submonoid.top_prod_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))) (Top.top.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.hasTop.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instTopSubmonoid.{u1} N _inst_2))) (Top.top.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instTopSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.top_prod_top Submonoid.top_prod_topₓ'. -/
@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Submonoid M).Prod (⊤ : Submonoid N) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align submonoid.top_prod_top Submonoid.top_prod_top
#align add_submonoid.top_prod_top AddSubmonoid.top_prod_top

/- warning: submonoid.bot_prod_bot -> Submonoid.bot_prod_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1)) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))) (Bot.bot.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.hasBot.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1)) (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2))) (Bot.bot.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instBotSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.bot_prod_bot Submonoid.bot_prod_botₓ'. -/
@[to_additive]
theorem bot_prod_bot : (⊥ : Submonoid M).Prod (⊥ : Submonoid N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod, Prod.one_eq_mk]
#align submonoid.bot_prod_bot Submonoid.bot_prod_bot
#align add_submonoid.bot_prod_bot AddSubmonoid.bot_prod_bot

/- warning: submonoid.prod_equiv -> Submonoid.prodEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1) (t : Submonoid.{u2} N _inst_2), MulEquiv.{max u1 u2, max u1 u2} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) Type.{max u1 u2} (SetLike.hasCoeToSort.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (Prod.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) s) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) t)) (Submonoid.mul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (Prod.hasMul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) s) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) t) (Submonoid.mul.{u1} M _inst_1 s) (Submonoid.mul.{u2} N _inst_2 t))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1) (t : Submonoid.{u2} N _inst_2), MulEquiv.{max u1 u2, max u2 u1} (Subtype.{succ (max u1 u2)} (Prod.{u1, u2} M N) (fun (x : Prod.{u1, u2} M N) => Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Submonoid.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (SetLike.instMembership.{max u1 u2, max u1 u2} (Submonoid.{max u2 u1} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.instSetLikeSubmonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2))) x (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t))) (Prod.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x t))) (Submonoid.mul.{max u1 u2} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (Prod.instMulProd.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x t)) (Submonoid.mul.{u1} M _inst_1 s) (Submonoid.mul.{u2} N _inst_2 t))
Case conversion may be inaccurate. Consider using '#align submonoid.prod_equiv Submonoid.prodEquivₓ'. -/
/-- The product of submonoids is isomorphic to their product as monoids. -/
@[to_additive prod_equiv
      "The product of additive submonoids is isomorphic to their product\nas additive monoids"]
def prodEquiv (s : Submonoid M) (t : Submonoid N) : s.Prod t ≃* s × t :=
  { Equiv.Set.prod ↑s ↑t with map_mul' := fun x y => rfl }
#align submonoid.prod_equiv Submonoid.prodEquiv
#align add_submonoid.prod_equiv AddSubmonoid.prodEquiv

open MonoidHom

/- warning: submonoid.map_inl -> Submonoid.map_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1), Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.map.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2) s) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (s : Submonoid.{u2} M _inst_1), Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.map.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2) s) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.map_inl Submonoid.map_inlₓ'. -/
@[to_additive]
theorem map_inl (s : Submonoid M) : s.map (inl M N) = s.Prod ⊥ :=
  ext fun p =>
    ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨hx, Set.mem_singleton 1⟩, fun ⟨hps, hp1⟩ =>
      ⟨p.1, hps, Prod.ext rfl <| (Set.eq_of_mem_singleton hp1).symm⟩⟩
#align submonoid.map_inl Submonoid.map_inl
#align add_submonoid.map_inl AddSubmonoid.map_inl

/- warning: submonoid.map_inr -> Submonoid.map_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u2} N _inst_2), Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.map.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2) s) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1)) s)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u2} N _inst_2), Eq.{max (succ u1) (succ u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.map.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u2 u1} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2) s) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1)) s)
Case conversion may be inaccurate. Consider using '#align submonoid.map_inr Submonoid.map_inrₓ'. -/
@[to_additive]
theorem map_inr (s : Submonoid N) : s.map (inr M N) = prod ⊥ s :=
  ext fun p =>
    ⟨fun ⟨x, hx, hp⟩ => hp ▸ ⟨Set.mem_singleton 1, hx⟩, fun ⟨hp1, hps⟩ =>
      ⟨p.2, hps, Prod.ext (Set.eq_of_mem_singleton hp1).symm rfl⟩⟩
#align submonoid.map_inr Submonoid.map_inr
#align add_submonoid.map_inr AddSubmonoid.map_inr

/- warning: submonoid.prod_bot_sup_bot_prod -> Submonoid.prod_bot_sup_bot_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (s : Submonoid.{u1} M _inst_1) (t : Submonoid.{u2} N _inst_2), Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (HasSup.sup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SemilatticeSup.toHasSup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.completeLattice.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1)) t)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (s : Submonoid.{u2} M _inst_1) (t : Submonoid.{u1} N _inst_2), Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (HasSup.sup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (SemilatticeSup.toHasSup.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2))))) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2))) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1)) t)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t)
Case conversion may be inaccurate. Consider using '#align submonoid.prod_bot_sup_bot_prod Submonoid.prod_bot_sup_bot_prodₓ'. -/
@[simp, to_additive prod_bot_sup_bot_prod]
theorem prod_bot_sup_bot_prod (s : Submonoid M) (t : Submonoid N) :
    s.Prod ⊥ ⊔ prod ⊥ t = s.Prod t :=
  le_antisymm (sup_le (prod_mono (le_refl s) bot_le) (prod_mono bot_le (le_refl t))) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem ((le_sup_left : s.Prod ⊥ ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, Set.mem_singleton 1⟩)
        ((le_sup_right : prod ⊥ t ≤ s.Prod ⊥ ⊔ prod ⊥ t) ⟨Set.mem_singleton 1, hp.2⟩)
#align submonoid.prod_bot_sup_bot_prod Submonoid.prod_bot_sup_bot_prod
#align add_submonoid.prod_bot_sup_bot_prod AddSubmonoid.prod_bot_sup_bot_prod

/- warning: submonoid.mem_map_equiv -> Submonoid.mem_map_equiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {f : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)} {K : Submonoid.{u1} M _inst_1} {x : N}, Iff (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) x (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 f) K)) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (fun (_x : MulEquiv.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (MulEquiv.symm.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) f) x) K)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {f : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)} {K : Submonoid.{u2} M _inst_1} {x : N}, Iff (Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u2, u1} M N _inst_1 _inst_2 f) K)) (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => M) x) (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : N) => M) _x) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1) (MonoidHomClass.toMulHomClass.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) N M _inst_2 _inst_1 (MulEquivClass.instMonoidHomClass.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1)) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M (MulOneClass.toMul.{u1} N _inst_2) (MulOneClass.toMul.{u2} M _inst_1))))) (MulEquiv.symm.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) f) x) K)
Case conversion may be inaccurate. Consider using '#align submonoid.mem_map_equiv Submonoid.mem_map_equivₓ'. -/
@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Submonoid M} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
#align submonoid.mem_map_equiv Submonoid.mem_map_equiv
#align add_submonoid.mem_map_equiv AddSubmonoid.mem_map_equiv

/- warning: submonoid.map_equiv_eq_comap_symm -> Submonoid.map_equiv_eq_comap_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (K : Submonoid.{u1} M _inst_1), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 f) K) (Submonoid.comap.{u2, u1, max u1 u2} N M _inst_2 _inst_1 (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.toMonoidHom.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.symm.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) f)) K)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (K : Submonoid.{u2} M _inst_1), Eq.{succ u1} (Submonoid.{u1} N _inst_2) (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u2, u1} M N _inst_1 _inst_2 f) K) (Submonoid.comap.{u1, u2, max u2 u1} N M _inst_2 _inst_1 (MonoidHom.{u1, u2} N M _inst_2 _inst_1) (MonoidHom.monoidHomClass.{u1, u2} N M _inst_2 _inst_1) (MulEquiv.toMonoidHom.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.symm.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) f)) K)
Case conversion may be inaccurate. Consider using '#align submonoid.map_equiv_eq_comap_symm Submonoid.map_equiv_eq_comap_symmₓ'. -/
@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f.toMonoidHom = K.comap f.symm.toMonoidHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align submonoid.map_equiv_eq_comap_symm Submonoid.map_equiv_eq_comap_symm
#align add_submonoid.map_equiv_eq_comap_symm AddSubmonoid.map_equiv_eq_comap_symm

/- warning: submonoid.comap_equiv_eq_map_symm -> Submonoid.comap_equiv_eq_map_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MulEquiv.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1)) (K : Submonoid.{u1} M _inst_1), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.comap.{u2, u1, max u1 u2} N M _inst_2 _inst_1 (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.toMonoidHom.{u2, u1} N M _inst_2 _inst_1 f) K) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.symm.{u2, u1} N M (MulOneClass.toHasMul.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} M _inst_1) f)) K)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MulEquiv.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1)) (K : Submonoid.{u1} M _inst_1), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.comap.{u2, u1, max u1 u2} N M _inst_2 _inst_1 (MonoidHom.{u2, u1} N M _inst_2 _inst_1) (MonoidHom.monoidHomClass.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.toMonoidHom.{u2, u1} N M _inst_2 _inst_1 f) K) (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.symm.{u2, u1} N M (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} M _inst_1) f)) K)
Case conversion may be inaccurate. Consider using '#align submonoid.comap_equiv_eq_map_symm Submonoid.comap_equiv_eq_map_symmₓ'. -/
@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f.toMonoidHom = K.map f.symm.toMonoidHom :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align submonoid.comap_equiv_eq_map_symm Submonoid.comap_equiv_eq_map_symm
#align add_submonoid.comap_equiv_eq_map_symm AddSubmonoid.comap_equiv_eq_map_symm

/- warning: submonoid.map_equiv_top -> Submonoid.map_equiv_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 f) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)), Eq.{succ u1} (Submonoid.{u1} N _inst_2) (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u2, u1} M N _inst_1 _inst_2 f) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))) (Top.top.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instTopSubmonoid.{u1} N _inst_2))
Case conversion may be inaccurate. Consider using '#align submonoid.map_equiv_top Submonoid.map_equiv_topₓ'. -/
@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f.toMonoidHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.Surjective.range_eq
#align submonoid.map_equiv_top Submonoid.map_equiv_top
#align add_submonoid.map_equiv_top AddSubmonoid.map_equiv_top

/- warning: submonoid.le_prod_iff -> Submonoid.le_prod_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s : Submonoid.{u1} M _inst_1} {t : Submonoid.{u2} N _inst_2} {u : Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)}, Iff (LE.le.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) u (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (And (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.map.{max u1 u2, u1, max u1 u2} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2) u) s) (LE.le.{u2} (Submonoid.{u2} N _inst_2) (Preorder.toLE.{u2} (Submonoid.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (Submonoid.map.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2) u) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s : Submonoid.{u2} M _inst_1} {t : Submonoid.{u1} N _inst_2} {u : Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)}, Iff (LE.le.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))))) u (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (And (LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) (Submonoid.map.{max u2 u1, u2, max u2 u1} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2) u) s) (LE.le.{u1} (Submonoid.{u1} N _inst_2) (Preorder.toLE.{u1} (Submonoid.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instCompleteLatticeSubmonoid.{u1} N _inst_2))))) (Submonoid.map.{max u2 u1, u1, max u2 u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u2, u1} M N _inst_1 _inst_2) u) t))
Case conversion may be inaccurate. Consider using '#align submonoid.le_prod_iff Submonoid.le_prod_iffₓ'. -/
@[to_additive le_prod_iff]
theorem le_prod_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    u ≤ s.Prod t ↔ u.map (fst M N) ≤ s ∧ u.map (snd M N) ≤ t :=
  by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
#align submonoid.le_prod_iff Submonoid.le_prod_iff
#align add_submonoid.le_prod_iff AddSubmonoid.le_prod_iff

/- warning: submonoid.prod_le_iff -> Submonoid.prod_le_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s : Submonoid.{u1} M _inst_1} {t : Submonoid.{u2} N _inst_2} {u : Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)}, Iff (LE.le.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t) u) (And (LE.le.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.map.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2) s) u) (LE.le.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Submonoid.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (Submonoid.map.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2) t) u))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s : Submonoid.{u2} M _inst_1} {t : Submonoid.{u1} N _inst_2} {u : Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)}, Iff (LE.le.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))))) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t) u) (And (LE.le.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))))) (Submonoid.map.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2) s) u) (LE.le.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))))) (Submonoid.map.{u1, max u2 u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2) t) u))
Case conversion may be inaccurate. Consider using '#align submonoid.prod_le_iff Submonoid.prod_le_iffₓ'. -/
@[to_additive prod_le_iff]
theorem prod_le_iff {s : Submonoid M} {t : Submonoid N} {u : Submonoid (M × N)} :
    s.Prod t ≤ u ↔ s.map (inl M N) ≤ u ∧ t.map (inr M N) ≤ u :=
  by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, Submonoid.one_mem _⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨Submonoid.one_mem _, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : inl M N x1 ∈ u := by
      apply hH
      simpa using h1
    have h2' : inr M N x2 ∈ u := by
      apply hK
      simpa using h2
    simpa using Submonoid.mul_mem _ h1' h2'
#align submonoid.prod_le_iff Submonoid.prod_le_iff
#align add_submonoid.prod_le_iff AddSubmonoid.prod_le_iff

end Submonoid

namespace MonoidHom

variable {F : Type _} [mc : MonoidHomClass F M N]

open Submonoid

library_note "range copy pattern"/--
For many categories (monoids, modules, rings, ...) the set-theoretic image of a morphism `f` is
a subobject of the codomain. When this is the case, it is useful to define the range of a morphism
in such a way that the underlying carrier set of the range subobject is definitionally
`set.range f`. In particular this means that the types `↥(set.range f)` and `↥f.range` are
interchangeable without proof obligations.

A convenient candidate definition for range which is mathematically correct is `map ⊤ f`, just as
`set.range` could have been defined as `f '' set.univ`. However, this lacks the desired definitional
convenience, in that it both does not match `set.range`, and that it introduces a redudant `x ∈ ⊤`
term which clutters proofs. In such a case one may resort to the `copy`
pattern. A `copy` function converts the definitional problem for the carrier set of a subobject
into a one-off propositional proof obligation which one discharges while writing the definition of
the definitionally convenient range (the parameter `hs` in the example below).

A good example is the case of a morphism of monoids. A convenient definition for
`monoid_hom.mrange` would be `(⊤ : submonoid M).map f`. However since this lacks the required
definitional convenience, we first define `submonoid.copy` as follows:
```lean
protected def copy (S : submonoid M) (s : set M) (hs : s = S) : submonoid M :=
{ carrier  := s,
  one_mem' := hs.symm ▸ S.one_mem',
  mul_mem' := hs.symm ▸ S.mul_mem' }
```
and then finally define:
```lean
def mrange (f : M →* N) : submonoid N :=
((⊤ : submonoid M).map f).copy (set.range f) set.image_univ.symm
```
-/


include mc

#print MonoidHom.mrange /-
/-- The range of a monoid homomorphism is a submonoid. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_monoid_hom` is an `add_submonoid`."]
def mrange (f : F) : Submonoid N :=
  ((⊤ : Submonoid M).map f).copy (Set.range f) Set.image_univ.symm
#align monoid_hom.mrange MonoidHom.mrange
#align add_monoid_hom.mrange AddMonoidHom.mrange
-/

/- warning: monoid_hom.coe_mrange -> MonoidHom.coe_mrange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u2} (Set.{u2} N) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submonoid.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Submonoid.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)))) (MonoidHom.mrange.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)) (Set.range.{u2, succ u1} N M (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Set.{u3} N) (SetLike.coe.{u3, u3} (Submonoid.{u3} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u3} N _inst_2) (MonoidHom.mrange.{u2, u3, u1} M N _inst_1 _inst_2 F mc f)) (Set.range.{u3, succ u2} N M (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_mrange MonoidHom.coe_mrangeₓ'. -/
@[simp, to_additive]
theorem coe_mrange (f : F) : (mrange f : Set N) = Set.range f :=
  rfl
#align monoid_hom.coe_mrange MonoidHom.coe_mrange
#align add_monoid_hom.coe_mrange AddMonoidHom.coe_mrange

/- warning: monoid_hom.mem_mrange -> MonoidHom.mem_mrange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F} {y : N}, Iff (Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) y (MonoidHom.mrange.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)) (Exists.{succ u1} M (fun (x : M) => Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F} {y : N}, Iff (Membership.mem.{u3, u3} N (Submonoid.{u3} N _inst_2) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u3} N _inst_2)) y (MonoidHom.mrange.{u2, u3, u1} M N _inst_1 _inst_2 F mc f)) (Exists.{succ u2} M (fun (x : M) => Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f x) y))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mem_mrange MonoidHom.mem_mrangeₓ'. -/
@[simp, to_additive]
theorem mem_mrange {f : F} {y : N} : y ∈ mrange f ↔ ∃ x, f x = y :=
  Iff.rfl
#align monoid_hom.mem_mrange MonoidHom.mem_mrange
#align add_monoid_hom.mem_mrange AddMonoidHom.mem_mrange

/- warning: monoid_hom.mrange_eq_map -> MonoidHom.mrange_eq_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Submonoid.{u3} N _inst_2) (MonoidHom.mrange.{u2, u3, u1} M N _inst_1 _inst_2 F mc f) (Submonoid.map.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mrange_eq_map MonoidHom.mrange_eq_mapₓ'. -/
@[to_additive]
theorem mrange_eq_map (f : F) : mrange f = (⊤ : Submonoid M).map f :=
  Submonoid.copy_eq _
#align monoid_hom.mrange_eq_map MonoidHom.mrange_eq_map
#align add_monoid_hom.mrange_eq_map AddMonoidHom.mrange_eq_map

omit mc

/- warning: monoid_hom.map_mrange -> MonoidHom.map_mrange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u3} (Submonoid.{u3} P _inst_3) (Submonoid.map.{u2, u3, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u2, u3} N P _inst_2 _inst_3) g (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) (MonoidHom.mrange.{u1, u3, max u3 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : MulOneClass.{u2} P] (g : MonoidHom.{u3, u2} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u3} M N _inst_1 _inst_2), Eq.{succ u2} (Submonoid.{u2} P _inst_3) (Submonoid.map.{u3, u2, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u3, u2} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u3, u2} N P _inst_2 _inst_3) g (MonoidHom.mrange.{u1, u3, max u1 u3} M N _inst_1 _inst_2 (MonoidHom.{u1, u3} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u3} M N _inst_1 _inst_2) f)) (MonoidHom.mrange.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_mrange MonoidHom.map_mrangeₓ'. -/
@[to_additive]
theorem map_mrange (g : N →* P) (f : M →* N) : f.mrange.map g = (g.comp f).mrange := by
  simpa only [mrange_eq_map] using (⊤ : Submonoid M).map_map g f
#align monoid_hom.map_mrange MonoidHom.map_mrange
#align add_monoid_hom.map_mrange AddMonoidHom.map_mrange

include mc

/- warning: monoid_hom.mrange_top_iff_surjective -> MonoidHom.mrange_top_iff_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] {f : F}, Iff (Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))) (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] {f : F}, Iff (Eq.{succ u3} (Submonoid.{u3} N _inst_2) (MonoidHom.mrange.{u2, u3, u1} M N _inst_1 _inst_2 F mc f) (Top.top.{u3} (Submonoid.{u3} N _inst_2) (Submonoid.instTopSubmonoid.{u3} N _inst_2))) (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mrange_top_iff_surjective MonoidHom.mrange_top_iff_surjectiveₓ'. -/
@[to_additive]
theorem mrange_top_iff_surjective {f : F} : mrange f = (⊤ : Submonoid N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_mrange, coe_top]) Set.range_iff_surjective
#align monoid_hom.mrange_top_iff_surjective MonoidHom.mrange_top_iff_surjective
#align add_monoid_hom.mrange_top_iff_surjective AddMonoidHom.mrange_top_iff_surjective

/- warning: monoid_hom.mrange_top_of_surjective -> MonoidHom.mrange_top_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), (Function.Surjective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f)) -> (Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{u1, u2, u3} M N _inst_1 _inst_2 F mc f) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F), (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f)) -> (Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{u3, u2, u1} M N _inst_1 _inst_2 F mc f) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instTopSubmonoid.{u2} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mrange_top_of_surjective MonoidHom.mrange_top_of_surjectiveₓ'. -/
/-- The range of a surjective monoid hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` hom is the whole of the codomain."]
theorem mrange_top_of_surjective (f : F) (hf : Function.Surjective f) :
    mrange f = (⊤ : Submonoid N) :=
  mrange_top_iff_surjective.2 hf
#align monoid_hom.mrange_top_of_surjective MonoidHom.mrange_top_of_surjective
#align add_monoid_hom.mrange_top_of_surjective AddMonoidHom.mrange_top_of_surjective

/- warning: monoid_hom.mclosure_preimage_le -> MonoidHom.mclosure_preimage_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) (s : Set.{u2} N), LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 (Set.preimage.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f) s)) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.closure.{u2} N _inst_2 s))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u2, u3} F M N _inst_1 _inst_2] (f : F) (s : Set.{u3} N), LE.le.{u2} (Submonoid.{u2} M _inst_1) (Preorder.toLE.{u2} (Submonoid.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u2} M _inst_1))))) (Submonoid.closure.{u2} M _inst_1 (Set.preimage.{u2, u3} M N (FunLike.coe.{succ u1, succ u2, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u2, u3} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2 mc)) f) s)) (Submonoid.comap.{u2, u3, u1} M N _inst_1 _inst_2 F mc f (Submonoid.closure.{u3} N _inst_2 s))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mclosure_preimage_le MonoidHom.mclosure_preimage_leₓ'. -/
@[to_additive]
theorem mclosure_preimage_le (f : F) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align monoid_hom.mclosure_preimage_le MonoidHom.mclosure_preimage_le
#align add_monoid_hom.mclosure_preimage_le AddMonoidHom.mclosure_preimage_le

/- warning: monoid_hom.map_mclosure -> MonoidHom.map_mclosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) (s : Set.{u1} M), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Submonoid.closure.{u1} M _inst_1 s)) (Submonoid.closure.{u2} N _inst_2 (Set.image.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f) s))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F) (s : Set.{u3} M), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (Submonoid.map.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (Submonoid.closure.{u3} M _inst_1 s)) (Submonoid.closure.{u2} N _inst_2 (Set.image.{u3, u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f) s))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_mclosure MonoidHom.map_mclosureₓ'. -/
/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set. -/
@[to_additive
      "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals\nthe `add_submonoid` generated by the image of the set."]
theorem map_mclosure (f : F) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align monoid_hom.map_mclosure MonoidHom.map_mclosure
#align add_monoid_hom.map_mclosure AddMonoidHom.map_mclosure

omit mc

#print MonoidHom.restrict /-
/-- Restriction of a monoid hom to a submonoid of the domain. -/
@[to_additive "Restriction of an add_monoid hom to an `add_submonoid` of the domain."]
def restrict {N S : Type _} [MulOneClass N] [SetLike S M] [SubmonoidClass S M] (f : M →* N)
    (s : S) : s →* N :=
  f.comp (SubmonoidClass.Subtype _)
#align monoid_hom.restrict MonoidHom.restrict
#align add_monoid_hom.restrict AddMonoidHom.restrict
-/

/- warning: monoid_hom.restrict_apply -> MonoidHom.restrict_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u2}} {S : Type.{u3}} [_inst_4 : MulOneClass.{u2} N] [_inst_5 : SetLike.{u3, u1} S M] [_inst_6 : SubmonoidClass.{u3, u1} S M _inst_1 _inst_5] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_4) (s : S) (x : coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) N (SubmonoidClass.toMulOneClass.{u1, u3} M _inst_1 S _inst_5 _inst_6 s) _inst_4) (fun (_x : MonoidHom.{u1, u2} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) N (SubmonoidClass.toMulOneClass.{u1, u3} M _inst_1 S _inst_5 _inst_6 s) _inst_4) => (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) -> N) (MonoidHom.hasCoeToFun.{u1, u2} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) N (SubmonoidClass.toMulOneClass.{u1, u3} M _inst_1 S _inst_5 _inst_6 s) _inst_4) (MonoidHom.restrict.{u1, u2, u3} M _inst_1 N S _inst_4 _inst_5 _inst_6 f s) x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_4) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_4) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) M (coeBase.{succ u1, succ u1} (coeSort.{succ u3, succ (succ u1)} S Type.{u1} (SetLike.hasCoeToSort.{u3, u1} S M _inst_5) s) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u3} M S (SetLike.hasMem.{u3, u1} S M _inst_5) x s))))) x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u3}} {S : Type.{u2}} [_inst_4 : MulOneClass.{u3} N] [_inst_5 : SetLike.{u2, u1} S M] [_inst_6 : SubmonoidClass.{u2, u1} S M _inst_1 _inst_5] (f : MonoidHom.{u1, u3} M N _inst_1 _inst_4) (s : S) (x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) => N) x) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s) _inst_4) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) (fun (_x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) => N) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s) _inst_4) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (MulOneClass.toMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s)) (MulOneClass.toMul.{u3} N _inst_4) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s) _inst_4) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s) _inst_4 (MonoidHom.monoidHomClass.{u1, u3} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M S (SetLike.instMembership.{u2, u1} S M _inst_5) x s)) N (SubmonoidClass.toMulOneClass.{u1, u2} M _inst_1 S _inst_5 _inst_6 s) _inst_4))) (MonoidHom.restrict.{u1, u3, u2} M _inst_1 N S _inst_4 _inst_5 _inst_6 f s) x) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} M N _inst_1 _inst_4) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} M N _inst_1 _inst_4) M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u3} N _inst_4) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} M N _inst_1 _inst_4) M N _inst_1 _inst_4 (MonoidHom.monoidHomClass.{u1, u3} M N _inst_1 _inst_4))) f (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u2, u1} S M _inst_5 s)) x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.restrict_apply MonoidHom.restrict_applyₓ'. -/
@[simp, to_additive]
theorem restrict_apply {N S : Type _} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M →* N) (s : S) (x : s) : f.restrict s x = f x :=
  rfl
#align monoid_hom.restrict_apply MonoidHom.restrict_apply
#align add_monoid_hom.restrict_apply AddMonoidHom.restrict_apply

/- warning: monoid_hom.restrict_mrange -> MonoidHom.restrict_mrange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{u1, u2, max u2 u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (SubmonoidClass.toMulOneClass.{u1, u1} M _inst_1 (Submonoid.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) S) _inst_2 (MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (SubmonoidClass.toMulOneClass.{u1, u1} M _inst_1 (Submonoid.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) S) _inst_2) (MonoidHom.monoidHomClass.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (SubmonoidClass.toMulOneClass.{u1, u1} M _inst_1 (Submonoid.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) S) _inst_2) (MonoidHom.restrict.{u1, u2, u1} M _inst_1 N (Submonoid.{u1} M _inst_1) _inst_2 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) f S)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (S : Submonoid.{u2} M _inst_1) (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Submonoid.{u1} N _inst_2) (MonoidHom.mrange.{u2, u1, max u2 u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2 (MonoidHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2) (MonoidHom.monoidHomClass.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2) (MonoidHom.restrict.{u2, u1, u2} M _inst_1 N (Submonoid.{u2} M _inst_1) _inst_2 (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) f S)) (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S)
Case conversion may be inaccurate. Consider using '#align monoid_hom.restrict_mrange MonoidHom.restrict_mrangeₓ'. -/
@[simp, to_additive]
theorem restrict_mrange (f : M →* N) : (f.restrict S).mrange = S.map f := by
  simp_rw [SetLike.ext_iff, mem_mrange, mem_map, restrict_apply, SetLike.exists, Subtype.coe_mk,
    iff_self_iff, forall_const]
#align monoid_hom.restrict_mrange MonoidHom.restrict_mrange
#align add_monoid_hom.restrict_mrange AddMonoidHom.restrict_mrange

/- warning: monoid_hom.cod_restrict -> MonoidHom.codRestrict is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {S : Type.{u3}} [_inst_4 : SetLike.{u3, u2} S N] [_inst_5 : SubmonoidClass.{u3, u2} S N _inst_2 _inst_4] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (s : S), (forall (x : M), Membership.Mem.{u2, u3} N S (SetLike.hasMem.{u3, u2} S N _inst_4) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) s) -> (MonoidHom.{u1, u2} M (coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S N _inst_4) s) _inst_1 (SubmonoidClass.toMulOneClass.{u2, u3} N _inst_2 S _inst_4 _inst_5 s))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {S : Type.{u3}} [_inst_4 : SetLike.{u3, u2} S N] [_inst_5 : SubmonoidClass.{u3, u2} S N _inst_2 _inst_4] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (s : S), (forall (x : M), Membership.mem.{u2, u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) S (SetLike.instMembership.{u3, u2} S N _inst_4) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2))) f x) s) -> (MonoidHom.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u3} N S (SetLike.instMembership.{u3, u2} S N _inst_4) x s)) _inst_1 (SubmonoidClass.toMulOneClass.{u2, u3} N _inst_2 S _inst_4 _inst_5 s))
Case conversion may be inaccurate. Consider using '#align monoid_hom.cod_restrict MonoidHom.codRestrictₓ'. -/
/-- Restriction of a monoid hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an `add_monoid` hom to an `add_submonoid` of the codomain.",
  simps apply]
def codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : M →* N) (s : S) (h : ∀ x, f x ∈ s) :
    M →* s where
  toFun n := ⟨f n, h n⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.cod_restrict MonoidHom.codRestrict
#align add_monoid_hom.codRestrict AddMonoidHom.codRestrict

/- warning: monoid_hom.mrange_restrict -> MonoidHom.mrangeRestrict is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u2}} [_inst_4 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_4), MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u2}} [_inst_4 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_4), MonoidHom.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mrange_restrict MonoidHom.mrangeRestrictₓ'. -/
/-- Restriction of a monoid hom to its range interpreted as a submonoid. -/
@[to_additive "Restriction of an `add_monoid` hom to its range interpreted as a submonoid."]
def mrangeRestrict {N} [MulOneClass N] (f : M →* N) : M →* f.mrange :=
  f.codRestrict f.mrange fun x => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict MonoidHom.mrangeRestrict
#align add_monoid_hom.mrangeRestrict AddMonoidHom.mrangeRestrict

/- warning: monoid_hom.coe_mrange_restrict -> MonoidHom.coe_mrangeRestrict is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u2}} [_inst_4 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_4) (x : M), Eq.{succ u2} N ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) N (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) N (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) N (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) N (coeSubtype.{succ u2} N (fun (x : N) => Membership.Mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (fun (_x : MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) => M -> (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (MonoidHom.hasCoeToFun.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_4) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.setLike.{u2} N _inst_4)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (MonoidHom.mrangeRestrict.{u1, u2} M _inst_1 N _inst_4 f) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_4) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_4) f x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {N : Type.{u2}} [_inst_4 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_4) (x : M), Eq.{succ u2} N (Subtype.val.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Set.{u2} N) (Set.instMembershipSet.{u2} N) x (SetLike.coe.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4) (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f)) (MonoidHom.monoidHomClass.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_4) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_4)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_4 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_4 (MonoidHom.{u1, u2} M N _inst_1 _inst_4) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4) f))))) (MonoidHom.mrangeRestrict.{u1, u2} M _inst_1 N _inst_4 f) x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_4) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_4) M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_4) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_4) M N _inst_1 _inst_4 (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_4))) f x)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_mrange_restrict MonoidHom.coe_mrangeRestrictₓ'. -/
@[simp, to_additive]
theorem coe_mrangeRestrict {N} [MulOneClass N] (f : M →* N) (x : M) :
    (f.mrangeRestrict x : N) = f x :=
  rfl
#align monoid_hom.coe_mrange_restrict MonoidHom.coe_mrangeRestrict
#align add_monoid_hom.coe_mrange_restrict AddMonoidHom.coe_mrangeRestrict

/- warning: monoid_hom.mrange_restrict_surjective -> MonoidHom.mrangeRestrict_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (fun (_x : MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) => M -> (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (MonoidHom.hasCoeToFun.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (MonoidHom.mrangeRestrict.{u1, u2} M _inst_1 N _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f)) (MonoidHom.monoidHomClass.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))))) (MonoidHom.mrangeRestrict.{u2, u1} M _inst_1 N _inst_2 f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mrange_restrict_surjective MonoidHom.mrangeRestrict_surjectiveₓ'. -/
@[to_additive]
theorem mrangeRestrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
#align monoid_hom.mrange_restrict_surjective MonoidHom.mrangeRestrict_surjective
#align add_monoid_hom.mrange_restrict_surjective AddMonoidHom.mrangeRestrict_surjective

include mc

#print MonoidHom.mker /-
/-- The multiplicative kernel of a monoid homomorphism is the submonoid of elements `x : G` such
that `f x = 1` -/
@[to_additive
      "The additive kernel of an `add_monoid` homomorphism is the `add_submonoid` of\nelements such that `f x = 0`"]
def mker (f : F) : Submonoid M :=
  (⊥ : Submonoid N).comap f
#align monoid_hom.mker MonoidHom.mker
#align add_monoid_hom.mker AddMonoidHom.mker
-/

/- warning: monoid_hom.mem_mker -> MonoidHom.mem_mker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (MonoidHom.mker.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)) (Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F) {x : M}, Iff (Membership.mem.{u3, u3} M (Submonoid.{u3} M _inst_1) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1)) x (MonoidHom.mker.{u3, u2, u1} M N _inst_1 _inst_2 F mc f)) (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) _inst_2))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mem_mker MonoidHom.mem_mkerₓ'. -/
@[to_additive]
theorem mem_mker (f : F) {x : M} : x ∈ mker f ↔ f x = 1 :=
  Iff.rfl
#align monoid_hom.mem_mker MonoidHom.mem_mker
#align add_monoid_hom.mem_mker AddMonoidHom.mem_mker

/- warning: monoid_hom.coe_mker -> MonoidHom.coe_mker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (MonoidHom.mker.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)) (Set.preimage.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 mc))) f) (Singleton.singleton.{u2, u2} N (Set.{u2} N) (Set.hasSingleton.{u2} N) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Set.{u3} M) (SetLike.coe.{u3, u3} (Submonoid.{u3} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u3} M _inst_1) (MonoidHom.mker.{u3, u2, u1} M N _inst_1 _inst_2 F mc f)) (Set.preimage.{u3, u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N _inst_1 _inst_2 mc)) f) (Singleton.singleton.{u2, u2} N (Set.{u2} N) (Set.instSingletonSet.{u2} N) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (MulOneClass.toOne.{u2} N _inst_2)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_mker MonoidHom.coe_mkerₓ'. -/
@[to_additive]
theorem coe_mker (f : F) : (mker f : Set M) = (f : M → N) ⁻¹' {1} :=
  rfl
#align monoid_hom.coe_mker MonoidHom.coe_mker
#align add_monoid_hom.coe_mker AddMonoidHom.coe_mker

/- warning: monoid_hom.decidable_mem_mker -> MonoidHom.decidableMemMker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u2} N] (f : F), DecidablePred.{succ u1} M (fun (_x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) _x (MonoidHom.mker.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u2} N] (f : F), DecidablePred.{succ u1} M (fun (_x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) _x (MonoidHom.mker.{u1, u2, u3} M N _inst_1 _inst_2 F mc f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.decidable_mem_mker MonoidHom.decidableMemMkerₓ'. -/
@[to_additive]
instance decidableMemMker [DecidableEq N] (f : F) : DecidablePred (· ∈ mker f) := fun x =>
  decidable_of_iff (f x = 1) (mem_mker f)
#align monoid_hom.decidable_mem_mker MonoidHom.decidableMemMker
#align add_monoid_hom.decidable_mem_mker AddMonoidHom.decidableMemMker

omit mc

/- warning: monoid_hom.comap_mker -> MonoidHom.comap_mker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f (MonoidHom.mker.{u2, u3, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u2, u3} N P _inst_2 _inst_3) g)) (MonoidHom.mker.{u1, u3, max u3 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : MulOneClass.{u2} P] (g : MonoidHom.{u3, u2} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u3} M N _inst_1 _inst_2), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u3, max u1 u3} M N _inst_1 _inst_2 (MonoidHom.{u1, u3} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u3} M N _inst_1 _inst_2) f (MonoidHom.mker.{u3, u2, max u3 u2} N P _inst_2 _inst_3 (MonoidHom.{u3, u2} N P _inst_2 _inst_3) (MonoidHom.monoidHomClass.{u3, u2} N P _inst_2 _inst_3) g)) (MonoidHom.mker.{u1, u2, max u2 u1} M P _inst_1 _inst_3 (MonoidHom.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.monoidHomClass.{u1, u2} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comap_mker MonoidHom.comap_mkerₓ'. -/
@[to_additive]
theorem comap_mker (g : N →* P) (f : M →* N) : g.mker.comap f = (g.comp f).mker :=
  rfl
#align monoid_hom.comap_mker MonoidHom.comap_mker
#align add_monoid_hom.comap_mker AddMonoidHom.comap_mker

include mc

/- warning: monoid_hom.comap_bot' -> MonoidHom.comap_bot' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u3}} [mc : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.comap.{u1, u2, u3} M N _inst_1 _inst_2 F mc f (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))) (MonoidHom.mker.{u1, u2, u3} M N _inst_1 _inst_2 F mc f)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] {F : Type.{u1}} [mc : MonoidHomClass.{u1, u3, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u3} (Submonoid.{u3} M _inst_1) (Submonoid.comap.{u3, u2, u1} M N _inst_1 _inst_2 F mc f (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instBotSubmonoid.{u2} N _inst_2))) (MonoidHom.mker.{u3, u2, u1} M N _inst_1 _inst_2 F mc f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.comap_bot' MonoidHom.comap_bot'ₓ'. -/
@[simp, to_additive]
theorem comap_bot' (f : F) : (⊥ : Submonoid N).comap f = mker f :=
  rfl
#align monoid_hom.comap_bot' MonoidHom.comap_bot'
#align add_monoid_hom.comap_bot' AddMonoidHom.comap_bot'

omit mc

/- warning: monoid_hom.restrict_mker -> MonoidHom.restrict_mker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (S : Submonoid.{u1} M _inst_1) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Submonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (Submonoid.toMulOneClass.{u1} M _inst_1 S)) (MonoidHom.mker.{u1, u2, max u2 u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_2 (MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (SubmonoidClass.toMulOneClass.{u1, u1} M _inst_1 (Submonoid.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) S) _inst_2) (MonoidHom.monoidHomClass.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) N (SubmonoidClass.toMulOneClass.{u1, u1} M _inst_1 (Submonoid.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) S) _inst_2) (MonoidHom.restrict.{u1, u2, u1} M _inst_1 N (Submonoid.{u1} M _inst_1) _inst_2 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoid_class.{u1} M _inst_1) f S)) (Submonoid.comap.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1 (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (MonoidHom.monoidHomClass.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) M (Submonoid.toMulOneClass.{u1} M _inst_1 S) _inst_1) (Submonoid.subtype.{u1} M _inst_1 S) (MonoidHom.mker.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (S : Submonoid.{u2} M _inst_1) (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u2} (Submonoid.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S)) (MonoidHom.mker.{u2, u1, max u2 u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2 (MonoidHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2) (MonoidHom.monoidHomClass.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) N (SubmonoidClass.toMulOneClass.{u2, u2} M _inst_1 (Submonoid.{u2} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) S) _inst_2) (MonoidHom.restrict.{u2, u1, u2} M _inst_1 N (Submonoid.{u2} M _inst_1) _inst_2 (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u2} M _inst_1) f S)) (Submonoid.comap.{u2, u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u2} M _inst_1 S) _inst_1 (MonoidHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u2} M _inst_1 S) _inst_1) (MonoidHom.monoidHomClass.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x S)) M (Submonoid.toMulOneClass.{u2} M _inst_1 S) _inst_1) (Submonoid.subtype.{u2} M _inst_1 S) (MonoidHom.mker.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.restrict_mker MonoidHom.restrict_mkerₓ'. -/
@[simp, to_additive]
theorem restrict_mker (f : M →* N) : (f.restrict S).mker = f.mker.comap S.Subtype :=
  rfl
#align monoid_hom.restrict_mker MonoidHom.restrict_mker
#align add_monoid_hom.restrict_mker AddMonoidHom.restrict_mker

/- warning: monoid_hom.range_restrict_mker -> MonoidHom.mrangeRestrict_mker is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mker.{u1, u2, max u2 u1} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) (MonoidHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (MonoidHom.monoidHomClass.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) _inst_1 (Submonoid.toMulOneClass.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (MonoidHom.mrangeRestrict.{u1, u2} M _inst_1 N _inst_2 f)) (MonoidHom.mker.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u2} (Submonoid.{u2} M _inst_1) (MonoidHom.mker.{u2, u1, max u2 u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f)) (MonoidHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (MonoidHom.monoidHomClass.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) _inst_1 (Submonoid.toMulOneClass.{u1} N _inst_2 (MonoidHom.mrange.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f))) (MonoidHom.mrangeRestrict.{u2, u1} M _inst_1 N _inst_2 f)) (MonoidHom.mker.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.range_restrict_mker MonoidHom.mrangeRestrict_mkerₓ'. -/
@[to_additive]
theorem mrangeRestrict_mker (f : M →* N) : mker (mrangeRestrict f) = mker f :=
  by
  ext
  change (⟨f x, _⟩ : mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp only
#align monoid_hom.range_restrict_mker MonoidHom.mrangeRestrict_mker
#align add_monoid_hom.range_restrict_mker AddMonoidHom.mrangeRestrict_mker

/- warning: monoid_hom.mker_one -> MonoidHom.mker_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mker.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (OfNat.mk.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (One.one.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{succ u2} (Submonoid.{u2} M _inst_1) (MonoidHom.mker.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) 1 (One.toOfNat1.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (instOneMonoidHom.{u2, u1} M N _inst_1 _inst_2)))) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mker_one MonoidHom.mker_oneₓ'. -/
@[simp, to_additive]
theorem mker_one : (1 : M →* N).mker = ⊤ := by
  ext
  simp [mem_mker]
#align monoid_hom.mker_one MonoidHom.mker_one
#align add_monoid_hom.mker_zero AddMonoidHom.mker_zero

/- warning: monoid_hom.prod_map_comap_prod' -> MonoidHom.prod_map_comap_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_4 : MulOneClass.{u3} M'] [_inst_5 : MulOneClass.{u4} N'] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u4} M' N' _inst_4 _inst_5) (S : Submonoid.{u2} N _inst_2) (S' : Submonoid.{u4} N' _inst_5), Eq.{succ (max u1 u3)} (Submonoid.{max u1 u3} (Prod.{u1, u3} M M') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4)) (Submonoid.comap.{max u1 u3, max u2 u4, max (max u2 u4) u1 u3} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5) (MonoidHom.{max u1 u3, max u2 u4} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5)) (MonoidHom.monoidHomClass.{max u1 u3, max u2 u4} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5)) (MonoidHom.prodMap.{u1, u3, u2, u4} M M' _inst_1 _inst_4 N N' _inst_2 _inst_5 f g) (Submonoid.prod.{u2, u4} N N' _inst_2 _inst_5 S S')) (Submonoid.prod.{u1, u3} M M' _inst_1 _inst_4 (Submonoid.comap.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f S) (Submonoid.comap.{u3, u4, max u4 u3} M' N' _inst_4 _inst_5 (MonoidHom.{u3, u4} M' N' _inst_4 _inst_5) (MonoidHom.monoidHomClass.{u3, u4} M' N' _inst_4 _inst_5) g S'))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {M' : Type.{u4}} {N' : Type.{u3}} [_inst_4 : MulOneClass.{u4} M'] [_inst_5 : MulOneClass.{u3} N'] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (g : MonoidHom.{u4, u3} M' N' _inst_4 _inst_5) (S : Submonoid.{u1} N _inst_2) (S' : Submonoid.{u3} N' _inst_5), Eq.{max (succ u2) (succ u4)} (Submonoid.{max u2 u4} (Prod.{u2, u4} M M') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4)) (Submonoid.comap.{max u2 u4, max u1 u3, max (max (max u3 u1) u4) u2} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5) (MonoidHom.{max u4 u2, max u3 u1} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5)) (MonoidHom.monoidHomClass.{max u2 u4, max u1 u3} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5)) (MonoidHom.prodMap.{u2, u4, u1, u3} M M' _inst_1 _inst_4 N N' _inst_2 _inst_5 f g) (Submonoid.prod.{u1, u3} N N' _inst_2 _inst_5 S S')) (Submonoid.prod.{u2, u4} M M' _inst_1 _inst_4 (Submonoid.comap.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f S) (Submonoid.comap.{u4, u3, max u4 u3} M' N' _inst_4 _inst_5 (MonoidHom.{u4, u3} M' N' _inst_4 _inst_5) (MonoidHom.monoidHomClass.{u4, u3} M' N' _inst_4 _inst_5) g S'))
Case conversion may be inaccurate. Consider using '#align monoid_hom.prod_map_comap_prod' MonoidHom.prod_map_comap_prod'ₓ'. -/
@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N']
    (f : M →* N) (g : M' →* N') (S : Submonoid N) (S' : Submonoid N') :
    (S.Prod S').comap (prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
#align monoid_hom.prod_map_comap_prod' MonoidHom.prod_map_comap_prod'
#align add_monoid_hom.prod_map_comap_prod' AddMonoidHom.prod_map_comap_prod'

/- warning: monoid_hom.mker_prod_map -> MonoidHom.mker_prod_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_4 : MulOneClass.{u3} M'] [_inst_5 : MulOneClass.{u4} N'] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u3, u4} M' N' _inst_4 _inst_5), Eq.{succ (max u1 u3)} (Submonoid.{max u1 u3} (Prod.{u1, u3} M M') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4)) (MonoidHom.mker.{max u1 u3, max u2 u4, max (max u2 u4) u1 u3} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5) (MonoidHom.{max u1 u3, max u2 u4} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5)) (MonoidHom.monoidHomClass.{max u1 u3, max u2 u4} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.mulOneClass.{u1, u3} M M' _inst_1 _inst_4) (Prod.mulOneClass.{u2, u4} N N' _inst_2 _inst_5)) (MonoidHom.prodMap.{u1, u3, u2, u4} M M' _inst_1 _inst_4 N N' _inst_2 _inst_5 f g)) (Submonoid.prod.{u1, u3} M M' _inst_1 _inst_4 (MonoidHom.mker.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f) (MonoidHom.mker.{u3, u4, max u4 u3} M' N' _inst_4 _inst_5 (MonoidHom.{u3, u4} M' N' _inst_4 _inst_5) (MonoidHom.monoidHomClass.{u3, u4} M' N' _inst_4 _inst_5) g))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {M' : Type.{u4}} {N' : Type.{u3}} [_inst_4 : MulOneClass.{u4} M'] [_inst_5 : MulOneClass.{u3} N'] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (g : MonoidHom.{u4, u3} M' N' _inst_4 _inst_5), Eq.{max (succ u2) (succ u4)} (Submonoid.{max u2 u4} (Prod.{u2, u4} M M') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4)) (MonoidHom.mker.{max u2 u4, max u1 u3, max (max (max u3 u1) u4) u2} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5) (MonoidHom.{max u4 u2, max u3 u1} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5)) (MonoidHom.monoidHomClass.{max u2 u4, max u1 u3} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulOneClassProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulOneClassProd.{u1, u3} N N' _inst_2 _inst_5)) (MonoidHom.prodMap.{u2, u4, u1, u3} M M' _inst_1 _inst_4 N N' _inst_2 _inst_5 f g)) (Submonoid.prod.{u2, u4} M M' _inst_1 _inst_4 (MonoidHom.mker.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f) (MonoidHom.mker.{u4, u3, max u4 u3} M' N' _inst_4 _inst_5 (MonoidHom.{u4, u3} M' N' _inst_4 _inst_5) (MonoidHom.monoidHomClass.{u4, u3} M' N' _inst_4 _inst_5) g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mker_prod_map MonoidHom.mker_prod_mapₓ'. -/
@[to_additive]
theorem mker_prod_map {M' : Type _} {N' : Type _} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') : (prodMap f g).mker = f.mker.Prod g.mker := by
  rw [← comap_bot', ← comap_bot', ← comap_bot', ← prod_map_comap_prod', bot_prod_bot]
#align monoid_hom.mker_prod_map MonoidHom.mker_prod_map
#align add_monoid_hom.mker_prod_map AddMonoidHom.mker_prod_map

/- warning: monoid_hom.mker_inl -> MonoidHom.mker_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mker.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{succ u2} (Submonoid.{u2} M _inst_1) (MonoidHom.mker.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mker_inl MonoidHom.mker_inlₓ'. -/
@[simp, to_additive]
theorem mker_inl : (inl M N).mker = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inl MonoidHom.mker_inl
#align add_monoid_hom.mker_inl AddMonoidHom.mker_inl

/- warning: monoid_hom.mker_inr -> MonoidHom.mker_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mker.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mker.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u2 u1} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instBotSubmonoid.{u2} N _inst_2))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mker_inr MonoidHom.mker_inrₓ'. -/
@[simp, to_additive]
theorem mker_inr : (inr M N).mker = ⊥ := by
  ext x
  simp [mem_mker]
#align monoid_hom.mker_inr MonoidHom.mker_inr
#align add_monoid_hom.mker_inr AddMonoidHom.mker_inr

/- warning: monoid_hom.submonoid_comap -> MonoidHom.submonoidComap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (N' : Submonoid.{u2} N _inst_2), MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (Submonoid.comap.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f N')) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) N') (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.comap.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f N')) (Submonoid.toMulOneClass.{u2} N _inst_2 N')
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (N' : Submonoid.{u2} N _inst_2), MonoidHom.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.comap.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f N'))) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x N')) (Submonoid.toMulOneClass.{u1} M _inst_1 (Submonoid.comap.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f N')) (Submonoid.toMulOneClass.{u2} N _inst_2 N')
Case conversion may be inaccurate. Consider using '#align monoid_hom.submonoid_comap MonoidHom.submonoidComapₓ'. -/
/-- The `monoid_hom` from the preimage of a submonoid to itself. -/
@[to_additive "the `add_monoid_hom` from the preimage of an additive submonoid to itself.", simps]
def submonoidComap (f : M →* N) (N' : Submonoid N) : N'.comap f →* N'
    where
  toFun x := ⟨f x, x.Prop⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
#align monoid_hom.submonoid_comap MonoidHom.submonoidComap
#align add_monoid_hom.add_submonoid_comap AddMonoidHom.addSubmonoidComap

/- warning: monoid_hom.submonoid_map -> MonoidHom.submonoidMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (M' : Submonoid.{u1} M _inst_1), MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M')) (Submonoid.toMulOneClass.{u1} M _inst_1 M') (Submonoid.toMulOneClass.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (M' : Submonoid.{u1} M _inst_1), MonoidHom.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x M')) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u1} M _inst_1 M') (Submonoid.toMulOneClass.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))
Case conversion may be inaccurate. Consider using '#align monoid_hom.submonoid_map MonoidHom.submonoidMapₓ'. -/
/-- The `monoid_hom` from a submonoid to its image.
See `mul_equiv.submonoid_map` for a variant for `mul_equiv`s. -/
@[to_additive
      "the `add_monoid_hom` from an additive submonoid to its image. See\n`add_equiv.add_submonoid_map` for a variant for `add_equiv`s.",
  simps]
def submonoidMap (f : M →* N) (M' : Submonoid M) : M' →* M'.map f
    where
  toFun x := ⟨f x, ⟨x, x.Prop, rfl⟩⟩
  map_one' := Subtype.eq <| f.map_one
  map_mul' x y := Subtype.eq <| f.map_mul x y
#align monoid_hom.submonoid_map MonoidHom.submonoidMap
#align add_monoid_hom.add_submonoid_map AddMonoidHom.addSubmonoidMap

/- warning: monoid_hom.submonoid_map_surjective -> MonoidHom.submonoidMap_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (M' : Submonoid.{u1} M _inst_1), Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M')) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M')) (Submonoid.toMulOneClass.{u1} M _inst_1 M') (Submonoid.toMulOneClass.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))) (fun (_x : MonoidHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M')) (Submonoid.toMulOneClass.{u1} M _inst_1 M') (Submonoid.toMulOneClass.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))) => (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') -> (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))) (MonoidHom.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M')) (Submonoid.toMulOneClass.{u1} M _inst_1 M') (Submonoid.toMulOneClass.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f M'))) (MonoidHom.submonoidMap.{u1, u2} M N _inst_1 _inst_2 f M'))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (M' : Submonoid.{u2} M _inst_1), Function.Surjective.{succ u2, succ u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u2} M _inst_1 M') (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u2} M _inst_1 M') (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (MulOneClass.toMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Submonoid.toMulOneClass.{u2} M _inst_1 M')) (MulOneClass.toMul.{u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u2} M _inst_1 M') (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u2} M _inst_1 M') (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M')) (MonoidHom.monoidHomClass.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Submonoid.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u1} N _inst_2)) x (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))) (Submonoid.toMulOneClass.{u2} M _inst_1 M') (Submonoid.toMulOneClass.{u1} N _inst_2 (Submonoid.map.{u2, u1, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2) f M'))))) (MonoidHom.submonoidMap.{u2, u1} M N _inst_1 _inst_2 f M'))
Case conversion may be inaccurate. Consider using '#align monoid_hom.submonoid_map_surjective MonoidHom.submonoidMap_surjectiveₓ'. -/
@[to_additive]
theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') :=
  by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
#align monoid_hom.submonoid_map_surjective MonoidHom.submonoidMap_surjective
#align add_monoid_hom.add_submonoid_map_surjective AddMonoidHom.addSubmonoidMap_surjective

end MonoidHom

namespace Submonoid

open MonoidHom

/- warning: submonoid.mrange_inl -> Submonoid.mrange_inl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1)) (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_inl Submonoid.mrange_inlₓ'. -/
@[to_additive]
theorem mrange_inl : (inl M N).mrange = prod ⊤ ⊥ := by simpa only [mrange_eq_map] using map_inl ⊤
#align submonoid.mrange_inl Submonoid.mrange_inl
#align add_submonoid.mrange_inl AddSubmonoid.mrange_inl

/- warning: submonoid.mrange_inr -> Submonoid.mrange_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1)) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u1, max u2 u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1)) (Top.top.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instTopSubmonoid.{u1} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_inr Submonoid.mrange_inrₓ'. -/
@[to_additive]
theorem mrange_inr : (inr M N).mrange = prod ⊥ ⊤ := by simpa only [mrange_eq_map] using map_inr ⊤
#align submonoid.mrange_inr Submonoid.mrange_inr
#align add_submonoid.mrange_inr AddSubmonoid.mrange_inr

/- warning: submonoid.mrange_inl' -> Submonoid.mrange_inl' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.comap.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2) (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.comap.{max u2 u1, u1, max u2 u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u2, u1} M N _inst_1 _inst_2) (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_inl' Submonoid.mrange_inl'ₓ'. -/
@[to_additive]
theorem mrange_inl' : (inl M N).mrange = comap (snd M N) ⊥ :=
  mrange_inl.trans (top_prod _)
#align submonoid.mrange_inl' Submonoid.mrange_inl'
#align add_submonoid.mrange_inl' AddSubmonoid.mrange_inl'

/- warning: submonoid.mrange_inr' -> Submonoid.mrange_inr' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.comap.{max u1 u2, u1, max u1 u2} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u1, max u2 u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.comap.{max u2 u1, u2, max u2 u1} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2) (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_inr' Submonoid.mrange_inr'ₓ'. -/
@[to_additive]
theorem mrange_inr' : (inr M N).mrange = comap (fst M N) ⊥ :=
  mrange_inr.trans (prod_top _)
#align submonoid.mrange_inr' Submonoid.mrange_inr'
#align add_submonoid.mrange_inr' AddSubmonoid.mrange_inr'

/- warning: submonoid.mrange_fst -> Submonoid.mrange_fst is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mrange.{max u1 u2, u1, max u1 u2} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u1, u2} M N _inst_1 _inst_2)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{succ u2} (Submonoid.{u2} M _inst_1) (MonoidHom.mrange.{max u2 u1, u2, max u2 u1} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MonoidHom.{max u1 u2, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.monoidHomClass.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) _inst_1) (MonoidHom.fst.{u2, u1} M N _inst_1 _inst_2)) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_fst Submonoid.mrange_fstₓ'. -/
@[simp, to_additive]
theorem mrange_fst : (fst M N).mrange = ⊤ :=
  mrange_top_of_surjective (fst M N) <| @Prod.fst_surjective _ _ ⟨1⟩
#align submonoid.mrange_fst Submonoid.mrange_fst
#align add_submonoid.mrange_fst AddSubmonoid.mrange_fst

/- warning: submonoid.mrange_snd -> Submonoid.mrange_snd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2)) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ u2} (Submonoid.{u2} N _inst_2) (MonoidHom.mrange.{max u1 u2, u2, max u1 u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MonoidHom.{max u2 u1, u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.monoidHomClass.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.instMulOneClassProd.{u1, u2} M N _inst_1 _inst_2) _inst_2) (MonoidHom.snd.{u1, u2} M N _inst_1 _inst_2)) (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.instTopSubmonoid.{u2} N _inst_2))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_snd Submonoid.mrange_sndₓ'. -/
@[simp, to_additive]
theorem mrange_snd : (snd M N).mrange = ⊤ :=
  mrange_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩
#align submonoid.mrange_snd Submonoid.mrange_snd
#align add_submonoid.mrange_snd AddSubmonoid.mrange_snd

/- warning: submonoid.prod_eq_bot_iff -> Submonoid.prod_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s : Submonoid.{u1} M _inst_1} {t : Submonoid.{u2} N _inst_2}, Iff (Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t) (Bot.bot.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.hasBot.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)))) (And (Eq.{succ u1} (Submonoid.{u1} M _inst_1) s (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Eq.{succ u2} (Submonoid.{u2} N _inst_2) t (Bot.bot.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasBot.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s : Submonoid.{u2} M _inst_1} {t : Submonoid.{u1} N _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t) (Bot.bot.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instBotSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))) (And (Eq.{succ u2} (Submonoid.{u2} M _inst_1) s (Bot.bot.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instBotSubmonoid.{u2} M _inst_1))) (Eq.{succ u1} (Submonoid.{u1} N _inst_2) t (Bot.bot.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instBotSubmonoid.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align submonoid.prod_eq_bot_iff Submonoid.prod_eq_bot_iffₓ'. -/
@[to_additive]
theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.Prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot', mker_inl, mker_inr]
#align submonoid.prod_eq_bot_iff Submonoid.prod_eq_bot_iff
#align add_submonoid.prod_eq_bot_iff AddSubmonoid.prod_eq_bot_iff

/- warning: submonoid.prod_eq_top_iff -> Submonoid.prod_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {s : Submonoid.{u1} M _inst_1} {t : Submonoid.{u2} N _inst_2}, Iff (Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.prod.{u1, u2} M N _inst_1 _inst_2 s t) (Top.top.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.hasTop.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)))) (And (Eq.{succ u1} (Submonoid.{u1} M _inst_1) s (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) (Eq.{succ u2} (Submonoid.{u2} N _inst_2) t (Top.top.{u2} (Submonoid.{u2} N _inst_2) (Submonoid.hasTop.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {s : Submonoid.{u2} M _inst_1} {t : Submonoid.{u1} N _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.prod.{u2, u1} M N _inst_1 _inst_2 s t) (Top.top.{max u2 u1} (Submonoid.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instTopSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))) (And (Eq.{succ u2} (Submonoid.{u2} M _inst_1) s (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))) (Eq.{succ u1} (Submonoid.{u1} N _inst_2) t (Top.top.{u1} (Submonoid.{u1} N _inst_2) (Submonoid.instTopSubmonoid.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align submonoid.prod_eq_top_iff Submonoid.prod_eq_top_iffₓ'. -/
@[to_additive]
theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.Prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← mrange_eq_map, mrange_fst,
    mrange_snd]
#align submonoid.prod_eq_top_iff Submonoid.prod_eq_top_iff
#align add_submonoid.prod_eq_top_iff AddSubmonoid.prod_eq_top_iff

/- warning: submonoid.mrange_inl_sup_mrange_inr -> Submonoid.mrange_inl_sup_mrange_inr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Eq.{succ (max u1 u2)} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (HasSup.sup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (SemilatticeSup.toHasSup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.completeLattice.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2))))) (MonoidHom.mrange.{u1, max u1 u2, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u1 u2} M (Prod.{u1, u2} M N) _inst_1 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inl.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u2, max u1 u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u1 u2} N (Prod.{u1, u2} M N) _inst_2 (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (MonoidHom.inr.{u1, u2} M N _inst_1 _inst_2))) (Top.top.{max u1 u2} (Submonoid.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)) (Submonoid.hasTop.{max u1 u2} (Prod.{u1, u2} M N) (Prod.mulOneClass.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Eq.{max (succ u2) (succ u1)} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (HasSup.sup.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (SemilatticeSup.toHasSup.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Lattice.toSemilatticeSup.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toLattice.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instCompleteLatticeSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2))))) (MonoidHom.mrange.{u2, max u2 u1, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, max u1 u2} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u2, max u2 u1} M (Prod.{u2, u1} M N) _inst_1 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inl.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.mrange.{u1, max u2 u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u1, max u1 u2} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.monoidHomClass.{u1, max u2 u1} N (Prod.{u2, u1} M N) _inst_2 (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (MonoidHom.inr.{u2, u1} M N _inst_1 _inst_2))) (Top.top.{max u2 u1} (Submonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)) (Submonoid.instTopSubmonoid.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulOneClassProd.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align submonoid.mrange_inl_sup_mrange_inr Submonoid.mrange_inl_sup_mrange_inrₓ'. -/
@[simp, to_additive]
theorem mrange_inl_sup_mrange_inr : (inl M N).mrange ⊔ (inr M N).mrange = ⊤ := by
  simp only [mrange_inl, mrange_inr, prod_bot_sup_bot_prod, top_prod_top]
#align submonoid.mrange_inl_sup_mrange_inr Submonoid.mrange_inl_sup_mrange_inr
#align add_submonoid.mrange_inl_sup_mrange_inr AddSubmonoid.mrange_inl_sup_mrange_inr

/- warning: submonoid.inclusion -> Submonoid.inclusion is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S T) -> (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) T) (Submonoid.toMulOneClass.{u1} M _inst_1 S) (Submonoid.toMulOneClass.{u1} M _inst_1 T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) S T) -> (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x T)) (Submonoid.toMulOneClass.{u1} M _inst_1 S) (Submonoid.toMulOneClass.{u1} M _inst_1 T))
Case conversion may be inaccurate. Consider using '#align submonoid.inclusion Submonoid.inclusionₓ'. -/
/-- The monoid hom associated to an inclusion of submonoids. -/
@[to_additive "The `add_monoid` hom associated to an inclusion of submonoids."]
def inclusion {S T : Submonoid M} (h : S ≤ T) : S →* T :=
  S.Subtype.codRestrict _ fun x => h x.2
#align submonoid.inclusion Submonoid.inclusion
#align add_submonoid.inclusion AddSubmonoid.inclusion

/- warning: submonoid.range_subtype -> Submonoid.range_subtype is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mrange.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) s) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1 (MonoidHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) s) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1) (MonoidHom.monoidHomClass.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) s) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1) (Submonoid.subtype.{u1} M _inst_1 s)) s
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.mrange.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1 (MonoidHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1) (MonoidHom.monoidHomClass.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)) M (Submonoid.toMulOneClass.{u1} M _inst_1 s) _inst_1) (Submonoid.subtype.{u1} M _inst_1 s)) s
Case conversion may be inaccurate. Consider using '#align submonoid.range_subtype Submonoid.range_subtypeₓ'. -/
@[simp, to_additive]
theorem range_subtype (s : Submonoid M) : s.Subtype.mrange = s :=
  SetLike.coe_injective <| (coe_mrange _).trans <| Subtype.range_coe
#align submonoid.range_subtype Submonoid.range_subtype
#align add_submonoid.range_subtype AddSubmonoid.range_subtype

/- warning: submonoid.eq_top_iff' -> Submonoid.eq_top_iff' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) (forall (x : M), Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) (forall (x : M), Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)
Case conversion may be inaccurate. Consider using '#align submonoid.eq_top_iff' Submonoid.eq_top_iff'ₓ'. -/
@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align submonoid.eq_top_iff' Submonoid.eq_top_iff'
#align add_submonoid.eq_top_iff' AddSubmonoid.eq_top_iff'

/- warning: submonoid.eq_bot_iff_forall -> Submonoid.eq_bot_iff_forall is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (forall (x : M), (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))) (forall (x : M), (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align submonoid.eq_bot_iff_forall Submonoid.eq_bot_iff_forallₓ'. -/
@[to_additive]
theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) :=
  SetLike.ext_iff.trans <| by simp (config := { contextual := true }) [iff_def, S.one_mem]
#align submonoid.eq_bot_iff_forall Submonoid.eq_bot_iff_forall
#align add_submonoid.eq_bot_iff_forall AddSubmonoid.eq_bot_iff_forall

/- warning: submonoid.nontrivial_iff_exists_ne_one -> Submonoid.nontrivial_iff_exists_ne_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Nontrivial.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S)) (Exists.{succ u1} M (fun (x : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (fun (H : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) => Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Iff (Nontrivial.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S))) (Exists.{succ u1} M (fun (x : M) => And (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align submonoid.nontrivial_iff_exists_ne_one Submonoid.nontrivial_iff_exists_ne_oneₓ'. -/
@[to_additive]
theorem nontrivial_iff_exists_ne_one (S : Submonoid M) : Nontrivial S ↔ ∃ x ∈ S, x ≠ (1 : M) :=
  calc
    Nontrivial S ↔ ∃ x : S, x ≠ 1 := nontrivial_iff_exists_ne 1
    _ ↔ ∃ (x : _)(hx : x ∈ S), (⟨x, hx⟩ : S) ≠ ⟨1, S.one_mem⟩ := Subtype.exists
    _ ↔ ∃ x ∈ S, x ≠ (1 : M) := by simp only [Ne.def]
    
#align submonoid.nontrivial_iff_exists_ne_one Submonoid.nontrivial_iff_exists_ne_one
#align add_submonoid.nontrivial_iff_exists_ne_zero AddSubmonoid.nontrivial_iff_exists_ne_zero

/- warning: submonoid.bot_or_nontrivial -> Submonoid.bot_or_nontrivial is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Or (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Nontrivial.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Or (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))) (Nontrivial.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)))
Case conversion may be inaccurate. Consider using '#align submonoid.bot_or_nontrivial Submonoid.bot_or_nontrivialₓ'. -/
/-- A submonoid is either the trivial submonoid or nontrivial. -/
@[to_additive "An additive submonoid is either the trivial additive submonoid or nontrivial."]
theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [eq_bot_iff_forall, nontrivial_iff_exists_ne_one, ← not_forall, Classical.em]
#align submonoid.bot_or_nontrivial Submonoid.bot_or_nontrivial
#align add_submonoid.bot_or_nontrivial AddSubmonoid.bot_or_nontrivial

/- warning: submonoid.bot_or_exists_ne_one -> Submonoid.bot_or_exists_ne_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Or (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Exists.{succ u1} M (fun (x : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (fun (H : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) => Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Or (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))) (Exists.{succ u1} M (fun (x : M) => And (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align submonoid.bot_or_exists_ne_one Submonoid.bot_or_exists_ne_oneₓ'. -/
/-- A submonoid is either the trivial submonoid or contains a nonzero element. -/
@[to_additive
      "An additive submonoid is either the trivial additive submonoid or contains a nonzero\nelement."]
theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) :=
  S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp
#align submonoid.bot_or_exists_ne_one Submonoid.bot_or_exists_ne_one
#align add_submonoid.bot_or_exists_ne_zero AddSubmonoid.bot_or_exists_ne_zero

end Submonoid

namespace MulEquiv

variable {S} {T : Submonoid M}

/- warning: mul_equiv.submonoid_congr -> MulEquiv.submonoidCongr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S T) -> (MulEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) T) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u1} M _inst_1 T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S T) -> (MulEquiv.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x T)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u1} M _inst_1 T))
Case conversion may be inaccurate. Consider using '#align mul_equiv.submonoid_congr MulEquiv.submonoidCongrₓ'. -/
/-- Makes the identity isomorphism from a proof that two submonoids of a multiplicative
    monoid are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two\nsubmonoids of an additive monoid are equal."]
def submonoidCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.submonoid_congr MulEquiv.submonoidCongr
#align add_equiv.add_submonoid_congr AddEquiv.addSubmonoidCongr

/- warning: mul_equiv.of_left_inverse' -> MulEquiv.ofLeftInverse' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) {g : N -> M}, (Function.LeftInverse.{succ u1, succ u2} M N g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (MulEquiv.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)) (MulOneClass.toHasMul.{u1} M _inst_1) (Submonoid.mul.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) {g : N -> M}, (Function.LeftInverse.{succ u1, succ u2} M N g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2))) f)) -> (MulEquiv.{u1, u2} M (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f))) (MulOneClass.toMul.{u1} M _inst_1) (Submonoid.mul.{u2} N _inst_2 (MonoidHom.mrange.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) f)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.of_left_inverse' MulEquiv.ofLeftInverse'ₓ'. -/
-- this name is primed so that the version to `f.range` instead of `f.mrange` can be unprimed.
/-- A monoid homomorphism `f : M →* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.mrange`.

This is a bidirectional version of `monoid_hom.mrange_restrict`. -/
@[to_additive
      "\nAn additive monoid homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.mrange`.\n\nThis is a bidirectional version of `add_monoid_hom.mrange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse' (f : M →* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.mrange :=
  { f.mrangeRestrict with
    toFun := f.mrangeRestrict
    invFun := g ∘ f.mrange.Subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MonoidHom.mem_mrange.mp x.Prop
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse' MulEquiv.ofLeftInverse'
#align add_equiv.of_left_inverse' AddEquiv.ofLeftInverse'

/- warning: mul_equiv.submonoid_map -> MulEquiv.submonoidMap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (e : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (S : Submonoid.{u1} M _inst_1), MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.setLike.{u2} N _inst_2)) (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 e) S)) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u2 u1} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 e) S))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (e : MulEquiv.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2)) (S : Submonoid.{u1} M _inst_1), MulEquiv.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S)) (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N _inst_2) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N _inst_2) N (Submonoid.instSetLikeSubmonoid.{u2} N _inst_2)) x (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 e) S))) (Submonoid.mul.{u1} M _inst_1 S) (Submonoid.mul.{u2} N _inst_2 (Submonoid.map.{u1, u2, max u1 u2} M N _inst_1 _inst_2 (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 e) S))
Case conversion may be inaccurate. Consider using '#align mul_equiv.submonoid_map MulEquiv.submonoidMapₓ'. -/
/-- A `mul_equiv` `φ` between two monoids `M` and `N` induces a `mul_equiv` between
a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`.
See `monoid_hom.submonoid_map` for a variant for `monoid_hom`s. -/
@[to_additive
      "An `add_equiv` `φ` between two additive monoids `M` and `N` induces an `add_equiv`\nbetween a submonoid `S ≤ M` and the submonoid `φ(S) ≤ N`. See `add_monoid_hom.add_submonoid_map`\nfor a variant for `add_monoid_hom`s."]
def submonoidMap (e : M ≃* N) (S : Submonoid M) : S ≃* S.map e.toMonoidHom :=
  { (e : M ≃ N).image S with map_mul' := fun _ _ => Subtype.ext (map_mul e _ _) }
#align mul_equiv.submonoid_map MulEquiv.submonoidMap
#align add_equiv.add_submonoid_map AddEquiv.addSubmonoidMap

@[simp, to_additive]
theorem coe_submonoid_map_apply (e : M ≃* N) (S : Submonoid M) (g : S) :
    ((submonoidMap e S g : S.map (e : M →* N)) : N) = e g :=
  rfl
#align mul_equiv.coe_submonoid_map_apply MulEquiv.coe_submonoid_map_apply
#align add_equiv.coe_add_submonoid_map_apply AddEquiv.coe_add_submonoid_map_apply

@[simp, to_additive AddEquiv.add_submonoid_map_symm_apply]
theorem submonoid_map_symm_apply (e : M ≃* N) (S : Submonoid M) (g : S.map (e : M →* N)) :
    (e.submonoidMap S).symm g = ⟨e.symm g, SetLike.mem_coe.1 <| Set.mem_image_equiv.1 g.2⟩ :=
  rfl
#align mul_equiv.submonoid_map_symm_apply MulEquiv.submonoid_map_symm_apply
#align add_equiv.add_submonoid_map_symm_apply AddEquiv.add_submonoid_map_symm_apply

end MulEquiv

@[simp, to_additive]
theorem Submonoid.equiv_map_of_injective_coe_mul_equiv (e : M ≃* N) :
    S.equivMapOfInjective (e : M →* N) (EquivLike.injective e) = e.submonoidMap S :=
  by
  ext
  rfl
#align submonoid.equiv_map_of_injective_coe_mul_equiv Submonoid.equiv_map_of_injective_coe_mul_equiv
#align add_submonoid.equiv_map_of_injective_coe_add_equiv AddSubmonoid.equiv_map_of_injective_coe_add_equiv

section Actions

/-! ### Actions by `submonoid`s

These instances tranfer the action by an element `m : M` of a monoid `M` written as `m • a` onto the
action by an element `s : S` of a submonoid `S : submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `monoid.to_mul_action`, enabling
`s • m` as an alias for `↑s * m`.
-/


namespace Submonoid

variable {M' : Type _} {α β : Type _}

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance [SMul M' α] (S : Submonoid M') : SMul S α :=
  SMul.comp _ S.Subtype

/- warning: submonoid.smul_comm_class_left -> Submonoid.smulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : MulOneClass.{u1} M'] [_inst_5 : SMul.{u1, u3} M' β] [_inst_6 : SMul.{u2, u3} α β] [_inst_7 : SMulCommClass.{u1, u2, u3} M' α β _inst_5 _inst_6] (S : Submonoid.{u1} M' _inst_4), SMulCommClass.{u1, u2, u3} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) α β (Submonoid.hasSmul.{u1, u3} M' β _inst_4 _inst_5 S) _inst_6
but is expected to have type
  forall {M' : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : MulOneClass.{u1} M'] [_inst_5 : SMul.{u1, u3} M' β] [_inst_6 : SMul.{u2, u3} α β] [_inst_7 : SMulCommClass.{u1, u2, u3} M' α β _inst_5 _inst_6] (S : Submonoid.{u1} M' _inst_4), SMulCommClass.{u1, u2, u3} (Subtype.{succ u1} M' (fun (x : M') => Membership.mem.{u1, u1} M' (Submonoid.{u1} M' _inst_4) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u1} M' _inst_4)) x S)) α β (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u3} M' β _inst_4 _inst_5 S) _inst_6
Case conversion may be inaccurate. Consider using '#align submonoid.smul_comm_class_left Submonoid.smulCommClass_leftₓ'. -/
@[to_additive]
instance smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β] (S : Submonoid M') :
    SMulCommClass S α β :=
  ⟨fun a => (smul_comm (a : M') : _)⟩
#align submonoid.smul_comm_class_left Submonoid.smulCommClass_left
#align add_submonoid.vadd_comm_class_left AddSubmonoid.vaddCommClass_left

/- warning: submonoid.smul_comm_class_right -> Submonoid.smulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : MulOneClass.{u1} M'] [_inst_5 : SMul.{u2, u3} α β] [_inst_6 : SMul.{u1, u3} M' β] [_inst_7 : SMulCommClass.{u2, u1, u3} α M' β _inst_5 _inst_6] (S : Submonoid.{u1} M' _inst_4), SMulCommClass.{u2, u1, u3} α (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) β _inst_5 (Submonoid.hasSmul.{u1, u3} M' β _inst_4 _inst_6 S)
but is expected to have type
  forall {M' : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_4 : MulOneClass.{u1} M'] [_inst_5 : SMul.{u2, u3} α β] [_inst_6 : SMul.{u1, u3} M' β] [_inst_7 : SMulCommClass.{u2, u1, u3} α M' β _inst_5 _inst_6] (S : Submonoid.{u1} M' _inst_4), SMulCommClass.{u2, u1, u3} α (Subtype.{succ u1} M' (fun (x : M') => Membership.mem.{u1, u1} M' (Submonoid.{u1} M' _inst_4) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u1} M' _inst_4)) x S)) β _inst_5 (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u1, u3} M' β _inst_4 _inst_6 S)
Case conversion may be inaccurate. Consider using '#align submonoid.smul_comm_class_right Submonoid.smulCommClass_rightₓ'. -/
@[to_additive]
instance smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β] (S : Submonoid M') :
    SMulCommClass α S β :=
  ⟨fun a s => (smul_comm a (s : M') : _)⟩
#align submonoid.smul_comm_class_right Submonoid.smulCommClass_right
#align add_submonoid.vadd_comm_class_right AddSubmonoid.vaddCommClass_right

/-- Note that this provides `is_scalar_tower S M' M'` which is needed by `smul_mul_assoc`. -/
instance [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] (S : Submonoid M') :
    IsScalarTower S α β :=
  ⟨fun a => (smul_assoc (a : M') : _)⟩

/- warning: submonoid.smul_def -> Submonoid.smul_def is a dubious translation:
lean 3 declaration is
  forall {M' : Type.{u1}} {α : Type.{u2}} [_inst_4 : MulOneClass.{u1} M'] [_inst_5 : SMul.{u1, u2} M' α] {S : Submonoid.{u1} M' _inst_4} (g : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) (m : α), Eq.{succ u2} α (SMul.smul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) α (Submonoid.hasSmul.{u1, u2} M' α _inst_4 _inst_5 S) g m) (SMul.smul.{u1, u2} M' α _inst_5 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) M' (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) M' (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) M' (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M' _inst_4) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) S) M' (coeSubtype.{succ u1} M' (fun (x : M') => Membership.Mem.{u1, u1} M' (Submonoid.{u1} M' _inst_4) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M' _inst_4) M' (Submonoid.setLike.{u1} M' _inst_4)) x S))))) g) m)
but is expected to have type
  forall {M' : Type.{u2}} {α : Type.{u1}} [_inst_4 : MulOneClass.{u2} M'] [_inst_5 : SMul.{u2, u1} M' α] {S : Submonoid.{u2} M' _inst_4} (g : Subtype.{succ u2} M' (fun (x : M') => Membership.mem.{u2, u2} M' (Submonoid.{u2} M' _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u2} M' _inst_4)) x S)) (m : α), Eq.{succ u1} α (HSMul.hSMul.{u2, u1, u1} (Subtype.{succ u2} M' (fun (x : M') => Membership.mem.{u2, u2} M' (Submonoid.{u2} M' _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u2} M' _inst_4)) x S)) α α (instHSMul.{u2, u1} (Subtype.{succ u2} M' (fun (x : M') => Membership.mem.{u2, u2} M' (Submonoid.{u2} M' _inst_4) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u2} M' _inst_4)) x S)) α (Submonoid.instSMulSubtypeMemSubmonoidInstMembershipInstSetLikeSubmonoid.{u2, u1} M' α _inst_4 _inst_5 S)) g m) (HSMul.hSMul.{u2, u1, u1} M' α α (instHSMul.{u2, u1} M' α _inst_5) (Subtype.val.{succ u2} M' (fun (x : M') => Membership.mem.{u2, u2} M' (Set.{u2} M') (Set.instMembershipSet.{u2} M') x (SetLike.coe.{u2, u2} (Submonoid.{u2} M' _inst_4) M' (Submonoid.instSetLikeSubmonoid.{u2} M' _inst_4) S)) g) m)
Case conversion may be inaccurate. Consider using '#align submonoid.smul_def Submonoid.smul_defₓ'. -/
@[to_additive]
theorem smul_def [SMul M' α] {S : Submonoid M'} (g : S) (m : α) : g • m = (g : M') • m :=
  rfl
#align submonoid.smul_def Submonoid.smul_def
#align add_submonoid.vadd_def AddSubmonoid.vadd_def

instance [SMul M' α] [FaithfulSMul M' α] (S : Submonoid M') : FaithfulSMul S α :=
  ⟨fun x y h => Subtype.ext <| eq_of_smul_eq_smul h⟩

end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      "The additive action by an add_submonoid is the action by the underlying\nadd_monoid. "]
instance [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  MulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [AddMonoid α] [DistribMulAction M' α] (S : Submonoid M') : DistribMulAction S α :=
  DistribMulAction.compHom _ S.Subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance [Monoid α] [MulDistribMulAction M' α] (S : Submonoid M') : MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.Subtype

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

end Submonoid

end Actions

