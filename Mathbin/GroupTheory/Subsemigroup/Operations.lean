/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky, Jireh Loreaux

! This file was ported from Lean 3 source module group_theory.subsemigroup.operations
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subsemigroup.Basic
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Group.TypeTags

/-!
# Operations on `subsemigroup`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define various operations on `subsemigroup`s and `mul_hom`s.

## Main definitions

### Conversion between multiplicative and additive definitions

* `subsemigroup.to_add_subsemigroup`, `subsemigroup.to_add_subsemigroup'`,
  `add_subsemigroup.to_subsemigroup`, `add_subsemigroup.to_subsemigroup'`:
  convert between multiplicative and additive subsemigroups of `M`,
  `multiplicative M`, and `additive M`. These are stated as `order_iso`s.

### (Commutative) semigroup structure on a subsemigroup

* `subsemigroup.to_semigroup`, `subsemigroup.to_comm_semigroup`: a subsemigroup inherits a
  (commutative) semigroup structure.

### Operations on subsemigroups

* `subsemigroup.comap`: preimage of a subsemigroup under a semigroup homomorphism as a subsemigroup
  of the domain;
* `subsemigroup.map`: image of a subsemigroup under a semigroup homomorphism as a subsemigroup of
  the codomain;
* `subsemigroup.prod`: product of two subsemigroups `s : subsemigroup M` and `t : subsemigroup N`
  as a subsemigroup of `M × N`;

### Semigroup homomorphisms between subsemigroups

* `subsemigroup.subtype`: embedding of a subsemigroup into the ambient semigroup.
* `subsemigroup.inclusion`: given two subsemigroups `S`, `T` such that `S ≤ T`, `S.inclusion T` is
  the inclusion of `S` into `T` as a semigroup homomorphism;
* `mul_equiv.subsemigroup_congr`: converts a proof of `S = T` into a semigroup isomorphism between
  `S` and `T`.
* `subsemigroup.prod_equiv`: semigroup isomorphism between `s.prod t` and `s × t`;

### Operations on `mul_hom`s

* `mul_hom.srange`: range of a semigroup homomorphism as a subsemigroup of the codomain;
* `mul_hom.restrict`: restrict a semigroup homomorphism to a subsemigroup;
* `mul_hom.cod_restrict`: restrict the codomain of a semigroup homomorphism to a subsemigroup;
* `mul_hom.srange_restrict`: restrict a semigroup homomorphism to its range;

### Implementation notes

This file follows closely `group_theory/submonoid/operations.lean`, omitting only that which is
necessary.

## Tags

subsemigroup, range, product, map, comap
-/


variable {M N P σ : Type _}

/-!
### Conversion to/from `additive`/`multiplicative`
-/


section

variable [Mul M]

/- warning: subsemigroup.to_add_subsemigroup -> Subsemigroup.toAddSubsemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], OrderIso.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], OrderIso.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1))))))
Case conversion may be inaccurate. Consider using '#align subsemigroup.to_add_subsemigroup Subsemigroup.toAddSubsemigroupₓ'. -/
/-- Subsemigroups of semigroup `M` are isomorphic to additive subsemigroups of `additive M`. -/
@[simps]
def Subsemigroup.toAddSubsemigroup : Subsemigroup M ≃o AddSubsemigroup (Additive M)
    where
  toFun S :=
    { carrier := Additive.toMul ⁻¹' S
      add_mem' := fun _ _ => S.mul_mem' }
  invFun S :=
    { carrier := Additive.ofMul ⁻¹' S
      mul_mem' := fun _ _ => S.add_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align subsemigroup.to_add_subsemigroup Subsemigroup.toAddSubsemigroup

/- warning: add_subsemigroup.to_subsemigroup' -> AddSubsemigroup.toSubsemigroup' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], OrderIso.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1))))) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], OrderIso.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))))) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align add_subsemigroup.to_subsemigroup' AddSubsemigroup.toSubsemigroup'ₓ'. -/
/-- Additive subsemigroups of an additive semigroup `additive M` are isomorphic to subsemigroups
of `M`. -/
abbrev AddSubsemigroup.toSubsemigroup' : AddSubsemigroup (Additive M) ≃o Subsemigroup M :=
  Subsemigroup.toAddSubsemigroup.symm
#align add_subsemigroup.to_subsemigroup' AddSubsemigroup.toSubsemigroup'

/- warning: subsemigroup.to_add_subsemigroup_closure -> Subsemigroup.toAddSubsemigroup_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} M), Eq.{succ u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)))))) (fun (_x : RelIso.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))))) (LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1))))))) => (Subsemigroup.{u1} M _inst_1) -> (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1))) (RelIso.hasCoeToFun.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))))) (LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1))))))) (Subsemigroup.toAddSubsemigroup.{u1} M _inst_1) (Subsemigroup.closure.{u1} M _inst_1 S)) (AddSubsemigroup.closure.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1) (Set.preimage.{u1, u1} (Additive.{u1} M) M (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} M) M) => (Additive.{u1} M) -> M) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.toMul.{u1} M)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subsemigroup.{u1} M _inst_1) => AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.closure.{u1} M _inst_1 S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1))) (Subsemigroup.{u1} M _inst_1) (fun (_x : Subsemigroup.{u1} M _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subsemigroup.{u1} M _inst_1) => AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1))) (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))) (RelEmbedding.toEmbedding.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Subsemigroup.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Subsemigroup.{u1} M _inst_1) => LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Subsemigroup.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Subsemigroup.{u1} M _inst_1) => LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (Subsemigroup.toAddSubsemigroup.{u1} M _inst_1))) (Subsemigroup.closure.{u1} M _inst_1 S)) (AddSubsemigroup.closure.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1) (Set.preimage.{u1, u1} (Additive.{u1} M) M (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) (fun (_x : Additive.{u1} M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u1} M) => M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) M (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} M) M) (Additive.{u1} M) M (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Additive.{u1} M) M))) (Additive.toMul.{u1} M)) S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.to_add_subsemigroup_closure Subsemigroup.toAddSubsemigroup_closureₓ'. -/
theorem Subsemigroup.toAddSubsemigroup_closure (S : Set M) :
    (Subsemigroup.closure S).toAddSubsemigroup = AddSubsemigroup.closure (Additive.toMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup.le_symm_apply.1 <|
      Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
#align subsemigroup.to_add_subsemigroup_closure Subsemigroup.toAddSubsemigroup_closure

/- warning: add_subsemigroup.to_subsemigroup'_closure -> AddSubsemigroup.toSubsemigroup'_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Additive.{u1} M)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1))))) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))))) (fun (_x : RelIso.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)))))) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))))) => (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) -> (Subsemigroup.{u1} M _inst_1)) (RelIso.hasCoeToFun.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)) (Additive.{u1} M) (AddSubsemigroup.setLike.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1)))))) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))))) (AddSubsemigroup.toSubsemigroup'.{u1} M _inst_1) (AddSubsemigroup.closure.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_1) S)) (Subsemigroup.closure.{u1} M _inst_1 (Set.preimage.{u1, u1} M (Multiplicative.{u1} M) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) (fun (_x : Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) => M -> (Multiplicative.{u1} M)) (Equiv.hasCoeToFun.{succ u1, succ u1} M (Multiplicative.{u1} M)) (Multiplicative.ofAdd.{u1} M)) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (S : Set.{u1} (Additive.{u1} M)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => Subsemigroup.{u1} M _inst_1) (AddSubsemigroup.closure.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1) S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1)) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (fun (_x : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => Subsemigroup.{u1} M _inst_1) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1)) (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1))) (RelEmbedding.toEmbedding.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Subsemigroup.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Subsemigroup.{u1} M _inst_1) => LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Subsemigroup.{u1} M _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) => LE.le.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Subsemigroup.{u1} M _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Subsemigroup.{u1} M _inst_1) => LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (AddSubsemigroup.toSubsemigroup'.{u1} M _inst_1))) (AddSubsemigroup.closure.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_1) S)) (Subsemigroup.closure.{u1} M _inst_1 (Set.preimage.{u1, u1} M (Multiplicative.{u1} M) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Multiplicative.{u1} M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (Multiplicative.{u1} M) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Multiplicative.{u1} M)) M (Multiplicative.{u1} M) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} M (Multiplicative.{u1} M)))) (Multiplicative.ofAdd.{u1} M)) S))
Case conversion may be inaccurate. Consider using '#align add_subsemigroup.to_subsemigroup'_closure AddSubsemigroup.toSubsemigroup'_closureₓ'. -/
theorem AddSubsemigroup.toSubsemigroup'_closure (S : Set (Additive M)) :
    (AddSubsemigroup.closure S).toSubsemigroup' =
      Subsemigroup.closure (Multiplicative.ofAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup'.le_symm_apply.1 <|
      AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
#align add_subsemigroup.to_subsemigroup'_closure AddSubsemigroup.toSubsemigroup'_closure

end

section

variable {A : Type _} [Add A]

/- warning: add_subsemigroup.to_subsemigroup -> AddSubsemigroup.toSubsemigroup is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A], OrderIso.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1)))) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A], OrderIso.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1))))) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1))))))
Case conversion may be inaccurate. Consider using '#align add_subsemigroup.to_subsemigroup AddSubsemigroup.toSubsemigroupₓ'. -/
/-- Additive subsemigroups of an additive semigroup `A` are isomorphic to
multiplicative subsemigroups of `multiplicative A`. -/
@[simps]
def AddSubsemigroup.toSubsemigroup : AddSubsemigroup A ≃o Subsemigroup (Multiplicative A)
    where
  toFun S :=
    { carrier := Multiplicative.toAdd ⁻¹' S
      mul_mem' := fun _ _ => S.add_mem' }
  invFun S :=
    { carrier := Multiplicative.ofAdd ⁻¹' S
      add_mem' := fun _ _ => S.mul_mem' }
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl
  map_rel_iff' a b := Iff.rfl
#align add_subsemigroup.to_subsemigroup AddSubsemigroup.toSubsemigroup

/- warning: subsemigroup.to_add_subsemigroup' -> Subsemigroup.toAddSubsemigroup' is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A], OrderIso.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1))))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A], OrderIso.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1)))))
Case conversion may be inaccurate. Consider using '#align subsemigroup.to_add_subsemigroup' Subsemigroup.toAddSubsemigroup'ₓ'. -/
/-- Subsemigroups of a semigroup `multiplicative A` are isomorphic to additive subsemigroups
of `A`. -/
abbrev Subsemigroup.toAddSubsemigroup' : Subsemigroup (Multiplicative A) ≃o AddSubsemigroup A :=
  AddSubsemigroup.toSubsemigroup.symm
#align subsemigroup.to_add_subsemigroup' Subsemigroup.toAddSubsemigroup'

/- warning: add_subsemigroup.to_subsemigroup_closure -> AddSubsemigroup.toSubsemigroup_closure is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A] (S : Set.{u1} A), Eq.{succ u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1)))) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)))))) (fun (_x : RelIso.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1))))) (LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1))))))) => (AddSubsemigroup.{u1} A _inst_1) -> (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1))) (RelIso.hasCoeToFun.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1))))) (LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1))))))) (AddSubsemigroup.toSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.closure.{u1} A _inst_1 S)) (Subsemigroup.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1) (Set.preimage.{u1, u1} (Multiplicative.{u1} A) A (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) => (Multiplicative.{u1} A) -> A) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.toAdd.{u1} A)) S))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A] (S : Set.{u1} A), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubsemigroup.{u1} A _inst_1) => Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.closure.{u1} A _inst_1 S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1))) (AddSubsemigroup.{u1} A _inst_1) (fun (_x : AddSubsemigroup.{u1} A _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : AddSubsemigroup.{u1} A _inst_1) => Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1))) (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))) (RelEmbedding.toEmbedding.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubsemigroup.{u1} A _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubsemigroup.{u1} A _inst_1) => LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : AddSubsemigroup.{u1} A _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : AddSubsemigroup.{u1} A _inst_1) => LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (AddSubsemigroup.toSubsemigroup.{u1} A _inst_1))) (AddSubsemigroup.closure.{u1} A _inst_1 S)) (Subsemigroup.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1) (Set.preimage.{u1, u1} (Multiplicative.{u1} A) A (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) (fun (_x : Multiplicative.{u1} A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u1} A) => A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) A (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} A) A) (Multiplicative.{u1} A) A (Equiv.instEquivLikeEquiv.{succ u1, succ u1} (Multiplicative.{u1} A) A))) (Multiplicative.toAdd.{u1} A)) S))
Case conversion may be inaccurate. Consider using '#align add_subsemigroup.to_subsemigroup_closure AddSubsemigroup.toSubsemigroup_closureₓ'. -/
theorem AddSubsemigroup.toSubsemigroup_closure (S : Set A) :
    (AddSubsemigroup.closure S).toSubsemigroup =
      Subsemigroup.closure (Multiplicative.toAdd ⁻¹' S) :=
  le_antisymm
    (AddSubsemigroup.toSubsemigroup.to_galois_connection.l_le <|
      AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
    (Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
#align add_subsemigroup.to_subsemigroup_closure AddSubsemigroup.toSubsemigroup_closure

/- warning: subsemigroup.to_add_subsemigroup'_closure -> Subsemigroup.toAddSubsemigroup'_closure is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A] (S : Set.{u1} (Multiplicative.{u1} A)), Eq.{succ u1} (AddSubsemigroup.{u1} A _inst_1) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1))))) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1))))) (fun (_x : RelIso.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)))))) (LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1)))))) => (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) -> (AddSubsemigroup.{u1} A _inst_1)) (RelIso.hasCoeToFun.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)) (Multiplicative.{u1} A) (Subsemigroup.setLike.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1)))))) (LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (SetLike.partialOrder.{u1, u1} (AddSubsemigroup.{u1} A _inst_1) A (AddSubsemigroup.setLike.{u1} A _inst_1)))))) (Subsemigroup.toAddSubsemigroup'.{u1} A _inst_1) (Subsemigroup.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.hasMul.{u1} A _inst_1) S)) (AddSubsemigroup.closure.{u1} A _inst_1 (Set.preimage.{u1, u1} A (Additive.{u1} A) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) (fun (_x : Equiv.{succ u1, succ u1} A (Additive.{u1} A)) => A -> (Additive.{u1} A)) (Equiv.hasCoeToFun.{succ u1, succ u1} A (Additive.{u1} A)) (Additive.ofMul.{u1} A)) S))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : Add.{u1} A] (S : Set.{u1} (Multiplicative.{u1} A)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => AddSubsemigroup.{u1} A _inst_1) (Subsemigroup.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1) S)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1)) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (fun (_x : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => AddSubsemigroup.{u1} A _inst_1) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1)) (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1))) (RelEmbedding.toEmbedding.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubsemigroup.{u1} A _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubsemigroup.{u1} A _inst_1) => LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u1, u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (AddSubsemigroup.{u1} A _inst_1) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) => LE.le.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Preorder.toLE.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1)))))) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : AddSubsemigroup.{u1} A _inst_1) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : AddSubsemigroup.{u1} A _inst_1) => LE.le.{u1} (AddSubsemigroup.{u1} A _inst_1) (Preorder.toLE.{u1} (AddSubsemigroup.{u1} A _inst_1) (PartialOrder.toPreorder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (AddSubsemigroup.{u1} A _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (AddSubsemigroup.{u1} A _inst_1) (AddSubsemigroup.instCompleteLatticeSubsemigroup.{u1} A _inst_1))))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (Subsemigroup.toAddSubsemigroup'.{u1} A _inst_1))) (Subsemigroup.closure.{u1} (Multiplicative.{u1} A) (Multiplicative.mul.{u1} A _inst_1) S)) (AddSubsemigroup.closure.{u1} A _inst_1 (Set.preimage.{u1, u1} A (Additive.{u1} A) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (fun (_x : A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Additive.{u1} A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (Additive.{u1} A) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Additive.{u1} A)) A (Additive.{u1} A) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} A (Additive.{u1} A)))) (Additive.ofMul.{u1} A)) S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.to_add_subsemigroup'_closure Subsemigroup.toAddSubsemigroup'_closureₓ'. -/
theorem Subsemigroup.toAddSubsemigroup'_closure (S : Set (Multiplicative A)) :
    (Subsemigroup.closure S).toAddSubsemigroup' = AddSubsemigroup.closure (Additive.ofMul ⁻¹' S) :=
  le_antisymm
    (Subsemigroup.toAddSubsemigroup'.to_galois_connection.l_le <|
      Subsemigroup.closure_le.2 AddSubsemigroup.subset_closure)
    (AddSubsemigroup.closure_le.2 Subsemigroup.subset_closure)
#align subsemigroup.to_add_subsemigroup'_closure Subsemigroup.toAddSubsemigroup'_closure

end

namespace Subsemigroup

open Set

/-!
### `comap` and `map`
-/


variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.comap /-
/-- The preimage of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The preimage of an `add_subsemigroup` along an `add_semigroup` homomorphism is an\n`add_subsemigroup`."]
def comap (f : M →ₙ* N) (S : Subsemigroup N) : Subsemigroup M
    where
  carrier := f ⁻¹' S
  mul_mem' a b ha hb := show f (a * b) ∈ S by rw [map_mul] <;> exact mul_mem ha hb
#align subsemigroup.comap Subsemigroup.comap
-/

#print Subsemigroup.coe_comap /-
@[simp, to_additive]
theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S :=
  rfl
#align subsemigroup.coe_comap Subsemigroup.coe_comap
-/

#print Subsemigroup.mem_comap /-
@[simp, to_additive]
theorem mem_comap {S : Subsemigroup N} {f : M →ₙ* N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align subsemigroup.mem_comap Subsemigroup.mem_comap
-/

#print Subsemigroup.comap_comap /-
@[to_additive]
theorem comap_comap (S : Subsemigroup P) (g : N →ₙ* P) (f : M →ₙ* N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl
#align subsemigroup.comap_comap Subsemigroup.comap_comap
-/

#print Subsemigroup.comap_id /-
@[simp, to_additive]
theorem comap_id (S : Subsemigroup P) : S.comap (MulHom.id _) = S :=
  ext (by simp)
#align subsemigroup.comap_id Subsemigroup.comap_id
-/

#print Subsemigroup.map /-
/-- The image of a subsemigroup along a semigroup homomorphism is a subsemigroup. -/
@[to_additive
      "The image of an `add_subsemigroup` along an `add_semigroup` homomorphism is\nan `add_subsemigroup`."]
def map (f : M →ₙ* N) (S : Subsemigroup M) : Subsemigroup N
    where
  carrier := f '' S
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, @mul_mem (Subsemigroup M) M _ _ _ _ _ _ hx hy, by rw [map_mul] <;> rfl⟩
#align subsemigroup.map Subsemigroup.map
-/

/- warning: subsemigroup.coe_map -> Subsemigroup.coe_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (S : Subsemigroup.{u1} M _inst_1), Eq.{succ u2} (Set.{u2} N) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (Set.image.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (S : Subsemigroup.{u2} M _inst_1), Eq.{succ u1} (Set.{u1} N) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)) (Set.image.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_map Subsemigroup.coe_mapₓ'. -/
@[simp, to_additive]
theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S :=
  rfl
#align subsemigroup.coe_map Subsemigroup.coe_map

/- warning: subsemigroup.mem_map -> Subsemigroup.mem_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2} {S : Subsemigroup.{u1} M _inst_1} {y : N}, Iff (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) y (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (Exists.{succ u1} M (fun (x : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S) (fun (H : Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S) => Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) y)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2} {S : Subsemigroup.{u2} M _inst_1} {y : N}, Iff (Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) y (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)) (Exists.{succ u2} M (fun (x : M) => And (Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S) (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) a) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) y)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_map Subsemigroup.mem_mapₓ'. -/
@[simp, to_additive]
theorem mem_map {f : M →ₙ* N} {S : Subsemigroup M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex
#align subsemigroup.mem_map Subsemigroup.mem_map

/- warning: subsemigroup.mem_map_of_mem -> Subsemigroup.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) {S : Subsemigroup.{u1} M _inst_1} {x : M}, (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S) -> (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) {S : Subsemigroup.{u2} M _inst_1} {x : M}, (Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S) -> (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_map_of_mem Subsemigroup.mem_map_of_memₓ'. -/
@[to_additive]
theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
#align subsemigroup.mem_map_of_mem Subsemigroup.mem_map_of_mem

/- warning: subsemigroup.apply_coe_mem_map -> Subsemigroup.apply_coe_mem_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (S : Subsemigroup.{u1} M _inst_1) (x : coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S), Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S))))) x)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (S : Subsemigroup.{u2} M _inst_1) (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) S)) x)) (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) S)) x)) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)
Case conversion may be inaccurate. Consider using '#align subsemigroup.apply_coe_mem_map Subsemigroup.apply_coe_mem_mapₓ'. -/
@[to_additive]
theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop
#align subsemigroup.apply_coe_mem_map Subsemigroup.apply_coe_mem_map

/- warning: subsemigroup.map_map -> Subsemigroup.map_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (S : Subsemigroup.{u1} M _inst_1) (g : MulHom.{u2, u3} N P _inst_2 _inst_3) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u3} (Subsemigroup.{u3} P _inst_3) (Subsemigroup.map.{u2, u3} N P _inst_2 _inst_3 g (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (Subsemigroup.map.{u1, u3} M P _inst_1 _inst_3 (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) S)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u3} N] [_inst_3 : Mul.{u2} P] (S : Subsemigroup.{u1} M _inst_1) (g : MulHom.{u3, u2} N P _inst_2 _inst_3) (f : MulHom.{u1, u3} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} P _inst_3) (Subsemigroup.map.{u3, u2} N P _inst_2 _inst_3 g (Subsemigroup.map.{u1, u3} M N _inst_1 _inst_2 f S)) (Subsemigroup.map.{u1, u2} M P _inst_1 _inst_3 (MulHom.comp.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 g f) S)
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_map Subsemigroup.map_mapₓ'. -/
@[to_additive]
theorem map_map (g : N →ₙ* P) (f : M →ₙ* N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
#align subsemigroup.map_map Subsemigroup.map_map

/- warning: subsemigroup.mem_map_iff_mem -> Subsemigroup.mem_map_iff_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall {S : Subsemigroup.{u1} M _inst_1} {x : M}, Iff (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (forall {S : Subsemigroup.{u2} M _inst_1} {x : M}, Iff (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)) (Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_map_iff_mem Subsemigroup.mem_map_iff_memₓ'. -/
@[to_additive]
theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S :=
  hf.mem_set_image
#align subsemigroup.mem_map_iff_mem Subsemigroup.mem_map_iff_mem

/- warning: subsemigroup.map_le_iff_le_comap -> Subsemigroup.map_le_iff_le_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2} {S : Subsemigroup.{u1} M _inst_1} {T : Subsemigroup.{u2} N _inst_2}, Iff (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) T) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2} {S : Subsemigroup.{u2} M _inst_1} {T : Subsemigroup.{u1} N _inst_2}, Iff (LE.le.{u1} (Subsemigroup.{u1} N _inst_2) (Preorder.toLE.{u1} (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2))))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S) T) (LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) S (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_le_iff_le_comap Subsemigroup.map_le_iff_le_comapₓ'. -/
@[to_additive]
theorem map_le_iff_le_comap {f : M →ₙ* N} {S : Subsemigroup M} {T : Subsemigroup N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
#align subsemigroup.map_le_iff_le_comap Subsemigroup.map_le_iff_le_comap

/- warning: subsemigroup.gc_map_comap -> Subsemigroup.gc_map_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), GaloisConnection.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), GaloisConnection.{u2, u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align subsemigroup.gc_map_comap Subsemigroup.gc_map_comapₓ'. -/
@[to_additive]
theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (map f) (comap f) := fun S T =>
  map_le_iff_le_comap
#align subsemigroup.gc_map_comap Subsemigroup.gc_map_comap

/- warning: subsemigroup.map_le_of_le_comap -> Subsemigroup.map_le_of_le_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {T : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T)) -> (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) T)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {T : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T)) -> (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2))))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) T)
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_le_of_le_comap Subsemigroup.map_le_of_le_comapₓ'. -/
@[to_additive]
theorem map_le_of_le_comap {T : Subsemigroup N} {f : M →ₙ* N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
#align subsemigroup.map_le_of_le_comap Subsemigroup.map_le_of_le_comap

/- warning: subsemigroup.le_comap_of_map_le -> Subsemigroup.le_comap_of_map_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {T : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) T) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {T : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2))))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) T) -> (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.le_comap_of_map_le Subsemigroup.le_comap_of_map_leₓ'. -/
@[to_additive]
theorem le_comap_of_map_le {T : Subsemigroup N} {f : M →ₙ* N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
#align subsemigroup.le_comap_of_map_le Subsemigroup.le_comap_of_map_le

/- warning: subsemigroup.le_comap_map -> Subsemigroup.le_comap_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (S : Subsemigroup.{u2} M _inst_1) {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) S (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.le_comap_map Subsemigroup.le_comap_mapₓ'. -/
@[to_additive]
theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align subsemigroup.le_comap_map Subsemigroup.le_comap_map

/- warning: subsemigroup.map_comap_le -> Subsemigroup.map_comap_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {S : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S)) S
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {S : Subsemigroup.{u2} N _inst_2} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2))))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S)) S
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_comap_le Subsemigroup.map_comap_leₓ'. -/
@[to_additive]
theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
#align subsemigroup.map_comap_le Subsemigroup.map_comap_le

/- warning: subsemigroup.monotone_map -> Subsemigroup.monotone_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, Monotone.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, Monotone.{u2, u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align subsemigroup.monotone_map Subsemigroup.monotone_mapₓ'. -/
@[to_additive]
theorem monotone_map {f : M →ₙ* N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
#align subsemigroup.monotone_map Subsemigroup.monotone_map

/- warning: subsemigroup.monotone_comap -> Subsemigroup.monotone_comap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, Monotone.{u2, u1} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, Monotone.{u1, u2} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align subsemigroup.monotone_comap Subsemigroup.monotone_comapₓ'. -/
@[to_additive]
theorem monotone_comap {f : M →ₙ* N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u
#align subsemigroup.monotone_comap Subsemigroup.monotone_comap

/- warning: subsemigroup.map_comap_map -> Subsemigroup.map_comap_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (S : Subsemigroup.{u2} M _inst_1) {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_comap_map Subsemigroup.map_comap_mapₓ'. -/
@[simp, to_additive]
theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _
#align subsemigroup.map_comap_map Subsemigroup.map_comap_map

#print Subsemigroup.comap_map_comap /-
@[simp, to_additive]
theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
#align subsemigroup.comap_map_comap Subsemigroup.comap_map_comap
-/

/- warning: subsemigroup.map_sup -> Subsemigroup.map_sup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) (T : Subsemigroup.{u1} M _inst_1) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1)))) S T)) (HasSup.sup.{u2} (Subsemigroup.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (S : Subsemigroup.{u2} M _inst_1) (T : Subsemigroup.{u2} M _inst_1) (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (HasSup.sup.{u2} (Subsemigroup.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) S T)) (HasSup.sup.{u1} (Subsemigroup.{u1} N _inst_2) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} N _inst_2) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_sup Subsemigroup.map_supₓ'. -/
@[to_additive]
theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup
#align subsemigroup.map_sup Subsemigroup.map_sup

/- warning: subsemigroup.map_supr -> Subsemigroup.map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Sort.{u3}} (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (s : ι -> (Subsemigroup.{u1} M _inst_1)), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (supᵢ.{u1, u3} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι s)) (supᵢ.{u2, u3} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2))) ι (fun (i : ι) => Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (s i)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {ι : Sort.{u3}} (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (s : ι -> (Subsemigroup.{u2} M _inst_1)), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (supᵢ.{u2, u3} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toSupSet.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)) ι s)) (supᵢ.{u1, u3} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toSupSet.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)) ι (fun (i : ι) => Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (s i)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_supr Subsemigroup.map_supᵢₓ'. -/
@[to_additive]
theorem map_supᵢ {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup M) :
    (supᵢ s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr
#align subsemigroup.map_supr Subsemigroup.map_supᵢ

/- warning: subsemigroup.comap_inf -> Subsemigroup.comap_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (HasInf.inf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) S T)) (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (HasInf.inf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instHasInfSubsemigroup.{u2} N _inst_2) S T)) (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instHasInfSubsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_inf Subsemigroup.comap_infₓ'. -/
@[to_additive]
theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf
#align subsemigroup.comap_inf Subsemigroup.comap_inf

/- warning: subsemigroup.comap_infi -> Subsemigroup.comap_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Sort.{u3}} (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (s : ι -> (Subsemigroup.{u2} N _inst_2)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (infᵢ.{u2, u3} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) ι s)) (infᵢ.{u1, u3} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) ι (fun (i : ι) => Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (s i)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {ι : Sort.{u3}} (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (s : ι -> (Subsemigroup.{u1} N _inst_2)), Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (infᵢ.{u1, u3} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instInfSetSubsemigroup.{u1} N _inst_2) ι s)) (infᵢ.{u2, u3} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u2} M _inst_1) ι (fun (i : ι) => Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (s i)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_infi Subsemigroup.comap_infᵢₓ'. -/
@[to_additive]
theorem comap_infᵢ {ι : Sort _} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (infᵢ s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi
#align subsemigroup.comap_infi Subsemigroup.comap_infᵢ

/- warning: subsemigroup.map_bot -> Subsemigroup.map_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Bot.bot.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasBot.{u1} M _inst_1))) (Bot.bot.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasBot.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (Bot.bot.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instBotSubsemigroup.{u2} M _inst_1))) (Bot.bot.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instBotSubsemigroup.{u1} N _inst_2))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_bot Subsemigroup.map_botₓ'. -/
@[simp, to_additive]
theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align subsemigroup.map_bot Subsemigroup.map_bot

/- warning: subsemigroup.comap_top -> Subsemigroup.comap_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))) (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))) (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_top Subsemigroup.comap_topₓ'. -/
@[simp, to_additive]
theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align subsemigroup.comap_top Subsemigroup.comap_top

#print Subsemigroup.map_id /-
@[simp, to_additive]
theorem map_id (S : Subsemigroup M) : S.map (MulHom.id M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩
#align subsemigroup.map_id Subsemigroup.map_id
-/

section GaloisCoinsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Injective f)

include hf

/- warning: subsemigroup.gci_map_comap -> Subsemigroup.gciMapComap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (GaloisCoinsertion.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (GaloisCoinsertion.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.gci_map_comap Subsemigroup.gciMapComapₓ'. -/
/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
@[to_additive " `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. "]
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]
#align subsemigroup.gci_map_comap Subsemigroup.gciMapComap

/- warning: subsemigroup.comap_map_eq_of_injective -> Subsemigroup.comap_map_eq_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : Subsemigroup.{u1} M _inst_1), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) S)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (forall (S : Subsemigroup.{u2} M _inst_1), Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)) S)
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_map_eq_of_injective Subsemigroup.comap_map_eq_of_injectiveₓ'. -/
@[to_additive]
theorem comap_map_eq_of_injective (S : Subsemigroup M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
#align subsemigroup.comap_map_eq_of_injective Subsemigroup.comap_map_eq_of_injective

#print Subsemigroup.comap_surjective_of_injective /-
@[to_additive]
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align subsemigroup.comap_surjective_of_injective Subsemigroup.comap_surjective_of_injective
-/

/- warning: subsemigroup.map_injective_of_injective -> Subsemigroup.map_injective_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Function.Injective.{succ u1, succ u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (Function.Injective.{succ u2, succ u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_injective_of_injective Subsemigroup.map_injective_of_injectiveₓ'. -/
@[to_additive]
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align subsemigroup.map_injective_of_injective Subsemigroup.map_injective_of_injective

/- warning: subsemigroup.comap_inf_map_of_injective -> Subsemigroup.comap_inf_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : Subsemigroup.{u1} M _inst_1) (T : Subsemigroup.{u1} M _inst_1), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (HasInf.inf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f T))) (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (forall (S : Subsemigroup.{u2} M _inst_1) (T : Subsemigroup.{u2} M _inst_1), Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (HasInf.inf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instHasInfSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f T))) (HasInf.inf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instHasInfSubsemigroup.{u2} M _inst_1) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_inf_map_of_injective Subsemigroup.comap_inf_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_inf_map_of_injective (S T : Subsemigroup M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
#align subsemigroup.comap_inf_map_of_injective Subsemigroup.comap_inf_map_of_injective

/- warning: subsemigroup.comap_infi_map_of_injective -> Subsemigroup.comap_infᵢ_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u3}} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : ι -> (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (infᵢ.{u2, succ u3} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) ι (fun (i : ι) => Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (S i)))) (infᵢ.{u1, succ u3} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) ι S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u1}} {f : MulHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f)) -> (forall (S : ι -> (Subsemigroup.{u3} M _inst_1)), Eq.{succ u3} (Subsemigroup.{u3} M _inst_1) (Subsemigroup.comap.{u3, u2} M N _inst_1 _inst_2 f (infᵢ.{u2, succ u1} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instInfSetSubsemigroup.{u2} N _inst_2) ι (fun (i : ι) => Subsemigroup.map.{u3, u2} M N _inst_1 _inst_2 f (S i)))) (infᵢ.{u3, succ u1} (Subsemigroup.{u3} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u3} M _inst_1) ι S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_infi_map_of_injective Subsemigroup.comap_infᵢ_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_infᵢ_map_of_injective (S : ι → Subsemigroup M) :
    (⨅ i, (S i).map f).comap f = infᵢ S :=
  (gciMapComap hf).u_infi_l _
#align subsemigroup.comap_infi_map_of_injective Subsemigroup.comap_infᵢ_map_of_injective

/- warning: subsemigroup.comap_sup_map_of_injective -> Subsemigroup.comap_sup_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : Subsemigroup.{u1} M _inst_1) (T : Subsemigroup.{u1} M _inst_1), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (HasSup.sup.{u2} (Subsemigroup.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f T))) (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (forall (S : Subsemigroup.{u2} M _inst_1) (T : Subsemigroup.{u2} M _inst_1), Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (HasSup.sup.{u1} (Subsemigroup.{u1} N _inst_2) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} N _inst_2) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f T))) (HasSup.sup.{u2} (Subsemigroup.{u2} M _inst_1) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} M _inst_1) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_sup_map_of_injective Subsemigroup.comap_sup_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_sup_map_of_injective (S T : Subsemigroup M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
#align subsemigroup.comap_sup_map_of_injective Subsemigroup.comap_sup_map_of_injective

/- warning: subsemigroup.comap_supr_map_of_injective -> Subsemigroup.comap_supᵢ_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u3}} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : ι -> (Subsemigroup.{u1} M _inst_1)), Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (supᵢ.{u2, succ u3} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2))) ι (fun (i : ι) => Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (S i)))) (supᵢ.{u1, succ u3} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι S))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u1}} {f : MulHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f)) -> (forall (S : ι -> (Subsemigroup.{u3} M _inst_1)), Eq.{succ u3} (Subsemigroup.{u3} M _inst_1) (Subsemigroup.comap.{u3, u2} M N _inst_1 _inst_2 f (supᵢ.{u2, succ u1} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toSupSet.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2)) ι (fun (i : ι) => Subsemigroup.map.{u3, u2} M N _inst_1 _inst_2 f (S i)))) (supᵢ.{u3, succ u1} (Subsemigroup.{u3} M _inst_1) (CompleteLattice.toSupSet.{u3} (Subsemigroup.{u3} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u3} M _inst_1)) ι S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_supr_map_of_injective Subsemigroup.comap_supᵢ_map_of_injectiveₓ'. -/
@[to_additive]
theorem comap_supᵢ_map_of_injective (S : ι → Subsemigroup M) :
    (⨆ i, (S i).map f).comap f = supᵢ S :=
  (gciMapComap hf).u_supr_l _
#align subsemigroup.comap_supr_map_of_injective Subsemigroup.comap_supᵢ_map_of_injective

/- warning: subsemigroup.map_le_map_iff_of_injective -> Subsemigroup.map_le_map_iff_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall {S : Subsemigroup.{u1} M _inst_1} {T : Subsemigroup.{u1} M _inst_1}, Iff (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f T)) (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (forall {S : Subsemigroup.{u2} M _inst_1} {T : Subsemigroup.{u2} M _inst_1}, Iff (LE.le.{u1} (Subsemigroup.{u1} N _inst_2) (Preorder.toLE.{u1} (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2))))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f T)) (LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_le_map_iff_of_injective Subsemigroup.map_le_map_iff_of_injectiveₓ'. -/
@[to_additive]
theorem map_le_map_iff_of_injective {S T : Subsemigroup M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
#align subsemigroup.map_le_map_iff_of_injective Subsemigroup.map_le_map_iff_of_injective

/- warning: subsemigroup.map_strict_mono_of_injective -> Subsemigroup.map_strictMono_of_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (StrictMono.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (StrictMono.{u2, u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2)))) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_strict_mono_of_injective Subsemigroup.map_strictMono_of_injectiveₓ'. -/
@[to_additive]
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l
#align subsemigroup.map_strict_mono_of_injective Subsemigroup.map_strictMono_of_injective

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →ₙ* N} (hf : Function.Surjective f)

include hf

/- warning: subsemigroup.gi_map_comap -> Subsemigroup.giMapComap is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (GaloisInsertion.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (GaloisInsertion.{u1, u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2)))) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.gi_map_comap Subsemigroup.giMapComapₓ'. -/
/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
@[to_additive " `map f` and `comap f` form a `galois_insertion` when `f` is surjective. "]
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
#align subsemigroup.gi_map_comap Subsemigroup.giMapComap

#print Subsemigroup.map_comap_eq_of_surjective /-
@[to_additive]
theorem map_comap_eq_of_surjective (S : Subsemigroup N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
#align subsemigroup.map_comap_eq_of_surjective Subsemigroup.map_comap_eq_of_surjective
-/

/- warning: subsemigroup.map_surjective_of_surjective -> Subsemigroup.map_surjective_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Function.Surjective.{succ u1, succ u2} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Function.Surjective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) -> (Function.Surjective.{succ u2, succ u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_surjective_of_surjective Subsemigroup.map_surjective_of_surjectiveₓ'. -/
@[to_additive]
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align subsemigroup.map_surjective_of_surjective Subsemigroup.map_surjective_of_surjective

#print Subsemigroup.comap_injective_of_surjective /-
@[to_additive]
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align subsemigroup.comap_injective_of_surjective Subsemigroup.comap_injective_of_surjective
-/

/- warning: subsemigroup.map_inf_comap_of_surjective -> Subsemigroup.map_inf_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))) (HasInf.inf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) S T))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (forall (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (HasInf.inf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instHasInfSubsemigroup.{u1} M _inst_1) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))) (HasInf.inf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instHasInfSubsemigroup.{u2} N _inst_2) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_inf_comap_of_surjective Subsemigroup.map_inf_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_inf_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
#align subsemigroup.map_inf_comap_of_surjective Subsemigroup.map_inf_comap_of_surjective

/- warning: subsemigroup.map_infi_comap_of_surjective -> Subsemigroup.map_infᵢ_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u3}} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : ι -> (Subsemigroup.{u2} N _inst_2)), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (infᵢ.{u1, succ u3} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasInf.{u1} M _inst_1) ι (fun (i : ι) => Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (S i)))) (infᵢ.{u2, succ u3} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasInf.{u2} N _inst_2) ι S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u3} N] {ι : Type.{u1}} {f : MulHom.{u2, u3} M N _inst_1 _inst_2}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MulHom.{u2, u3} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MulHom.{u2, u3} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u3} M N _inst_1 _inst_2)) f)) -> (forall (S : ι -> (Subsemigroup.{u3} N _inst_2)), Eq.{succ u3} (Subsemigroup.{u3} N _inst_2) (Subsemigroup.map.{u2, u3} M N _inst_1 _inst_2 f (infᵢ.{u2, succ u1} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instInfSetSubsemigroup.{u2} M _inst_1) ι (fun (i : ι) => Subsemigroup.comap.{u2, u3} M N _inst_1 _inst_2 f (S i)))) (infᵢ.{u3, succ u1} (Subsemigroup.{u3} N _inst_2) (Subsemigroup.instInfSetSubsemigroup.{u3} N _inst_2) ι S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_infi_comap_of_surjective Subsemigroup.map_infᵢ_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_infᵢ_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨅ i, (S i).comap f).map f = infᵢ S :=
  (giMapComap hf).l_infi_u _
#align subsemigroup.map_infi_comap_of_surjective Subsemigroup.map_infᵢ_comap_of_surjective

/- warning: subsemigroup.map_sup_comap_of_surjective -> Subsemigroup.map_sup_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1)))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))) (HasSup.sup.{u2} (Subsemigroup.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2)))) S T))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (forall (S : Subsemigroup.{u2} N _inst_2) (T : Subsemigroup.{u2} N _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (HasSup.sup.{u1} (Subsemigroup.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T))) (HasSup.sup.{u2} (Subsemigroup.{u2} N _inst_2) (SemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (Lattice.toSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toLattice.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2)))) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_sup_comap_of_surjective Subsemigroup.map_sup_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_sup_comap_of_surjective (S T : Subsemigroup N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
#align subsemigroup.map_sup_comap_of_surjective Subsemigroup.map_sup_comap_of_surjective

/- warning: subsemigroup.map_supr_comap_of_surjective -> Subsemigroup.map_supᵢ_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {ι : Type.{u3}} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall (S : ι -> (Subsemigroup.{u2} N _inst_2)), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (supᵢ.{u1, succ u3} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (S i)))) (supᵢ.{u2, succ u3} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeSup.toHasSup.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeSup.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.completeLattice.{u2} N _inst_2))) ι S))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u3} N] {ι : Type.{u1}} {f : MulHom.{u2, u3} M N _inst_1 _inst_2}, (Function.Surjective.{succ u2, succ u3} M N (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MulHom.{u2, u3} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MulHom.{u2, u3} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u3} M N _inst_1 _inst_2)) f)) -> (forall (S : ι -> (Subsemigroup.{u3} N _inst_2)), Eq.{succ u3} (Subsemigroup.{u3} N _inst_2) (Subsemigroup.map.{u2, u3} M N _inst_1 _inst_2 f (supᵢ.{u2, succ u1} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toSupSet.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1)) ι (fun (i : ι) => Subsemigroup.comap.{u2, u3} M N _inst_1 _inst_2 f (S i)))) (supᵢ.{u3, succ u1} (Subsemigroup.{u3} N _inst_2) (CompleteLattice.toSupSet.{u3} (Subsemigroup.{u3} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u3} N _inst_2)) ι S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_supr_comap_of_surjective Subsemigroup.map_supᵢ_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem map_supᵢ_comap_of_surjective (S : ι → Subsemigroup N) :
    (⨆ i, (S i).comap f).map f = supᵢ S :=
  (giMapComap hf).l_supr_u _
#align subsemigroup.map_supr_comap_of_surjective Subsemigroup.map_supᵢ_comap_of_surjective

/- warning: subsemigroup.comap_le_comap_iff_of_surjective -> Subsemigroup.comap_le_comap_iff_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (forall {S : Subsemigroup.{u2} N _inst_2} {T : Subsemigroup.{u2} N _inst_2}, Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T)) (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) S T))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (forall {S : Subsemigroup.{u2} N _inst_2} {T : Subsemigroup.{u2} N _inst_2}, Iff (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f T)) (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2))))) S T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_le_comap_iff_of_surjective Subsemigroup.comap_le_comap_iff_of_surjectiveₓ'. -/
@[to_additive]
theorem comap_le_comap_iff_of_surjective {S T : Subsemigroup N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
#align subsemigroup.comap_le_comap_iff_of_surjective Subsemigroup.comap_le_comap_iff_of_surjective

/- warning: subsemigroup.comap_strict_mono_of_surjective -> Subsemigroup.comap_strictMono_of_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (StrictMono.{u2, u1} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2)) f)) -> (StrictMono.{u2, u1} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} N _inst_2)))) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1)))) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align subsemigroup.comap_strict_mono_of_surjective Subsemigroup.comap_strictMono_of_surjectiveₓ'. -/
@[to_additive]
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u
#align subsemigroup.comap_strict_mono_of_surjective Subsemigroup.comap_strictMono_of_surjective

end GaloisInsertion

end Subsemigroup

namespace MulMemClass

variable {A : Type _} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

include hA

#print MulMemClass.mul /-
-- lower priority so other instances are found first
/-- A submagma of a magma inherits a multiplication. -/
@[to_additive "An additive submagma of an additive magma inherits an addition."]
instance (priority := 900) mul : Mul S' :=
  ⟨fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩⟩
#align mul_mem_class.has_mul MulMemClass.mul
-/

/- warning: mul_mem_class.coe_mul -> MulMemClass.coe_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : SetLike.{u2, u1} A M] [hA : MulMemClass.{u2, u1} A M _inst_1 _inst_2] (S' : A) (x : coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (y : coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S'), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (instHMul.{u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S')) x y)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) y))
but is expected to have type
  forall {M : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : SetLike.{u1, u2} A M] [hA : MulMemClass.{u1, u2} A M _inst_1 _inst_2] (S' : A) (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (y : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')), Eq.{succ u2} M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) (HMul.hMul.{u2, u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (instHMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S')) x y)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) x) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) y))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.coe_mul MulMemClass.coe_mulₓ'. -/
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, norm_cast, to_additive]
theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y :=
  rfl
#align mul_mem_class.coe_mul MulMemClass.coe_mul

/- warning: mul_mem_class.mk_mul_mk -> MulMemClass.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : SetLike.{u2, u1} A M] [hA : MulMemClass.{u2, u1} A M _inst_1 _inst_2] (S' : A) (x : M) (y : M) (hx : Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') (hy : Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) y S'), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S')) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S')) (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S')) (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S')) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S')) (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S')) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') x hx) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') y hy)) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y) (MulMemClass.mul_mem.{u2, u1} A M _inst_1 _inst_2 hA S' x y hx hy))
but is expected to have type
  forall {M : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : SetLike.{u1, u2} A M] [hA : MulMemClass.{u1, u2} A M _inst_1 _inst_2] (S' : A) (x : M) (y : M) (hx : Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') (hy : Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) y S'), Eq.{succ u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (HMul.hMul.{u2, u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (instHMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S')) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') x hx) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') y hy)) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y) (MulMemClass.mul_mem.{u1, u2} A M _inst_1 _inst_2 hA S' x y hx hy))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.mk_mul_mk MulMemClass.mk_mul_mkₓ'. -/
-- lower priority so later simp lemmas are used first; to appease simp_nf
@[simp, to_additive]
theorem mk_mul_mk (x y : M) (hx : x ∈ S') (hy : y ∈ S') :
    (⟨x, hx⟩ : S') * ⟨y, hy⟩ = ⟨x * y, mul_mem hx hy⟩ :=
  rfl
#align mul_mem_class.mk_mul_mk MulMemClass.mk_mul_mk

/- warning: mul_mem_class.mul_def -> MulMemClass.mul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : SetLike.{u2, u1} A M] [hA : MulMemClass.{u2, u1} A M _inst_1 _inst_2] (S' : A) (x : coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (y : coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S'), Eq.{succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (HMul.hMul.{u1, u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (instHMul.{u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S')) x y) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) y)) (MulMemClass.mul_mem.{u2, u1} A M _inst_1 _inst_2 hA S' ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))) y) (Subtype.property.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') x) (Subtype.property.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S') y)))
but is expected to have type
  forall {M : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : SetLike.{u1, u2} A M] [hA : MulMemClass.{u1, u2} A M _inst_1 _inst_2] (S' : A) (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (y : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')), Eq.{succ u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (HMul.hMul.{u2, u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (instHMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S')) x y) (Subtype.mk.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) x) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) y)) (MulMemClass.mul_mem.{u1, u2} A M _inst_1 _inst_2 hA S' (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) x) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} A M _inst_2 S')) y) (Subtype.property.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') x) (Subtype.property.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S') y)))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.mul_def MulMemClass.mul_defₓ'. -/
@[to_additive]
theorem mul_def (x y : S') : x * y = ⟨x * y, mul_mem x.2 y.2⟩ :=
  rfl
#align mul_mem_class.mul_def MulMemClass.mul_def

omit hA

/- warning: mul_mem_class.to_semigroup -> MulMemClass.toSemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_3 : Semigroup.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [_inst_5 : MulMemClass.{u2, u1} A M (Semigroup.toHasMul.{u1} M _inst_3) _inst_4] (S : A), Semigroup.{u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_3 : Semigroup.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [_inst_5 : MulMemClass.{u2, u1} A M (Semigroup.toMul.{u1} M _inst_3) _inst_4] (S : A), Semigroup.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M A (SetLike.instMembership.{u2, u1} A M _inst_4) x S))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.to_semigroup MulMemClass.toSemigroupₓ'. -/
/-- A subsemigroup of a semigroup inherits a semigroup structure. -/
@[to_additive "An `add_subsemigroup` of an `add_semigroup` inherits an `add_semigroup` structure."]
instance toSemigroup {M : Type _} [Semigroup M] {A : Type _} [SetLike A M] [MulMemClass A M]
    (S : A) : Semigroup S :=
  Subtype.coe_injective.Semigroup coe fun _ _ => rfl
#align mul_mem_class.to_semigroup MulMemClass.toSemigroup

/- warning: mul_mem_class.to_comm_semigroup -> MulMemClass.toCommSemigroup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_3 : CommSemigroup.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [_inst_5 : MulMemClass.{u2, u1} A M (Semigroup.toHasMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_3)) _inst_4] (S : A), CommSemigroup.{u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_4) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_3 : CommSemigroup.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [_inst_5 : MulMemClass.{u2, u1} A M (Semigroup.toMul.{u1} M (CommSemigroup.toSemigroup.{u1} M _inst_3)) _inst_4] (S : A), CommSemigroup.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u2} M A (SetLike.instMembership.{u2, u1} A M _inst_4) x S))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.to_comm_semigroup MulMemClass.toCommSemigroupₓ'. -/
/-- A subsemigroup of a `comm_semigroup` is a `comm_semigroup`. -/
@[to_additive "An `add_subsemigroup` of an `add_comm_semigroup` is an `add_comm_semigroup`."]
instance toCommSemigroup {M} [CommSemigroup M] {A : Type _} [SetLike A M] [MulMemClass A M]
    (S : A) : CommSemigroup S :=
  Subtype.coe_injective.CommSemigroup coe fun _ _ => rfl
#align mul_mem_class.to_comm_semigroup MulMemClass.toCommSemigroup

include hA

#print MulMemClass.subtype /-
/-- The natural semigroup hom from a subsemigroup of semigroup `M` to `M`. -/
@[to_additive "The natural semigroup hom from an `add_subsemigroup` of `add_semigroup` `M` to `M`."]
def subtype : S' →ₙ* M :=
  ⟨coe, fun _ _ => rfl⟩
#align mul_mem_class.subtype MulMemClass.subtype
-/

/- warning: mul_mem_class.coe_subtype -> MulMemClass.coe_subtype is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : SetLike.{u2, u1} A M] [hA : MulMemClass.{u2, u1} A M _inst_1 _inst_2] (S' : A), Eq.{succ u1} ((fun (_x : MulHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S') _inst_1) => (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') -> M) (MulMemClass.subtype.{u1, u2} M A _inst_1 _inst_2 hA S')) (coeFn.{succ u1, succ u1} (MulHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S') _inst_1) (fun (_x : MulHom.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S') _inst_1) => (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') -> M) (MulHom.hasCoeToFun.{u1, u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (MulMemClass.mul.{u1, u2} M A _inst_1 _inst_2 hA S') _inst_1) (MulMemClass.subtype.{u1, u2} M A _inst_1 _inst_2 hA S')) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} A Type.{u1} (SetLike.hasCoeToSort.{u2, u1} A M _inst_2) S') M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_2) x S'))))))
but is expected to have type
  forall {M : Type.{u2}} {A : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : SetLike.{u1, u2} A M] [hA : MulMemClass.{u1, u2} A M _inst_1 _inst_2] (S' : A), Eq.{succ u2} (forall (a : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) => M) a) (FunLike.coe.{succ u2, succ u2, succ u2} (MulHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) M (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S') _inst_1) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) => M) _x) (MulHomClass.toFunLike.{u2, u2, u2} (MulHom.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) M (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S') _inst_1) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) M (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S') _inst_1 (MulHom.mulHomClass.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S')) M (MulMemClass.mul.{u2, u1} M A _inst_1 _inst_2 hA S') _inst_1)) (MulMemClass.subtype.{u2, u1} M A _inst_1 _inst_2 hA S')) (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M A (SetLike.instMembership.{u1, u2} A M _inst_2) x S'))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.coe_subtype MulMemClass.coe_subtypeₓ'. -/
@[simp, to_additive]
theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = coe :=
  rfl
#align mul_mem_class.coe_subtype MulMemClass.coe_subtype

end MulMemClass

namespace Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.topEquiv /-
/-- The top subsemigroup is isomorphic to the semigroup. -/
@[to_additive "The top additive subsemigroup is isomorphic to the additive semigroup.", simps]
def topEquiv : (⊤ : Subsemigroup M) ≃* M
    where
  toFun x := x
  invFun x := ⟨x, mem_top x⟩
  left_inv x := x.eta _
  right_inv _ := rfl
  map_mul' _ _ := rfl
#align subsemigroup.top_equiv Subsemigroup.topEquiv
-/

#print Subsemigroup.topEquiv_toMulHom /-
@[simp, to_additive]
theorem topEquiv_toMulHom :
    (topEquiv : _ ≃* M).toMulHom = MulMemClass.subtype (⊤ : Subsemigroup M) :=
  rfl
#align subsemigroup.top_equiv_to_mul_hom Subsemigroup.topEquiv_toMulHom
-/

#print Subsemigroup.equivMapOfInjective /-
/-- A subsemigroup is isomorphic to its image under an injective function -/
@[to_additive "An additive subsemigroup is isomorphic to its image under an injective function"]
noncomputable def equivMapOfInjective (f : M →ₙ* N) (hf : Function.Injective f) : S ≃* S.map f :=
  { Equiv.Set.image f S hf with map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
#align subsemigroup.equiv_map_of_injective Subsemigroup.equivMapOfInjective
-/

/- warning: subsemigroup.coe_equiv_map_of_injective_apply -> Subsemigroup.coe_equivMapOfInjective_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (S : Subsemigroup.{u1} M _inst_1) (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (hf : Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) (x : coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S), Eq.{succ u2} N ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) N (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) N (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) N (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) N (coeSubtype.{succ u2} N (fun (x : N) => Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) x (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) S) (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))) (fun (_x : MulEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) S) (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))) => (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) -> (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))) (MulEquiv.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S)) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) S) (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f S))) (Subsemigroup.equivMapOfInjective.{u1, u2} M N _inst_1 _inst_2 S f hf) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) x S))))) x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (S : Subsemigroup.{u2} M _inst_1) (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (hf : Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)) (x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)), Eq.{succ u1} N (Subtype.val.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Set.{u1} N) (Set.instMembershipSet.{u1} N) x (SetLike.coe.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x S)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) S) (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f S)))))) (Subsemigroup.equivMapOfInjective.{u2, u1} M N _inst_1 _inst_2 S f hf) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) S)) x))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_equiv_map_of_injective_apply Subsemigroup.coe_equivMapOfInjective_applyₓ'. -/
@[simp, to_additive]
theorem coe_equivMapOfInjective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (equivMapOfInjective S f hf x : N) = f x :=
  rfl
#align subsemigroup.coe_equiv_map_of_injective_apply Subsemigroup.coe_equivMapOfInjective_apply

#print Subsemigroup.closure_closure_coe_preimage /-
@[simp, to_additive]
theorem closure_closure_coe_preimage {s : Set M} : closure ((coe : closure s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x =>
    (Subtype.recOn x) fun x hx _ =>
      by
      refine' closure_induction' _ (fun g hg => _) (fun g₁ g₂ hg₁ hg₂ => _) hx
      · exact subset_closure hg
      · exact Subsemigroup.mul_mem _
#align subsemigroup.closure_closure_coe_preimage Subsemigroup.closure_closure_coe_preimage
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Subsemigroup.prod /-
/-- Given `subsemigroup`s `s`, `t` of semigroups `M`, `N` respectively, `s × t` as a subsemigroup
of `M × N`. -/
@[to_additive Prod
      "Given `add_subsemigroup`s `s`, `t` of `add_semigroup`s `A`, `B` respectively,\n`s × t` as an `add_subsemigroup` of `A × B`."]
def prod (s : Subsemigroup M) (t : Subsemigroup N) : Subsemigroup (M × N)
    where
  carrier := s ×ˢ t
  mul_mem' p q hp hq := ⟨s.mul_mem hp.1 hq.1, t.mul_mem hp.2 hq.2⟩
#align subsemigroup.prod Subsemigroup.prod
-/

/- warning: subsemigroup.coe_prod -> Subsemigroup.coe_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (s : Subsemigroup.{u1} M _inst_1) (t : Subsemigroup.{u2} N _inst_2), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} M N)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Set.{max u1 u2} (Prod.{u1, u2} M N)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Subsemigroup.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2))))) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (Set.prod.{u1, u2} M N ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Subsemigroup.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (s : Subsemigroup.{u2} M _inst_1) (t : Subsemigroup.{u1} N _inst_2), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} M N)) (SetLike.coe.{max u2 u1, max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Prod.{u2, u1} M N) (Subsemigroup.instSetLikeSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (Set.prod.{u2, u1} M N (SetLike.coe.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) s) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) t))
Case conversion may be inaccurate. Consider using '#align subsemigroup.coe_prod Subsemigroup.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive coe_prod]
theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) : (s.Prod t : Set (M × N)) = s ×ˢ t :=
  rfl
#align subsemigroup.coe_prod Subsemigroup.coe_prod

/- warning: subsemigroup.mem_prod -> Subsemigroup.mem_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {s : Subsemigroup.{u1} M _inst_1} {t : Subsemigroup.{u2} N _inst_2} {p : Prod.{u1, u2} M N}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} M N) (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Subsemigroup.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2))) p (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (And (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) (Prod.fst.{u1, u2} M N p) s) (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Prod.snd.{u1, u2} M N p) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {s : Subsemigroup.{u2} M _inst_1} {t : Subsemigroup.{u1} N _inst_2} {p : Prod.{u2, u1} M N}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Prod.{u2, u1} M N) (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (SetLike.instMembership.{max u2 u1, max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Prod.{u2, u1} M N) (Subsemigroup.instSetLikeSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2))) p (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (And (Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) (Prod.fst.{u2, u1} M N p) s) (Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) (Prod.snd.{u2, u1} M N p) t))
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_prod Subsemigroup.mem_prodₓ'. -/
@[to_additive mem_prod]
theorem mem_prod {s : Subsemigroup M} {t : Subsemigroup N} {p : M × N} :
    p ∈ s.Prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align subsemigroup.mem_prod Subsemigroup.mem_prod

/- warning: subsemigroup.prod_mono -> Subsemigroup.prod_mono is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {s₁ : Subsemigroup.{u1} M _inst_1} {s₂ : Subsemigroup.{u1} M _inst_1} {t₁ : Subsemigroup.{u2} N _inst_2} {t₂ : Subsemigroup.{u2} N _inst_2}, (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) s₁ s₂) -> (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) t₁ t₂) -> (LE.le.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Subsemigroup.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2))))) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s₁ t₁) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s₂ t₂))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {s₁ : Subsemigroup.{u2} M _inst_1} {s₂ : Subsemigroup.{u2} M _inst_1} {t₁ : Subsemigroup.{u1} N _inst_2} {t₂ : Subsemigroup.{u1} N _inst_2}, (LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) s₁ s₂) -> (LE.le.{u1} (Subsemigroup.{u1} N _inst_2) (Preorder.toLE.{u1} (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2))))) t₁ t₂) -> (LE.le.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.instCompleteLatticeSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)))))) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s₁ t₁) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s₂ t₂))
Case conversion may be inaccurate. Consider using '#align subsemigroup.prod_mono Subsemigroup.prod_monoₓ'. -/
@[to_additive prod_mono]
theorem prod_mono {s₁ s₂ : Subsemigroup M} {t₁ t₂ : Subsemigroup N} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁.Prod t₁ ≤ s₂.Prod t₂ :=
  Set.prod_mono hs ht
#align subsemigroup.prod_mono Subsemigroup.prod_mono

/- warning: subsemigroup.prod_top -> Subsemigroup.prod_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (s : Subsemigroup.{u1} M _inst_1), Eq.{succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))) (Subsemigroup.comap.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MulHom.fst.{u1, u2} M N _inst_1 _inst_2) s)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (s : Subsemigroup.{u2} M _inst_1), Eq.{max (succ u2) (succ u1)} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))) (Subsemigroup.comap.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MulHom.fst.{u2, u1} M N _inst_1 _inst_2) s)
Case conversion may be inaccurate. Consider using '#align subsemigroup.prod_top Subsemigroup.prod_topₓ'. -/
@[to_additive prod_top]
theorem prod_top (s : Subsemigroup M) : s.Prod (⊤ : Subsemigroup N) = s.comap (MulHom.fst M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_fst]
#align subsemigroup.prod_top Subsemigroup.prod_top

#print Subsemigroup.top_prod /-
@[to_additive top_prod]
theorem top_prod (s : Subsemigroup N) : (⊤ : Subsemigroup M).Prod s = s.comap (MulHom.snd M N) :=
  ext fun x => by simp [mem_prod, MulHom.coe_snd]
#align subsemigroup.top_prod Subsemigroup.top_prod
-/

/- warning: subsemigroup.top_prod_top -> Subsemigroup.top_prod_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N], Eq.{succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1)) (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))) (Top.top.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.hasTop.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N], Eq.{max (succ u2) (succ u1)} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1)) (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))) (Top.top.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.instTopSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.top_prod_top Subsemigroup.top_prod_topₓ'. -/
@[simp, to_additive top_prod_top]
theorem top_prod_top : (⊤ : Subsemigroup M).Prod (⊤ : Subsemigroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _
#align subsemigroup.top_prod_top Subsemigroup.top_prod_top

/- warning: subsemigroup.bot_prod_bot -> Subsemigroup.bot_prod_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N], Eq.{succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 (Bot.bot.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasBot.{u1} M _inst_1)) (Bot.bot.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasBot.{u2} N _inst_2))) (Bot.bot.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.hasBot.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N], Eq.{max (succ u2) (succ u1)} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 (Bot.bot.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instBotSubsemigroup.{u2} M _inst_1)) (Bot.bot.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instBotSubsemigroup.{u1} N _inst_2))) (Bot.bot.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.instBotSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align subsemigroup.bot_prod_bot Subsemigroup.bot_prod_botₓ'. -/
@[to_additive]
theorem bot_prod_bot : (⊥ : Subsemigroup M).Prod (⊥ : Subsemigroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod, Prod.one_eq_mk]
#align subsemigroup.bot_prod_bot Subsemigroup.bot_prod_bot

#print Subsemigroup.prodEquiv /-
/-- The product of subsemigroups is isomorphic to their product as semigroups. -/
@[to_additive prod_equiv
      "The product of additive subsemigroups is isomorphic to their product\nas additive semigroups"]
def prodEquiv (s : Subsemigroup M) (t : Subsemigroup N) : s.Prod t ≃* s × t :=
  { Equiv.Set.prod ↑s ↑t with map_mul' := fun x y => rfl }
#align subsemigroup.prod_equiv Subsemigroup.prodEquiv
-/

open MulHom

/- warning: subsemigroup.mem_map_equiv -> Subsemigroup.mem_map_equiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2} {K : Subsemigroup.{u1} M _inst_1} {x : N}, Iff (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) x (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u1, u2} M N _inst_1 _inst_2 f) K)) (Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 f) x) K)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2} {K : Subsemigroup.{u2} M _inst_1} {x : N}, Iff (Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u2, u1} M N _inst_1 _inst_2 f) K)) (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) x) (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 f) x) K)
Case conversion may be inaccurate. Consider using '#align subsemigroup.mem_map_equiv Subsemigroup.mem_map_equivₓ'. -/
@[to_additive]
theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map f.toMulHom ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
#align subsemigroup.mem_map_equiv Subsemigroup.mem_map_equiv

/- warning: subsemigroup.map_equiv_eq_comap_symm -> Subsemigroup.map_equiv_eq_comap_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (K : Subsemigroup.{u1} M _inst_1), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u1, u2} M N _inst_1 _inst_2 f) K) (Subsemigroup.comap.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.toMulHom.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 f)) K)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (K : Subsemigroup.{u2} M _inst_1), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u2, u1} M N _inst_1 _inst_2 f) K) (Subsemigroup.comap.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.toMulHom.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 f)) K)
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_equiv_eq_comap_symm Subsemigroup.map_equiv_eq_comap_symmₓ'. -/
@[to_additive]
theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map f.toMulHom = K.comap f.symm.toMulHom :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage K)
#align subsemigroup.map_equiv_eq_comap_symm Subsemigroup.map_equiv_eq_comap_symm

#print Subsemigroup.comap_equiv_eq_map_symm /-
@[to_additive]
theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap f.toMulHom = K.map f.symm.toMulHom :=
  (map_equiv_eq_comap_symm f.symm K).symm
#align subsemigroup.comap_equiv_eq_map_symm Subsemigroup.comap_equiv_eq_map_symm
-/

/- warning: subsemigroup.map_equiv_top -> Subsemigroup.map_equiv_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u1, u2} M N _inst_1 _inst_2 f) (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1))) (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 (MulEquiv.toMulHom.{u2, u1} M N _inst_1 _inst_2 f) (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1))) (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))
Case conversion may be inaccurate. Consider using '#align subsemigroup.map_equiv_top Subsemigroup.map_equiv_topₓ'. -/
@[simp, to_additive]
theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map f.toMulHom = ⊤ :=
  SetLike.coe_injective <| Set.image_univ.trans f.Surjective.range_eq
#align subsemigroup.map_equiv_top Subsemigroup.map_equiv_top

/- warning: subsemigroup.le_prod_iff -> Subsemigroup.le_prod_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {s : Subsemigroup.{u1} M _inst_1} {t : Subsemigroup.{u2} N _inst_2} {u : Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)}, Iff (LE.le.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Preorder.toLE.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Prod.{u1, u2} M N) (Subsemigroup.setLike.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2))))) u (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s t)) (And (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.map.{max u1 u2, u1} (Prod.{u1, u2} M N) M (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_1 (MulHom.fst.{u1, u2} M N _inst_1 _inst_2) u) s) (LE.le.{u2} (Subsemigroup.{u2} N _inst_2) (Preorder.toLE.{u2} (Subsemigroup.{u2} N _inst_2) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} N _inst_2) (SetLike.partialOrder.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (Subsemigroup.map.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MulHom.snd.{u1, u2} M N _inst_1 _inst_2) u) t))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {s : Subsemigroup.{u2} M _inst_1} {t : Subsemigroup.{u1} N _inst_2} {u : Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)}, Iff (LE.le.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Preorder.toLE.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (PartialOrder.toPreorder.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.instCompleteLatticeSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)))))) u (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s t)) (And (LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) (Subsemigroup.map.{max u2 u1, u2} (Prod.{u2, u1} M N) M (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_1 (MulHom.fst.{u2, u1} M N _inst_1 _inst_2) u) s) (LE.le.{u1} (Subsemigroup.{u1} N _inst_2) (Preorder.toLE.{u1} (Subsemigroup.{u1} N _inst_2) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} N _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} N _inst_2))))) (Subsemigroup.map.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MulHom.snd.{u2, u1} M N _inst_1 _inst_2) u) t))
Case conversion may be inaccurate. Consider using '#align subsemigroup.le_prod_iff Subsemigroup.le_prod_iffₓ'. -/
@[to_additive le_prod_iff]
theorem le_prod_iff {s : Subsemigroup M} {t : Subsemigroup N} {u : Subsemigroup (M × N)} :
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
#align subsemigroup.le_prod_iff Subsemigroup.le_prod_iff

end Subsemigroup

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print MulHom.srange /-
/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive "The range of an `add_hom` is an `add_subsemigroup`."]
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm
#align mul_hom.srange MulHom.srange
-/

/- warning: mul_hom.coe_srange -> MulHom.coe_srange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} N) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (Subsemigroup.{u2} N _inst_2) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)))) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) (Set.range.{u2, succ u1} N M (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} N) (SetLike.coe.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f)) (Set.range.{u1, succ u2} N M (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_srange MulHom.coe_srangeₓ'. -/
@[simp, to_additive]
theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.range f :=
  rfl
#align mul_hom.coe_srange MulHom.coe_srange

/- warning: mul_hom.mem_srange -> MulHom.mem_srange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2} {y : N}, Iff (Membership.Mem.{u2, u2} N (Subsemigroup.{u2} N _inst_2) (SetLike.hasMem.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) y (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) (Exists.{succ u1} M (fun (x : M) => Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2} {y : N}, Iff (Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) y (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f)) (Exists.{succ u2} M (fun (x : M) => Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) y))
Case conversion may be inaccurate. Consider using '#align mul_hom.mem_srange MulHom.mem_srangeₓ'. -/
@[simp, to_additive]
theorem mem_srange {f : M →ₙ* N} {y : N} : y ∈ f.srange ↔ ∃ x, f x = y :=
  Iff.rfl
#align mul_hom.mem_srange MulHom.mem_srange

/- warning: mul_hom.srange_eq_map -> MulHom.srange_eq_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align mul_hom.srange_eq_map MulHom.srange_eq_mapₓ'. -/
@[to_additive]
theorem srange_eq_map (f : M →ₙ* N) : f.srange = (⊤ : Subsemigroup M).map f :=
  copy_eq _
#align mul_hom.srange_eq_map MulHom.srange_eq_map

/- warning: mul_hom.map_srange -> MulHom.map_srange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (g : MulHom.{u2, u3} N P _inst_2 _inst_3) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u3} (Subsemigroup.{u3} P _inst_3) (Subsemigroup.map.{u2, u3} N P _inst_2 _inst_3 g (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) (MulHom.srange.{u1, u3} M P _inst_1 _inst_3 (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {P : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u3} N] [_inst_3 : Mul.{u2} P] (g : MulHom.{u3, u2} N P _inst_2 _inst_3) (f : MulHom.{u1, u3} M N _inst_1 _inst_2), Eq.{succ u2} (Subsemigroup.{u2} P _inst_3) (Subsemigroup.map.{u3, u2} N P _inst_2 _inst_3 g (MulHom.srange.{u1, u3} M N _inst_1 _inst_2 f)) (MulHom.srange.{u1, u2} M P _inst_1 _inst_3 (MulHom.comp.{u1, u3, u2} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align mul_hom.map_srange MulHom.map_srangeₓ'. -/
@[to_additive]
theorem map_srange (g : N →ₙ* P) (f : M →ₙ* N) : f.srange.map g = (g.comp f).srange := by
  simpa only [srange_eq_map] using (⊤ : Subsemigroup M).map_map g f
#align mul_hom.map_srange MulHom.map_srange

#print MulHom.srange_top_iff_surjective /-
@[to_additive]
theorem srange_top_iff_surjective {N} [Mul N] {f : M →ₙ* N} :
    f.srange = (⊤ : Subsemigroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_iff_surjective
#align mul_hom.srange_top_iff_surjective MulHom.srange_top_iff_surjective
-/

#print MulHom.srange_top_of_surjective /-
/-- The range of a surjective semigroup hom is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_semigroup` hom is the whole of the codomain."]
theorem srange_top_of_surjective {N} [Mul N] (f : M →ₙ* N) (hf : Function.Surjective f) :
    f.srange = (⊤ : Subsemigroup N) :=
  srange_top_iff_surjective.2 hf
#align mul_hom.srange_top_of_surjective MulHom.srange_top_of_surjective
-/

/- warning: mul_hom.mclosure_preimage_le -> MulHom.mclosure_preimage_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (s : Set.{u2} N), LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) (Subsemigroup.closure.{u1} M _inst_1 (Set.preimage.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) s)) (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.closure.{u2} N _inst_2 s))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (s : Set.{u1} N), LE.le.{u2} (Subsemigroup.{u2} M _inst_1) (Preorder.toLE.{u2} (Subsemigroup.{u2} M _inst_1) (PartialOrder.toPreorder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subsemigroup.{u2} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u2} M _inst_1))))) (Subsemigroup.closure.{u2} M _inst_1 (Set.preimage.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f) s)) (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.closure.{u1} N _inst_2 s))
Case conversion may be inaccurate. Consider using '#align mul_hom.mclosure_preimage_le MulHom.mclosure_preimage_leₓ'. -/
@[to_additive]
theorem mclosure_preimage_le (f : M →ₙ* N) (s : Set N) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx
#align mul_hom.mclosure_preimage_le MulHom.mclosure_preimage_le

/- warning: mul_hom.map_mclosure -> MulHom.map_mclosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (s : Set.{u1} M), Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f (Subsemigroup.closure.{u1} M _inst_1 s)) (Subsemigroup.closure.{u2} N _inst_2 (Set.image.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) s))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (s : Set.{u2} M), Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f (Subsemigroup.closure.{u2} M _inst_1 s)) (Subsemigroup.closure.{u1} N _inst_2 (Set.image.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f) s))
Case conversion may be inaccurate. Consider using '#align mul_hom.map_mclosure MulHom.map_mclosureₓ'. -/
/-- The image under a semigroup hom of the subsemigroup generated by a set equals the subsemigroup
generated by the image of the set. -/
@[to_additive
      "The image under an `add_semigroup` hom of the `add_subsemigroup` generated by a set\nequals the `add_subsemigroup` generated by the image of the set."]
theorem map_mclosure (f : M →ₙ* N) (s : Set M) : (closure s).map f = closure (f '' s) :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      le_trans (closure_mono <| Set.subset_preimage_image _ _) (mclosure_preimage_le _ _))
    (closure_le.2 <| Set.image_subset _ subset_closure)
#align mul_hom.map_mclosure MulHom.map_mclosure

#print MulHom.restrict /-
/-- Restriction of a semigroup hom to a subsemigroup of the domain. -/
@[to_additive "Restriction of an add_semigroup hom to an `add_subsemigroup` of the domain."]
def restrict {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) (S : σ) : S →ₙ* N :=
  f.comp (MulMemClass.subtype S)
#align mul_hom.restrict MulHom.restrict
-/

#print MulHom.restrict_apply /-
@[simp, to_additive]
theorem restrict_apply {N : Type _} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) {S : σ}
    (x : S) : f.restrict S x = f x :=
  rfl
#align mul_hom.restrict_apply MulHom.restrict_apply
-/

#print MulHom.codRestrict /-
/-- Restriction of a semigroup hom to a subsemigroup of the codomain. -/
@[to_additive "Restriction of an `add_semigroup` hom to an `add_subsemigroup` of the\ncodomain.",
  simps]
def codRestrict [SetLike σ N] [MulMemClass σ N] (f : M →ₙ* N) (S : σ) (h : ∀ x, f x ∈ S) : M →ₙ* S
    where
  toFun n := ⟨f n, h n⟩
  map_mul' x y := Subtype.eq (map_mul f x y)
#align mul_hom.cod_restrict MulHom.codRestrict
-/

#print MulHom.srangeRestrict /-
/-- Restriction of a semigroup hom to its range interpreted as a subsemigroup. -/
@[to_additive "Restriction of an `add_semigroup` hom to its range interpreted as a subsemigroup."]
def srangeRestrict {N} [Mul N] (f : M →ₙ* N) : M →ₙ* f.srange :=
  (f.codRestrict f.srange) fun x => ⟨x, rfl⟩
#align mul_hom.srange_restrict MulHom.srangeRestrict
-/

#print MulHom.coe_srangeRestrict /-
@[simp, to_additive]
theorem coe_srangeRestrict {N} [Mul N] (f : M →ₙ* N) (x : M) : (f.srangeRestrict x : N) = f x :=
  rfl
#align mul_hom.coe_srange_restrict MulHom.coe_srangeRestrict
-/

/- warning: mul_hom.srange_restrict_surjective -> MulHom.srangeRestrict_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} M (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) _inst_1 (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f))) (fun (_x : MulHom.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) _inst_1 (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f))) => M -> (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f))) (MulHom.hasCoeToFun.{u1, u2} M (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f)) _inst_1 (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (MulHom.srange.{u1, u2} M N _inst_1 _inst_2 f))) (MulHom.srangeRestrict.{u1, u2} M _inst_1 N _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) _inst_1 (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) _inst_1 (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) _inst_1 (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f)) (MulHom.mulHomClass.{u2, u1} M (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f))) _inst_1 (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (MulHom.srange.{u2, u1} M N _inst_1 _inst_2 f)))) (MulHom.srangeRestrict.{u2, u1} M _inst_1 N _inst_2 f))
Case conversion may be inaccurate. Consider using '#align mul_hom.srange_restrict_surjective MulHom.srangeRestrict_surjectiveₓ'. -/
@[to_additive]
theorem srangeRestrict_surjective (f : M →ₙ* N) : Function.Surjective f.srangeRestrict :=
  fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩
#align mul_hom.srange_restrict_surjective MulHom.srangeRestrict_surjective

/- warning: mul_hom.prod_map_comap_prod' -> MulHom.prod_map_comap_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {M' : Type.{u3}} {N' : Type.{u4}} [_inst_4 : Mul.{u3} M'] [_inst_5 : Mul.{u4} N'] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u3, u4} M' N' _inst_4 _inst_5) (S : Subsemigroup.{u2} N _inst_2) (S' : Subsemigroup.{u4} N' _inst_5), Eq.{succ (max u1 u3)} (Subsemigroup.{max u1 u3} (Prod.{u1, u3} M M') (Prod.hasMul.{u1, u3} M M' _inst_1 _inst_4)) (Subsemigroup.comap.{max u1 u3, max u2 u4} (Prod.{u1, u3} M M') (Prod.{u2, u4} N N') (Prod.hasMul.{u1, u3} M M' _inst_1 _inst_4) (Prod.hasMul.{u2, u4} N N' _inst_2 _inst_5) (MulHom.prodMap.{u1, u3, u2, u4} M M' N N' _inst_1 _inst_4 _inst_2 _inst_5 f g) (Subsemigroup.prod.{u2, u4} N N' _inst_2 _inst_5 S S')) (Subsemigroup.prod.{u1, u3} M M' _inst_1 _inst_4 (Subsemigroup.comap.{u1, u2} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u3, u4} M' N' _inst_4 _inst_5 g S'))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {M' : Type.{u4}} {N' : Type.{u3}} [_inst_4 : Mul.{u4} M'] [_inst_5 : Mul.{u3} N'] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (g : MulHom.{u4, u3} M' N' _inst_4 _inst_5) (S : Subsemigroup.{u1} N _inst_2) (S' : Subsemigroup.{u3} N' _inst_5), Eq.{max (succ u2) (succ u4)} (Subsemigroup.{max u4 u2} (Prod.{u2, u4} M M') (Prod.instMulProd.{u2, u4} M M' _inst_1 _inst_4)) (Subsemigroup.comap.{max u4 u2, max u3 u1} (Prod.{u2, u4} M M') (Prod.{u1, u3} N N') (Prod.instMulProd.{u2, u4} M M' _inst_1 _inst_4) (Prod.instMulProd.{u1, u3} N N' _inst_2 _inst_5) (MulHom.prodMap.{u2, u4, u1, u3} M M' N N' _inst_1 _inst_4 _inst_2 _inst_5 f g) (Subsemigroup.prod.{u1, u3} N N' _inst_2 _inst_5 S S')) (Subsemigroup.prod.{u2, u4} M M' _inst_1 _inst_4 (Subsemigroup.comap.{u2, u1} M N _inst_1 _inst_2 f S) (Subsemigroup.comap.{u4, u3} M' N' _inst_4 _inst_5 g S'))
Case conversion may be inaccurate. Consider using '#align mul_hom.prod_map_comap_prod' MulHom.prod_map_comap_prod'ₓ'. -/
@[to_additive]
theorem prod_map_comap_prod' {M' : Type _} {N' : Type _} [Mul M'] [Mul N'] (f : M →ₙ* N)
    (g : M' →ₙ* N') (S : Subsemigroup N) (S' : Subsemigroup N') :
    (S.Prod S').comap (prodMap f g) = (S.comap f).Prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
#align mul_hom.prod_map_comap_prod' MulHom.prod_map_comap_prod'

#print MulHom.subsemigroupComap /-
/-- The `mul_hom` from the preimage of a subsemigroup to itself. -/
@[to_additive "the `add_hom` from the preimage of an additive subsemigroup to itself.", simps]
def subsemigroupComap (f : M →ₙ* N) (N' : Subsemigroup N) : N'.comap f →ₙ* N'
    where
  toFun x := ⟨f x, x.Prop⟩
  map_mul' x y := Subtype.eq (@map_mul M N _ _ _ _ f x y)
#align mul_hom.subsemigroup_comap MulHom.subsemigroupComap
-/

#print MulHom.subsemigroupMap /-
/-- The `mul_hom` from a subsemigroup to its image.
See `mul_equiv.subsemigroup_map` for a variant for `mul_equiv`s. -/
@[to_additive
      "the `add_hom` from an additive subsemigroup to its image. See\n`add_equiv.add_subsemigroup_map` for a variant for `add_equiv`s.",
  simps]
def subsemigroupMap (f : M →ₙ* N) (M' : Subsemigroup M) : M' →ₙ* M'.map f
    where
  toFun x := ⟨f x, ⟨x, x.Prop, rfl⟩⟩
  map_mul' x y := Subtype.eq <| @map_mul M N _ _ _ _ f x y
#align mul_hom.subsemigroup_map MulHom.subsemigroupMap
-/

/- warning: mul_hom.subsemigroup_map_surjective -> MulHom.subsemigroupMap_surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (M' : Subsemigroup.{u1} M _inst_1), Function.Surjective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M')) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M')) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) M') (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M'))) (fun (_x : MulHom.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M')) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) M') (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M'))) => (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) M') -> (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M'))) (MulHom.hasCoeToFun.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) M') (coeSort.{succ u2, succ (succ u2)} (Subsemigroup.{u2} N _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subsemigroup.{u2} N _inst_2) N (Subsemigroup.setLike.{u2} N _inst_2)) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M')) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) M') (MulMemClass.mul.{u2, u2} N (Subsemigroup.{u2} N _inst_2) _inst_2 (Subsemigroup.setLike.{u2} N _inst_2) (Subsemigroup.mul_mem_class.{u2} N _inst_2) (Subsemigroup.map.{u1, u2} M N _inst_1 _inst_2 f M'))) (MulHom.subsemigroupMap.{u1, u2} M N _inst_1 _inst_2 f M'))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (M' : Subsemigroup.{u2} M _inst_1), Function.Surjective.{succ u2, succ u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) M') (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (fun (_x : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) => Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) M') (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) M') (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M')) (MulHom.mulHomClass.{u2, u1} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Subsemigroup.{u2} M _inst_1) (SetLike.instMembership.{u2, u2} (Subsemigroup.{u2} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1)) x M')) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Subsemigroup.{u1} N _inst_2) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} N _inst_2) N (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2)) x (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M'))) (MulMemClass.mul.{u2, u2} M (Subsemigroup.{u2} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u2} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u2} M _inst_1) M') (MulMemClass.mul.{u1, u1} N (Subsemigroup.{u1} N _inst_2) _inst_2 (Subsemigroup.instSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} N _inst_2) (Subsemigroup.map.{u2, u1} M N _inst_1 _inst_2 f M')))) (MulHom.subsemigroupMap.{u2, u1} M N _inst_1 _inst_2 f M'))
Case conversion may be inaccurate. Consider using '#align mul_hom.subsemigroup_map_surjective MulHom.subsemigroupMap_surjectiveₓ'. -/
@[to_additive]
theorem subsemigroupMap_surjective (f : M →ₙ* N) (M' : Subsemigroup M) :
    Function.Surjective (f.subsemigroupMap M') :=
  by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩
#align mul_hom.subsemigroup_map_surjective MulHom.subsemigroupMap_surjective

end MulHom

namespace Subsemigroup

open MulHom

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

#print Subsemigroup.srange_fst /-
@[simp, to_additive]
theorem srange_fst [Nonempty N] : (fst M N).srange = ⊤ :=
  (fst M N).srange_top_of_surjective <| Prod.fst_surjective
#align subsemigroup.srange_fst Subsemigroup.srange_fst
-/

/- warning: subsemigroup.srange_snd -> Subsemigroup.srange_snd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_4 : Nonempty.{succ u1} M], Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) (MulHom.srange.{max u1 u2, u2} (Prod.{u1, u2} M N) N (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2) _inst_2 (MulHom.snd.{u1, u2} M N _inst_1 _inst_2)) (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] [_inst_4 : Nonempty.{succ u2} M], Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) (MulHom.srange.{max u2 u1, u1} (Prod.{u2, u1} M N) N (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2) _inst_2 (MulHom.snd.{u2, u1} M N _inst_1 _inst_2)) (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))
Case conversion may be inaccurate. Consider using '#align subsemigroup.srange_snd Subsemigroup.srange_sndₓ'. -/
@[simp, to_additive]
theorem srange_snd [Nonempty M] : (snd M N).srange = ⊤ :=
  (snd M N).srange_top_of_surjective <| Prod.snd_surjective
#align subsemigroup.srange_snd Subsemigroup.srange_snd

/- warning: subsemigroup.prod_eq_top_iff -> Subsemigroup.prod_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_4 : Nonempty.{succ u1} M] [_inst_5 : Nonempty.{succ u2} N] {s : Subsemigroup.{u1} M _inst_1} {t : Subsemigroup.{u2} N _inst_2}, Iff (Eq.{succ (max u1 u2)} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u1, u2} M N _inst_1 _inst_2 s t) (Top.top.{max u1 u2} (Subsemigroup.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)) (Subsemigroup.hasTop.{max u1 u2} (Prod.{u1, u2} M N) (Prod.hasMul.{u1, u2} M N _inst_1 _inst_2)))) (And (Eq.{succ u1} (Subsemigroup.{u1} M _inst_1) s (Top.top.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.hasTop.{u1} M _inst_1))) (Eq.{succ u2} (Subsemigroup.{u2} N _inst_2) t (Top.top.{u2} (Subsemigroup.{u2} N _inst_2) (Subsemigroup.hasTop.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] [_inst_4 : Nonempty.{succ u2} M] [_inst_5 : Nonempty.{succ u1} N] {s : Subsemigroup.{u2} M _inst_1} {t : Subsemigroup.{u1} N _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.prod.{u2, u1} M N _inst_1 _inst_2 s t) (Top.top.{max u2 u1} (Subsemigroup.{max u1 u2} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)) (Subsemigroup.instTopSubsemigroup.{max u2 u1} (Prod.{u2, u1} M N) (Prod.instMulProd.{u2, u1} M N _inst_1 _inst_2)))) (And (Eq.{succ u2} (Subsemigroup.{u2} M _inst_1) s (Top.top.{u2} (Subsemigroup.{u2} M _inst_1) (Subsemigroup.instTopSubsemigroup.{u2} M _inst_1))) (Eq.{succ u1} (Subsemigroup.{u1} N _inst_2) t (Top.top.{u1} (Subsemigroup.{u1} N _inst_2) (Subsemigroup.instTopSubsemigroup.{u1} N _inst_2))))
Case conversion may be inaccurate. Consider using '#align subsemigroup.prod_eq_top_iff Subsemigroup.prod_eq_top_iffₓ'. -/
@[to_additive]
theorem prod_eq_top_iff [Nonempty M] [Nonempty N] {s : Subsemigroup M} {t : Subsemigroup N} :
    s.Prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, ← (gc_map_comap _).le_iff_le, ← srange_eq_map, srange_fst,
    srange_snd]
#align subsemigroup.prod_eq_top_iff Subsemigroup.prod_eq_top_iff

/- warning: subsemigroup.inclusion -> Subsemigroup.inclusion is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Subsemigroup.{u1} M _inst_1} {T : Subsemigroup.{u1} M _inst_1}, (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)))) S T) -> (MulHom.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) S) (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.setLike.{u1} M _inst_1)) T) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) S) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.setLike.{u1} M _inst_1) (Subsemigroup.mul_mem_class.{u1} M _inst_1) T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] {S : Subsemigroup.{u1} M _inst_1} {T : Subsemigroup.{u1} M _inst_1}, (LE.le.{u1} (Subsemigroup.{u1} M _inst_1) (Preorder.toLE.{u1} (Subsemigroup.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subsemigroup.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subsemigroup.{u1} M _inst_1) (Subsemigroup.instCompleteLatticeSubsemigroup.{u1} M _inst_1))))) S T) -> (MulHom.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x S)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Subsemigroup.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M _inst_1) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1)) x T)) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} M _inst_1) S) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M _inst_1) _inst_1 (Subsemigroup.instSetLikeSubsemigroup.{u1} M _inst_1) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} M _inst_1) T))
Case conversion may be inaccurate. Consider using '#align subsemigroup.inclusion Subsemigroup.inclusionₓ'. -/
/-- The semigroup hom associated to an inclusion of subsemigroups. -/
@[to_additive "The `add_semigroup` hom associated to an inclusion of subsemigroups."]
def inclusion {S T : Subsemigroup M} (h : S ≤ T) : S →ₙ* T :=
  (MulMemClass.subtype S).codRestrict _ fun x => h x.2
#align subsemigroup.inclusion Subsemigroup.inclusion

#print Subsemigroup.range_subtype /-
@[simp, to_additive]
theorem range_subtype (s : Subsemigroup M) : (MulMemClass.subtype s).srange = s :=
  SetLike.coe_injective <| (coe_srange _).trans <| Subtype.range_coe
#align subsemigroup.range_subtype Subsemigroup.range_subtype
-/

#print Subsemigroup.eq_top_iff' /-
@[to_additive]
theorem eq_top_iff' : S = ⊤ ↔ ∀ x : M, x ∈ S :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
#align subsemigroup.eq_top_iff' Subsemigroup.eq_top_iff'
-/

end Subsemigroup

namespace MulEquiv

variable [Mul M] [Mul N] {S T : Subsemigroup M}

#print MulEquiv.subsemigroupCongr /-
/-- Makes the identity isomorphism from a proof that two subsemigroups of a multiplicative
    semigroup are equal. -/
@[to_additive
      "Makes the identity additive isomorphism from a proof two\nsubsemigroups of an additive semigroup are equal."]
def subsemigroupCongr (h : S = T) : S ≃* T :=
  { Equiv.setCongr <| congr_arg _ h with map_mul' := fun _ _ => rfl }
#align mul_equiv.subsemigroup_congr MulEquiv.subsemigroupCongr
-/

#print MulEquiv.ofLeftInverse /-
-- this name is primed so that the version to `f.range` instead of `f.srange` can be unprimed.
/-- A semigroup homomorphism `f : M →ₙ* N` with a left-inverse `g : N → M` defines a multiplicative
equivalence between `M` and `f.srange`.

This is a bidirectional version of `mul_hom.srange_restrict`. -/
@[to_additive
      "\nAn additive semigroup homomorphism `f : M →+ N` with a left-inverse `g : N → M` defines an additive\nequivalence between `M` and `f.srange`.\n\nThis is a bidirectional version of `add_hom.srange_restrict`. ",
  simps (config := { simpRhs := true })]
def ofLeftInverse (f : M →ₙ* N) {g : N → M} (h : Function.LeftInverse g f) : M ≃* f.srange :=
  { f.srangeRestrict with
    toFun := f.srangeRestrict
    invFun := g ∘ MulMemClass.subtype f.srange
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := MulHom.mem_srange.mp x.Prop
        show f (g x) = x by rw [← hx', h x'] }
#align mul_equiv.of_left_inverse MulEquiv.ofLeftInverse
-/

#print MulEquiv.subsemigroupMap /-
/-- A `mul_equiv` `φ` between two semigroups `M` and `N` induces a `mul_equiv` between
a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`.
See `mul_hom.subsemigroup_map` for a variant for `mul_hom`s. -/
@[to_additive
      "An `add_equiv` `φ` between two additive semigroups `M` and `N` induces an `add_equiv`\nbetween a subsemigroup `S ≤ M` and the subsemigroup `φ(S) ≤ N`. See `add_hom.add_subsemigroup_map`\nfor a variant for `add_hom`s.",
  simps]
def subsemigroupMap (e : M ≃* N) (S : Subsemigroup M) : S ≃* S.map e.toMulHom :=
  {-- we restate this for `simps` to avoid `⇑e.symm.to_equiv x`
          e.toMulHom.subsemigroupMap
      S,
    e.toEquiv.image S with
    toFun := fun x => ⟨e x, _⟩
    invFun := fun x => ⟨e.symm x, _⟩ }
#align mul_equiv.subsemigroup_map MulEquiv.subsemigroupMap
-/

end MulEquiv

