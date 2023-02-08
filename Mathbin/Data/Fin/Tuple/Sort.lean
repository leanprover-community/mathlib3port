/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.fin.tuple.sort
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.List.FinRange
import Mathbin.Data.Prod.Lex
import Mathbin.GroupTheory.Perm.Basic

/-!

# Sorting tuples by their values

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given an `n`-tuple `f : fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ tuple.sort f`.

## Main declarations

* `tuple.sort`: given `f : fin n → α`, produces a permutation on `fin n`
* `tuple.monotone_sort`: `f ∘ tuple.sort f` is `monotone`

-/


namespace Tuple

variable {n : ℕ}

variable {α : Type _} [LinearOrder α]

#print Tuple.graph /-
/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)
#align tuple.graph Tuple.graph
-/

#print Tuple.graph.proj /-
/-- Given `p : α ×ₗ (fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1
#align tuple.graph.proj Tuple.graph.proj
-/

#print Tuple.graph.card /-
@[simp]
theorem graph.card (f : Fin n → α) : (graph f).card = n :=
  by
  rw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    simp
#align tuple.graph.card Tuple.graph.card
-/

#print Tuple.graphEquiv₁ /-
/-- `graph_equiv₁ f` is the natural equivalence between `fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f
    where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by simpa [graph] using h
#align tuple.graph_equiv₁ Tuple.graphEquiv₁
-/

#print Tuple.proj_equiv₁' /-
@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl
#align tuple.proj_equiv₁' Tuple.proj_equiv₁'
-/

#print Tuple.graphEquiv₂ /-
/-- `graph_equiv₂ f` is an equivalence between `fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)
#align tuple.graph_equiv₂ Tuple.graphEquiv₂
-/

#print Tuple.sort /-
/-- `sort f` is the permutation that orders `fin n` according to the order of the outputs of `f`. -/
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm
#align tuple.sort Tuple.sort
-/

/- warning: tuple.graph_equiv₂_apply -> Tuple.graphEquiv₂_apply is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (f : (Fin n) -> α) (i : Fin n), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (coeFn.{succ u1, succ u1} (OrderIso.{0, u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (Fin.hasLe n) (Subtype.hasLe.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.instLE.{u1, 0} α (Fin n) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Fin.hasLe n)) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.Mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.hasMem.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f)))) (fun (_x : RelIso.{0, u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (Subtype.hasLe.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.instLE.{u1, 0} α (Fin n) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Fin.hasLe n)) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.Mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.hasMem.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))))) => (Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f))) (RelIso.hasCoeToFun.{0, u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) (Subtype.hasLe.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.instLE.{u1, 0} α (Fin n) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Fin.hasLe n)) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.Mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.hasMem.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))))) (Tuple.graphEquiv₂.{u1} n α _inst_1 f) i) (coeFn.{succ u1, succ u1} (Equiv.{1, succ u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f))) (fun (_x : Equiv.{1, succ u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f))) => (Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f))) (Equiv.hasCoeToFun.{1, succ u1} (Fin n) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f))) (Tuple.graphEquiv₁.{u1} n α _inst_1 f) (coeFn.{1, 1} (Equiv.Perm.{1} (Fin n)) (fun (_x : Equiv.{1, 1} (Fin n) (Fin n)) => (Fin n) -> (Fin n)) (Equiv.hasCoeToFun.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f) i))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (f : (Fin n) -> α) (i : Fin n), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) i) (FunLike.coe.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f)))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) _x) (EmbeddingLike.toFunLike.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f)))) (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (Function.instEmbeddingLikeEmbedding.{1, succ u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))))) (RelEmbedding.toEmbedding.{0, u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) => LE.le.{u1} (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (Subtype.le.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.instLE.{u1, 0} α (Fin n) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (instLEFin n)) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) => LE.le.{u1} (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (Subtype.le.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.instLE.{u1, 0} α (Fin n) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (instLEFin n)) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (Tuple.graphEquiv₂.{u1} n α _inst_1 f))) i) (FunLike.coe.{succ u1, 1, succ u1} (Equiv.{1, succ u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f)))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Fin n) => Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) _x) (Equiv.instFunLikeEquiv.{1, succ u1} (Fin n) (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f)))) (Tuple.graphEquiv₁.{u1} n α _inst_1 f) (FunLike.coe.{1, 1, 1} (Equiv.Perm.{1} (Fin n)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Fin n) => Fin n) _x) (Equiv.instFunLikeEquiv.{1, 1} (Fin n) (Fin n)) (Tuple.sort.{u1} n α _inst_1 f) i))
Case conversion may be inaccurate. Consider using '#align tuple.graph_equiv₂_apply Tuple.graphEquiv₂_applyₓ'. -/
theorem graphEquiv₂_apply (f : Fin n → α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm
#align tuple.graph_equiv₂_apply Tuple.graphEquiv₂_apply

#print Tuple.self_comp_sort /-
theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp
#align tuple.self_comp_sort Tuple.self_comp_sort
-/

/- warning: tuple.monotone_proj -> Tuple.monotone_proj is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (f : (Fin n) -> α), Monotone.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) Type.{u1} (Finset.hasCoeToSort.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Tuple.graph.{u1} n α _inst_1 f)) α (Subtype.preorder.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.preorder.{u1, 0} α (Fin n) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.Mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.hasMem.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (Tuple.graph.proj.{u1} n α _inst_1 f)
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (f : (Fin n) -> α), Monotone.{u1, u1} (Subtype.{succ u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) α (Subtype.preorder.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Prod.Lex.preorder.{u1, 0} α (Fin n) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n))) (fun (x : Lex.{u1} (Prod.{u1, 0} α (Fin n))) => Membership.mem.{u1, u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n))) (Finset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) (Finset.instMembershipFinset.{u1} (Lex.{u1} (Prod.{u1, 0} α (Fin n)))) x (Tuple.graph.{u1} n α _inst_1 f))) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (Tuple.graph.proj.{u1} n α _inst_1 f)
Case conversion may be inaccurate. Consider using '#align tuple.monotone_proj Tuple.monotone_projₓ'. -/
theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) :=
  by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]
#align tuple.monotone_proj Tuple.monotone_proj

#print Tuple.monotone_sort /-
theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) :=
  by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graph_equiv₂ f).Monotone
#align tuple.monotone_sort Tuple.monotone_sort
-/

end Tuple

namespace Tuple

open List

variable {n : ℕ} {α : Type _}

#print Tuple.unique_monotone /-
/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
theorem unique_monotone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    eq_of_perm_of_sorted ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm) hfσ.ofFn_sorted
      hfτ.ofFn_sorted
#align tuple.unique_monotone Tuple.unique_monotone
-/

variable [LinearOrder α] {f : Fin n → α} {σ : Equiv.Perm (Fin n)}

#print Tuple.eq_sort_iff' /-
/-- A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target). -/
theorem eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f) :=
  by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graph_equiv₂ f).StrictMono
  · have := Subsingleton.elim (graph_equiv₂ f) (h.order_iso_of_surjective _ <| Equiv.surjective _)
    ext1
    exact (graph_equiv₁ f).apply_eq_iff_eq_symm_apply.1 (FunLike.congr_fun this x).symm
#align tuple.eq_sort_iff' Tuple.eq_sort_iff'
-/

#print Tuple.eq_sort_iff /-
/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j :=
  by
  rw [eq_sort_iff']
  refine' ⟨fun h => ⟨(monotone_proj f).comp h.Monotone, fun i j hij hfij => _⟩, fun h i j hij => _⟩
  · exact (((Prod.Lex.lt_iff _ _).1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply (Prod.Lex.lt_iff _ _).2
    exacts[Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]
#align tuple.eq_sort_iff Tuple.eq_sort_iff
-/

/- warning: tuple.sort_eq_refl_iff_monotone -> Tuple.sort_eq_refl_iff_monotone is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α}, Iff (Eq.{1} (Equiv.Perm.{1} (Fin n)) (Tuple.sort.{u1} n α _inst_1 f) (Equiv.refl.{1} (Fin n))) (Monotone.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) f)
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {f : (Fin n) -> α}, Iff (Eq.{1} (Equiv.Perm.{1} (Fin n)) (Tuple.sort.{u1} n α _inst_1 f) (Equiv.refl.{1} (Fin n))) (Monotone.{0, u1} (Fin n) α (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) f)
Case conversion may be inaccurate. Consider using '#align tuple.sort_eq_refl_iff_monotone Tuple.sort_eq_refl_iff_monotoneₓ'. -/
/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f :=
  by
  rw [eq_comm, eq_sort_iff, Equiv.coe_refl, Function.comp.right_id]
  simp only [id.def, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij
#align tuple.sort_eq_refl_iff_monotone Tuple.sort_eq_refl_iff_monotone

#print Tuple.comp_sort_eq_comp_iff_monotone /-
/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩
#align tuple.comp_sort_eq_comp_iff_monotone Tuple.comp_sort_eq_comp_iff_monotone
-/

#print Tuple.comp_perm_comp_sort_eq_comp_sort /-
/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f :=
  by
  rw [Function.comp.assoc, ← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)
#align tuple.comp_perm_comp_sort_eq_comp_sort Tuple.comp_perm_comp_sort_eq_comp_sort
-/

#print Tuple.antitone_pair_of_not_sorted' /-
/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
    ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i :=
  by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)
#align tuple.antitone_pair_of_not_sorted' Tuple.antitone_pair_of_not_sorted'
-/

#print Tuple.antitone_pair_of_not_sorted /-
/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
theorem antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ ≠ _)
#align tuple.antitone_pair_of_not_sorted Tuple.antitone_pair_of_not_sorted
-/

end Tuple

