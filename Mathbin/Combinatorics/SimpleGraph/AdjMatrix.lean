/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang

! This file was ported from Lean 3 source module combinatorics.simple_graph.adj_matrix
! leanprover-community/mathlib commit 3e068ece210655b7b9a9477c3aff38a492400aa1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Combinatorics.SimpleGraph.Connectivity
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.LinearAlgebra.Matrix.Symmetric

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `matrix.is_adj_matrix`: `A : matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `matrix.is_adj_matrix.to_graph`: for `A : matrix V V α` and `h : A.is_adj_matrix`,
  `h.to_graph` is the simple graph induced by `A`.

* `matrix.compl`: for `A : matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `simple_graph.adj_matrix`: the adjacency matrix of a `simple_graph`.

* `simple_graph.adj_matrix_pow_apply_eq_card_walk`: each entry of the `n`th power of
  a graph's adjacency matrix counts the number of length-`n` walks between the corresponding
  pair of vertices.

-/


open BigOperators Matrix

open Finset Matrix SimpleGraph

variable {V α β : Type _}

namespace Matrix

#print Matrix.IsAdjMatrix /-
/-- `A : matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by obviously
  symm : A.IsSymm := by obviously
  apply_diag : ∀ i, A i i = 0 := by obviously
#align matrix.is_adj_matrix Matrix.IsAdjMatrix
-/

namespace IsAdjMatrix

variable {A : Matrix V V α}

/- warning: matrix.is_adj_matrix.apply_diag_ne -> Matrix.IsAdjMatrix.apply_diag_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V), Not (Eq.{succ u2} α (A i i) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)))))))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V), Not (Eq.{succ u2} α (A i i) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.apply_diag_ne Matrix.IsAdjMatrix.apply_diag_neₓ'. -/
@[simp]
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) : ¬A i i = 1 :=
  by simp [h.apply_diag i]
#align matrix.is_adj_matrix.apply_diag_ne Matrix.IsAdjMatrix.apply_diag_ne

/- warning: matrix.is_adj_matrix.apply_ne_one_iff -> Matrix.IsAdjMatrix.apply_ne_one_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V) (j : V), Iff (Not (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1))))))) (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)))))))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V) (j : V), Iff (Not (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)))))) (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroOneClass.toZero.{u2} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.apply_ne_one_iff Matrix.IsAdjMatrix.apply_ne_one_iffₓ'. -/
@[simp]
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]
#align matrix.is_adj_matrix.apply_ne_one_iff Matrix.IsAdjMatrix.apply_ne_one_iff

/- warning: matrix.is_adj_matrix.apply_ne_zero_iff -> Matrix.IsAdjMatrix.apply_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V) (j : V), Iff (Not (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1))))))) (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)))))))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (forall (i : V) (j : V), Iff (Not (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MulZeroOneClass.toZero.{u2} α _inst_1))))) (Eq.{succ u2} α (A i j) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.apply_ne_zero_iff Matrix.IsAdjMatrix.apply_ne_zero_iffₓ'. -/
@[simp]
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]
#align matrix.is_adj_matrix.apply_ne_zero_iff Matrix.IsAdjMatrix.apply_ne_zero_iff

/- warning: matrix.is_adj_matrix.to_graph -> Matrix.IsAdjMatrix.toGraph is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (SimpleGraph.{u1} V)
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {A : Matrix.{u1, u1, u2} V V α} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α], (Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) -> (SimpleGraph.{u1} V)
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.to_graph Matrix.IsAdjMatrix.toGraphₓ'. -/
/-- For `A : matrix V V α` and `h : is_adj_matrix A`,
    `h.to_graph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V
    where
  Adj i j := A i j = 1
  symm i j hij := by rwa [h.symm.apply i j]
  loopless i := by simp [h]
#align matrix.is_adj_matrix.to_graph Matrix.IsAdjMatrix.toGraph

instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [to_graph]
  infer_instance

end IsAdjMatrix

#print Matrix.compl /-
/-- For `A : matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adj_matrix`. -/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  fun i j => ite (i = j) 0 (ite (A i j = 0) 1 0)
#align matrix.compl Matrix.compl
-/

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

#print Matrix.compl_apply_diag /-
@[simp]
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]
#align matrix.compl_apply_diag Matrix.compl_apply_diag
-/

#print Matrix.compl_apply /-
@[simp]
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 :=
  by
  unfold compl
  split_ifs <;> simp
#align matrix.compl_apply Matrix.compl_apply
-/

#print Matrix.isSymm_compl /-
@[simp]
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm :=
  by
  ext
  simp [compl, h.apply, eq_comm]
#align matrix.is_symm_compl Matrix.isSymm_compl
-/

#print Matrix.isAdjMatrix_compl /-
@[simp]
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }
#align matrix.is_adj_matrix_compl Matrix.isAdjMatrix_compl
-/

namespace IsAdjMatrix

variable {A}

#print Matrix.IsAdjMatrix.compl /-
@[simp]
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm
#align matrix.is_adj_matrix.compl Matrix.IsAdjMatrix.compl
-/

/- warning: matrix.is_adj_matrix.to_graph_compl_eq -> Matrix.IsAdjMatrix.toGraph_compl_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} V] {A : Matrix.{u1, u1, u2} V V α} [_inst_3 : MulZeroOneClass.{u2} α] [_inst_4 : Nontrivial.{u2} α] (h : Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_3)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) A), Eq.{succ u1} (SimpleGraph.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α (Matrix.compl.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_3)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) (fun (a : α) (b : α) => _inst_1 a b) (fun (a : V) (b : V) => _inst_2 a b) A) _inst_3 _inst_4 (Matrix.IsAdjMatrix.compl.{u1, u2} V α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : V) (b : V) => _inst_2 a b) A (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_3)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) h)) (HasCompl.compl.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasCompl.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α A _inst_3 _inst_4 h))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} V] {A : Matrix.{u1, u1, u2} V V α} [_inst_3 : MulZeroOneClass.{u2} α] [_inst_4 : Nontrivial.{u2} α] (h : Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_3) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) A), Eq.{succ u1} (SimpleGraph.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α (Matrix.compl.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_3) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) (fun (a : α) (b : α) => _inst_1 a b) (fun (a : V) (b : V) => _inst_2 a b) A) _inst_3 _inst_4 (Matrix.IsAdjMatrix.compl.{u1, u2} V α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : V) (b : V) => _inst_2 a b) A (MulZeroOneClass.toZero.{u2} α _inst_3) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_3)) h)) (HasCompl.compl.{u1} (SimpleGraph.{u1} V) (SimpleGraph.hasCompl.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α A _inst_3 _inst_4 h))
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.to_graph_compl_eq Matrix.IsAdjMatrix.toGraph_compl_eqₓ'. -/
theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext (v w)
  cases' h.zero_or_one v w with h h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]
#align matrix.is_adj_matrix.to_graph_compl_eq Matrix.IsAdjMatrix.toGraph_compl_eq

end IsAdjMatrix

end Compl

end Matrix

open Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (α)

#print SimpleGraph.adjMatrix /-
/-- `adj_matrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0
#align simple_graph.adj_matrix SimpleGraph.adjMatrix
-/

variable {α}

#print SimpleGraph.adjMatrix_apply /-
-- TODO: set as an equation lemma for `adj_matrix`, see mathlib4#3024
@[simp]
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl
#align simple_graph.adj_matrix_apply SimpleGraph.adjMatrix_apply
-/

#print SimpleGraph.transpose_adjMatrix /-
@[simp]
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α :=
  by
  ext
  simp [adj_comm]
#align simple_graph.transpose_adj_matrix SimpleGraph.transpose_adjMatrix
-/

#print SimpleGraph.isSymm_adjMatrix /-
@[simp]
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G
#align simple_graph.is_symm_adj_matrix SimpleGraph.isSymm_adjMatrix
-/

variable (α)

#print SimpleGraph.isAdjMatrix_adjMatrix /-
/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix :=
  { zero_or_one := fun i j => by by_cases G.adj i j <;> simp [h] }
#align simple_graph.is_adj_matrix_adj_matrix SimpleGraph.isAdjMatrix_adjMatrix
-/

/- warning: simple_graph.to_graph_adj_matrix_eq -> SimpleGraph.toGraph_adjMatrix_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} (α : Type.{u2}) (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : MulZeroOneClass.{u2} α] [_inst_3 : Nontrivial.{u2} α], Eq.{succ u1} (SimpleGraph.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_2)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2))) _inst_2 _inst_3 (SimpleGraph.isAdjMatrix_adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_2)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2)))) G
but is expected to have type
  forall {V : Type.{u1}} (α : Type.{u2}) (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : MulZeroOneClass.{u2} α] [_inst_3 : Nontrivial.{u2} α], Eq.{succ u1} (SimpleGraph.{u1} V) (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2))) _inst_2 _inst_3 (SimpleGraph.isAdjMatrix_adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α _inst_2) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_2)))) G
Case conversion may be inaccurate. Consider using '#align simple_graph.to_graph_adj_matrix_eq SimpleGraph.toGraph_adjMatrix_eqₓ'. -/
/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [is_adj_matrix.to_graph_adj, adj_matrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not
#align simple_graph.to_graph_adj_matrix_eq SimpleGraph.toGraph_adjMatrix_eq

variable {α} [Fintype V]

/- warning: simple_graph.adj_matrix_dot_product -> SimpleGraph.adjMatrix_dotProduct is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} V α _inst_2 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3))) v) vec) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} V α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3) v) vec) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_dot_product SimpleGraph.adjMatrix_dotProductₓ'. -/
@[simp]
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct (G.adjMatrix α v) vec = ∑ u in G.neighborFinset v, vec u := by
  simp [neighbor_finset_eq_filter, dot_product, sum_filter]
#align simple_graph.adj_matrix_dot_product SimpleGraph.adjMatrix_dotProduct

/- warning: simple_graph.dot_product_adj_matrix -> SimpleGraph.dotProduct_adjMatrix is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} V α _inst_2 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) vec (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3))) v)) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.dotProduct.{u2, u1} V α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) vec (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3) v)) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
Case conversion may be inaccurate. Consider using '#align simple_graph.dot_product_adj_matrix SimpleGraph.dotProduct_adjMatrixₓ'. -/
@[simp]
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct vec (G.adjMatrix α v) = ∑ u in G.neighborFinset v, vec u := by
  simp [neighbor_finset_eq_filter, dot_product, sum_filter, Finset.sum_apply]
#align simple_graph.dot_product_adj_matrix SimpleGraph.dotProduct_adjMatrix

/- warning: simple_graph.adj_matrix_mul_vec_apply -> SimpleGraph.adjMatrix_mulVec_apply is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) vec v) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) vec v) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_mul_vec_apply SimpleGraph.adjMatrix_mulVec_applyₓ'. -/
@[simp]
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    ((G.adjMatrix α).mulVec vec) v = ∑ u in G.neighborFinset v, vec u := by
  rw [mul_vec, adj_matrix_dot_product]
#align simple_graph.adj_matrix_mul_vec_apply SimpleGraph.adjMatrix_mulVec_apply

/- warning: simple_graph.adj_matrix_vec_mul_apply -> SimpleGraph.adjMatrix_vecMul_apply is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.vecMul.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_2 vec (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) v) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (v : V) (vec : V -> α), Eq.{succ u2} α (Matrix.vecMul.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3) _inst_2 vec (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) v) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => vec u))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_vec_mul_apply SimpleGraph.adjMatrix_vecMul_applyₓ'. -/
@[simp]
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    ((G.adjMatrix α).vecMul vec) v = ∑ u in G.neighborFinset v, vec u :=
  by
  rw [← dot_product_adj_matrix, vec_mul]
  refine' congr rfl _; ext
  rw [← transpose_apply (adj_matrix α G) x v, transpose_adj_matrix]
#align simple_graph.adj_matrix_vec_mul_apply SimpleGraph.adjMatrix_vecMul_apply

/- warning: simple_graph.adj_matrix_mul_apply -> SimpleGraph.adjMatrix_mul_apply is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (M : Matrix.{u1, u1, u2} V V α) (v : V) (w : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) M v w) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => M u w))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (M : Matrix.{u1, u1, u2} V V α) (v : V) (w : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) M v w) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v)) (fun (u : V) => M u w))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_mul_apply SimpleGraph.adjMatrix_mul_applyₓ'. -/
@[simp]
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α ⬝ M) v w = ∑ u in G.neighborFinset v, M u w := by
  simp [mul_apply, neighbor_finset_eq_filter, sum_filter]
#align simple_graph.adj_matrix_mul_apply SimpleGraph.adjMatrix_mul_apply

/- warning: simple_graph.mul_adj_matrix_apply -> SimpleGraph.mul_adjMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (M : Matrix.{u1, u1, u2} V V α) (v : V) (w : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) M (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) v w) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G w (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) w)) (fun (u : V) => M v u))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (M : Matrix.{u1, u1, u2} V V α) (v : V) (w : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) M (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) v w) (Finset.sum.{u2, u1} α V (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.neighborFinset.{u1} V G w (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) w)) (fun (u : V) => M v u))
Case conversion may be inaccurate. Consider using '#align simple_graph.mul_adj_matrix_apply SimpleGraph.mul_adjMatrix_applyₓ'. -/
@[simp]
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M ⬝ G.adjMatrix α) v w = ∑ u in G.neighborFinset w, M v u := by
  simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_comm]
#align simple_graph.mul_adj_matrix_apply SimpleGraph.mul_adjMatrix_apply

variable (α)

/- warning: simple_graph.trace_adj_matrix -> SimpleGraph.trace_adjMatrix is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} (α : Type.{u2}) (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : AddCommMonoid.{u2} α] [_inst_4 : One.{u2} α], Eq.{succ u2} α (Matrix.trace.{u1, u2} V α _inst_2 _inst_3 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_3))) _inst_4)) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_3))))))
but is expected to have type
  forall {V : Type.{u1}} (α : Type.{u2}) (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : AddCommMonoid.{u2} α] [_inst_4 : One.{u2} α], Eq.{succ u2} α (Matrix.trace.{u1, u2} V α _inst_2 _inst_3 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_3)) _inst_4)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align simple_graph.trace_adj_matrix SimpleGraph.trace_adjMatrixₓ'. -/
@[simp]
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]
#align simple_graph.trace_adj_matrix SimpleGraph.trace_adjMatrix

variable {α}

/- warning: simple_graph.adj_matrix_mul_self_apply_self -> SimpleGraph.adjMatrix_mul_self_apply_self is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (i : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))) i i) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α _inst_3)))))) (SimpleGraph.degree.{u1} V G i (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) i)))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u1} V) [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : NonAssocSemiring.{u2} α] (i : V), Eq.{succ u2} α (Matrix.mul.{u2, u1, u1, u1} V V V α _inst_2 (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroOneClass.toZero.{u2} α (NonAssocSemiring.toMulZeroOneClass.{u2} α _inst_3)) (NonAssocSemiring.toOne.{u2} α _inst_3)) i i) (Nat.cast.{u2} α (NonAssocSemiring.toNatCast.{u2} α _inst_3) (SimpleGraph.degree.{u1} V G i (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) i)))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_mul_self_apply_self SimpleGraph.adjMatrix_mul_self_apply_selfₓ'. -/
theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α ⬝ G.adjMatrix α) i i = degree G i := by simp [degree]
#align simple_graph.adj_matrix_mul_self_apply_self SimpleGraph.adjMatrix_mul_self_apply_self

variable {G}

/- warning: simple_graph.adj_matrix_mul_vec_const_apply -> SimpleGraph.adjMatrix_mulVec_const_apply is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {G : SimpleGraph.{u1} V} [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : Semiring.{u2} α] {a : α} {v : V}, Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))) (Function.const.{succ u2, succ u1} α V a) v) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))))) (SimpleGraph.degree.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v))) a)
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {G : SimpleGraph.{u1} V} [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : Semiring.{u2} α] {a : α} {v : V}, Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_3)) (Semiring.toOne.{u2} α _inst_3)) (Function.const.{succ u2, succ u1} α V a) v) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)))) (Nat.cast.{u2} α (Semiring.toNatCast.{u2} α _inst_3) (SimpleGraph.degree.{u1} V G v (SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v))) a)
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_mul_vec_const_apply SimpleGraph.adjMatrix_mulVec_const_applyₓ'. -/
@[simp]
theorem adjMatrix_mulVec_const_apply [Semiring α] {a : α} {v : V} :
    (G.adjMatrix α).mulVec (Function.const _ a) v = G.degree v * a := by simp [degree]
#align simple_graph.adj_matrix_mul_vec_const_apply SimpleGraph.adjMatrix_mulVec_const_apply

/- warning: simple_graph.adj_matrix_mul_vec_const_apply_of_regular -> SimpleGraph.adjMatrix_mulVec_const_apply_of_regular is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {G : SimpleGraph.{u1} V} [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : Semiring.{u2} α] {d : Nat} {a : α}, (SimpleGraph.IsRegularOfDegree.{u1} V G (fun (v : V) => SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v) d) -> (forall {v : V}, Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))) (Function.const.{succ u2, succ u1} α V a) v) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3))))))) d) a))
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} {G : SimpleGraph.{u1} V} [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : Semiring.{u2} α] {d : Nat} {a : α}, (SimpleGraph.IsRegularOfDegree.{u1} V G (fun (v : V) => SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v) d) -> (forall {v : V}, Eq.{succ u2} α (Matrix.mulVec.{u2, u1, u1} V V α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)) _inst_2 (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α _inst_3)) (Semiring.toOne.{u2} α _inst_3)) (Function.const.{succ u2, succ u1} α V a) v) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_3)))) (Nat.cast.{u2} α (Semiring.toNatCast.{u2} α _inst_3) d) a))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_mul_vec_const_apply_of_regular SimpleGraph.adjMatrix_mulVec_const_apply_of_regularₓ'. -/
theorem adjMatrix_mulVec_const_apply_of_regular [Semiring α] {d : ℕ} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α).mulVec (Function.const _ a) v = d * a :=
  by simp [hd v]
#align simple_graph.adj_matrix_mul_vec_const_apply_of_regular SimpleGraph.adjMatrix_mulVec_const_apply_of_regular

/- warning: simple_graph.adj_matrix_pow_apply_eq_card_walk -> SimpleGraph.adjMatrix_pow_apply_eq_card_walk is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} {G : SimpleGraph.{u1} V} [_inst_1 : DecidableRel.{succ u1} V (SimpleGraph.Adj.{u1} V G)] [_inst_2 : Fintype.{u1} V] [_inst_3 : DecidableEq.{succ u1} V] [_inst_4 : Semiring.{u2} α] (n : Nat) (u : V) (v : V), Eq.{succ u2} α (HPow.hPow.{max u1 u2, 0, max u1 u2} (Matrix.{u1, u1, u2} V V α) Nat (Matrix.{u1, u1, u2} V V α) (instHPow.{max u1 u2, 0} (Matrix.{u1, u1, u2} V V α) Nat (Monoid.Pow.{max u1 u2} (Matrix.{u1, u1, u2} V V α) (MonoidWithZero.toMonoid.{max u1 u2} (Matrix.{u1, u1, u2} V V α) (Semiring.toMonoidWithZero.{max u1 u2} (Matrix.{u1, u1, u2} V V α) (Matrix.semiring.{u2, u1} V α _inst_4 _inst_2 (fun (a : V) (b : V) => _inst_3 a b)))))) (SimpleGraph.adjMatrix.{u1, u2} V α G (fun (a : V) (b : V) => _inst_1 a b) (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4)))) (AddMonoidWithOne.toOne.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))) n u v) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u2} Nat α (CoeTCₓ.coe.{1, succ u2} Nat α (Nat.castCoe.{u2} α (AddMonoidWithOne.toNatCast.{u2} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} α (NonAssocSemiring.toAddCommMonoidWithOne.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_4))))))) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (SimpleGraph.Walk.{u1} V G u v)) Type.{u1} (Set.hasCoeToSort.{u1} (SimpleGraph.Walk.{u1} V G u v)) (setOf.{u1} (SimpleGraph.Walk.{u1} V G u v) (fun (p : SimpleGraph.Walk.{u1} V G u v) => Eq.{1} Nat (SimpleGraph.Walk.length.{u1} V G u v p) n))) (SimpleGraph.fintypeSetWalkLength.{u1} V G (fun (a : V) (b : V) => _inst_3 a b) (fun (v : V) => SimpleGraph.neighborSetFintype.{u1} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v) u v n)))
but is expected to have type
  forall {V : Type.{u2}} {α : Type.{u1}} {G : SimpleGraph.{u2} V} [_inst_1 : DecidableRel.{succ u2} V (SimpleGraph.Adj.{u2} V G)] [_inst_2 : Fintype.{u2} V] [_inst_3 : DecidableEq.{succ u2} V] [_inst_4 : Semiring.{u1} α] (n : Nat) (u : V) (v : V), Eq.{succ u1} α (HPow.hPow.{max u2 u1, 0, max u2 u1} (Matrix.{u2, u2, u1} V V α) Nat (Matrix.{u2, u2, u1} V V α) (instHPow.{max u2 u1, 0} (Matrix.{u2, u2, u1} V V α) Nat (Monoid.Pow.{max u2 u1} (Matrix.{u2, u2, u1} V V α) (MonoidWithZero.toMonoid.{max u2 u1} (Matrix.{u2, u2, u1} V V α) (Semiring.toMonoidWithZero.{max u2 u1} (Matrix.{u2, u2, u1} V V α) (Matrix.semiring.{u1, u2} V α _inst_4 _inst_2 (fun (a : V) (b : V) => _inst_3 a b)))))) (SimpleGraph.adjMatrix.{u2, u1} V α G (fun (a : V) (b : V) => _inst_1 a b) (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_4)) (Semiring.toOne.{u1} α _inst_4)) n u v) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α _inst_4) (Fintype.card.{u2} (Set.Elem.{u2} (SimpleGraph.Walk.{u2} V G u v) (setOf.{u2} (SimpleGraph.Walk.{u2} V G u v) (fun (p : SimpleGraph.Walk.{u2} V G u v) => Eq.{1} Nat (SimpleGraph.Walk.length.{u2} V G u v p) n))) (SimpleGraph.fintypeSetWalkLength.{u2} V G (fun (a : V) (b : V) => _inst_3 a b) (fun (v : V) => SimpleGraph.neighborSetFintype.{u2} V G _inst_2 (fun (a : V) (b : V) => _inst_1 a b) v) u v n)))
Case conversion may be inaccurate. Consider using '#align simple_graph.adj_matrix_pow_apply_eq_card_walk SimpleGraph.adjMatrix_pow_apply_eq_card_walkₓ'. -/
theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } :=
  by
  rw [card_set_walk_length_eq]
  induction' n with n ih generalizing u v
  · obtain rfl | h := eq_or_ne u v <;> simp [finset_walk_length, *]
  · nth_rw 1 [Nat.succ_eq_one_add]
    simp only [pow_add, pow_one, finset_walk_length, ih, mul_eq_mul, adj_matrix_mul_apply]
    rw [Finset.card_bunionᵢ]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighbor_finset_def]
      apply Finset.sum_toFinset_eq_subtype
    -- Disjointness for card_bUnion
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.coeFn_mk, exists_prop] at
          hp <;>
        obtain ⟨⟨px, hpx, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simpa using hxy
#align simple_graph.adj_matrix_pow_apply_eq_card_walk SimpleGraph.adjMatrix_pow_apply_eq_card_walk

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]

variable {A : Matrix V V α} (h : IsAdjMatrix A)

/- warning: matrix.is_adj_matrix.adj_matrix_to_graph_eq -> Matrix.IsAdjMatrix.adjMatrix_toGraph_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {α : Type.{u2}} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α] {A : Matrix.{u1, u1, u2} V V α} (h : Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) [_inst_3 : DecidableEq.{succ u2} α], Eq.{succ (max u1 u2)} (Matrix.{u1, u1, u2} V V α) (SimpleGraph.adjMatrix.{u1, u2} V α (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α A _inst_1 _inst_2 h) (fun (a : V) (b : V) => Matrix.IsAdjMatrix.Adj.decidableRel.{u1, u2} V α A _inst_1 _inst_2 (fun (a : α) (b : α) => _inst_3 a b) h a b) (MulZeroClass.toHasZero.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulOneClass.toHasOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1))) A
but is expected to have type
  forall {V : Type.{u1}} {α : Type.{u2}} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : Nontrivial.{u2} α] {A : Matrix.{u1, u1, u2} V V α} (h : Matrix.IsAdjMatrix.{u1, u2} V α (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1)) A) [_inst_3 : DecidableEq.{succ u2} α], Eq.{max (succ u1) (succ u2)} (Matrix.{u1, u1, u2} V V α) (SimpleGraph.adjMatrix.{u1, u2} V α (Matrix.IsAdjMatrix.toGraph.{u1, u2} V α A _inst_1 _inst_2 h) (fun (a : V) (b : V) => Matrix.IsAdjMatrix.instDecidableRelAdjToGraph.{u1, u2} V α A _inst_1 _inst_2 (fun (a : α) (b : α) => _inst_3 a b) h a b) (MulZeroOneClass.toZero.{u2} α _inst_1) (MulOneClass.toOne.{u2} α (MulZeroOneClass.toMulOneClass.{u2} α _inst_1))) A
Case conversion may be inaccurate. Consider using '#align matrix.is_adj_matrix.adj_matrix_to_graph_eq Matrix.IsAdjMatrix.adjMatrix_toGraph_eqₓ'. -/
/-- If `A` is qualified as an adjacency matrix,
    then the adjacency matrix of the graph induced by `A` is itself. -/
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A :=
  by
  ext (i j)
  obtain h' | h' := h.zero_or_one i j <;> simp [h']
#align matrix.is_adj_matrix.adj_matrix_to_graph_eq Matrix.IsAdjMatrix.adjMatrix_toGraph_eq

end Matrix.IsAdjMatrix

