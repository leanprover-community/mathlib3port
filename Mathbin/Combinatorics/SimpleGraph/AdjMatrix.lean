import Mathbin.Combinatorics.SimpleGraph.Basic 
import Mathbin.Data.Rel 
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

-/


open_locale BigOperators Matrix

open Finset Matrix SimpleGraph

variable {V α β : Type _}

namespace Matrix

/-- `A : matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure is_adj_matrix [HasZero α] [HasOne α] (A : Matrix V V α) : Prop where 
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 :=  by 
  runTac 
    obviously 
  symm : A.is_symm :=  by 
  runTac 
    obviously 
  apply_diag : ∀ i, A i i = 0 :=  by 
  runTac 
    obviously

namespace IsAdjMatrix

variable {A : Matrix V V α}

@[simp]
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : is_adj_matrix A) (i : V) : ¬A i i = 1 :=
  by 
    simp [h.apply_diag i]

@[simp]
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : is_adj_matrix A) (i j : V) : ¬A i j = 1 ↔ A i j = 0 :=
  by 
    obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : is_adj_matrix A) (i j : V) : ¬A i j = 0 ↔ A i j = 1 :=
  by 
    rw [←apply_ne_one_iff h, not_not]

/-- For `A : matrix V V α` and `h : is_adj_matrix A`,
    `h.to_graph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def to_graph [MulZeroOneClass α] [Nontrivial α] (h : is_adj_matrix A) : SimpleGraph V :=
  { Adj := fun i j => A i j = 1,
    symm :=
      fun i j hij =>
        by 
          rwa [h.symm.apply i j],
    loopless :=
      fun i =>
        by 
          simp [h] }

instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : is_adj_matrix A) : DecidableRel h.to_graph.adj :=
  by 
    simp only [to_graph]
    infer_instance

end IsAdjMatrix

/-- For `A : matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adj_matrix`. -/
def compl [HasZero α] [HasOne α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  fun i j => ite (i = j) 0 (ite (A i j = 0) 1 0)

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
theorem compl_apply_diag [HasZero α] [HasOne α] (i : V) : A.compl i i = 0 :=
  by 
    simp [compl]

@[simp]
theorem compl_apply [HasZero α] [HasOne α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 :=
  by 
    unfold compl 
    splitIfs <;> simp 

@[simp]
theorem is_symm_compl [HasZero α] [HasOne α] (h : A.is_symm) : A.compl.is_symm :=
  by 
    ext 
    simp [compl, h.apply, eq_comm]

@[simp]
theorem is_adj_matrix_compl [HasZero α] [HasOne α] (h : A.is_symm) : is_adj_matrix A.compl :=
  { symm :=
      by 
        simp [h] }

namespace IsAdjMatrix

variable {A}

@[simp]
theorem compl [HasZero α] [HasOne α] (h : is_adj_matrix A) : is_adj_matrix A.compl :=
  is_adj_matrix_compl A h.symm

theorem to_graph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : is_adj_matrix A) : h.compl.to_graph = h.to_graphᶜ :=
  by 
    ext v w 
    cases' h.zero_or_one v w with h h <;> byCases' hvw : v = w <;> simp [Matrix.compl, h, hvw]

end IsAdjMatrix

end Compl

end Matrix

open Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.adj]

variable (α)

/-- `adj_matrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix [HasZero α] [HasOne α] : Matrix V V α
| i, j => if G.adj i j then 1 else 0

variable {α}

@[simp]
theorem adj_matrix_apply (v w : V) [HasZero α] [HasOne α] : G.adj_matrix α v w = if G.adj v w then 1 else 0 :=
  rfl

@[simp]
theorem transpose_adj_matrix [HasZero α] [HasOne α] : (G.adj_matrix α)ᵀ = G.adj_matrix α :=
  by 
    ext 
    simp [adj_comm]

@[simp]
theorem is_symm_adj_matrix [HasZero α] [HasOne α] : (G.adj_matrix α).IsSymm :=
  transpose_adj_matrix G

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
theorem is_adj_matrix_adj_matrix [HasZero α] [HasOne α] : (G.adj_matrix α).IsAdjMatrix :=
  { zero_or_one :=
      fun i j =>
        by 
          byCases' G.adj i j <;> simp [h] }

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
theorem to_graph_adj_matrix_eq [MulZeroOneClass α] [Nontrivial α] : (G.is_adj_matrix_adj_matrix α).toGraph = G :=
  by 
    ext 
    simp only [is_adj_matrix.to_graph_adj, adj_matrix_apply, ite_eq_left_iff, zero_ne_one]
    apply not_not

variable {α} [Fintype V]

@[simp]
theorem adj_matrix_dot_product [NonAssocSemiring α] (v : V) (vec : V → α) :
  dot_product (G.adj_matrix α v) vec = ∑ u in G.neighbor_finset v, vec u :=
  by 
    simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
theorem dot_product_adj_matrix [NonAssocSemiring α] (v : V) (vec : V → α) :
  dot_product vec (G.adj_matrix α v) = ∑ u in G.neighbor_finset v, vec u :=
  by 
    simp [neighbor_finset_eq_filter, dot_product, sum_filter, Finset.sum_apply]

@[simp]
theorem adj_matrix_mul_vec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).mulVec vec) v = ∑ u in G.neighbor_finset v, vec u :=
  by 
    rw [mul_vec, adj_matrix_dot_product]

@[simp]
theorem adj_matrix_vec_mul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).vecMul vec) v = ∑ u in G.neighbor_finset v, vec u :=
  by 
    rw [←dot_product_adj_matrix, vec_mul]
    refine' congr rfl _ 
    ext 
    rw [←transpose_apply (adj_matrix α G) x v, transpose_adj_matrix]

@[simp]
theorem adj_matrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
  (G.adj_matrix α ⬝ M) v w = ∑ u in G.neighbor_finset v, M u w :=
  by 
    simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
theorem mul_adj_matrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
  (M ⬝ G.adj_matrix α) v w = ∑ u in G.neighbor_finset w, M v u :=
  by 
    simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_comm]

variable (α)

theorem trace_adj_matrix [NonAssocSemiring α] [Semiringₓ β] [Module β α] : Matrix.trace _ β _ (G.adj_matrix α) = 0 :=
  by 
    simp 

variable {α}

theorem adj_matrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
  (G.adj_matrix α ⬝ G.adj_matrix α) i i = degree G i :=
  by 
    simp [degree]

variable {G}

@[simp]
theorem adj_matrix_mul_vec_const_apply [Semiringₓ α] {a : α} {v : V} :
  (G.adj_matrix α).mulVec (Function.const _ a) v = G.degree v*a :=
  by 
    simp [degree]

theorem adj_matrix_mul_vec_const_apply_of_regular [Semiringₓ α] {d : ℕ} {a : α} (hd : G.is_regular_of_degree d)
  {v : V} : (G.adj_matrix α).mulVec (Function.const _ a) v = d*a :=
  by 
    simp [hd v]

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]

variable {A : Matrix V V α} (h : is_adj_matrix A)

/-- If `A` is qualified as an adjacency matrix,
    then the adjacency matrix of the graph induced by `A` is itself. -/
theorem adj_matrix_to_graph_eq [DecidableEq α] : h.to_graph.adj_matrix α = A :=
  by 
    ext i j 
    obtain h' | h' := h.zero_or_one i j <;> simp [h']

end Matrix.IsAdjMatrix

