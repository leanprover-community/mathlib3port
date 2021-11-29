import Mathbin.Combinatorics.SimpleGraph.Basic 
import Mathbin.Data.Set.Finite

/-!
# Strongly regular graphs

## Main definitions

* `G.is_SRG_of n k l m` (see `is_simple_graph.is_SRG_of`) is a structure for a `simple_graph`
  satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `l`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `m`

## TODO
- Prove that the complement of a strongly regular graph is strongly regular with parameters
  `is_SRG_of n (n - k - 1) (n - 2 - 2k + m) (v - 2k + l)`
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * m = k * (k - l - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + lA + m(J - I - A)`
-/


universe u

namespace SimpleGraph

variable{V : Type u}

variable(G : SimpleGraph V)[DecidableRel G.adj]

variable[Fintype V][DecidableEq V]

/--
A graph is strongly regular with parameters `n k l m` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `l` common neighbors
 * every pair of nonadjacent vertices has `m` common neighbors
-/
structure is_SRG_of(n k l m : ℕ) : Prop where 
  card : Fintype.card V = n 
  regular : G.is_regular_of_degree k 
  adj_common : ∀ (v w : V), G.adj v w → Fintype.card (G.common_neighbors v w) = l 
  nadj_common : ∀ (v w : V), ¬G.adj v w ∧ v ≠ w → Fintype.card (G.common_neighbors v w) = m

open Finset

-- error in Combinatorics.SimpleGraph.StronglyRegular: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Complete graphs are strongly regular. Note that the parameter `m` can take any value
  for complete graphs, since there are no distinct pairs of nonadjacent vertices. -/
theorem complete_strongly_regular
(m : exprℕ()) : («expr⊤»() : simple_graph V).is_SRG_of (fintype.card V) «expr - »(fintype.card V, 1) «expr - »(fintype.card V, 2) m :=
{ card := rfl,
  regular := complete_graph_degree,
  adj_common := λ (v w) (h : «expr ≠ »(v, w)), begin
    simp [] [] ["only"] ["[", expr fintype.card_of_finset, ",", expr mem_common_neighbors, ",", expr filter_not, ",", "<-", expr not_or_distrib, ",", expr filter_eq, ",", expr filter_or, ",", expr card_univ_diff, ",", expr mem_univ, ",", expr if_pos, ",", "<-", expr insert_eq, ",", expr top_adj, "]"] [] [],
    rw ["[", expr card_insert_of_not_mem, ",", expr card_singleton, "]"] [],
    simp [] [] [] ["[", expr h, "]"] [] []
  end,
  nadj_common := λ (v w) (h : «expr ∧ »(«expr¬ »(«expr ≠ »(v, w)), _)), (h.1 h.2).elim }

end SimpleGraph

