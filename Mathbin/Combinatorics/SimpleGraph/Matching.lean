import Mathbin.Combinatorics.SimpleGraph.Subgraph

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `simple_graph.subgraph.is_matching`: `M.is_matching` means that `M` is a matching of its
  underlying graph.
  denoted `M.is_matching`.

* `simple_graph.subgraph.is_perfect_matching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.is_perfect_matching`.

## TODO

* https://github.com/leanprover-community/mathlib/pull/10210#pullrequestreview-806303684

* Lemma stating that the existence of a perfect matching on `G` implies that
  the cardinality of `V` is even (assuming it's finite)

* Tutte's Theorem

* Hall's Marriage Theorem (see combinatorics.hall)
-/


universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} (M : subgraph G)

namespace Subgraph

/--
The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def is_matching : Prop :=
  ∀ ⦃v⦄, v ∈ M.verts → ∃! w, M.adj v w

/--
The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def is_perfect_matching : Prop :=
  M.is_matching ∧ M.is_spanning

theorem is_matching.support_eq_verts {M : subgraph G} (h : M.is_matching) : M.support = M.verts :=
  by 
    refine' M.support_subset_verts.antisymm fun v hv => _ 
    obtain ⟨w, hvw, -⟩ := h hv 
    exact ⟨_, hvw⟩

theorem is_perfect_matching_iff : M.is_perfect_matching ↔ ∀ v, ∃! w, M.adj v w :=
  by 
    refine' ⟨_, fun hm => ⟨fun v hv => hm v, fun v => _⟩⟩
    ·
      rintro ⟨hm, hs⟩ v 
      exact hm (hs v)
    ·
      obtain ⟨w, hw, -⟩ := hm v 
      exact M.edge_vert hw

end Subgraph

end SimpleGraph

