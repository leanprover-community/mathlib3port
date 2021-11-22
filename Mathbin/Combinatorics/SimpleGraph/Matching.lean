import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# Matchings


## Main definitions

* a `matching` on a simple graph is a subset of its edge set such that
   no two edges share an endpoint.

* a `perfect_matching` on a simple graph is a matching in which every
   vertex belongs to an edge.

TODO:
  - Lemma stating that the existence of a perfect matching on `G` implies that
    the cardinality of `V` is even (assuming it's finite)
  - Hall's Marriage Theorem (see combinatorics.hall)
  - Tutte's Theorem
  - consider coercions instead of type definition for `matching`:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532935457
  - consider expressing `matching_verts` as union:
    https://github.com/leanprover-community/mathlib/pull/5156#discussion_r532906131

TODO: Tutte and Hall require a definition of subgraphs.
-/


open Finset

universe u

namespace SimpleGraph

variable{V : Type u}(G : SimpleGraph V)

/--
A matching on `G` is a subset of its edges such that no two edges share a vertex.
-/
structure matching where 
  Edges : Set (Sym2 V)
  sub_edges : edges ⊆ G.edge_set 
  Disjoint : ∀ x y _ : x ∈ edges _ : y ∈ edges v : V, v ∈ x ∧ v ∈ y → x = y

instance  : Inhabited (matching G) :=
  ⟨⟨∅, Set.empty_subset _, fun _ _ hx => False.elim (Set.not_mem_empty _ hx)⟩⟩

variable{G}

/--
`M.support` is the set of vertices of `G` that are
contained in some edge of matching `M`
-/
def matching.support (M : G.matching) : Set V :=
  { v : V | ∃ (x : _)(_ : x ∈ M.edges), v ∈ x }

/--
A perfect matching `M` on graph `G` is a matching such that
  every vertex is contained in an edge of `M`.
-/
def matching.is_perfect (M : G.matching) : Prop :=
  M.support = Set.Univ

theorem matching.is_perfect_iff (M : G.matching) : M.is_perfect ↔ ∀ v : V, ∃ (e : _)(_ : e ∈ M.edges), v ∈ e :=
  Set.eq_univ_iff_forall

end SimpleGraph

