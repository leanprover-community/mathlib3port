/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Connectivity
import Mathbin.Data.Nat.Parity

/-!

# Trails and Eulerian trails

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `simple_graph.walk.is_eulerian` is the predicate that a trail is an Eulerian trail.
* `simple_graph.walk.is_trail.even_countp_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `simple_graph.walk.is_eulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `simple_graph.walk.is_eulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## Todo

* Prove that there exists an Eulerian trail when the conclusion to
  `simple_graph.walk.is_eulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/


namespace SimpleGraph

variable {V : Type _} {G : SimpleGraph V}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
@[reducible]
def IsTrail.edgesFinset {u v : V} {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩

variable [DecidableEq V]

theorem IsTrail.even_countp_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countp fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction' p with u u v w huv p ih
  · simp
    
  · rw [cons_is_trail_iff] at ht
    specialize ih ht.1
    simp only [← List.countp_cons, ← Ne.def, ← edges_cons, ← Sym2.mem_iff]
    split_ifs with h
    · obtain rfl | rfl := h
      · rw [Nat.even_add_one, ih]
        simp only [← huv.ne, ← imp_false, ← Ne.def, ← not_false_iff, ← true_andₓ, ← not_forall, ← not_not, ←
          exists_prop, ← eq_self_iff_true, ← not_true, ← false_andₓ, ← and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless _ huv
        
      · rw [Nat.even_add_one, ih, ← not_iff_not]
        simp only [← huv.ne.symm, ← Ne.def, ← eq_self_iff_true, ← not_true, ← false_andₓ, ← not_forall, ← not_false_iff,
          ← exists_prop, ← and_trueₓ, ← not_not, ← true_andₓ, ← iff_and_self]
        rintro rfl
        exact huv.ne
        
      
    · rw [not_or_distrib] at h
      simp only [← h.1, ← h.2, ← not_false_iff, ← true_andₓ, ← add_zeroₓ, ← Ne.def] at ih⊢
      rw [ih]
      constructor <;>
        · rintro h' h'' rfl
          simp only [← imp_false, ← eq_self_iff_true, ← not_true, ← not_not] at h'
          cases h'
          simpa using h
          
      
    

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `simple_graph.walk.is_eulerian.is_trail` shows
that these are trails.

Combine with `p.is_circuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.EdgeSet → p.edges.count e = 1

theorem IsEulerian.is_trail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [is_trail_def, List.nodup_iff_count_le_one]
  intro e
  by_cases' he : e ∈ p.edges
  · exact (h e (edges_subset_edge_set _ he)).le
    
  · simp [← he]
    

theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.EdgeSet :=
  ⟨fun h => p.edges_subset_edge_set h, fun he => by
    simpa using (h e he).Ge⟩

/-- The edge set of an Eulerian graph is finite. -/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : Fintype G.EdgeSet :=
  (Fintype.ofFinset h.IsTrail.edgesFinset) fun e => by
    simp only [← Finset.mem_mk, ← Multiset.mem_coe, ← h.mem_edges_iff]

theorem IsTrail.is_eulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.EdgeSet → e ∈ p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)

theorem is_eulerian_iff {u v : V} (p : G.Walk u v) : p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.EdgeSet → e ∈ p.edges := by
  constructor
  · intro h
    exact ⟨h.is_trail, fun _ => h.mem_edges_iff.mpr⟩
    
  · rintro ⟨h, hl⟩
    exact h.is_eulerian_of_forall_mem hl
    

theorem IsEulerian.edges_finset_eq [Fintype G.EdgeSet] {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    h.IsTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [← h.mem_edges_iff]

theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V] [DecidableRel G.Adj] :
    Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  convert ht.is_trail.even_countp_edges_iff x
  rw [← Multiset.coe_countp, Multiset.countp_eq_card_filter, ← card_incidence_finset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to _ = (ht.is_trail.edges_finset.filter (HasMem.Mem x)).val
  rw [ht.edges_finset_eq, G.incidence_finset_eq_filter x]

theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) {s} (h : s = (Finset.univ : Finset V).filter fun v => Odd (G.degree v)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [← Nat.odd_iff_not_even, ← Finset.card_eq_zero]
  simp only [← ht.even_degree_iff, ← Ne.def, ← not_forall, ← not_and, ← not_not, ← exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · left
    simp
    
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [← hn]
      
    · congr
      ext x
      simp [← hn, ← imp_iff_not_or]
      
    

theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (ht : p.IsEulerian) :
    Fintype.card { v : V | Odd (G.degree v) } = 0 ∨ Fintype.card { v : V | Odd (G.degree v) } = 2 := by
  rw [← Set.to_finset_card]
  apply is_eulerian.card_filter_odd_degree ht
  ext v
  simp

end Walk

end SimpleGraph

