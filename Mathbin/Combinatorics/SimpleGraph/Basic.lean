/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import Mathbin.Data.Rel
import Mathbin.Data.Set.Finite
import Mathbin.Data.Sym.Sym2

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `simple_graph.neighbor_set` is the `set` of vertices adjacent to a given vertex

* `simple_graph.common_neighbors` is the intersection of the neighbor sets of two given vertices

* `simple_graph.neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `simple_graph.incidence_set` is the `set` of edges containing a given vertex

* `simple_graph.incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

* `simple_graph.dart` is an ordered pair of adjacent vertices, thought of as being an
  orientated edge. These are also known as "half-edges" or "bonds."

* `simple_graph.hom`, `simple_graph.embedding`, and `simple_graph.iso` for graph
  homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `boolean_algebra` instance: Under the subgraph relation, `simple_graph` forms a `boolean_algebra`.
  In other words, this is the lattice of spanning subgraphs of the complete graph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

## Implementation notes

* A locally finite graph is one with instances `Π v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `rel_hom`, `rel_embedding`, and `rel_iso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

## Todo

* Upgrade `simple_graph.boolean_algebra` to a `complete_boolean_algebra`.

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/


open Finset

universe u v w

/-- A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric adj := by obviously
  loopless : Irreflexive adj := by obviously

noncomputable instance {V : Type u} [Fintype V] : Fintype (SimpleGraph V) := by
  classical
  exact Fintype.ofInjective SimpleGraph.Adj SimpleGraph.ext

/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
  symm := fun a b ⟨hn, hr⟩ => ⟨hn.symm, hr.symm⟩
  loopless := fun a ⟨hn, _⟩ => hn rfl

@[simp]
theorem SimpleGraph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
    (SimpleGraph.fromRel r).Adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
  Iff.rfl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `mathlib`, this is usually referred to as `⊤`. -/
def completeGraph (V : Type u) : SimpleGraph V where Adj := Ne

/-- The graph with no edges on a given vertex type `V`. `mathlib` prefers the notation `⊥`. -/
def emptyGraph (V : Type u) : SimpleGraph V where Adj i j := False

/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def completeBipartiteGraph (V W : Type _) : SimpleGraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm := by
    intro v w
    cases v <;> cases w <;> simp
  loopless := by
    intro v
    cases v <;> simp

namespace SimpleGraph

variable {𝕜 : Type _} {V : Type u} {W : Type v} {X : Type w} (G : SimpleGraph V) (G' : SimpleGraph W) {a b c u v w : V}
  {e : Sym2 V}

@[simp]
protected theorem irrefl {v : V} : ¬G.Adj v v :=
  G.loopless v

theorem adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u :=
  ⟨fun x => G.symm x, fun x => G.symm x⟩

@[symm]
theorem adj_symm (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem Adj.symm {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h

theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  rintro rfl
  exact G.irrefl h

protected theorem Adj.ne {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : a ≠ b :=
  G.ne_of_adj h

protected theorem Adj.ne' {G : SimpleGraph V} {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.Ne.symm

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' => hn (h' ▸ h)

section Order

/-- The relation that one `simple_graph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def IsSubgraph (x y : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (SimpleGraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem is_subgraph_eq_le : (IsSubgraph : SimpleGraph V → SimpleGraph V → Prop) = (· ≤ ·) :=
  rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : HasSup (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj ⊔ y.Adj, symm := fun v w h => by rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem sup_adj (x y : SimpleGraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w :=
  Iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : HasInf (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj ⊓ y.Adj, symm := fun v w h => by rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem inf_adj (x y : SimpleGraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w :=
  Iff.rfl

/-- We define `Gᶜ` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves).
-/
instance : HasCompl (SimpleGraph V) :=
  ⟨fun G =>
    { Adj := fun v w => v ≠ w ∧ ¬G.Adj v w, symm := fun v w ⟨hne, _⟩ => ⟨hne.symm, by rwa [adj_comm]⟩,
      loopless := fun v ⟨hne, _⟩ => (hne rfl).elim }⟩

@[simp]
theorem compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w :=
  Iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : Sdiff (SimpleGraph V) :=
  ⟨fun x y =>
    { Adj := x.Adj \ y.Adj, symm := fun v w h => by change x.adj w v ∧ ¬y.adj w v <;> rwa [x.adj_comm, y.adj_comm] }⟩

@[simp]
theorem sdiff_adj (x y : SimpleGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

instance : BooleanAlgebra (SimpleGraph V) :=
  { PartialOrder.lift Adj ext with le := (· ≤ ·), sup := (· ⊔ ·), inf := (· ⊓ ·), compl := HasCompl.compl,
    sdiff := (· \ ·), top := completeGraph V, bot := emptyGraph V, le_top := fun x v w h => x.ne_of_adj h,
    bot_le := fun x v w h => h.elim, sup_le := fun x y z hxy hyz v w h => h.casesOn (fun h => hxy h) fun h => hyz h,
    sdiff_eq := fun x y => by
      ext v w
      refine' ⟨fun h => ⟨h.1, ⟨_, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rintro rfl
      exact x.irrefl h.1,
    le_sup_left := fun x y v w h => Or.inl h, le_sup_right := fun x y v w h => Or.inr h,
    le_inf := fun x y z hxy hyz v w h => ⟨hxy h, hyz h⟩,
    le_sup_inf := fun a b c v w h =>
      Or.dcases_on h.2 Or.inl <| (Or.dcases_on h.1 fun h _ => Or.inl h) fun hb hc => Or.inr ⟨hb, hc⟩,
    inf_compl_le_bot := fun a v w h => False.elim <| h.2.2 h.1,
    top_le_sup_compl := fun a v w ne => by
      by_cases a.adj v w
      exact Or.inl h
      exact Or.inr ⟨Ne, h⟩,
    inf_le_left := fun x y v w h => h.1, inf_le_right := fun x y v w h => h.2 }

@[simp]
theorem top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v ≠ w :=
  Iff.rfl

@[simp]
theorem bot_adj (v w : V) : (⊥ : SimpleGraph V).Adj v w ↔ False :=
  Iff.rfl

@[simp]
theorem complete_graph_eq_top (V : Type u) : completeGraph V = ⊤ :=
  rfl

@[simp]
theorem empty_graph_eq_bot (V : Type u) : emptyGraph V = ⊥ :=
  rfl

@[simps]
instance (V : Type u) : Inhabited (SimpleGraph V) :=
  ⟨⊥⟩

section Decidable

variable (V) (H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SimpleGraph V).Adj := fun v w => Decidable.false

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj := fun v w => Or.decidable

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj := fun v w => And.decidable

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj := fun v w => And.decidable

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SimpleGraph V).Adj := fun v w => Not.decidable

instance Compl.adjDecidable : DecidableRel Gᶜ.Adj := fun v w => And.decidable

end Decidable

end Order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def Support : Set V :=
  Rel.Dom G.Adj

theorem mem_support {v : V} : v ∈ G.Support ↔ ∃ w, G.Adj v w :=
  Iff.rfl

theorem support_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.Support ⊆ G'.Support :=
  Rel.dom_mono h

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def NeighborSet (v : V) : Set V :=
  SetOf (G.Adj v)

instance NeighborSet.memDecidable (v : V) [DecidableRel G.Adj] : DecidablePred (· ∈ G.NeighborSet v) := by
  unfold neighbor_set
  infer_instance

/-- The edges of G consist of the unordered pairs of vertices related by
`G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj v w`.)
-/
def EdgeSet : Set (Sym2 V) :=
  Sym2.FromRel G.symm

@[simp]
theorem mem_edge_set : ⟦(v, w)⟧ ∈ G.EdgeSet ↔ G.Adj v w :=
  Iff.rfl

theorem edge_set_mono {G G' : SimpleGraph V} (h : G ≤ G') : G.EdgeSet ⊆ G'.EdgeSet := fun e =>
  Sym2.ind (fun v w => @h v w) e

/-- Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.EdgeSet, v ∈ e ∧ w ∈ e := by
  refine' ⟨fun _ => ⟨G.ne_of_adj ‹_›, ⟦(v, w)⟧, _⟩, _⟩
  · simpa
    
  · rintro ⟨hne, e, he, hv⟩
    rw [Sym2.mem_and_mem_iff hne] at hv
    subst e
    rwa [mem_edge_set] at he
    

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.EdgeSet, ↑e = ⟦(a, b)⟧ := by
  simp only [mem_edge_set, exists_prop, SetCoe.exists, exists_eq_right, Subtype.coe_mk]

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.EdgeSet) {v : V} (h : v ∈ e) : h.other ≠ v := by
  erw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.EdgeSet) :=
  Sym2.FromRel.decidablePred _

instance edgesFintype [DecidableEq V] [Fintype V] [DecidableRel G.Adj] : Fintype G.EdgeSet :=
  Subtype.fintype _

/-! ## Darts -/


/-- A `dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
@[ext]
structure Dart extends V × V where
  is_adj : G.Adj fst snd
  deriving DecidableEq

section Darts

variable {G}

/-- The first vertex for the dart. -/
abbrev Dart.fst (d : G.Dart) : V :=
  d.fst

/-- The second vertex for the dart. -/
abbrev Dart.snd (d : G.Dart) : V :=
  d.snd

theorem Dart.to_prod_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  dart.ext

instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σv, G.NeighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩, invFun := fun d => ⟨d.fst, d.snd, d.is_adj⟩,
      left_inv := fun s => by ext <;> simp, right_inv := fun d => by ext <;> simp }

/-- The edge associated to the dart. -/
def Dart.edge (d : G.Dart) : Sym2 V :=
  ⟦d.toProd⟧

@[simp]
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = ⟦p⟧ :=
  rfl

@[simp]
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.EdgeSet :=
  d.is_adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, G.symm d.is_adj⟩

@[simp]
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.mk_prod_swap_eq

@[simp]
theorem Dart.edge_comp_symm : dart.edge ∘ dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm

@[simp]
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _

@[simp]
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  dart.symm_symm

theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ dart.to_prod) d.is_adj.Ne

theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp [Sym2.mk_eq_mk_iff]

theorem dart_edge_eq_mk_iff : ∀ {d : G.Dart} {p : V × V}, d.edge = ⟦p⟧ ↔ d.toProd = p ∨ d.toProd = p.swap := by
  rintro ⟨p, h⟩
  apply Sym2.mk_eq_mk_iff

theorem dart_edge_eq_mk_iff' :
    ∀ {d : G.Dart} {u v : V}, d.edge = ⟦(u, v)⟧ ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk_iff]
  simp

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. --/
@[simps]
def dartOfNeighborSet (v : V) (w : G.NeighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩

theorem dart_of_neighbor_set_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) := fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert congr_arg Prod.snd h'

instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end Darts

/-! ### Incidence set -/


/-- Set of edges incident to a given vertex, aka incidence set. -/
def IncidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.EdgeSet | v ∈ e }

theorem incidence_set_subset (v : V) : G.IncidenceSet v ⊆ G.EdgeSet := fun _ h => h.1

theorem mk_mem_incidence_set_iff : ⟦(b, c)⟧ ∈ G.IncidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff

theorem mk_mem_incidence_set_left_iff : ⟦(a, b)⟧ ∈ G.IncidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_left _ _

theorem mk_mem_incidence_set_right_iff : ⟦(a, b)⟧ ∈ G.IncidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_right _ _

theorem edge_mem_incidence_set_iff {e : G.EdgeSet} : ↑e ∈ G.IncidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2

theorem incidence_set_inter_incidence_set_subset (h : a ≠ b) : G.IncidenceSet a ∩ G.IncidenceSet b ⊆ {⟦(a, b)⟧} :=
  fun e he => (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

theorem incidence_set_inter_incidence_set_of_adj (h : G.Adj a b) : G.IncidenceSet a ∩ G.IncidenceSet b = {⟦(a, b)⟧} :=
  by
  refine' (G.incidence_set_inter_incidence_set_subset <| h.ne).antisymm _
  rintro _ (rfl : _ = ⟦(a, b)⟧)
  exact ⟨G.mk_mem_incidence_set_left_iff.2 h, G.mk_mem_incidence_set_right_iff.2 h⟩

theorem adj_of_mem_incidence_set (h : a ≠ b) (ha : e ∈ G.IncidenceSet a) (hb : e ∈ G.IncidenceSet b) : G.Adj a b := by
  rwa [← mk_mem_incidence_set_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidence_set_inter_incidence_set_subset h ⟨ha, hb⟩]

theorem incidence_set_inter_incidence_set_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.IncidenceSet a ∩ G.IncidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidence_set hn ha hb)

instance decidableMemIncidenceSet [DecidableEq V] [DecidableRel G.Adj] (v : V) : DecidablePred (· ∈ G.IncidenceSet v) :=
  fun e => And.decidable

/-- The `edge_set` of the graph as a `finset`.
-/
@[reducible]
def edgeFinset [Fintype G.EdgeSet] : Finset (Sym2 V) :=
  Set.toFinset G.EdgeSet

@[simp]
theorem mem_edge_finset [Fintype G.EdgeSet] (e : Sym2 V) : e ∈ G.edgeFinset ↔ e ∈ G.EdgeSet :=
  Set.mem_to_finset

@[simp, norm_cast]
theorem coe_edge_finset [Fintype G.EdgeSet] : (G.edgeFinset : Set (Sym2 V)) = G.EdgeSet :=
  Set.coe_to_finset _

theorem edge_finset_mono {G G' : SimpleGraph V} [Fintype G.EdgeSet] [Fintype G'.EdgeSet] :
    G ≤ G' → G.edgeFinset ⊆ G'.edgeFinset := by
  simp_rw [← coe_subset, coe_edge_finset]
  exact edge_set_mono

theorem edge_finset_card [Fintype G.EdgeSet] : G.edgeFinset.card = Fintype.card G.EdgeSet :=
  Set.to_finset_card _

@[simp]
theorem edge_set_univ_card [Fintype G.EdgeSet] : (univ : Finset G.EdgeSet).card = G.edgeFinset.card :=
  Fintype.card_of_subtype G.edgeFinset (mem_edge_finset _)

@[simp]
theorem mem_neighbor_set (v w : V) : w ∈ G.NeighborSet v ↔ G.Adj v w :=
  Iff.rfl

@[simp]
theorem mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ G.IncidenceSet v ↔ G.Adj v w := by simp [incidence_set]

theorem mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.IncidenceSet v ↔ w ∈ G.NeighborSet v := by
  simp only [mem_incidence_set, mem_neighbor_set]

theorem adj_incidence_set_inter {v : V} {e : Sym2 V} (he : e ∈ G.EdgeSet) (h : v ∈ e) :
    G.IncidenceSet v ∩ G.IncidenceSet h.other = {e} := by
  ext e'
  simp only [incidence_set, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine' ⟨fun h' => _, _⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
    
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩
    

theorem complNeighborSetDisjoint (G : SimpleGraph V) (v : V) : Disjoint (G.NeighborSet v) (Gᶜ.NeighborSet v) := by
  rw [Set.disjoint_iff]
  rintro w ⟨h, h'⟩
  rw [mem_neighbor_set, compl_adj] at h'
  exact h'.2 h

theorem neighbor_set_union_compl_neighbor_set_eq (G : SimpleGraph V) (v : V) :
    G.NeighborSet v ∪ Gᶜ.NeighborSet v = {v}ᶜ := by
  ext w
  have h := @ne_of_adj _ G
  simp_rw [Set.mem_union, mem_neighbor_set, compl_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  tauto

-- TODO find out why TC inference has `h` failing a defeq check for `to_finset`
theorem card_neighbor_set_union_compl_neighbor_set [Fintype V] (G : SimpleGraph V) (v : V)
    [h : Fintype (G.NeighborSet v ∪ Gᶜ.NeighborSet v : Set V)] :
    (@Set.toFinset _ (G.NeighborSet v ∪ Gᶜ.NeighborSet v) h).card = Fintype.card V - 1 := by
  classical
  simp_rw [neighbor_set_union_compl_neighbor_set_eq, Set.to_finset_compl, Finset.card_compl, Set.to_finset_card,
    Set.card_singleton]

theorem neighbor_set_compl (G : SimpleGraph V) (v : V) : Gᶜ.NeighborSet v = G.NeighborSet vᶜ \ {v} := by
  ext w
  simp [and_comm', eq_comm]

/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def CommonNeighbors (v w : V) : Set V :=
  G.NeighborSet v ∩ G.NeighborSet w

theorem common_neighbors_eq (v w : V) : G.CommonNeighbors v w = G.NeighborSet v ∩ G.NeighborSet w :=
  rfl

theorem mem_common_neighbors {u v w : V} : u ∈ G.CommonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl

theorem common_neighbors_symm (v w : V) : G.CommonNeighbors v w = G.CommonNeighbors w v :=
  Set.inter_comm _ _

theorem not_mem_common_neighbors_left (v w : V) : v ∉ G.CommonNeighbors v w := fun h => ne_of_adj G h.1 rfl

theorem not_mem_common_neighbors_right (v w : V) : w ∉ G.CommonNeighbors v w := fun h => ne_of_adj G h.2 rfl

theorem common_neighbors_subset_neighbor_set_left (v w : V) : G.CommonNeighbors v w ⊆ G.NeighborSet v :=
  Set.inter_subset_left _ _

theorem common_neighbors_subset_neighbor_set_right (v w : V) : G.CommonNeighbors v w ⊆ G.NeighborSet w :=
  Set.inter_subset_right _ _

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) : DecidablePred (· ∈ G.CommonNeighbors v w) :=
  fun a => And.decidable

theorem common_neighbors_top_eq {v w : V} : (⊤ : SimpleGraph V).CommonNeighbors v w = Set.Univ \ {v, w} := by
  ext u
  simp [common_neighbors, eq_comm, not_or_distrib.symm]

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.IncidenceSet v) : V :=
  h.2.other'

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.IncidenceSet v) :
    e ∈ G.IncidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [other_vertex_of_incident, Sym2.other_mem']

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.IncidenceSet v) :
    G.otherVertexOfIncident h ∈ G.NeighborSet v := by
  cases' h with he hv
  rwa [← Sym2.other_spec' hv, mem_edge_set] at he

@[simp]
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.NeighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.IncidenceSet v ≃ G.NeighborSet v where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [other_vertex_of_incident]
  right_inv := fun ⟨w, hw⟩ => by simp

end Incidence

/-! ## Edge deletion -/


/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `simple_graph.subgraph.delete_edges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V where
  Adj := G.Adj \ Sym2.ToRel s
  symm a b := by simp [adj_comm, Sym2.eq_swap]

@[simp]
theorem delete_edges_adj (s : Set (Sym2 V)) (v w : V) : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬⟦(v, w)⟧ ∈ s :=
  Iff.rfl

theorem sdiff_eq_delete_edges (G G' : SimpleGraph V) : G \ G' = G.deleteEdges G'.EdgeSet := by
  ext
  simp

theorem compl_eq_delete_edges : Gᶜ = (⊤ : SimpleGraph V).deleteEdges G.EdgeSet := by
  ext
  simp

@[simp]
theorem delete_edges_delete_edges (s s' : Set (Sym2 V)) : (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') :=
  by
  ext
  simp [and_assoc', not_or_distrib]

@[simp]
theorem delete_edges_empty_eq : G.deleteEdges ∅ = G := by
  ext
  simp

@[simp]
theorem delete_edges_univ_eq : G.deleteEdges Set.Univ = ⊥ := by
  ext
  simp

theorem delete_edges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro
  simp (config := { contextual := true })

theorem delete_edges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') : G.deleteEdges s' ≤ G.deleteEdges s := fun v w => by
  simp (config := { contextual := true }) only [delete_edges_adj, and_imp, true_and_iff]
  exact fun ha hn hs => hn (h hs)

theorem delete_edges_eq_inter_edge_set (s : Set (Sym2 V)) : G.deleteEdges s = G.deleteEdges (s ∩ G.EdgeSet) := by
  ext
  simp (config := { contextual := true }) [imp_false]

theorem delete_edges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) : G.deleteEdges (G.EdgeSet \ H.EdgeSet) = H := by
  ext v w
  constructor <;> simp (config := { contextual := true }) [@h v w]

theorem edge_set_delete_edges (s : Set (Sym2 V)) : (G.deleteEdges s).EdgeSet = G.EdgeSet \ s := by
  ext e
  refine' Sym2.ind _ e
  simp

theorem edge_finset_delete_edges [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (s : Finset (Sym2 V))
    [DecidableRel (G.deleteEdges s).Adj] : (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edge_set_delete_edges]

section DeleteFar

variable (G) [OrderedRing 𝕜] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ s.card

open Classical

variable {G}

theorem delete_far_iff : G.DeleteFar p r ↔ ∀ ⦃H⦄, H ≤ G → p H → r ≤ G.edgeFinset.card - H.edgeFinset.card := by
  refine' ⟨fun h H hHG hH => _, fun h s hs hG => _⟩
  · have := h (sdiff_subset G.edge_finset H.edge_finset)
    simp only [delete_edges_sdiff_eq_of_le _ hHG, edge_finset_mono hHG, card_sdiff, card_le_of_subset, coe_sdiff,
      coe_edge_finset, Nat.cast_sub] at this
    exact this hH
    
  · simpa [card_sdiff hs, edge_finset_delete_edges, -Set.to_finset_card, Nat.cast_sub, card_le_of_subset hs] using
      h (G.delete_edges_le s) hG
    

alias delete_far_iff ↔ delete_far.le_card_sub_card _

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun s hs hG => hr.trans <| h hs hG

end DeleteFar

/-! ## Map and comap -/


/-- Given an injective function, there is an covariant induced map on graphs by pushing forward
the adjacency relation.

This is injective (see `simple_graph.map_injective`). -/
protected def map (f : V ↪ W) (G : SimpleGraph V) : SimpleGraph W where Adj := Relation.Map G.Adj f f

@[simp]
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

theorem map_monotone (f : V ↪ W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h _ _ ⟨u, v, ha, rfl, rfl⟩
  exact ⟨_, _, h ha, rfl, rfl⟩

/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `simple_graph.induce` for a wrapper.

This is surjective when `f` is injective (see `simple_graph.comap_surjective`).-/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where Adj u v := G.Adj (f u) (f v)

theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) := by
  intro G G' h _ _ ha
  exact h ha

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp

theorem left_inverse_comap_map (f : V ↪ W) : Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f

theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (left_inverse_comap_map f).Injective

theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (left_inverse_comap_map f).Surjective

theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) : G.map f ≤ G' ↔ G ≤ G'.comap f :=
  ⟨fun h u v ha => h ⟨_, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨u, v, ha, rfl, rfl⟩
    exact h ha⟩

theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f ≤ G := by
  rw [map_le_iff_le_comap]
  exact le_refl _

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `simple_graph V` and `simple_graph s`.

There is also a notion of induced subgraphs (see `simple_graph.subgraph.induce`). -/
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `simple_graph.comap`. -/
@[reducible]
def induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)

/-- Given a graph on a set of vertices, we can make it be a `simple_graph V` by
adding in the remaining vertices without adding in any additional edges.
This is a wrapper around `simple_graph.map`. -/
@[reducible]
def spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)

theorem induce_spanning_coe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

theorem spanning_coe_induce_le (s : Set V) : (G.induce s).spanningCoe ≤ G :=
  map_comap_le _ _

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/


variable (v) [Fintype (G.NeighborSet v)]

/-- `G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighborFinset : Finset V :=
  (G.NeighborSet v).toFinset

theorem neighbor_finset_def : G.neighborFinset v = (G.NeighborSet v).toFinset :=
  rfl

@[simp]
theorem mem_neighbor_finset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_to_finset

/-- `G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ :=
  (G.neighborFinset v).card

@[simp]
theorem card_neighbor_set_eq_degree : Fintype.card (G.NeighborSet v) = G.degree v :=
  (Set.to_finset_card _).symm

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighbor_finset]

theorem degree_compl [Fintype (Gᶜ.NeighborSet v)] [Fintype V] : Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
  rw [← card_neighbor_set_union_compl_neighbor_set G v, Set.to_finset_union]
  simp [card_disjoint_union (set.to_finset_disjoint_iff.mpr (compl_neighbor_set_disjoint G v))]

instance incidenceSetFintype [DecidableEq V] : Fintype (G.IncidenceSet v) :=
  Fintype.ofEquiv (G.NeighborSet v) (G.incidenceSetEquivNeighborSet v).symm

/-- This is the `finset` version of `incidence_set`.
-/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.IncidenceSet v).toFinset

@[simp]
theorem card_incidence_set_eq_degree [DecidableEq V] : Fintype.card (G.IncidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidence_set_equiv_neighbor_set v)]
  simp

@[simp]
theorem card_incidence_finset_eq_degree [DecidableEq V] : (G.incidenceFinset v).card = G.degree v := by
  rw [← G.card_incidence_set_eq_degree]
  apply Set.to_finset_card

@[simp]
theorem mem_incidence_finset [DecidableEq V] (e : Sym2 V) : e ∈ G.incidenceFinset v ↔ e ∈ G.IncidenceSet v :=
  Set.mem_to_finset

theorem incidence_finset_eq_filter [DecidableEq V] [Fintype G.EdgeSet] :
    G.incidenceFinset v = G.edgeFinset.filter (Membership.Mem v) := by
  ext e
  refine' Sym2.ind (fun x y => _) e
  simp [mk_mem_incidence_set_iff]

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def LocallyFinite :=
  ∀ v : V, Fintype (G.NeighborSet v)

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.NeighborSet v) :=
  @Subtype.fintype _ _
    (by
      simp_rw [mem_neighbor_set]
      infer_instance)
    _

theorem neighbor_finset_eq_filter {v : V} [DecidableRel G.Adj] : G.neighborFinset v = Finset.univ.filter (G.Adj v) := by
  ext
  simp

theorem neighbor_finset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = G.neighborFinset vᶜ \ {v} := by
  simp only [neighbor_finset, neighbor_set_compl, Set.to_finset_diff, Set.to_finset_compl, Set.to_finset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) : (⊤ : SimpleGraph V).degree v = Fintype.card V - 1 := by
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v), card_univ]

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  erw [degree, neighbor_finset_eq_filter, filter_false]
  exact Finset.card_empty

theorem IsRegularOfDegree.top [DecidableEq V] : (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  simp

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untop' 0 (univ.Image fun v => G.degree v).min

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] : ∃ v, G.minDegree = G.degree v := by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  refine' ⟨v, by simp [min_degree, ht]⟩

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem min_degree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [min_degree, ht]

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
theorem le_min_degree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ) (h : ∀ v, k ≤ G.degree v) :
    k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  Option.getOrElse (univ.Image fun v => G.degree v).max 0

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] : ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, rfl⟩
  refine' ⟨v, _⟩
  rw [max_degree, ht]
  rfl

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_max_degree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [max_degree, ht]

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
theorem max_degree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) : G.maxDegree ≤ k := by
  by_cases hV:(univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
    
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [max_degree, hV, image_empty]
    exact zero_le k
    

theorem degree_lt_card_verts [DecidableRel G.Adj] (v : V) : G.degree v < Fintype.card V := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  exact ⟨v, by simp, Finset.subset_univ _⟩

/-- The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
theorem max_degree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] : G.maxDegree < Fintype.card V := by
  cases' G.exists_maximal_degree_vertex with v hv
  rw [hv]
  apply G.degree_lt_card_verts v

theorem card_common_neighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.CommonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighbor_set_eq_degree]
  exact Set.card_le_of_subset (Set.inter_subset_left _ _)

theorem card_common_neighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.CommonNeighbors v w) ≤ G.degree w := by
  simp_rw [common_neighbors_symm _ v w, card_common_neighbors_le_degree_left]

theorem card_common_neighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.CommonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/-- If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
theorem Adj.card_common_neighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V} (h : G.Adj v w) :
    Fintype.card (G.CommonNeighbors v w) < G.degree v := by
  classical
  erw [← Set.to_finset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Set.mem_to_finset]
    apply not_mem_common_neighbors_right
    
  · rw [Finset.insert_subset]
    constructor
    · simpa
      
    · rw [neighbor_finset, Set.to_finset_subset]
      exact G.common_neighbors_subset_neighbor_set_left _ _
      
    

theorem card_common_neighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).CommonNeighbors v w) = Fintype.card V - 2 := by
  simp only [common_neighbors_top_eq, ← Set.to_finset_card, Set.to_finset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
    
  · simp only [Set.to_finset_subset, Set.subset_univ]
    

end Finite

section Maps

/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbrev Hom :=
  RelHom G.Adj G'.Adj

/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.adj f(v) f(w) ↔ G.adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj

/-- A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj

-- mathport name: «expr →g »
infixl:50 " →g " => Hom

-- mathport name: «expr ↪g »
infixl:50 " ↪g " => Embedding

-- mathport name: «expr ≃g »
infixl:50 " ≃g " => Iso

namespace Hom

variable {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbrev id : G →g G :=
  RelHom.id _

theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h

theorem map_mem_edge_set {e : Sym2 V} (h : e ∈ G.EdgeSet) : e.map f ∈ G'.EdgeSet :=
  Quotient.ind (fun e h => Sym2.from_rel_prop.mpr (f.map_rel' h)) e h

theorem apply_mem_neighbor_set {v w : V} (h : w ∈ G.NeighborSet v) : f w ∈ G'.NeighborSet (f v) :=
  map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps]
def mapEdgeSet (e : G.EdgeSet) : G'.EdgeSet :=
  ⟨Sym2.map f e, f.map_mem_edge_set e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
def mapNeighborSet (v : V) (w : G.NeighborSet v) : G'.NeighborSet (f v) :=
  ⟨f w, f.apply_mem_neighbor_set w.property⟩

/-- The map between darts induced by a homomorphism. -/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]
theorem map_dart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
@[simps]
def mapSpanningSubgraphs {G G' : SimpleGraph V} (h : G ≤ G') : G →g G' where
  toFun x := x
  map_rel' := h

theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [hom.map_edge_set]
  repeat' rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

/-- Every graph homomomorphism from a complete graph is injective. -/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) →g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `simple_graph.embedding.comap`). -/
@[simps]
protected def comap (f : V → W) (G : SimpleGraph W) : G.comap f →g G where
  toFun := f
  map_rel' := by simp

variable {G'' : SimpleGraph X}

/-- Composition of graph homomorphisms. -/
abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
  f'.comp f

@[simp]
theorem coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Hom

namespace Embedding

variable {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toRelHom

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edge_set_iff {e : Sym2 V} : e.map f ∈ G'.EdgeSet ↔ e ∈ G.EdgeSet :=
  Quotient.ind (fun ⟨v, w⟩ => f.map_adj_iff) e

theorem apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.NeighborSet (f v) ↔ w ∈ G.NeighborSet v :=
  map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
def mapEdgeSet : G.EdgeSet ↪ G'.EdgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f f.inj'

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.NeighborSet v ↪ G'.NeighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h⊢
    exact f.inj' h

/-- Given an injective function, there is an embedding from the comapped graph into the original
graph. -/
@[simps]
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G :=
  { f with map_rel_iff' := by simp }

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps]
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f :=
  { f with map_rel_iff' := by simp }

/-- Induced graphs embed in the original graph.

Note that if `G.induce s = ⊤` (i.e., if `s` is a clique) then this gives the embedding of a
complete graph. -/
@[reducible]
protected def induce (s : Set V) : G.induce s ↪g G :=
  SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G

/-- Graphs on a set of vertices embed in their `spanning_coe`. -/
@[reducible]
protected def spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  SimpleGraph.Embedding.map (Function.Embedding.subtype _) G

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ↪ β) : (⊤ : SimpleGraph α) ↪g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }

variable {G'' : SimpleGraph X}

/-- Composition of graph embeddings. -/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Embedding

namespace Iso

variable {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbrev refl : G ≃g G :=
  RelIso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbrev toHom : G →g G' :=
  f.toEmbedding.toHom

/-- The inverse of a graph isomorphism. --/
abbrev symm : G' ≃g G :=
  f.symm

theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

theorem map_mem_edge_set_iff {e : Sym2 V} : e.map f ∈ G'.EdgeSet ↔ e ∈ G.EdgeSet :=
  Quotient.ind (fun ⟨v, w⟩ => f.map_adj_iff) e

theorem apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.NeighborSet (f v) ↔ w ∈ G.NeighborSet v :=
  map_adj_iff f

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
def mapEdgeSet : G.EdgeSet ≃ G'.EdgeSet where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [hom.map_edge_set, Sym2.map_map, RelIso.coe_coe_fn, RelEmbedding.coe_coe_fn, Subtype.mk_eq_mk,
      Subtype.coe_mk, coe_coe]
    apply congr_fun
    convert Sym2.map_id
    exact funext fun _ => RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [hom.map_edge_set, Sym2.map_map, RelIso.coe_coe_fn, RelEmbedding.coe_coe_fn, Subtype.mk_eq_mk,
      Subtype.coe_mk, coe_coe]
    apply congr_fun
    convert Sym2.map_id
    exact funext fun _ => RelIso.apply_symm_apply _ _

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
def mapNeighborSet (v : V) : G.NeighborSet v ≃ G'.NeighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      convert f.symm.apply_mem_neighbor_set_iff.mpr w.2
      simp only [RelIso.symm_apply_apply]⟩
  left_inv w := by simp
  right_inv w := by simp

theorem card_eq_of_iso [Fintype V] [Fintype W] (f : G ≃g G') : Fintype.card V = Fintype.card W := by
  convert (Fintype.of_equiv_card f.to_equiv).symm

/-- Given a bijection, there is an embedding from the comapped graph into the original
graph. -/
@[simps]
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f.toEmbedding ≃g G :=
  { f with map_rel_iff' := by simp }

/-- Given an injective function, there is an embedding from a graph into the mapped graph. -/
@[simps]
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f.toEmbedding :=
  { f with map_rel_iff' := by simp }

/-- Equivalences of types induce isomorphisms of complete graphs on those types. -/
protected def completeGraph {α β : Type _} (f : α ≃ β) : (⊤ : SimpleGraph α) ≃g (⊤ : SimpleGraph β) :=
  { f with map_rel_iff' := by simp }

theorem to_embedding_complete_graph {α β : Type _} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

variable {G'' : SimpleGraph X}

/-- Composition of graph isomorphisms. -/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

end Iso

end Maps

end SimpleGraph

