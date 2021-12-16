import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `subgraph G` is the type of subgraphs of a `G : simple_graph`

* `subgraph.neighbor_set`, `subgraph.incidence_set`, and `subgraph.degree` are like their
  `simple_graph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `subgraph.coe` is the coercion from a `G' : subgraph G` to a `simple_graph G'.verts`.
  (This cannot be a `has_coe` instance since the destination type depends on `G'`.)

* `subgraph.is_spanning` for whether a subgraph is a spanning subgraph and
  `subgraph.is_induced` for whether a subgraph is an induced subgraph.

* Instances for `lattice (subgraph G)` and `bounded_order (subgraph G)`.

* `simple_graph.to_subgraph`: If a `simple_graph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `simple_graph.subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`subgraph.map_top`) and between subgraphs
  (`subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `set_like` does not apply to
  this kind of subobject.

## Todo

* Images of graph homomorphisms as subgraphs.

-/


universe u

namespace SimpleGraph

/-- A subgraph of a `simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `set (V × V)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure subgraph {V : Type u} (G : SimpleGraph V) where 
  Verts : Set V 
  Adj : V → V → Prop 
  adj_sub : ∀ {v w : V}, adj v w → G.adj v w 
  edge_vert : ∀ {v w : V}, adj v w → v ∈ verts 
  symm : Symmetric adj :=  by 
  runTac 
    obviously

namespace Subgraph

variable {V : Type u} {G : SimpleGraph V}

theorem adj_comm (G' : subgraph G) (v w : V) : G'.adj v w ↔ G'.adj w v :=
  ⟨fun x => G'.symm x, fun x => G'.symm x⟩

@[symm]
theorem adj_symm (G' : subgraph G) {u v : V} (h : G'.adj u v) : G'.adj v u :=
  G'.symm h

/-- Coercion from `G' : subgraph G` to a `simple_graph ↥G'.verts`. -/
@[simps]
def coeₓ (G' : subgraph G) : SimpleGraph G'.verts :=
  { Adj := fun v w => G'.adj v w, symm := fun v w h => G'.symm h, loopless := fun v h => loopless G v (G'.adj_sub h) }

@[simp]
theorem coe_adj_sub (G' : subgraph G) (u v : G'.verts) (h : G'.coe.adj u v) : G.adj u v :=
  G'.adj_sub h

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. --/
def is_spanning (G' : subgraph G) : Prop :=
  ∀ v : V, v ∈ G'.verts

theorem is_spanning_iff {G' : subgraph G} : G'.is_spanning ↔ G'.verts = Set.Univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `subgraph G` to `simple_graph V`.  If `G'` is a spanning
subgraph, then `G'.spanning_coe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
def spanning_coe (G' : subgraph G) : SimpleGraph V :=
  { Adj := G'.adj, symm := G'.symm, loopless := fun v hv => G.loopless v (G'.adj_sub hv) }

@[simp]
theorem spanning_coe_adj_sub (H : subgraph G) (u v : H.verts) (h : H.spanning_coe.adj u v) : G.adj u v :=
  H.adj_sub h

/-- `spanning_coe` is equivalent to `coe` for a subgraph that `is_spanning`.  -/
@[simps]
def spanning_coe_equiv_coe_of_spanning (G' : subgraph G) (h : G'.is_spanning) : G'.spanning_coe ≃g G'.coe :=
  { toFun := fun v => ⟨v, h v⟩, invFun := fun v => v, left_inv := fun v => rfl, right_inv := fun ⟨v, hv⟩ => rfl,
    map_rel_iff' := fun v w => Iff.rfl }

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def is_induced (G' : subgraph G) : Prop :=
  ∀ {v w : V}, v ∈ G'.verts → w ∈ G'.verts → G.adj v w → G'.adj v w

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (H : subgraph G) : Set V :=
  Rel.Dom H.adj

theorem mem_support (H : subgraph G) {v : V} : v ∈ H.support ↔ ∃ w, H.adj v w :=
  Iff.rfl

theorem support_subset_verts (H : subgraph G) : H.support ⊆ H.verts :=
  fun v ⟨w, h⟩ => H.edge_vert h

/-- `G'.neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def neighbor_set (G' : subgraph G) (v : V) : Set V :=
  SetOf (G'.adj v)

theorem neighbor_set_subset (G' : subgraph G) (v : V) : G'.neighbor_set v ⊆ G.neighbor_set v :=
  fun w h => G'.adj_sub h

@[simp]
theorem mem_neighbor_set (G' : subgraph G) (v w : V) : w ∈ G'.neighbor_set v ↔ G'.adj v w :=
  Iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coe_neighbor_set_equiv {G' : subgraph G} (v : G'.verts) : G'.coe.neighbor_set v ≃ G'.neighbor_set v :=
  { toFun :=
      fun w =>
        ⟨w,
          by 
            obtain ⟨w', hw'⟩ := w 
            simpa using hw'⟩,
    invFun :=
      fun w =>
        ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩,
          by 
            simpa using w.2⟩,
    left_inv :=
      fun w =>
        by 
          simp ,
    right_inv :=
      fun w =>
        by 
          simp  }

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edge_set (G' : subgraph G) : Set (Sym2 V) :=
  Sym2.FromRel G'.symm

theorem edge_set_subset (G' : subgraph G) : G'.edge_set ⊆ G.edge_set :=
  fun e => Quotientₓ.ind (fun e h => G'.adj_sub h) e

@[simp]
theorem mem_edge_set {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ G'.edge_set ↔ G'.adj v w :=
  Iff.rfl

theorem mem_verts_if_mem_edge {G' : subgraph G} {e : Sym2 V} {v : V} (he : e ∈ G'.edge_set) (hv : v ∈ e) :
  v ∈ G'.verts :=
  by 
    refine' Quotientₓ.ind (fun e he hv => _) e he hv 
    cases' e with v w 
    simp only [mem_edge_set] at he 
    cases' sym2.mem_iff.mp hv with h h <;> subst h
    ·
      exact G'.edge_vert he
    ·
      exact G'.edge_vert (G'.symm he)

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
/-- The `incidence_set` is the set of edges incident to a given vertex. -/
  def incidence_set ( G' : subgraph G ) ( v : V ) : Set Sym2 V := { e ∈ G'.edge_set | v ∈ e }

theorem incidence_set_subset_incidence_set (G' : subgraph G) (v : V) : G'.incidence_set v ⊆ G.incidence_set v :=
  fun e h => ⟨G'.edge_set_subset h.1, h.2⟩

theorem incidence_set_subset (G' : subgraph G) (v : V) : G'.incidence_set v ⊆ G'.edge_set :=
  fun _ h => h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : subgraph G) (v : V) (h : v ∈ G'.verts) : G'.verts :=
  ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : subgraph G) (V'' : Set V) (hV : V'' = G'.verts) (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  subgraph G :=
  { Verts := V'', Adj := adj', adj_sub := hadj.symm ▸ G'.adj_sub, edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert,
    symm := hadj.symm ▸ G'.symm }

theorem copy_eq (G' : subgraph G) (V'' : Set V) (hV : V'' = G'.verts) (adj' : V → V → Prop) (hadj : adj' = G'.adj) :
  G'.copy V'' hV adj' hadj = G' :=
  subgraph.ext _ _ hV hadj

/-- The union of two subgraphs. -/
def union (x y : subgraph G) : subgraph G :=
  { Verts := x.verts ∪ y.verts, Adj := x.adj⊔y.adj,
    adj_sub := fun v w h => Or.cases_on h (fun h => x.adj_sub h) fun h => y.adj_sub h,
    edge_vert := fun v w h => Or.cases_on h (fun h => Or.inl (x.edge_vert h)) fun h => Or.inr (y.edge_vert h),
    symm :=
      fun v w h =>
        by 
          rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm] }

/-- The intersection of two subgraphs. -/
def inter (x y : subgraph G) : subgraph G :=
  { Verts := x.verts ∩ y.verts, Adj := x.adj⊓y.adj, adj_sub := fun v w h => x.adj_sub h.1,
    edge_vert := fun v w h => ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
    symm :=
      fun v w h =>
        by 
          rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm] }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : subgraph G :=
  { Verts := Set.Univ, Adj := G.adj, adj_sub := fun v w h => h, edge_vert := fun v w h => Set.mem_univ v,
    symm := G.symm }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : subgraph G :=
  { Verts := ∅, Adj := fun v w => False, adj_sub := fun v w h => False.ndrec _ h,
    edge_vert := fun v w h => False.ndrec _ h, symm := fun u v h => h }

instance subgraph_inhabited : Inhabited (subgraph G) :=
  ⟨bot⟩

/-- The relation that one subgraph is a subgraph of another. -/
def is_subgraph (x y : subgraph G) : Prop :=
  x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.adj v w → y.adj v w

instance : Lattice (subgraph G) :=
  { le := is_subgraph, sup := union, inf := inter, le_refl := fun x => ⟨rfl.Subset, fun _ _ h => h⟩,
    le_trans := fun x y z hxy hyz => ⟨hxy.1.trans hyz.1, fun _ _ h => hyz.2 (hxy.2 h)⟩,
    le_antisymm :=
      by 
        intro x y hxy hyx 
        ext1 v 
        exact Set.Subset.antisymm hxy.1 hyx.1 
        ext v w 
        exact Iff.intro (fun h => hxy.2 h) fun h => hyx.2 h,
    sup_le :=
      fun x y z hxy hyz => ⟨Set.union_subset hxy.1 hyz.1, fun v w h => h.cases_on (fun h => hxy.2 h) fun h => hyz.2 h⟩,
    le_sup_left := fun x y => ⟨Set.subset_union_left x.verts y.verts, fun v w h => Or.inl h⟩,
    le_sup_right := fun x y => ⟨Set.subset_union_right x.verts y.verts, fun v w h => Or.inr h⟩,
    le_inf := fun x y z hxy hyz => ⟨Set.subset_inter hxy.1 hyz.1, fun v w h => ⟨hxy.2 h, hyz.2 h⟩⟩,
    inf_le_left := fun x y => ⟨Set.inter_subset_left x.verts y.verts, fun v w h => h.1⟩,
    inf_le_right := fun x y => ⟨Set.inter_subset_right x.verts y.verts, fun v w h => h.2⟩ }

instance : BoundedOrder (subgraph G) :=
  { top := top, bot := bot, le_top := fun x => ⟨Set.subset_univ _, fun v w h => x.adj_sub h⟩,
    bot_le := fun x => ⟨Set.empty_subset _, fun v w h => False.ndrec _ h⟩ }

@[simp]
theorem top_adj_iff {v w : V} : (⊤ : subgraph G).Adj v w ↔ G.adj v w :=
  Iff.rfl

@[simp]
theorem top_verts : (⊤ : subgraph G).Verts = Set.Univ :=
  rfl

@[simp]
theorem bot_adj_iff : (⊥ : subgraph G).Verts = ∅ :=
  rfl

@[simp]
theorem bot_verts {v w : V} : ¬(⊥ : subgraph G).Adj v w :=
  not_false

@[simp]
theorem spanning_coe_top : (⊤ : subgraph G).spanningCoe = G :=
  by 
    ext 
    rfl

/-- Turn a subgraph of a `simple_graph` into a member of its subgraph type. -/
@[simps]
def _root_.simple_graph.to_subgraph (H : SimpleGraph V) (h : H ≤ G) : G.subgraph :=
  { Verts := Set.Univ, Adj := H.adj, adj_sub := h, edge_vert := fun v w h => Set.mem_univ v, symm := H.symm }

theorem support_mono {H H' : subgraph G} (h : H ≤ H') : H.support ⊆ H'.support :=
  Rel.dom_mono h.2

theorem _root_.simple_graph.to_subgraph.is_spanning (H : SimpleGraph V) (h : H ≤ G) : (H.to_subgraph h).IsSpanning :=
  Set.mem_univ

theorem spanning_coe.is_subgraph_of_is_subgraph {H H' : subgraph G} (h : H ≤ H') : H.spanning_coe ≤ H'.spanning_coe :=
  h.2

/-- The top of the `subgraph G` lattice is equivalent to the graph itself. -/
def top_equiv : (⊤ : subgraph G).coe ≃g G :=
  { toFun := fun v => ↑v, invFun := fun v => ⟨v, trivialₓ⟩, left_inv := fun ⟨v, _⟩ => rfl, right_inv := fun v => rfl,
    map_rel_iff' := fun a b => Iff.rfl }

/-- The bottom of the `subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def bot_equiv : (⊥ : subgraph G).coe ≃g (⊥ : SimpleGraph Empty) :=
  { toFun := fun v => v.property.elim, invFun := fun v => v.elim, left_inv := fun ⟨_, h⟩ => h.elim,
    right_inv := fun v => v.elim, map_rel_iff' := fun a b => Iff.rfl }

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
def map {x y : subgraph G} (h : x ≤ y) : x.coe →g y.coe :=
  { toFun := fun v => ⟨↑v, And.left h v.property⟩, map_rel' := fun v w hvw => h.2 hvw }

theorem map.injective {x y : subgraph G} (h : x ≤ y) : Function.Injective (map h) :=
  fun v w h =>
    by 
      simp only [map, RelHom.coe_fn_mk, Subtype.mk_eq_mk] at h 
      exact Subtype.ext h

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
def map_top (x : subgraph G) : x.coe →g G :=
  { toFun := fun v => v, map_rel' := fun v w hvw => x.adj_sub hvw }

theorem map_top.injective {x : subgraph G} : Function.Injective x.map_top :=
  fun v w h => Subtype.ext h

@[simp]
theorem map_top_to_fun {x : subgraph G} (v : x.verts) : x.map_top v = v :=
  rfl

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
def map_spanning_top (x : subgraph G) : x.spanning_coe →g G :=
  { toFun := id, map_rel' := fun v w hvw => x.adj_sub hvw }

theorem map_spanning_top.injective {x : subgraph G} : Function.Injective x.map_spanning_top :=
  fun v w h => h

theorem neighbor_set_subset_of_subgraph {x y : subgraph G} (h : x ≤ y) (v : V) : x.neighbor_set v ⊆ y.neighbor_set v :=
  fun w h' => h.2 h'

instance neighbor_set.decidable_pred (G' : subgraph G) [h : DecidableRel G'.adj] (v : V) :
  DecidablePred (· ∈ G'.neighbor_set v) :=
  h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finite_at {G' : subgraph G} (v : G'.verts) [DecidableRel G'.adj] [Fintype (G.neighbor_set v)] :
  Fintype (G'.neighbor_set v) :=
  Set.fintypeSubset (G.neighbor_set v) (G'.neighbor_set_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finite_at_of_subgraph {G' G'' : subgraph G} [DecidableRel G'.adj] (h : G' ≤ G'') (v : G'.verts)
  [hf : Fintype (G''.neighbor_set v)] : Fintype (G'.neighbor_set v) :=
  Set.fintypeSubset (G''.neighbor_set v) (neighbor_set_subset_of_subgraph h v)

instance coe_finite_at {G' : subgraph G} (v : G'.verts) [Fintype (G'.neighbor_set v)] :
  Fintype (G'.coe.neighbor_set v) :=
  Fintype.ofEquiv _ (coe_neighbor_set_equiv v).symm

/-- The degree of a vertex in a subgraph.  Is zero for vertices outside the subgraph. -/
def degree (G' : subgraph G) (v : V) [Fintype (G'.neighbor_set v)] : ℕ :=
  Fintype.card (G'.neighbor_set v)

theorem degree_le (G' : subgraph G) (v : V) [Fintype (G'.neighbor_set v)] [Fintype (G.neighbor_set v)] :
  G'.degree v ≤ G.degree v :=
  by 
    rw [←card_neighbor_set_eq_degree]
    exact Set.card_le_of_subset (G'.neighbor_set_subset v)

theorem degree_le' (G' G'' : subgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.neighbor_set v)]
  [Fintype (G''.neighbor_set v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_of_subset (neighbor_set_subset_of_subgraph h v)

@[simp]
theorem coe_degree (G' : subgraph G) (v : G'.verts) [Fintype (G'.coe.neighbor_set v)] [Fintype (G'.neighbor_set v)] :
  G'.coe.degree v = G'.degree v :=
  by 
    rw [←card_neighbor_set_eq_degree]
    exact Fintype.card_congr (coe_neighbor_set_equiv v)

end Subgraph

end SimpleGraph

