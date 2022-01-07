import Mathbin.Combinatorics.SimpleGraph.Subgraph
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Setoid.Partition
import Mathbin.Order.Antichain

/-!
# Graph Coloring

This module defines colorings of simple graphs (also known as proper
colorings in the literature). A graph coloring is the attribution of
"colors" to all of its vertices such that adjacent vertices have
different colors. A coloring can be represented as a homomorphism into
a complete graph, whose vertices represent the colors.

## Main definitions

* `G.coloring α` is the type of `α`-colorings of a simple graph `G`,
  with `α` being the set of available colors. The type is defined to
  be homomorphisms from `G` into the complete graph on `α`, and
  colorings have a coercion to `V → α`.

* `G.colorable n` is the proposition that `G` is `n`-colorable, which
  is whether there exists a coloring with at most *n* colors.

* `G.chromatic_number` is the minimal `n` such that `G` is
  `n`-colorable, or `0` if it cannot be colored with finitely many
  colors.

* `C.color_class c` is the set of vertices colored by `c : α` in the
  coloring `C : G.coloring α`.

* `C.color_classes` is the set containing all color classes.

## Todo:

  * Gather material from:
    * https://github.com/leanprover-community/mathlib/blob/simple_graph_matching/src/combinatorics/simple_graph/coloring.lean
    * https://github.com/kmill/lean-graphcoloring/blob/master/src/graph.lean

  * Lowerbound for cliques

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.coloring α`)
-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev coloring (α : Type v) :=
  G →g (⊤ : SimpleGraph α)

variable {G} {α : Type v} (C : G.coloring α)

theorem coloring.valid {v w : V} (h : G.adj v w) : C v ≠ C w :=
  C.map_rel h

/-- Construct a term of `simple_graph.coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `simple_graph.hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[matchPattern]
def coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.adj v w → color v ≠ color w) : G.coloring α :=
  ⟨color, @valid⟩

/-- The color class of a given color.
-/
def coloring.color_class (c : α) : Set V :=
  { v : V | C v = c }

/-- The set containing all color classes. -/
def coloring.color_classes : Set (Set V) :=
  (Setoidₓ.ker C).Classes

theorem coloring.mem_color_class (v : V) : v ∈ C.color_class (C v) :=
  rfl

theorem coloring.color_classes_is_partition : Setoidₓ.IsPartition C.color_classes :=
  Setoidₓ.is_partition_classes (Setoidₓ.ker C)

theorem coloring.mem_color_classes {v : V} : C.color_class (C v) ∈ C.color_classes :=
  ⟨v, rfl⟩

theorem coloring.color_classes_finite_of_fintype [Fintype α] : C.color_classes.finite := by
  rw [Set.finite_def]
  apply Setoidₓ.nonempty_fintype_classes_ker

theorem coloring.card_color_classes_le [Fintype α] [Fintype C.color_classes] :
    Fintype.card C.color_classes ≤ Fintype.card α :=
  Setoidₓ.card_classes_ker_le C

theorem coloring.not_adj_of_mem_color_class {c : α} {v w : V} (hv : v ∈ C.color_class c) (hw : w ∈ C.color_class c) :
    ¬G.adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))

theorem coloring.color_classes_independent (c : α) : IsAntichain G.adj (C.color_class c) := fun v hv w hw h =>
  C.not_adj_of_mem_color_class hv hw

noncomputable instance [Fintype V] [Fintype α] : Fintype (coloring G α) := by
  classical
  change Fintype (RelHom G.adj (⊤ : SimpleGraph α).Adj)
  apply Fintype.ofInjective _ RelHom.coe_fn_injective
  infer_instance

variable (G)

/-- Whether a graph can be colored by at most `n` colors. -/
def colorable (n : ℕ) : Prop :=
  Nonempty (G.coloring (Finₓ n))

/-- The coloring of an empty graph. -/
def coloring_of_is_empty [IsEmpty V] : G.coloring α :=
  coloring.mk isEmptyElim fun v => isEmptyElim

theorem colorable_of_is_empty [IsEmpty V] (n : ℕ) : G.colorable n :=
  ⟨G.coloring_of_is_empty⟩

theorem is_empty_of_colorable_zero (h : G.colorable 0) : IsEmpty V := by
  constructor
  intro v
  obtain ⟨i, hi⟩ := h.some v
  exact Nat.not_lt_zeroₓ _ hi

/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def self_coloring : G.coloring V :=
  coloring.mk id fun v w => G.ne_of_adj

/-- The chromatic number of a graph is the minimal number of colors needed to color it.
If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromatic_number : ℕ :=
  Inf { n : ℕ | G.colorable n }

/-- Given an embedding, there is an induced embedding of colorings. -/
def recolor_of_embedding {α β : Type _} (f : α ↪ β) : G.coloring α ↪ G.coloring β where
  toFun := fun C => (embedding.complete_graph.of_embedding f).toHom.comp C
  inj' := by
    intro C C' h
    dsimp only  at h
    ext v
    apply (embedding.complete_graph.of_embedding f).inj'
    change ((embedding.complete_graph.of_embedding f).toHom.comp C) v = _
    rw [h]
    rfl

/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolor_of_equiv {α β : Type _} (f : α ≃ β) : G.coloring α ≃ G.coloring β where
  toFun := G.recolor_of_embedding f.to_embedding
  invFun := G.recolor_of_embedding f.symm.to_embedding
  left_inv := fun C => by
    ext v
    apply Equivₓ.symm_apply_apply
  right_inv := fun C => by
    ext v
    apply Equivₓ.apply_symm_apply

/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolor_of_card_le {α β : Type _} [Fintype α] [Fintype β] (hn : Fintype.card α ≤ Fintype.card β) :
    G.coloring α ↪ G.coloring β :=
  G.recolor_of_embedding $ (Function.Embedding.nonempty_of_card_le hn).some

variable {G}

theorem colorable.of_le {n m : ℕ} (hc : G.colorable n) (h : n ≤ m) : G.colorable m :=
  ⟨G.recolor_of_card_le
      (by
        simp [h])
      hc.some⟩

theorem coloring.to_colorable [Fintype α] (C : G.coloring α) : G.colorable (Fintype.card α) :=
  ⟨G.recolor_of_card_le
      (by
        simp )
      C⟩

theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.colorable (Fintype.card V) :=
  G.self_coloring.to_colorable

/-- Noncomputably get a coloring from colorability. -/
noncomputable def colorable.to_coloring [Fintype α] {n : ℕ} (hc : G.colorable n) (hn : n ≤ Fintype.card α) :
    G.coloring α := by
  rw [← Fintype.card_fin n] at hn
  exact G.recolor_of_card_le hn hc.some

theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) : G.colorable n ↔ ∃ C : G.coloring ℕ, ∀ v, C v < n := by
  constructor
  · rintro hc
    have C : G.coloring (Finₓ n) :=
      hc.to_coloring
        (by
          simp )
    let f := embedding.complete_graph.of_embedding (Finₓ.coeEmbedding n).toEmbedding
    use f.to_hom.comp C
    intro v
    cases' C with color valid
    exact Finₓ.is_lt (color v)
    
  · rintro ⟨C, Cf⟩
    refine' ⟨coloring.mk _ _⟩
    · exact fun v => ⟨C v, Cf v⟩
      
    · rintro v w hvw
      simp only [complete_graph_eq_top, top_adj, Subtype.mk_eq_mk, Ne.def]
      exact C.valid hvw
      
    

theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.colorable n) : { n : ℕ | G.colorable n }.Nonempty :=
  ⟨n, hc⟩

theorem chromatic_number_bdd_below : BddBelow { n : ℕ | G.colorable n } :=
  ⟨0, fun _ _ => zero_le _⟩

theorem chromatic_number_le_of_colorable {n : ℕ} (hc : G.colorable n) : G.chromatic_number ≤ n := by
  rw [chromatic_number]
  apply cInf_le chromatic_number_bdd_below
  fconstructor
  exact Classical.choice hc

theorem chromatic_number_le_card [Fintype α] (C : G.coloring α) : G.chromatic_number ≤ Fintype.card α :=
  cInf_le chromatic_number_bdd_below C.to_colorable

theorem colorable_chromatic_number {m : ℕ} (hc : G.colorable m) : G.colorable G.chromatic_number := by
  dsimp only [chromatic_number]
  rw [Nat.Inf_def]
  apply Nat.find_specₓ
  exact colorable_set_nonempty_of_colorable hc

theorem colorable_chromatic_number_of_fintype (G : SimpleGraph V) [Fintype V] : G.colorable G.chromatic_number :=
  colorable_chromatic_number G.colorable_of_fintype

theorem chromatic_number_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] : G.chromatic_number ≤ 1 := by
  rw [chromatic_number]
  apply cInf_le chromatic_number_bdd_below
  fconstructor
  refine' coloring.mk (fun _ => 0) _
  intro v w
  rw [Subsingleton.elimₓ v w]
  simp

theorem chromatic_number_eq_zero_of_isempty (G : SimpleGraph V) [IsEmpty V] : G.chromatic_number = 0 := by
  rw [← nonpos_iff_eq_zero]
  apply cInf_le chromatic_number_bdd_below
  apply colorable_of_is_empty

theorem is_empty_of_chromatic_number_eq_zero (G : SimpleGraph V) [Fintype V] (h : G.chromatic_number = 0) : IsEmpty V :=
  by
  have h' := G.colorable_chromatic_number_of_fintype
  rw [h] at h'
  exact G.is_empty_of_colorable_zero h'

theorem zero_lt_chromatic_number [Nonempty V] {n : ℕ} (hc : G.colorable n) : 0 < G.chromatic_number := by
  apply le_cInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_leₓ, Nat.lt_one_iff] at h'
  subst h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  exact Nat.not_lt_zeroₓ _ hi

theorem colorable_of_le_colorable {G' : SimpleGraph V} (h : G ≤ G') (n : ℕ) (hc : G'.colorable n) : G.colorable n :=
  ⟨hc.some.comp (hom.map_spanning_subgraphs h)⟩

theorem chromatic_number_le_of_forall_imp {G' : SimpleGraph V} {m : ℕ} (hc : G'.colorable m)
    (h : ∀ n, G'.colorable n → G.colorable n) : G.chromatic_number ≤ G'.chromatic_number := by
  apply cInf_le chromatic_number_bdd_below
  apply h
  apply colorable_chromatic_number hc

theorem chromatic_number_le_of_le_colorable (G' : SimpleGraph V) {m : ℕ} (hc : G'.colorable m) (h : G ≤ G') :
    G.chromatic_number ≤ G'.chromatic_number := by
  apply chromatic_number_le_of_forall_imp hc
  exact colorable_of_le_colorable h

theorem chromatic_number_eq_card_of_forall_surj [Fintype α] (C : G.coloring α)
    (h : ∀ C' : G.coloring α, Function.Surjective C') : G.chromatic_number = Fintype.card α := by
  apply le_antisymmₓ
  · apply chromatic_number_le_card C
    
  · by_contra hc
    rw [not_leₓ] at hc
    obtain ⟨n, cn, hc⟩ := exists_lt_of_cInf_lt (colorable_set_nonempty_of_colorable C.to_colorable) hc
    rw [← Fintype.card_fin n] at hc
    have f := (Function.Embedding.nonempty_of_card_le (le_of_ltₓ hc)).some
    have C' := cn.some
    specialize h (G.recolor_of_embedding f C')
    change Function.Surjective (f ∘ C') at h
    have h1 : Function.Surjective f := Function.Surjective.of_comp h
    have h2 := Fintype.card_le_of_surjective _ h1
    exact Nat.lt_le_antisymmₓ hc h2
    

theorem chromatic_number_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 := by
  let C : (⊥ : SimpleGraph V).Coloring (Finₓ 1) := coloring.mk (fun _ => 0) fun v w h => False.elim h
  apply le_antisymmₓ
  · exact chromatic_number_le_card C
    
  · exact zero_lt_chromatic_number C.to_colorable
    

theorem chromatic_number_complete_graph [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V := by
  apply chromatic_number_eq_card_of_forall_surj (self_coloring _)
  intro C
  rw [← Fintype.injective_iff_surjective]
  intro v w
  contrapose
  intro h
  exact C.valid h

/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def complete_bipartite_graph.bicoloring (V W : Type _) : (completeBipartiteGraph V W).Coloring Bool :=
  coloring.mk (fun v => v.is_right)
    (by
      intro v w
      cases v <;> cases w <;> simp )

theorem complete_bipartite_graph.chromatic_number {V W : Type _} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 := by
  apply chromatic_number_eq_card_of_forall_surj (complete_bipartite_graph.bicoloring V W)
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by
    simp
  have hn := C.valid h
  by_cases' he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
    
  · by_cases' he' : C (Sum.inr w) = b
    · exact ⟨_, he'⟩
      
    · exfalso
      cases b <;> simp only [eq_tt_eq_not_eq_ff, eq_ff_eq_not_eq_tt] at he he' <;> rw [he, he'] at hn <;> contradiction
      
    

end SimpleGraph

