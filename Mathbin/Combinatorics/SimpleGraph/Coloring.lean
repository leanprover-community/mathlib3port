/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.coloring
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Clique
import Mathbin.Data.Nat.Lattice
import Mathbin.Data.Setoid.Partition
import Mathbin.Order.Antichain

/-!
# Graph Coloring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

  * Trees

  * Planar graphs

  * Chromatic polynomials

  * develop API for partial colorings, likely as colorings of subgraphs (`H.coe.coloring α`)
-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

#print SimpleGraph.Coloring /-
/-- An `α`-coloring of a simple graph `G` is a homomorphism of `G` into the complete graph on `α`.
This is also known as a proper coloring.
-/
abbrev Coloring (α : Type v) :=
  G →g (⊤ : SimpleGraph α)
#align simple_graph.coloring SimpleGraph.Coloring
-/

variable {G} {α : Type v} (C : G.Coloring α)

#print SimpleGraph.Coloring.valid /-
theorem Coloring.valid {v w : V} (h : G.Adj v w) : C v ≠ C w :=
  C.map_rel h
#align simple_graph.coloring.valid SimpleGraph.Coloring.valid
-/

#print SimpleGraph.Coloring.mk /-
/-- Construct a term of `simple_graph.coloring` using a function that
assigns vertices to colors and a proof that it is as proper coloring.

(Note: this is a definitionally the constructor for `simple_graph.hom`,
but with a syntactically better proper coloring hypothesis.)
-/
@[match_pattern]
def Coloring.mk (color : V → α) (valid : ∀ {v w : V}, G.Adj v w → color v ≠ color w) :
    G.Coloring α :=
  ⟨color, @valid⟩
#align simple_graph.coloring.mk SimpleGraph.Coloring.mk
-/

#print SimpleGraph.Coloring.colorClass /-
/-- The color class of a given color.
-/
def Coloring.colorClass (c : α) : Set V :=
  { v : V | C v = c }
#align simple_graph.coloring.color_class SimpleGraph.Coloring.colorClass
-/

#print SimpleGraph.Coloring.colorClasses /-
/-- The set containing all color classes. -/
def Coloring.colorClasses : Set (Set V) :=
  (Setoid.ker C).classes
#align simple_graph.coloring.color_classes SimpleGraph.Coloring.colorClasses
-/

#print SimpleGraph.Coloring.mem_colorClass /-
theorem Coloring.mem_colorClass (v : V) : v ∈ C.colorClass (C v) :=
  rfl
#align simple_graph.coloring.mem_color_class SimpleGraph.Coloring.mem_colorClass
-/

#print SimpleGraph.Coloring.colorClasses_isPartition /-
theorem Coloring.colorClasses_isPartition : Setoid.IsPartition C.colorClasses :=
  Setoid.isPartition_classes (Setoid.ker C)
#align simple_graph.coloring.color_classes_is_partition SimpleGraph.Coloring.colorClasses_isPartition
-/

#print SimpleGraph.Coloring.mem_colorClasses /-
theorem Coloring.mem_colorClasses {v : V} : C.colorClass (C v) ∈ C.colorClasses :=
  ⟨v, rfl⟩
#align simple_graph.coloring.mem_color_classes SimpleGraph.Coloring.mem_colorClasses
-/

#print SimpleGraph.Coloring.colorClasses_finite /-
theorem Coloring.colorClasses_finite [Finite α] : C.colorClasses.Finite :=
  Setoid.finite_classes_ker _
#align simple_graph.coloring.color_classes_finite SimpleGraph.Coloring.colorClasses_finite
-/

#print SimpleGraph.Coloring.card_colorClasses_le /-
theorem Coloring.card_colorClasses_le [Fintype α] [Fintype C.colorClasses] :
    Fintype.card C.colorClasses ≤ Fintype.card α :=
  Setoid.card_classes_ker_le C
#align simple_graph.coloring.card_color_classes_le SimpleGraph.Coloring.card_colorClasses_le
-/

#print SimpleGraph.Coloring.not_adj_of_mem_colorClass /-
theorem Coloring.not_adj_of_mem_colorClass {c : α} {v w : V} (hv : v ∈ C.colorClass c)
    (hw : w ∈ C.colorClass c) : ¬G.Adj v w := fun h => C.valid h (Eq.trans hv (Eq.symm hw))
#align simple_graph.coloring.not_adj_of_mem_color_class SimpleGraph.Coloring.not_adj_of_mem_colorClass
-/

#print SimpleGraph.Coloring.color_classes_independent /-
theorem Coloring.color_classes_independent (c : α) : IsAntichain G.Adj (C.colorClass c) :=
  fun v hv w hw h => C.not_adj_of_mem_colorClass hv hw
#align simple_graph.coloring.color_classes_independent SimpleGraph.Coloring.color_classes_independent
-/

-- TODO make this computable
noncomputable instance [Fintype V] [Fintype α] : Fintype (Coloring G α) := by
  classical
    change Fintype (RelHom G.adj (⊤ : SimpleGraph α).Adj)
    apply Fintype.ofInjective _ RelHom.coe_fn_injective
    infer_instance

variable (G)

#print SimpleGraph.Colorable /-
/-- Whether a graph can be colored by at most `n` colors. -/
def Colorable (n : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin n))
#align simple_graph.colorable SimpleGraph.Colorable
-/

#print SimpleGraph.coloringOfIsEmpty /-
/-- The coloring of an empty graph. -/
def coloringOfIsEmpty [IsEmpty V] : G.Coloring α :=
  Coloring.mk isEmptyElim fun v => isEmptyElim
#align simple_graph.coloring_of_is_empty SimpleGraph.coloringOfIsEmpty
-/

#print SimpleGraph.colorable_of_isEmpty /-
theorem colorable_of_isEmpty [IsEmpty V] (n : ℕ) : G.Colorable n :=
  ⟨G.coloringOfIsEmpty⟩
#align simple_graph.colorable_of_is_empty SimpleGraph.colorable_of_isEmpty
-/

#print SimpleGraph.isEmpty_of_colorable_zero /-
theorem isEmpty_of_colorable_zero (h : G.Colorable 0) : IsEmpty V :=
  by
  constructor
  intro v
  obtain ⟨i, hi⟩ := h.some v
  exact Nat.not_lt_zero _ hi
#align simple_graph.is_empty_of_colorable_zero SimpleGraph.isEmpty_of_colorable_zero
-/

#print SimpleGraph.selfColoring /-
/-- The "tautological" coloring of a graph, using the vertices of the graph as colors. -/
def selfColoring : G.Coloring V :=
  Coloring.mk id fun v w => G.ne_of_adj
#align simple_graph.self_coloring SimpleGraph.selfColoring
-/

#print SimpleGraph.chromaticNumber /-
/-- The chromatic number of a graph is the minimal number of colors needed to color it.
If `G` isn't colorable with finitely many colors, this will be 0. -/
noncomputable def chromaticNumber : ℕ :=
  sInf { n : ℕ | G.Colorable n }
#align simple_graph.chromatic_number SimpleGraph.chromaticNumber
-/

#print SimpleGraph.recolorOfEmbedding /-
/-- Given an embedding, there is an induced embedding of colorings. -/
def recolorOfEmbedding {α β : Type _} (f : α ↪ β) : G.Coloring α ↪ G.Coloring β
    where
  toFun C := (Embedding.completeGraph f).toHom.comp C
  inj' :=
    by
    -- this was strangely painful; seems like missing lemmas about embeddings
    intro C C' h
    dsimp only at h
    ext v
    apply (embedding.complete_graph f).inj'
    change ((embedding.complete_graph f).toHom.comp C) v = _
    rw [h]
    rfl
#align simple_graph.recolor_of_embedding SimpleGraph.recolorOfEmbedding
-/

#print SimpleGraph.recolorOfEquiv /-
/-- Given an equivalence, there is an induced equivalence between colorings. -/
def recolorOfEquiv {α β : Type _} (f : α ≃ β) : G.Coloring α ≃ G.Coloring β
    where
  toFun := G.recolorOfEmbedding f.toEmbedding
  invFun := G.recolorOfEmbedding f.symm.toEmbedding
  left_inv C := by
    ext v
    apply Equiv.symm_apply_apply
  right_inv C := by
    ext v
    apply Equiv.apply_symm_apply
#align simple_graph.recolor_of_equiv SimpleGraph.recolorOfEquiv
-/

#print SimpleGraph.recolorOfCardLE /-
/-- There is a noncomputable embedding of `α`-colorings to `β`-colorings if
`β` has at least as large a cardinality as `α`. -/
noncomputable def recolorOfCardLE {α β : Type _} [Fintype α] [Fintype β]
    (hn : Fintype.card α ≤ Fintype.card β) : G.Coloring α ↪ G.Coloring β :=
  G.recolorOfEmbedding <| (Function.Embedding.nonempty_of_card_le hn).some
#align simple_graph.recolor_of_card_le SimpleGraph.recolorOfCardLE
-/

variable {G}

#print SimpleGraph.Colorable.mono /-
theorem Colorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.Colorable n) : G.Colorable m :=
  ⟨G.recolorOfCardLE (by simp [h]) hc.some⟩
#align simple_graph.colorable.mono SimpleGraph.Colorable.mono
-/

#print SimpleGraph.Coloring.to_colorable /-
theorem Coloring.to_colorable [Fintype α] (C : G.Coloring α) : G.Colorable (Fintype.card α) :=
  ⟨G.recolorOfCardLE (by simp) C⟩
#align simple_graph.coloring.to_colorable SimpleGraph.Coloring.to_colorable
-/

#print SimpleGraph.colorable_of_fintype /-
theorem colorable_of_fintype (G : SimpleGraph V) [Fintype V] : G.Colorable (Fintype.card V) :=
  G.selfColoring.to_colorable
#align simple_graph.colorable_of_fintype SimpleGraph.colorable_of_fintype
-/

#print SimpleGraph.Colorable.toColoring /-
/-- Noncomputably get a coloring from colorability. -/
noncomputable def Colorable.toColoring [Fintype α] {n : ℕ} (hc : G.Colorable n)
    (hn : n ≤ Fintype.card α) : G.Coloring α :=
  by
  rw [← Fintype.card_fin n] at hn
  exact G.recolor_of_card_le hn hc.some
#align simple_graph.colorable.to_coloring SimpleGraph.Colorable.toColoring
-/

/- warning: simple_graph.colorable.of_embedding -> SimpleGraph.Colorable.of_embedding is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {V' : Type.{u2}} {G' : SimpleGraph.{u2} V'}, (SimpleGraph.Embedding.{u1, u2} V V' G G') -> (forall {n : Nat}, (SimpleGraph.Colorable.{u2} V' G' n) -> (SimpleGraph.Colorable.{u1} V G n))
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {V' : Type.{u1}} {G' : SimpleGraph.{u1} V'}, (SimpleGraph.Embedding.{u2, u1} V V' G G') -> (forall {n : Nat}, (SimpleGraph.Colorable.{u1} V' G' n) -> (SimpleGraph.Colorable.{u2} V G n))
Case conversion may be inaccurate. Consider using '#align simple_graph.colorable.of_embedding SimpleGraph.Colorable.of_embeddingₓ'. -/
theorem Colorable.of_embedding {V' : Type _} {G' : SimpleGraph V'} (f : G ↪g G') {n : ℕ}
    (h : G'.Colorable n) : G.Colorable n :=
  ⟨(h.toColoring (by simp)).comp f⟩
#align simple_graph.colorable.of_embedding SimpleGraph.Colorable.of_embedding

#print SimpleGraph.colorable_iff_exists_bdd_nat_coloring /-
theorem colorable_iff_exists_bdd_nat_coloring (n : ℕ) :
    G.Colorable n ↔ ∃ C : G.Coloring ℕ, ∀ v, C v < n :=
  by
  constructor
  · rintro hc
    have C : G.coloring (Fin n) := hc.to_coloring (by simp)
    let f := embedding.complete_graph Fin.valEmbedding
    use f.to_hom.comp C
    intro v
    cases' C with color valid
    exact Fin.is_lt (color v)
  · rintro ⟨C, Cf⟩
    refine' ⟨coloring.mk _ _⟩
    · exact fun v => ⟨C v, Cf v⟩
    · rintro v w hvw
      simp only [Fin.mk_eq_mk, Ne.def]
      exact C.valid hvw
#align simple_graph.colorable_iff_exists_bdd_nat_coloring SimpleGraph.colorable_iff_exists_bdd_nat_coloring
-/

#print SimpleGraph.colorable_set_nonempty_of_colorable /-
theorem colorable_set_nonempty_of_colorable {n : ℕ} (hc : G.Colorable n) :
    { n : ℕ | G.Colorable n }.Nonempty :=
  ⟨n, hc⟩
#align simple_graph.colorable_set_nonempty_of_colorable SimpleGraph.colorable_set_nonempty_of_colorable
-/

#print SimpleGraph.chromaticNumber_bddBelow /-
theorem chromaticNumber_bddBelow : BddBelow { n : ℕ | G.Colorable n } :=
  ⟨0, fun _ _ => zero_le _⟩
#align simple_graph.chromatic_number_bdd_below SimpleGraph.chromaticNumber_bddBelow
-/

#print SimpleGraph.chromaticNumber_le_of_colorable /-
theorem chromaticNumber_le_of_colorable {n : ℕ} (hc : G.Colorable n) : G.chromaticNumber ≤ n :=
  by
  rw [chromatic_number]
  apply csInf_le chromatic_number_bdd_below
  fconstructor
  exact Classical.choice hc
#align simple_graph.chromatic_number_le_of_colorable SimpleGraph.chromaticNumber_le_of_colorable
-/

#print SimpleGraph.chromaticNumber_le_card /-
theorem chromaticNumber_le_card [Fintype α] (C : G.Coloring α) :
    G.chromaticNumber ≤ Fintype.card α :=
  csInf_le chromaticNumber_bddBelow C.to_colorable
#align simple_graph.chromatic_number_le_card SimpleGraph.chromaticNumber_le_card
-/

#print SimpleGraph.colorable_chromaticNumber /-
theorem colorable_chromaticNumber {m : ℕ} (hc : G.Colorable m) : G.Colorable G.chromaticNumber :=
  by
  dsimp only [chromatic_number]
  rw [Nat.sInf_def]
  apply Nat.find_spec
  exact colorable_set_nonempty_of_colorable hc
#align simple_graph.colorable_chromatic_number SimpleGraph.colorable_chromaticNumber
-/

#print SimpleGraph.colorable_chromaticNumber_of_fintype /-
theorem colorable_chromaticNumber_of_fintype (G : SimpleGraph V) [Finite V] :
    G.Colorable G.chromaticNumber := by
  cases nonempty_fintype V
  exact colorable_chromatic_number G.colorable_of_fintype
#align simple_graph.colorable_chromatic_number_of_fintype SimpleGraph.colorable_chromaticNumber_of_fintype
-/

#print SimpleGraph.chromaticNumber_le_one_of_subsingleton /-
theorem chromaticNumber_le_one_of_subsingleton (G : SimpleGraph V) [Subsingleton V] :
    G.chromaticNumber ≤ 1 := by
  rw [chromatic_number]
  apply csInf_le chromatic_number_bdd_below
  fconstructor
  refine' coloring.mk (fun _ => 0) _
  intro v w
  rw [Subsingleton.elim v w]
  simp
#align simple_graph.chromatic_number_le_one_of_subsingleton SimpleGraph.chromaticNumber_le_one_of_subsingleton
-/

#print SimpleGraph.chromaticNumber_eq_zero_of_isempty /-
theorem chromaticNumber_eq_zero_of_isempty (G : SimpleGraph V) [IsEmpty V] :
    G.chromaticNumber = 0 := by
  rw [← nonpos_iff_eq_zero]
  apply csInf_le chromatic_number_bdd_below
  apply colorable_of_is_empty
#align simple_graph.chromatic_number_eq_zero_of_isempty SimpleGraph.chromaticNumber_eq_zero_of_isempty
-/

#print SimpleGraph.isEmpty_of_chromaticNumber_eq_zero /-
theorem isEmpty_of_chromaticNumber_eq_zero (G : SimpleGraph V) [Finite V]
    (h : G.chromaticNumber = 0) : IsEmpty V :=
  by
  have h' := G.colorable_chromatic_number_of_fintype
  rw [h] at h'
  exact G.is_empty_of_colorable_zero h'
#align simple_graph.is_empty_of_chromatic_number_eq_zero SimpleGraph.isEmpty_of_chromaticNumber_eq_zero
-/

#print SimpleGraph.chromaticNumber_pos /-
theorem chromaticNumber_pos [Nonempty V] {n : ℕ} (hc : G.Colorable n) : 0 < G.chromaticNumber :=
  by
  apply le_csInf (colorable_set_nonempty_of_colorable hc)
  intro m hm
  by_contra h'
  simp only [not_le, Nat.lt_one_iff] at h'
  subst h'
  obtain ⟨i, hi⟩ := hm.some (Classical.arbitrary V)
  exact Nat.not_lt_zero _ hi
#align simple_graph.chromatic_number_pos SimpleGraph.chromaticNumber_pos
-/

#print SimpleGraph.colorable_of_chromaticNumber_pos /-
theorem colorable_of_chromaticNumber_pos (h : 0 < G.chromaticNumber) :
    G.Colorable G.chromaticNumber :=
  by
  obtain ⟨h, hn⟩ := Nat.nonempty_of_pos_sInf h
  exact colorable_chromatic_number hn
#align simple_graph.colorable_of_chromatic_number_pos SimpleGraph.colorable_of_chromaticNumber_pos
-/

#print SimpleGraph.Colorable.mono_left /-
theorem Colorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ} (hc : G'.Colorable n) :
    G.Colorable n :=
  ⟨hc.some.comp (Hom.mapSpanningSubgraphs h)⟩
#align simple_graph.colorable.mono_left SimpleGraph.Colorable.mono_left
-/

/- warning: simple_graph.colorable.chromatic_number_le_of_forall_imp -> SimpleGraph.Colorable.chromaticNumber_le_of_forall_imp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {V' : Type.{u2}} {G' : SimpleGraph.{u2} V'} {m : Nat}, (SimpleGraph.Colorable.{u2} V' G' m) -> (forall (n : Nat), (SimpleGraph.Colorable.{u2} V' G' n) -> (SimpleGraph.Colorable.{u1} V G n)) -> (LE.le.{0} Nat Nat.hasLe (SimpleGraph.chromaticNumber.{u1} V G) (SimpleGraph.chromaticNumber.{u2} V' G'))
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {V' : Type.{u1}} {G' : SimpleGraph.{u1} V'} {m : Nat}, (SimpleGraph.Colorable.{u1} V' G' m) -> (forall (n : Nat), (SimpleGraph.Colorable.{u1} V' G' n) -> (SimpleGraph.Colorable.{u2} V G n)) -> (LE.le.{0} Nat instLENat (SimpleGraph.chromaticNumber.{u2} V G) (SimpleGraph.chromaticNumber.{u1} V' G'))
Case conversion may be inaccurate. Consider using '#align simple_graph.colorable.chromatic_number_le_of_forall_imp SimpleGraph.Colorable.chromaticNumber_le_of_forall_impₓ'. -/
theorem Colorable.chromaticNumber_le_of_forall_imp {V' : Type _} {G' : SimpleGraph V'} {m : ℕ}
    (hc : G'.Colorable m) (h : ∀ n, G'.Colorable n → G.Colorable n) :
    G.chromaticNumber ≤ G'.chromaticNumber :=
  by
  apply csInf_le chromatic_number_bdd_below
  apply h
  apply colorable_chromatic_number hc
#align simple_graph.colorable.chromatic_number_le_of_forall_imp SimpleGraph.Colorable.chromaticNumber_le_of_forall_imp

#print SimpleGraph.Colorable.chromaticNumber_mono /-
theorem Colorable.chromaticNumber_mono (G' : SimpleGraph V) {m : ℕ} (hc : G'.Colorable m)
    (h : G ≤ G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  hc.chromaticNumber_le_of_forall_imp fun n => Colorable.mono_left h
#align simple_graph.colorable.chromatic_number_mono SimpleGraph.Colorable.chromaticNumber_mono
-/

/- warning: simple_graph.colorable.chromatic_number_mono_of_embedding -> SimpleGraph.Colorable.chromaticNumber_mono_of_embedding is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {G : SimpleGraph.{u1} V} {V' : Type.{u2}} {G' : SimpleGraph.{u2} V'} {n : Nat}, (SimpleGraph.Colorable.{u2} V' G' n) -> (SimpleGraph.Embedding.{u1, u2} V V' G G') -> (LE.le.{0} Nat Nat.hasLe (SimpleGraph.chromaticNumber.{u1} V G) (SimpleGraph.chromaticNumber.{u2} V' G'))
but is expected to have type
  forall {V : Type.{u2}} {G : SimpleGraph.{u2} V} {V' : Type.{u1}} {G' : SimpleGraph.{u1} V'} {n : Nat}, (SimpleGraph.Colorable.{u1} V' G' n) -> (SimpleGraph.Embedding.{u2, u1} V V' G G') -> (LE.le.{0} Nat instLENat (SimpleGraph.chromaticNumber.{u2} V G) (SimpleGraph.chromaticNumber.{u1} V' G'))
Case conversion may be inaccurate. Consider using '#align simple_graph.colorable.chromatic_number_mono_of_embedding SimpleGraph.Colorable.chromaticNumber_mono_of_embeddingₓ'. -/
theorem Colorable.chromaticNumber_mono_of_embedding {V' : Type _} {G' : SimpleGraph V'} {n : ℕ}
    (h : G'.Colorable n) (f : G ↪g G') : G.chromaticNumber ≤ G'.chromaticNumber :=
  h.chromaticNumber_le_of_forall_imp fun _ => Colorable.of_embedding f
#align simple_graph.colorable.chromatic_number_mono_of_embedding SimpleGraph.Colorable.chromaticNumber_mono_of_embedding

#print SimpleGraph.chromaticNumber_eq_card_of_forall_surj /-
theorem chromaticNumber_eq_card_of_forall_surj [Fintype α] (C : G.Coloring α)
    (h : ∀ C' : G.Coloring α, Function.Surjective C') : G.chromaticNumber = Fintype.card α :=
  by
  apply le_antisymm
  · apply chromatic_number_le_card C
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨n, cn, hc⟩ :=
      exists_lt_of_csInf_lt (colorable_set_nonempty_of_colorable C.to_colorable) hc
    rw [← Fintype.card_fin n] at hc
    have f := (Function.Embedding.nonempty_of_card_le (le_of_lt hc)).some
    have C' := cn.some
    specialize h (G.recolor_of_embedding f C')
    change Function.Surjective (f ∘ C') at h
    have h1 : Function.Surjective f := Function.Surjective.of_comp h
    have h2 := Fintype.card_le_of_surjective _ h1
    exact Nat.lt_le_antisymm hc h2
#align simple_graph.chromatic_number_eq_card_of_forall_surj SimpleGraph.chromaticNumber_eq_card_of_forall_surj
-/

/- warning: simple_graph.chromatic_number_bot -> SimpleGraph.chromaticNumber_bot is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Nonempty.{succ u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Bot.bot.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toHasBot.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : Nonempty.{succ u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Bot.bot.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toBot.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align simple_graph.chromatic_number_bot SimpleGraph.chromaticNumber_botₓ'. -/
theorem chromaticNumber_bot [Nonempty V] : (⊥ : SimpleGraph V).chromaticNumber = 1 :=
  by
  let C : (⊥ : SimpleGraph V).Coloring (Fin 1) := coloring.mk (fun _ => 0) fun v w h => False.elim h
  apply le_antisymm
  · exact chromatic_number_le_card C
  · exact chromatic_number_pos C.to_colorable
#align simple_graph.chromatic_number_bot SimpleGraph.chromaticNumber_bot

/- warning: simple_graph.chromatic_number_top -> SimpleGraph.chromaticNumber_top is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Fintype.{u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Top.top.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toHasTop.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (Fintype.card.{u1} V _inst_1)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : Fintype.{u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Top.top.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toTop.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (Fintype.card.{u1} V _inst_1)
Case conversion may be inaccurate. Consider using '#align simple_graph.chromatic_number_top SimpleGraph.chromaticNumber_topₓ'. -/
@[simp]
theorem chromaticNumber_top [Fintype V] : (⊤ : SimpleGraph V).chromaticNumber = Fintype.card V :=
  by
  apply chromatic_number_eq_card_of_forall_surj (self_coloring _)
  intro C
  rw [← Finite.injective_iff_surjective]
  intro v w
  contrapose
  intro h
  exact C.valid h
#align simple_graph.chromatic_number_top SimpleGraph.chromaticNumber_top

/- warning: simple_graph.chromatic_number_top_eq_zero_of_infinite -> SimpleGraph.chromaticNumber_top_eq_zero_of_infinite is a dubious translation:
lean 3 declaration is
  forall (V : Type.{u1}) [_inst_1 : Infinite.{succ u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Top.top.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toHasTop.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall (V : Type.{u1}) [_inst_1 : Infinite.{succ u1} V], Eq.{1} Nat (SimpleGraph.chromaticNumber.{u1} V (Top.top.{u1} (SimpleGraph.{u1} V) (CompleteLattice.toTop.{u1} (SimpleGraph.{u1} V) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} V) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} V) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} V) (SimpleGraph.completeBooleanAlgebra.{u1} V))))))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align simple_graph.chromatic_number_top_eq_zero_of_infinite SimpleGraph.chromaticNumber_top_eq_zero_of_infiniteₓ'. -/
theorem chromaticNumber_top_eq_zero_of_infinite (V : Type _) [Infinite V] :
    (⊤ : SimpleGraph V).chromaticNumber = 0 :=
  by
  let n := (⊤ : SimpleGraph V).chromaticNumber
  by_contra hc
  replace hc := pos_iff_ne_zero.mpr hc
  apply Nat.not_succ_le_self n
  convert_to(⊤ : SimpleGraph { m | m < n + 1 }).chromaticNumber ≤ _
  · simp
  refine' (colorable_of_chromatic_number_pos hc).chromaticNumber_mono_of_embedding _
  apply embedding.complete_graph
  exact (Function.Embedding.subtype _).trans (Infinite.natEmbedding V)
#align simple_graph.chromatic_number_top_eq_zero_of_infinite SimpleGraph.chromaticNumber_top_eq_zero_of_infinite

#print SimpleGraph.CompleteBipartiteGraph.bicoloring /-
/-- The bicoloring of a complete bipartite graph using whether a vertex
is on the left or on the right. -/
def CompleteBipartiteGraph.bicoloring (V W : Type _) : (completeBipartiteGraph V W).Coloring Bool :=
  Coloring.mk (fun v => v.isRight)
    (by
      intro v w
      cases v <;> cases w <;> simp)
#align simple_graph.complete_bipartite_graph.bicoloring SimpleGraph.CompleteBipartiteGraph.bicoloring
-/

/- warning: simple_graph.complete_bipartite_graph.chromatic_number -> SimpleGraph.CompleteBipartiteGraph.chromaticNumber is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {W : Type.{u2}} [_inst_1 : Nonempty.{succ u1} V] [_inst_2 : Nonempty.{succ u2} W], Eq.{1} Nat (SimpleGraph.chromaticNumber.{max u1 u2} (Sum.{u1, u2} V W) (completeBipartiteGraph.{u1, u2} V W)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {V : Type.{u2}} {W : Type.{u1}} [_inst_1 : Nonempty.{succ u2} V] [_inst_2 : Nonempty.{succ u1} W], Eq.{1} Nat (SimpleGraph.chromaticNumber.{max u2 u1} (Sum.{u2, u1} V W) (completeBipartiteGraph.{u2, u1} V W)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
Case conversion may be inaccurate. Consider using '#align simple_graph.complete_bipartite_graph.chromatic_number SimpleGraph.CompleteBipartiteGraph.chromaticNumberₓ'. -/
theorem CompleteBipartiteGraph.chromaticNumber {V W : Type _} [Nonempty V] [Nonempty W] :
    (completeBipartiteGraph V W).chromaticNumber = 2 :=
  by
  apply chromatic_number_eq_card_of_forall_surj (complete_bipartite_graph.bicoloring V W)
  intro C b
  have v := Classical.arbitrary V
  have w := Classical.arbitrary W
  have h : (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := by simp
  have hn := C.valid h
  by_cases he : C (Sum.inl v) = b
  · exact ⟨_, he⟩
  · by_cases he' : C (Sum.inr w) = b
    · exact ⟨_, he'⟩
    · exfalso
      cases b <;> simp only [eq_true_eq_not_eq_false, Bool.eq_false_eq_not_eq_true] at he he' <;>
          rw [he, he'] at hn <;>
        contradiction
#align simple_graph.complete_bipartite_graph.chromatic_number SimpleGraph.CompleteBipartiteGraph.chromaticNumber

/-! ### Cliques -/


#print SimpleGraph.IsClique.card_le_of_coloring /-
theorem IsClique.card_le_of_coloring {s : Finset V} (h : G.IsClique s) [Fintype α]
    (C : G.Coloring α) : s.card ≤ Fintype.card α :=
  by
  rw [is_clique_iff_induce_eq] at h
  have f : G.induce ↑s ↪g G := embedding.induce ↑s
  rw [h] at f
  convert Fintype.card_le_of_injective _ (C.comp f.to_hom).injective_of_top_hom using 1
  simp
#align simple_graph.is_clique.card_le_of_coloring SimpleGraph.IsClique.card_le_of_coloring
-/

#print SimpleGraph.IsClique.card_le_of_colorable /-
theorem IsClique.card_le_of_colorable {s : Finset V} (h : G.IsClique s) {n : ℕ}
    (hc : G.Colorable n) : s.card ≤ n :=
  by
  convert h.card_le_of_coloring hc.some
  simp
#align simple_graph.is_clique.card_le_of_colorable SimpleGraph.IsClique.card_le_of_colorable
-/

#print SimpleGraph.IsClique.card_le_chromaticNumber /-
-- TODO eliminate `finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem IsClique.card_le_chromaticNumber [Finite V] {s : Finset V} (h : G.IsClique s) :
    s.card ≤ G.chromaticNumber := by
  cases nonempty_fintype V
  exact h.card_le_of_colorable G.colorable_chromatic_number_of_fintype
#align simple_graph.is_clique.card_le_chromatic_number SimpleGraph.IsClique.card_le_chromaticNumber
-/

#print SimpleGraph.Colorable.cliqueFree /-
protected theorem Colorable.cliqueFree {n m : ℕ} (hc : G.Colorable n) (hm : n < m) :
    G.CliqueFree m := by
  by_contra h
  simp only [clique_free, is_n_clique_iff, not_forall, Classical.not_not] at h
  obtain ⟨s, h, rfl⟩ := h
  exact Nat.lt_le_antisymm hm (h.card_le_of_colorable hc)
#align simple_graph.colorable.clique_free SimpleGraph.Colorable.cliqueFree
-/

#print SimpleGraph.cliqueFree_of_chromaticNumber_lt /-
-- TODO eliminate `finite V` constraint once chromatic numbers are refactored.
-- This is just to ensure the chromatic number exists.
theorem cliqueFree_of_chromaticNumber_lt [Finite V] {n : ℕ} (hc : G.chromaticNumber < n) :
    G.CliqueFree n :=
  G.colorable_chromaticNumber_of_fintype.CliqueFree hc
#align simple_graph.clique_free_of_chromatic_number_lt SimpleGraph.cliqueFree_of_chromaticNumber_lt
-/

end SimpleGraph

