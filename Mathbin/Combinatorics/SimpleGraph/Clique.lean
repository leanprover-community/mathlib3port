/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.clique
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.Finset.Pairwise

/-!
# Graph cliques

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Do we need `clique_set`, a version of `clique_finset` for infinite graphs?
-/


open Finset Fintype

namespace SimpleGraph

variable {α : Type _} (G H : SimpleGraph α)

/-! ### Cliques -/


section Clique

variable {s t : Set α}

#print SimpleGraph.IsClique /-
/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
#align simple_graph.is_clique SimpleGraph.IsClique
-/

#print SimpleGraph.isClique_iff /-
theorem isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl
#align simple_graph.is_clique_iff SimpleGraph.isClique_iff
-/

/- warning: simple_graph.is_clique_iff_induce_eq -> SimpleGraph.isClique_iff_induce_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) {s : Set.{u1} α}, Iff (SimpleGraph.IsClique.{u1} α G s) (Eq.{succ u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (SimpleGraph.induce.{u1} α s G) (Top.top.{u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (CompleteLattice.toHasTop.{u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (SimpleGraph.completeBooleanAlgebra.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))))))))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) {s : Set.{u1} α}, Iff (SimpleGraph.IsClique.{u1} α G s) (Eq.{succ u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (SimpleGraph.induce.{u1} α s G) (Top.top.{u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (CompleteLattice.toTop.{u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} (Set.Elem.{u1} α s)) (SimpleGraph.completeBooleanAlgebra.{u1} (Set.Elem.{u1} α s))))))))
Case conversion may be inaccurate. Consider using '#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eqₓ'. -/
/-- A clique is a set of vertices whose induced graph is complete. -/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ :=
  by
  rw [is_clique_iff]
  constructor
  · intro h
    ext (⟨v, hv⟩⟨w, hw⟩)
    simp only [comap_adj, Subtype.coe_mk, top_adj, Ne.def, Subtype.mk_eq_mk]
    exact ⟨adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at this => rw [h]
    simpa [hne]
#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eq

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H}

#print SimpleGraph.IsClique.mono /-
theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s :=
  by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono' h
#align simple_graph.is_clique.mono SimpleGraph.IsClique.mono
-/

#print SimpleGraph.IsClique.subset /-
theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t :=
  by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono h
#align simple_graph.is_clique.subset SimpleGraph.IsClique.subset
-/

/- warning: simple_graph.is_clique_bot_iff -> SimpleGraph.isClique_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (SimpleGraph.IsClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toHasBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) s) (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (SimpleGraph.IsClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) s) (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iffₓ'. -/
@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff
#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iff

/- warning: simple_graph.is_clique.subsingleton -> SimpleGraph.IsClique.subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (SimpleGraph.IsClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toHasBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) s) -> (Set.Subsingleton.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (SimpleGraph.IsClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) s) -> (Set.Subsingleton.{u1} α s)
Case conversion may be inaccurate. Consider using '#align simple_graph.is_clique.subsingleton SimpleGraph.IsClique.subsingletonₓ'. -/
alias is_clique_bot_iff ↔ is_clique.subsingleton _
#align simple_graph.is_clique.subsingleton SimpleGraph.IsClique.subsingleton

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

#print SimpleGraph.IsNClique /-
/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  clique : G.IsClique s
  card_eq : s.card = n
#align simple_graph.is_n_clique SimpleGraph.IsNClique
-/

#print SimpleGraph.isNClique_iff /-
theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ s.card = n :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align simple_graph.is_n_clique_iff SimpleGraph.isNClique_iff
-/

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H}

#print SimpleGraph.IsNClique.mono /-
theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s :=
  by
  simp_rw [is_n_clique_iff]
  exact And.imp_left (is_clique.mono h)
#align simple_graph.is_n_clique.mono SimpleGraph.IsNClique.mono
-/

/- warning: simple_graph.is_n_clique_bot_iff -> SimpleGraph.isNClique_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {s : Finset.{u1} α}, Iff (SimpleGraph.IsNClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toHasBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) n s) (And (LE.le.{0} Nat Nat.hasLe n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{1} Nat (Finset.card.{u1} α s) n))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} {s : Finset.{u1} α}, Iff (SimpleGraph.IsNClique.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) n s) (And (LE.le.{0} Nat instLENat n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{1} Nat (Finset.card.{u1} α s) n))
Case conversion may be inaccurate. Consider using '#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iffₓ'. -/
@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n :=
  by
  rw [is_n_clique_iff, is_clique_bot_iff]
  refine' and_congr_left _
  rintro rfl
  exact card_le_one.symm
#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iff

variable [DecidableEq α] {a b c : α}

#print SimpleGraph.is3Clique_triple_iff /-
theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
  by
  simp only [is_n_clique_iff, is_clique_iff, Set.pairwise_insert_of_symmetric G.symm, coe_insert]
  have : ¬1 + 1 = 3 := by norm_num
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> subst_vars <;>
    simp [G.ne_of_adj, and_rotate, *]
#align simple_graph.is_3_clique_triple_iff SimpleGraph.is3Clique_triple_iff
-/

#print SimpleGraph.is3Clique_iff /-
theorem is3Clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 h.card_eq
    refine' ⟨a, b, c, _⟩
    rw [is_3_clique_triple_iff] at h
    tauto
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is_3_clique_triple_iff.2 ⟨hab, hbc, hca⟩
#align simple_graph.is_3_clique_iff SimpleGraph.is3Clique_iff
-/

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

#print SimpleGraph.CliqueFree /-
/-- `G.clique_free n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
#align simple_graph.clique_free SimpleGraph.CliqueFree
-/

variable {G H} {s : Finset α}

#print SimpleGraph.IsNClique.not_cliqueFree /-
theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n := fun h => h _ hG
#align simple_graph.is_n_clique.not_clique_free SimpleGraph.IsNClique.not_cliqueFree
-/

/- warning: simple_graph.not_clique_free_of_top_embedding -> SimpleGraph.not_cliqueFree_of_top_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toHasTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G) -> (Not (SimpleGraph.CliqueFree.{u1} α G n))
but is expected to have type
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G) -> (Not (SimpleGraph.CliqueFree.{u1} α G n))
Case conversion may be inaccurate. Consider using '#align simple_graph.not_clique_free_of_top_embedding SimpleGraph.not_cliqueFree_of_top_embeddingₓ'. -/
theorem not_cliqueFree_of_top_embedding {n : ℕ} (f : (⊤ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.CliqueFree n :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall, Classical.not_not]
  use finset.univ.map f.to_embedding
  simp only [card_map, Finset.card_fin, eq_self_iff_true, and_true_iff]
  ext (⟨v, hv⟩⟨w, hw⟩)
  simp only [coe_map, RelEmbedding.coe_toEmbedding, Set.mem_image, coe_univ, Set.mem_univ,
    true_and_iff] at hv hw
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  simp only [f.map_adj_iff, comap_adj, Function.Embedding.coe_subtype, Subtype.coe_mk, top_adj,
    Ne.def, Subtype.mk_eq_mk]
  exact (Function.Embedding.apply_eq_iff_eq _ _ _).symm.Not
#align simple_graph.not_clique_free_of_top_embedding SimpleGraph.not_cliqueFree_of_top_embedding

/- warning: simple_graph.top_embedding_of_not_clique_free -> SimpleGraph.topEmbeddingOfNotCliqueFree is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, (Not (SimpleGraph.CliqueFree.{u1} α G n)) -> (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toHasTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G)
but is expected to have type
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, (Not (SimpleGraph.CliqueFree.{u1} α G n)) -> (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G)
Case conversion may be inaccurate. Consider using '#align simple_graph.top_embedding_of_not_clique_free SimpleGraph.topEmbeddingOfNotCliqueFreeₓ'. -/
/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    (⊤ : SimpleGraph (Fin n)) ↪g G :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall,
    Classical.not_not] at h
  obtain ⟨ha, hb⟩ := h.some_spec
  have : (⊤ : SimpleGraph (Fin h.some.card)) ≃g (⊤ : SimpleGraph h.some) :=
    by
    apply iso.complete_graph
    simpa using (Fintype.equivFin h.some).symm
  rw [← ha] at this
  convert(embedding.induce ↑h.some).comp this.to_embedding <;> exact hb.symm
#align simple_graph.top_embedding_of_not_clique_free SimpleGraph.topEmbeddingOfNotCliqueFree

/- warning: simple_graph.not_clique_free_iff -> SimpleGraph.not_cliqueFree_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} (n : Nat), Iff (Not (SimpleGraph.CliqueFree.{u1} α G n)) (Nonempty.{succ u1} (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toHasTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G))
but is expected to have type
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} (n : Nat), Iff (Not (SimpleGraph.CliqueFree.{u1} α G n)) (Nonempty.{succ u1} (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G))
Case conversion may be inaccurate. Consider using '#align simple_graph.not_clique_free_iff SimpleGraph.not_cliqueFree_iffₓ'. -/
theorem not_cliqueFree_iff (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g G) :=
  by
  constructor
  · exact fun h => ⟨top_embedding_of_not_clique_free h⟩
  · rintro ⟨f⟩
    exact not_clique_free_of_top_embedding f
#align simple_graph.not_clique_free_iff SimpleGraph.not_cliqueFree_iff

/- warning: simple_graph.clique_free_iff -> SimpleGraph.cliqueFree_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, Iff (SimpleGraph.CliqueFree.{u1} α G n) (IsEmpty.{succ u1} (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toHasTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G))
but is expected to have type
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} {n : Nat}, Iff (SimpleGraph.CliqueFree.{u1} α G n) (IsEmpty.{succ u1} (SimpleGraph.Embedding.{0, u1} (Fin n) α (Top.top.{0} (SimpleGraph.{0} (Fin n)) (CompleteLattice.toTop.{0} (SimpleGraph.{0} (Fin n)) (Order.Coframe.toCompleteLattice.{0} (SimpleGraph.{0} (Fin n)) (CompleteDistribLattice.toCoframe.{0} (SimpleGraph.{0} (Fin n)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{0} (SimpleGraph.{0} (Fin n)) (SimpleGraph.completeBooleanAlgebra.{0} (Fin n))))))) G))
Case conversion may be inaccurate. Consider using '#align simple_graph.clique_free_iff SimpleGraph.cliqueFree_iffₓ'. -/
theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) ↪g G) := by
  rw [← not_iff_not, not_clique_free_iff, not_isEmpty_iff]
#align simple_graph.clique_free_iff SimpleGraph.cliqueFree_iff

/- warning: simple_graph.not_clique_free_card_of_top_embedding -> SimpleGraph.not_cliqueFree_card_of_top_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} [_inst_1 : Fintype.{u1} α], (SimpleGraph.Embedding.{u1, u1} α α (Top.top.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toHasTop.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) G) -> (Not (SimpleGraph.CliqueFree.{u1} α G (Fintype.card.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} {G : SimpleGraph.{u1} α} [_inst_1 : Fintype.{u1} α], (SimpleGraph.Embedding.{u1, u1} α α (Top.top.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toTop.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) G) -> (Not (SimpleGraph.CliqueFree.{u1} α G (Fintype.card.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align simple_graph.not_clique_free_card_of_top_embedding SimpleGraph.not_cliqueFree_card_of_top_embeddingₓ'. -/
theorem not_cliqueFree_card_of_top_embedding [Fintype α] (f : (⊤ : SimpleGraph α) ↪g G) :
    ¬G.CliqueFree (card α) := by
  rw [not_clique_free_iff]
  use (iso.complete_graph (Fintype.equivFin α)).symm.toEmbedding.trans f
#align simple_graph.not_clique_free_card_of_top_embedding SimpleGraph.not_cliqueFree_card_of_top_embedding

/- warning: simple_graph.clique_free_bot -> SimpleGraph.cliqueFree_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat}, (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) -> (SimpleGraph.CliqueFree.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toHasBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) n)
but is expected to have type
  forall {α : Type.{u1}} {n : Nat}, (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) -> (SimpleGraph.CliqueFree.{u1} α (Bot.bot.{u1} (SimpleGraph.{u1} α) (CompleteLattice.toBot.{u1} (SimpleGraph.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (SimpleGraph.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (SimpleGraph.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (SimpleGraph.{u1} α) (SimpleGraph.completeBooleanAlgebra.{u1} α)))))) n)
Case conversion may be inaccurate. Consider using '#align simple_graph.clique_free_bot SimpleGraph.cliqueFree_botₓ'. -/
theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n :=
  by
  rintro t ht
  rw [is_n_clique_bot_iff] at ht
  linarith
#align simple_graph.clique_free_bot SimpleGraph.cliqueFree_bot

#print SimpleGraph.CliqueFree.mono /-
theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n :=
  by
  rintro hG s hs
  obtain ⟨t, hts, ht⟩ := s.exists_smaller_set _ (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.clique.subset hts, ht⟩
#align simple_graph.clique_free.mono SimpleGraph.CliqueFree.mono
-/

#print SimpleGraph.CliqueFree.anti /-
theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun s => mt <| IsNClique.mono h
#align simple_graph.clique_free.anti SimpleGraph.CliqueFree.anti
-/

#print SimpleGraph.cliqueFree_of_card_lt /-
/-- See `simple_graph.clique_free_chromatic_number_succ` for a tighter bound. -/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n :=
  by
  by_contra h
  refine' Nat.lt_le_antisymm hc _
  rw [clique_free_iff, not_isEmpty_iff] at h
  simpa using Fintype.card_le_of_embedding h.some.to_embedding
#align simple_graph.clique_free_of_card_lt SimpleGraph.cliqueFree_of_card_lt
-/

end CliqueFree

/-! ### Set of cliques -/


section CliqueSet

variable (G) {n : ℕ} {a b c : α} {s : Finset α}

#print SimpleGraph.cliqueSet /-
/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }
#align simple_graph.clique_set SimpleGraph.cliqueSet
-/

#print SimpleGraph.mem_cliqueSet_iff /-
theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl
#align simple_graph.mem_clique_set_iff SimpleGraph.mem_cliqueSet_iff
-/

#print SimpleGraph.cliqueSet_eq_empty_iff /-
@[simp]
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, Set.eq_empty_iff_forall_not_mem, mem_clique_set_iff]
#align simple_graph.clique_set_eq_empty_iff SimpleGraph.cliqueSet_eq_empty_iff
-/

alias clique_set_eq_empty_iff ↔ _ clique_free.clique_set
#align simple_graph.clique_free.clique_set SimpleGraph.CliqueFree.cliqueSet

attribute [protected] clique_free.clique_set

variable {G H}

#print SimpleGraph.cliqueSet_mono /-
@[mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n := fun _ => IsNClique.mono h
#align simple_graph.clique_set_mono SimpleGraph.cliqueSet_mono
-/

#print SimpleGraph.cliqueSet_mono' /-
theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet := fun _ => cliqueSet_mono h
#align simple_graph.clique_set_mono' SimpleGraph.cliqueSet_mono'
-/

end CliqueSet

/-! ### Finset of cliques -/


section CliqueFinset

variable (G) [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

#print SimpleGraph.cliqueFinset /-
/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) :=
  univ.filterₓ <| G.IsNClique n
#align simple_graph.clique_finset SimpleGraph.cliqueFinset
-/

#print SimpleGraph.mem_cliqueFinset_iff /-
theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _
#align simple_graph.mem_clique_finset_iff SimpleGraph.mem_cliqueFinset_iff
-/

#print SimpleGraph.coe_cliqueFinset /-
@[simp]
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ => mem_cliqueFinset_iff _
#align simple_graph.coe_clique_finset SimpleGraph.coe_cliqueFinset
-/

#print SimpleGraph.cliqueFinset_eq_empty_iff /-
@[simp]
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]
#align simple_graph.clique_finset_eq_empty_iff SimpleGraph.cliqueFinset_eq_empty_iff
-/

alias clique_finset_eq_empty_iff ↔ _ _root_.simple_graph.clique_free.clique_finset
#align simple_graph.clique_free.clique_finset SimpleGraph.CliqueFree.cliqueFinset

attribute [protected] clique_free.clique_finset

variable {G} [DecidableRel H.Adj]

#print SimpleGraph.cliqueFinset_mono /-
@[mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ => IsNClique.mono h
#align simple_graph.clique_finset_mono SimpleGraph.cliqueFinset_mono
-/

end CliqueFinset

end SimpleGraph

