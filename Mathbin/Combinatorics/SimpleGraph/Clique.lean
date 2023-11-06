/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Combinatorics.SimpleGraph.Basic
import Data.Finset.Pairwise
import Data.Finset.Preimage

#align_import combinatorics.simple_graph.clique from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

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
* Dualise all the API to get independent sets
-/


open Finset Fintype Function

namespace SimpleGraph

variable {α β : Type _} (G H : SimpleGraph α)

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

#print SimpleGraph.isClique_iff_induce_eq /-
/-- A clique is a set of vertices whose induced graph is complete. -/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ :=
  by
  rw [is_clique_iff]
  constructor
  · intro h
    ext ⟨v, hv⟩ ⟨w, hw⟩
    simp only [comap_adj, Subtype.coe_mk, top_adj, Ne.def, Subtype.mk_eq_mk]
    exact ⟨adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at this => rw [h]
    simpa [hne]
#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eq
-/

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H} {a b : α}

@[simp]
theorem isClique_empty : G.IsClique ∅ :=
  Set.pairwise_empty _
#align simple_graph.is_clique_empty SimpleGraph.isClique_empty

@[simp]
theorem isClique_singleton (a : α) : G.IsClique {a} :=
  Set.pairwise_singleton _ _
#align simple_graph.is_clique_singleton SimpleGraph.isClique_singleton

theorem isClique_pair : G.IsClique {a, b} ↔ a ≠ b → G.Adj a b :=
  Set.pairwise_pair_of_symmetric G.symm
#align simple_graph.is_clique_pair SimpleGraph.isClique_pair

@[simp]
theorem isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, a ≠ b → G.Adj a b :=
  Set.pairwise_insert_of_symmetric G.symm
#align simple_graph.is_clique_insert SimpleGraph.isClique_insert

theorem isClique_insert_of_not_mem (ha : a ∉ s) :
    G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, G.Adj a b :=
  Set.pairwise_insert_of_symmetric_of_not_mem G.symm ha
#align simple_graph.is_clique_insert_of_not_mem SimpleGraph.isClique_insert_of_not_mem

theorem IsClique.insert (hs : G.IsClique s) (h : ∀ b ∈ s, a ≠ b → G.Adj a b) :
    G.IsClique (insert a s) :=
  hs.insert_of_symmetric G.symm h
#align simple_graph.is_clique.insert SimpleGraph.IsClique.insert

#print SimpleGraph.IsClique.mono /-
theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s :=
  Set.Pairwise.mono' h
#align simple_graph.is_clique.mono SimpleGraph.IsClique.mono
-/

#print SimpleGraph.IsClique.subset /-
theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t :=
  Set.Pairwise.mono h
#align simple_graph.is_clique.subset SimpleGraph.IsClique.subset
-/

protected theorem IsClique.map {G : SimpleGraph α} {s : Set α} (h : G.IsClique s) {f : α ↪ β} :
    (G.map f).IsClique (f '' s) :=
  by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  exact ⟨a, b, h ha hb <| ne_of_apply_ne _ hab, rfl, rfl⟩
#align simple_graph.is_clique.map SimpleGraph.IsClique.map

#print SimpleGraph.isClique_bot_iff /-
@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff
#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iff
-/

alias ⟨is_clique.subsingleton, _⟩ := is_clique_bot_iff
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

variable {G H} {a b c : α}

@[simp]
theorem isNClique_empty : G.IsNClique n ∅ ↔ n = 0 := by simp [is_n_clique_iff, eq_comm]
#align simple_graph.is_n_clique_empty SimpleGraph.isNClique_empty

@[simp]
theorem isNClique_singleton : G.IsNClique n {a} ↔ n = 1 := by simp [is_n_clique_iff, eq_comm]
#align simple_graph.is_n_clique_singleton SimpleGraph.isNClique_singleton

#print SimpleGraph.IsNClique.mono /-
theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [is_n_clique_iff]; exact And.imp_left (is_clique.mono h)
#align simple_graph.is_n_clique.mono SimpleGraph.IsNClique.mono
-/

protected theorem IsNClique.map (h : G.IsNClique n s) {f : α ↪ β} :
    (G.map f).IsNClique n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩
#align simple_graph.is_n_clique.map SimpleGraph.IsNClique.map

#print SimpleGraph.isNClique_bot_iff /-
@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n :=
  by
  rw [is_n_clique_iff, is_clique_bot_iff]
  refine' and_congr_left _
  rintro rfl
  exact card_le_one.symm
#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iff
-/

@[simp]
theorem isNClique_zero : G.IsNClique 0 s ↔ s = ∅ := by
  simp only [is_n_clique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp
#align simple_graph.is_n_clique_zero SimpleGraph.isNClique_zero

@[simp]
theorem isNClique_one : G.IsNClique 1 s ↔ ∃ a, s = {a} := by
  simp only [is_n_clique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp
#align simple_graph.is_n_clique_one SimpleGraph.isNClique_one

variable [DecidableEq α]

theorem IsNClique.insert (hs : G.IsNClique n s) (h : ∀ b ∈ s, G.Adj a b) :
    G.IsNClique (n + 1) (insert a s) := by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_not_mem fun ha => (h _ ha).Ne rfl, hs.2]
#align simple_graph.is_n_clique.insert SimpleGraph.IsNClique.insert

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

#print SimpleGraph.not_cliqueFree_of_top_embedding /-
theorem not_cliqueFree_of_top_embedding {n : ℕ} (f : (⊤ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.CliqueFree n :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, Classical.not_forall,
    Classical.not_not]
  use finset.univ.map f.to_embedding
  simp only [card_map, Finset.card_fin, eq_self_iff_true, and_true_iff]
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [coe_map, RelEmbedding.coe_toEmbedding, Set.mem_image, coe_univ, Set.mem_univ,
    true_and_iff] at hv hw 
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  simp only [f.map_adj_iff, comap_adj, Function.Embedding.coe_subtype, Subtype.coe_mk, top_adj,
    Ne.def, Subtype.mk_eq_mk]
  exact (Function.Embedding.apply_eq_iff_eq _ _ _).symm.Not
#align simple_graph.not_clique_free_of_top_embedding SimpleGraph.not_cliqueFree_of_top_embedding
-/

#print SimpleGraph.topEmbeddingOfNotCliqueFree /-
/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    (⊤ : SimpleGraph (Fin n)) ↪g G :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, Classical.not_forall,
    Classical.not_not] at h 
  obtain ⟨ha, hb⟩ := h.some_spec
  have : (⊤ : SimpleGraph (Fin h.some.card)) ≃g (⊤ : SimpleGraph h.some) :=
    by
    apply iso.complete_graph
    simpa using (Fintype.equivFin h.some).symm
  rw [← ha] at this 
  convert (embedding.induce ↑h.some).comp this.to_embedding <;> exact hb.symm
#align simple_graph.top_embedding_of_not_clique_free SimpleGraph.topEmbeddingOfNotCliqueFree
-/

#print SimpleGraph.not_cliqueFree_iff /-
theorem not_cliqueFree_iff (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g G) :=
  by
  constructor
  · exact fun h => ⟨top_embedding_of_not_clique_free h⟩
  · rintro ⟨f⟩
    exact not_clique_free_of_top_embedding f
#align simple_graph.not_clique_free_iff SimpleGraph.not_cliqueFree_iff
-/

#print SimpleGraph.cliqueFree_iff /-
theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) ↪g G) := by
  rw [← not_iff_not, not_clique_free_iff, not_isEmpty_iff]
#align simple_graph.clique_free_iff SimpleGraph.cliqueFree_iff
-/

#print SimpleGraph.not_cliqueFree_card_of_top_embedding /-
theorem not_cliqueFree_card_of_top_embedding [Fintype α] (f : (⊤ : SimpleGraph α) ↪g G) :
    ¬G.CliqueFree (card α) := by
  rw [not_clique_free_iff]
  use(iso.complete_graph (Fintype.equivFin α)).symm.toEmbedding.trans f
#align simple_graph.not_clique_free_card_of_top_embedding SimpleGraph.not_cliqueFree_card_of_top_embedding
-/

#print SimpleGraph.cliqueFree_bot /-
@[simp]
theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n :=
  by
  rintro t ht
  rw [is_n_clique_bot_iff] at ht 
  linarith
#align simple_graph.clique_free_bot SimpleGraph.cliqueFree_bot
-/

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
  refine' Nat.lt_le_asymm hc _
  rw [clique_free_iff, not_isEmpty_iff] at h 
  simpa using Fintype.card_le_of_embedding h.some.to_embedding
#align simple_graph.clique_free_of_card_lt SimpleGraph.cliqueFree_of_card_lt
-/

@[simp]
theorem cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥ := by
  classical
  constructor
  · simp_rw [← edge_set_eq_empty, Set.eq_empty_iff_forall_not_mem, Sym2.forall, mem_edge_set]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_doubleton hab.Ne⟩
  · rintro rfl
    exact clique_free_bot le_rfl
#align simple_graph.clique_free_two SimpleGraph.cliqueFree_two

end CliqueFree

section CliqueFreeOn

variable {s s₁ s₂ : Set α} {t : Finset α} {a b : α} {m n : ℕ}

/-- `G.clique_free_on s n` means that `G` has no `n`-cliques contained in `s`. -/
def CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNClique n t
#align simple_graph.clique_free_on SimpleGraph.CliqueFreeOn

theorem CliqueFreeOn.subset (hs : s₁ ⊆ s₂) (h₂ : G.CliqueFreeOn s₂ n) : G.CliqueFreeOn s₁ n :=
  fun t hts => h₂ <| hts.trans hs
#align simple_graph.clique_free_on.subset SimpleGraph.CliqueFreeOn.subset

theorem CliqueFreeOn.mono (hmn : m ≤ n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n :=
  by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := t.exists_smaller_set _ (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.clique.subset hut, hu⟩
#align simple_graph.clique_free_on.mono SimpleGraph.CliqueFreeOn.mono

theorem CliqueFreeOn.anti (hGH : G ≤ H) (hH : H.CliqueFreeOn s n) : G.CliqueFreeOn s n :=
  fun t hts ht => hH hts <| ht.mono hGH
#align simple_graph.clique_free_on.anti SimpleGraph.CliqueFreeOn.anti

@[simp]
theorem cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n ≠ 0 := by
  simp [clique_free_on, Set.subset_empty_iff]
#align simple_graph.clique_free_on_empty SimpleGraph.cliqueFreeOn_empty

@[simp]
theorem cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;> simp [clique_free_on, Set.subset_singleton_iff_eq]
#align simple_graph.clique_free_on_singleton SimpleGraph.cliqueFreeOn_singleton

@[simp]
theorem cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n := by
  simp [clique_free, clique_free_on]
#align simple_graph.clique_free_on_univ SimpleGraph.cliqueFreeOn_univ

protected theorem CliqueFree.cliqueFreeOn (hG : G.CliqueFree n) : G.CliqueFreeOn s n := fun t _ =>
  hG _
#align simple_graph.clique_free.clique_free_on SimpleGraph.CliqueFree.cliqueFreeOn

theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : s.card < n) : G.CliqueFreeOn s n :=
  fun t hts ht => h.not_le <| ht.2.symm.trans_le <| card_mono hts
#align simple_graph.clique_free_on_of_card_lt SimpleGraph.cliqueFreeOn_of_card_lt

--TOOD: Restate using `simple_graph.indep_set` once we have it
@[simp]
theorem cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine' ⟨fun h a ha b hb _ hab => h _ ⟨by simpa [hab.ne], card_doubleton hab.Ne⟩, _⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [clique_free_on, is_n_clique_iff, card_eq_two, coe_subset, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst 
  refine' h hst.1 hst.2 hab (ht _ _ hab) <;> simp
#align simple_graph.clique_free_on_two SimpleGraph.cliqueFreeOn_two

theorem CliqueFreeOn.of_succ (hs : G.CliqueFreeOn s (n + 1)) (ha : a ∈ s) :
    G.CliqueFreeOn (s ∩ G.neighborSet a) n := by
  classical
  refine' fun t hts ht => hs _ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans <| Set.inter_subset_left _ _⟩
#align simple_graph.clique_free_on.of_succ SimpleGraph.CliqueFreeOn.of_succ

end CliqueFreeOn

/-! ### Set of cliques -/


section CliqueSet

variable (G) {n : ℕ} {a b c : α} {s : Finset α}

#print SimpleGraph.cliqueSet /-
/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  {s | G.IsNClique n s}
#align simple_graph.clique_set SimpleGraph.cliqueSet
-/

#print SimpleGraph.mem_cliqueSet_iff /-
@[simp]
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

variable {G H}

#print SimpleGraph.CliqueFree.cliqueSet /-
protected theorem CliqueFree.cliqueSet : G.CliqueFree n → G.cliqueSet n = ∅ :=
  G.cliqueSet_eq_empty_iff.2
#align simple_graph.clique_free.clique_set SimpleGraph.CliqueFree.cliqueSet
-/

#print SimpleGraph.cliqueSet_mono /-
@[mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n := fun _ => IsNClique.mono h
#align simple_graph.clique_set_mono SimpleGraph.cliqueSet_mono
-/

#print SimpleGraph.cliqueSet_mono' /-
theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet := fun _ => cliqueSet_mono h
#align simple_graph.clique_set_mono' SimpleGraph.cliqueSet_mono'
-/

@[simp]
theorem cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅} :=
  Set.ext fun s => by simp
#align simple_graph.clique_set_zero SimpleGraph.cliqueSet_zero

@[simp]
theorem cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]
#align simple_graph.clique_set_one SimpleGraph.cliqueSet_one

@[simp]
theorem cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅ :=
  (cliqueFree_bot hn).cliqueSet
#align simple_graph.clique_set_bot SimpleGraph.cliqueSet_bot

@[simp]
theorem cliqueSet_map (hn : n ≠ 1) (G : SimpleGraph α) (f : α ↪ β) :
    (G.map f).cliqueSet n = map f '' G.cliqueSet n :=
  by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f <| f.injective.inj_on _).map f = s := by
      classical
      rw [map_eq_image, image_preimage, filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩) a
      obtain ⟨c, _, _, hc, _⟩ := hs ha hb hba.symm
      exact ⟨c, hc⟩
    refine' ⟨s.preimage f <| f.injective.inj_on _, ⟨_, by rw [← card_map f, hs']⟩, hs'⟩
    rw [coe_preimage]
    exact fun a ha b hb hab => map_adj_apply.1 (hs ha hb <| f.injective.ne hab)
  · rintro ⟨s, hs, rfl⟩
    exact is_n_clique.map hs
#align simple_graph.clique_set_map SimpleGraph.cliqueSet_map

@[simp]
theorem cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueSet n = map e.toEmbedding '' G.cliqueSet n :=
  by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · exact clique_set_map hn _ _
#align simple_graph.clique_set_map_of_equiv SimpleGraph.cliqueSet_map_of_equiv

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
@[simp]
theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _
#align simple_graph.mem_clique_finset_iff SimpleGraph.mem_cliqueFinset_iff
-/

#print SimpleGraph.coe_cliqueFinset /-
@[simp, norm_cast]
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

alias ⟨_, _root_.simple_graph.clique_free.clique_finset⟩ := clique_finset_eq_empty_iff
#align simple_graph.clique_free.clique_finset SimpleGraph.CliqueFree.cliqueFinset

attribute [protected] clique_free.clique_finset

variable {G}

theorem card_cliqueFinset_le : (G.cliqueFinset n).card ≤ (card α).choose n :=
  by
  rw [← card_univ, ← card_powerset_len]
  refine' card_mono fun s => _
  simpa [mem_powerset_len_univ_iff] using is_n_clique.card_eq
#align simple_graph.card_clique_finset_le SimpleGraph.card_cliqueFinset_le

variable [DecidableRel H.Adj]

#print SimpleGraph.cliqueFinset_mono /-
@[mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ => IsNClique.mono h
#align simple_graph.clique_finset_mono SimpleGraph.cliqueFinset_mono
-/

variable [Fintype β] [DecidableEq β] (G)

@[simp]
theorem cliqueFinset_map (f : α ↪ β) (hn : n ≠ 1) :
    (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩ :=
  coe_injective <| by
    simp_rw [coe_clique_finset, clique_set_map hn, coe_map, coe_clique_finset, embedding.coe_fn_mk]
#align simple_graph.clique_finset_map SimpleGraph.cliqueFinset_map

@[simp]
theorem cliqueFinset_map_of_equiv (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueFinset n =
      (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
  coe_injective <| by push_cast <;> exact clique_set_map_of_equiv _ _ _
#align simple_graph.clique_finset_map_of_equiv SimpleGraph.cliqueFinset_map_of_equiv

end CliqueFinset

end SimpleGraph

