/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.Finset.Pairwise

/-!
# Graph cliques

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Going back and forth between cliques and complete subgraphs or embeddings of complete graphs.
* Do we need `clique_set`, a version of `clique_finset` for infinite graphs?
-/


open Finset Fintype

namespace SimpleGraph

variable {α : Type _} (G H : SimpleGraph α)

/-! ### Cliques -/


section Clique

variable {s t : Set α}

/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj

theorem is_clique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidableOfIff' _ G.is_clique_iff

variable {G H}

theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono' h

theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t := by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono h

@[simp]
theorem is_clique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff

alias is_clique_bot_iff ↔ is_clique.subsingleton _

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  clique : G.IsClique s
  card_eq : s.card = n

theorem is_n_clique_iff : G.IsNClique n s ↔ G.IsClique s ∧ s.card = n :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} : Decidable (G.IsNClique n s) :=
  decidableOfIff' _ G.is_n_clique_iff

variable {G H}

theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [is_n_clique_iff]
  exact And.imp_left (is_clique.mono h)

@[simp]
theorem is_n_clique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n := by
  rw [is_n_clique_iff, is_clique_bot_iff]
  refine' and_congr_left _
  rintro rfl
  exact card_le_one.symm

variable [DecidableEq α] {a b c : α}

theorem is_3_clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  simp only [← is_n_clique_iff, ← is_clique_iff, ← Set.pairwise_insert_of_symmetric G.symm, ← coe_insert]
  have : ¬1 + 1 = 3 := by
    norm_num
  by_cases' hab : a = b <;>
    by_cases' hbc : b = c <;> by_cases' hac : a = c <;> subst_vars <;> simp [← G.ne_of_adj, ← and_rotate, *]

theorem is_3_clique_iff : G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 h.card_eq
    refine' ⟨a, b, c, _⟩
    rw [is_3_clique_triple_iff] at h
    tauto
    
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is_3_clique_triple_iff.2 ⟨hab, hbc, hca⟩
    

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.clique_free n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t

variable {G H}

theorem clique_free_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n := by
  rintro t ht
  rw [is_n_clique_bot_iff] at ht
  linarith

theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n := by
  rintro hG s hs
  obtain ⟨t, hts, ht⟩ := s.exists_smaller_set _ (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.clique.subset hts, ht⟩

theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun s => mt <| IsNClique.mono h

end CliqueFree

/-! ### Set of cliques -/


section CliqueSet

variable (G) {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
def CliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }

theorem mem_clique_set_iff : s ∈ G.CliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl

@[simp]
theorem clique_set_eq_empty_iff : G.CliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, Set.eq_empty_iff_forall_not_mem, mem_clique_set_iff]

alias clique_set_eq_empty_iff ↔ _ clique_free.clique_set

attribute [protected] clique_free.clique_set

variable {G H}

@[mono]
theorem clique_set_mono (h : G ≤ H) : G.CliqueSet n ⊆ H.CliqueSet n := fun _ => IsNClique.mono h

theorem clique_set_mono' (h : G ≤ H) : G.CliqueSet ≤ H.CliqueSet := fun _ => clique_set_mono h

end CliqueSet

/-! ### Finset of cliques -/


section CliqueFinset

variable (G) [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) :=
  univ.filter <| G.IsNClique n

theorem mem_clique_finset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

@[simp]
theorem coe_clique_finset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.CliqueSet n :=
  Set.ext fun _ => mem_clique_finset_iff _

@[simp]
theorem clique_finset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]

alias clique_finset_eq_empty_iff ↔ _ _root_.simple_graph.clique_free.clique_finset

attribute [protected] clique_free.clique_finset

variable {G} [DecidableRel H.Adj]

@[mono]
theorem clique_finset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  (monotone_filter_right _) fun _ => IsNClique.mono h

end CliqueFinset

end SimpleGraph

