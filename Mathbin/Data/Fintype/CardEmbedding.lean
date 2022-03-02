/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Equiv.Fin
import Mathbin.Data.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


-- mathport name: «expr| |»
local notation "|" x "|" => Finset.card x

-- mathport name: «expr‖ ‖»
local notation "‖" x "‖" => Fintype.card x

open_locale Nat

attribute [local semireducible] Function.Embedding.fintype

namespace Fintype

-- We need the separate `fintype α` instance as it contains data,
-- and may not match definitionally with the instance coming from `unique.fintype`.
theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equivₓ.uniqueEmbeddingEquivResult

private theorem card_embedding_aux {n : ℕ} {β} [Fintype β] [DecidableEq β] (h : n ≤ ‖β‖) :
    ‖Finₓ n ↪ β‖ = ‖β‖.descFactorial n := by
  induction' n with n hn
  · nontriviality Finₓ 0 ↪ β
    rw [Nat.desc_factorial_zero, Fintype.card_eq_one_iff]
    refine' ⟨Nonempty.some Nontrivial.to_nonempty, fun x => Function.Embedding.ext Finₓ.elim0⟩
    
  rw [Nat.succ_eq_add_one, ← card_congr (Equivₓ.embeddingCongr finSumFinEquiv (Equivₓ.refl β)),
    card_congr Equivₓ.sumEmbeddingEquivSigmaEmbeddingRestricted]
  -- these `rw`s create goals for instances, which it doesn't infer for some reason
  all_goals
    try
      infer_instance
  -- however, this needs to be done here instead of at the end
  -- else, a later `simp`, which depends on the `fintype` instance, won't work.
  have : ∀ f : Finₓ n ↪ β, ‖Finₓ 1 ↪ (Set.Range fᶜ : Set β)‖ = ‖β‖ - n := by
    intro f
    rw [card_embedding_eq_of_unique]
    rw [card_of_finset' (Finset.map f Finset.univᶜ)]
    · rw [Finset.card_compl, Finset.card_map, Finset.card_fin]
      
    · simp
      
  -- putting `card_sigma` in `simp` causes it to not fully simplify
  rw [card_sigma]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_idₓ]
  replace h := (Nat.lt_of_succ_leₓ h).le
  rw [Nat.desc_factorial_succ, hn h, mul_comm]

-- Establishes the cardinality of the type of all injections between two finite types.
@[simp]
theorem card_embedding_eq {α β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  obtain h | h := lt_or_geₓ ‖β‖ ‖α‖
  · rw [card_eq_zero_iff.mpr (Function.Embedding.is_empty_of_card_lt h), nat.desc_factorial_eq_zero_iff_lt.mpr h]
    
  · trunc_cases Fintype.truncEquivFin α with eq
    rw [Fintype.card_congr (Equivₓ.embeddingCongr Eq (Equivₓ.refl β))]
    exact card_embedding_aux h
    

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β} [Infinite α] [Fintype β] : ‖α ↪ β‖ = 0 :=
  card_eq_zero_iff.mpr Function.Embedding.is_empty

end Fintype

