/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Logic.Equiv.Fin
import Mathbin.Logic.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


-- mathport name: finset.card
local notation "|" x "|" => Finsetₓ.card x

-- mathport name: fintype.card
local notation "‖" x "‖" => Fintypeₓ.card x

open Function

open Nat BigOperators

namespace Fintypeₓ

theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintypeₓ β] [Fintypeₓ (α ↪ β)] : ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equivₓ.uniqueEmbeddingEquivResult

-- Establishes the cardinality of the type of all injections between two finite types.
@[simp]
theorem card_embedding_eq {α β} [Fintypeₓ α] [Fintypeₓ β] [Fintypeₓ (α ↪ β)] : ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  classical
  induction' ‹Fintypeₓ α› using Fintypeₓ.induction_empty_option with α₁ α₂ h₂ e ih α h ih
  · letI := Fintypeₓ.ofEquiv _ e.symm
    rw [← card_congr (Equivₓ.embeddingCongr e (Equivₓ.refl β)), ih, card_congr e]
    
  · rw [card_pempty, Nat.desc_factorial_zero, card_eq_one_iff]
    exact ⟨embedding.of_is_empty, fun x => FunLike.ext _ _ isEmptyElim⟩
    
  · rw [card_option, Nat.desc_factorial_succ, card_congr (embedding.option_embedding_equiv α β), card_sigma, ← ih]
    simp only [Fintypeₓ.card_compl_set, Fintypeₓ.card_range, Finsetₓ.sum_const, Finsetₓ.card_univ, smul_eq_mul,
      mul_comm]
    

/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β : Type _} [Infinite α] [Fintypeₓ β] [Fintypeₓ (α ↪ β)] : ‖α ↪ β‖ = 0 :=
  card_eq_zero

end Fintypeₓ

