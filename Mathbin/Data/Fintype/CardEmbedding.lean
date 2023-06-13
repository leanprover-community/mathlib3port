/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.fintype.card_embedding
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Logic.Equiv.Embedding

/-!
# Number of embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes the cardinality of `α ↪ β` in full generality.
-/


local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open Function

open scoped Nat BigOperators

namespace Fintype

#print Fintype.card_embedding_eq_of_unique /-
theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult
#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_unique
-/

#print Fintype.card_embedding_eq /-
-- Establishes the cardinality of the type of all injections between two finite types.
@[simp]
theorem card_embedding_eq {α β} [Fintype α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by
  classical
  induction' ‹Fintype α› using Fintype.induction_empty_option with α₁ α₂ h₂ e ih α h ih
  · letI := Fintype.ofEquiv _ e.symm
    rw [← card_congr (Equiv.embeddingCongr e (Equiv.refl β)), ih, card_congr e]
  · rw [card_pempty, Nat.descFactorial_zero, card_eq_one_iff]
    exact ⟨embedding.of_is_empty, fun x => FunLike.ext _ _ isEmptyElim⟩
  · rw [card_option, Nat.descFactorial_succ, card_congr (embedding.option_embedding_equiv α β),
      card_sigma, ← ih]
    simp only [Fintype.card_compl_set, Fintype.card_range, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
#align fintype.card_embedding_eq Fintype.card_embedding_eq
-/

#print Fintype.card_embedding_eq_of_infinite /-
/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β : Type _} [Infinite α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero
#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infinite
-/

end Fintype

