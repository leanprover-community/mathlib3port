/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Data.Fintype.BigOperators
import Logic.Equiv.Embedding

#align_import data.fintype.card_embedding from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

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
    ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ := by classical
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

