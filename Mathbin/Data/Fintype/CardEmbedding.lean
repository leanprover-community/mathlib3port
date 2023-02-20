/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module data.fintype.card_embedding
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
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


-- mathport name: finset.card
local notation "|" x "|" => Finset.card x

-- mathport name: fintype.card
local notation "‖" x "‖" => Fintype.card x

open Function

open Nat BigOperators

namespace Fintype

/- warning: fintype.card_embedding_eq_of_unique -> Fintype.card_embedding_eq_of_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Unique.{succ u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : Fintype.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β)], Eq.{1} Nat (Fintype.card.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β) _inst_3) (Fintype.card.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Unique.{succ u2} α] [_inst_2 : Fintype.{u1} β] [_inst_3 : Fintype.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β)], Eq.{1} Nat (Fintype.card.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β) _inst_3) (Fintype.card.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_uniqueₓ'. -/
theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult
#align fintype.card_embedding_eq_of_unique Fintype.card_embedding_eq_of_unique

/- warning: fintype.card_embedding_eq -> Fintype.card_embedding_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : Fintype.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β)], Eq.{1} Nat (Fintype.card.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β) _inst_3) (Nat.descFactorial (Fintype.card.{u2} β _inst_2) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] [_inst_3 : Fintype.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β)], Eq.{1} Nat (Fintype.card.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β) _inst_3) (Nat.descFactorial (Fintype.card.{u1} β _inst_2) (Fintype.card.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align fintype.card_embedding_eq Fintype.card_embedding_eqₓ'. -/
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

/- warning: fintype.card_embedding_eq_of_infinite -> Fintype.card_embedding_eq_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : Fintype.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β)], Eq.{1} Nat (Fintype.card.{max u1 u2} (Function.Embedding.{succ u1, succ u2} α β) _inst_3) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u2} α] [_inst_2 : Fintype.{u1} β] [_inst_3 : Fintype.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β)], Eq.{1} Nat (Fintype.card.{max u2 u1} (Function.Embedding.{succ u2, succ u1} α β) _inst_3) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infiniteₓ'. -/
/- The cardinality of embeddings from an infinite type to a finite type is zero.
This is a re-statement of the pigeonhole principle. -/
@[simp]
theorem card_embedding_eq_of_infinite {α β : Type _} [Infinite α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = 0 :=
  card_eq_zero
#align fintype.card_embedding_eq_of_infinite Fintype.card_embedding_eq_of_infinite

end Fintype

