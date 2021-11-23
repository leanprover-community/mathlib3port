import Mathbin.Data.Fintype.Card 
import Mathbin.Data.Equiv.Fin 
import Mathbin.Data.Equiv.Embedding

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/


local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open_locale Nat

attribute [local semireducible] Function.Embedding.fintype

namespace Fintype

theorem card_embedding_eq_of_unique {α β : Type _} [Unique α] [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
  ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult

-- error in Data.Fintype.CardEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem card_embedding_aux
{n : exprℕ()}
{β}
[fintype β]
[decidable_eq β]
(h : «expr ≤ »(n, «expr‖ ‖»(β))) : «expr = »(«expr‖ ‖»(«expr ↪ »(fin n, β)), «expr‖ ‖»(β).desc_factorial n) :=
begin
  induction [expr n] [] ["with", ident n, ident hn] [],
  { nontriviality [expr «expr ↪ »(fin 0, β)] [],
    rw ["[", expr nat.desc_factorial_zero, ",", expr fintype.card_eq_one_iff, "]"] [],
    refine [expr ⟨nonempty.some nontrivial.to_nonempty, λ x, function.embedding.ext fin.elim0⟩] },
  rw ["[", expr nat.succ_eq_add_one, ",", "<-", expr card_congr (equiv.embedding_congr fin_sum_fin_equiv (equiv.refl β)), ",", expr card_congr equiv.sum_embedding_equiv_sigma_embedding_restricted, "]"] [],
  all_goals { try { apply_instance } },
  have [] [":", expr ∀
   f : «expr ↪ »(fin n, β), «expr = »(«expr‖ ‖»(«expr ↪ »(fin 1, («expr ᶜ»(set.range f) : set β))), «expr - »(«expr‖ ‖»(β), n))] [],
  { intro [ident f],
    rw [expr card_embedding_eq_of_unique] [],
    rw [expr card_of_finset' «expr ᶜ»(finset.map f finset.univ)] [],
    { rw ["[", expr finset.card_compl, ",", expr finset.card_map, ",", expr finset.card_fin, "]"] [] },
    { simp [] [] [] [] [] [] } },
  rw [expr card_sigma] [],
  simp [] [] ["only"] ["[", expr this, ",", expr finset.sum_const, ",", expr finset.card_univ, ",", expr nsmul_eq_mul, ",", expr nat.cast_id, "]"] [] [],
  replace [ident h] [] [":=", expr (nat.lt_of_succ_le h).le],
  rw ["[", expr nat.desc_factorial_succ, ",", expr hn h, ",", expr mul_comm, "]"] []
end

@[simp]
theorem card_embedding_eq {α β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
  ‖α ↪ β‖ = ‖β‖.descFactorial ‖α‖ :=
  by 
    obtain h | h := lt_or_geₓ ‖β‖ ‖α‖
    ·
      rw [card_eq_zero_iff.mpr (Function.Embedding.is_empty_of_card_lt h), nat.desc_factorial_eq_zero_iff_lt.mpr h]
    ·
      truncCases Fintype.truncEquivFin α with eq 
      rw [Fintype.card_congr (Equiv.embeddingCongr Eq (Equiv.refl β))]
      exact card_embedding_aux h

@[simp]
theorem card_embedding_eq_of_infinite {α β} [Infinite α] [Fintype β] : ‖α ↪ β‖ = 0 :=
  card_eq_zero_iff.mpr Function.Embedding.is_empty

end Fintype

