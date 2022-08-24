/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Data.Fin.Interval

/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open Finset

open Fintype

namespace Finₓ

variable {α β : Type _} {n : ℕ}

@[simp]
theorem Ioi_zero_eq_map : ioi (0 : Finₓ n.succ) = univ.map (Finₓ.succEmbedding _).toEmbedding := by
  ext i
  simp only [mem_Ioi, mem_map, mem_univ, Function.Embedding.coe_fn_mk, exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
      
    · intro j _
      exact ⟨j, rfl⟩
      
    
  · rintro ⟨i, _, rfl⟩
    exact succ_pos _
    

@[simp]
theorem Ioi_succ (i : Finₓ n) : ioi i.succ = (ioi i).map (Finₓ.succEmbedding _).toEmbedding := by
  ext i
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_andₓ, Function.Embedding.coe_fn_mk, exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
      
    · intro i hi
      refine' ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
      
    
  · rintro ⟨i, hi, rfl⟩
    simpa
    

theorem card_filter_univ_succ' (p : Finₓ (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card = ite (p 0) 1 0 + (univ.filter (p ∘ Finₓ.succ)).card := by
  rw [Finₓ.univ_succ, filter_cons, card_disj_union, map_filter, card_map]
  split_ifs <;> simp

theorem card_filter_univ_succ (p : Finₓ (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card = if p 0 then (univ.filter (p ∘ Finₓ.succ)).card + 1 else (univ.filter (p ∘ Finₓ.succ)).card :=
  (card_filter_univ_succ' p).trans
    (by
      split_ifs <;> simp [add_commₓ 1])

theorem card_filter_univ_eq_vector_nth_eq_count [DecidableEq α] (a : α) (v : Vector α n) :
    (univ.filter fun i => a = v.nth i).card = v.toList.count a := by
  induction' v using Vector.inductionOn with n x xs hxs
  · simp
    
  · simp_rw [card_filter_univ_succ', Vector.nth_cons_zero, Vector.to_list_cons, Function.comp, Vector.nth_cons_succ,
      hxs, List.count_cons', add_commₓ (ite (a = x) 1 0)]
    

end Finₓ

