/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.fintype.fin
! leanprover-community/mathlib commit 759575657f189ccb424b990164c8b1fa9f55cdfe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Interval

/-!
# The structure of `fintype (fin n)`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open Finset

open Fintype

namespace Fin

variable {α β : Type _} {n : ℕ}

#print Fin.map_valEmbedding_univ /-
-- TODO: replace `subtype` with `coe` in the name of this lemma and `fin.map_subtype_embedding_Iio`
theorem map_valEmbedding_univ : (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n :=
  by
  ext
  simp [order_iso_subtype.symm.surjective.exists, OrderIso.symm]
#align fin.map_subtype_embedding_univ Fin.map_valEmbedding_univ
-/

#print Fin.Ioi_zero_eq_map /-
@[simp]
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmbedding _).toEmbedding :=
  by
  ext i
  simp only [mem_Ioi, mem_map, mem_univ, Function.Embedding.coeFn_mk, exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
    · intro j _; exact ⟨j, rfl⟩
  · rintro ⟨i, _, rfl⟩
    exact succ_pos _
#align fin.Ioi_zero_eq_map Fin.Ioi_zero_eq_map
-/

#print Fin.Iio_last_eq_map /-
@[simp]
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb.toEmbedding :=
  by
  apply Finset.map_injective Fin.valEmbedding
  rw [Finset.map_map, Fin.map_valEmbedding_Iio, Fin.val_last]
  exact map_subtype_embedding_univ.symm
#align fin.Iio_last_eq_map Fin.Iio_last_eq_map
-/

#print Fin.Ioi_succ /-
@[simp]
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmbedding _).toEmbedding :=
  by
  ext i
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and_iff, Function.Embedding.coeFn_mk,
    exists_true_left]
  constructor
  · refine' cases _ _ i
    · rintro ⟨⟨⟩⟩
    · intro i hi
      refine' ⟨i, succ_lt_succ_iff.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; simpa
#align fin.Ioi_succ Fin.Ioi_succ
-/

#print Fin.Iio_castSuccEmb /-
@[simp]
theorem Iio_castSuccEmb (i : Fin n) :
    Iio (castSuccEmb i) = (Iio i).map Fin.castSuccEmb.toEmbedding :=
  by
  apply Finset.map_injective Fin.valEmbedding
  rw [Finset.map_map, Fin.map_valEmbedding_Iio]
  exact (Fin.map_valEmbedding_Iio i).symm
#align fin.Iio_cast_succ Fin.Iio_castSuccEmb
-/

#print Fin.card_filter_univ_succ' /-
theorem card_filter_univ_succ' (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filterₓ p).card = ite (p 0) 1 0 + (univ.filterₓ (p ∘ Fin.succ)).card :=
  by
  rw [Fin.univ_succ, filter_cons, card_disj_union, filter_map, card_map]
  split_ifs <;> simp
#align fin.card_filter_univ_succ' Fin.card_filter_univ_succ'
-/

#print Fin.card_filter_univ_succ /-
theorem card_filter_univ_succ (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filterₓ p).card =
      if p 0 then (univ.filterₓ (p ∘ Fin.succ)).card + 1 else (univ.filterₓ (p ∘ Fin.succ)).card :=
  (card_filter_univ_succ' p).trans (by split_ifs <;> simp [add_comm 1])
#align fin.card_filter_univ_succ Fin.card_filter_univ_succ
-/

#print Fin.card_filter_univ_eq_vector_get_eq_count /-
theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : Vector α n) :
    (univ.filterₓ fun i => a = v.get? i).card = v.toList.count a :=
  by
  induction' v using Vector.inductionOn with n x xs hxs
  · simp
  ·
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Function.comp,
      Vector.get_cons_succ, hxs, List.count_cons', add_comm (ite (a = x) 1 0)]
#align fin.card_filter_univ_eq_vector_nth_eq_count Fin.card_filter_univ_eq_vector_get_eq_count
-/

end Fin

