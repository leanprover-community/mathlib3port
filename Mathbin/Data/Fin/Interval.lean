/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.fin.interval
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals in `fin n`

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Fin Function

open BigOperators

variable (n : ℕ)

instance : LocallyFiniteOrder (Fin n) :=
  OrderIso.locallyFiniteOrder Fin.orderIsoSubtype

instance : LocallyFiniteOrderBot (Fin n) :=
  OrderIso.locallyFiniteOrderBot Fin.orderIsoSubtype

instance : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | n + 1 => inferInstance

namespace Fin

variable {n} (a b : Fin n)

theorem Icc_eq_finset_subtype : icc a b = (icc (a : ℕ) b).Fin n :=
  rfl
#align fin.Icc_eq_finset_subtype Fin.Icc_eq_finset_subtype

theorem Ico_eq_finset_subtype : ico a b = (ico (a : ℕ) b).Fin n :=
  rfl
#align fin.Ico_eq_finset_subtype Fin.Ico_eq_finset_subtype

theorem Ioc_eq_finset_subtype : ioc a b = (ioc (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioc_eq_finset_subtype Fin.Ioc_eq_finset_subtype

theorem Ioo_eq_finset_subtype : ioo a b = (ioo (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioo_eq_finset_subtype Fin.Ioo_eq_finset_subtype

@[simp]
theorem map_subtype_embedding_Icc : (icc a b).map Fin.coeEmbedding = icc a b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Icc Fin.map_subtype_embedding_Icc

@[simp]
theorem map_subtype_embedding_Ico : (ico a b).map Fin.coeEmbedding = ico a b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ico Fin.map_subtype_embedding_Ico

@[simp]
theorem map_subtype_embedding_Ioc : (ioc a b).map Fin.coeEmbedding = ioc a b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Ioc Fin.map_subtype_embedding_Ioc

@[simp]
theorem map_subtype_embedding_Ioo : (ioo a b).map Fin.coeEmbedding = ioo a b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ioo Fin.map_subtype_embedding_Ioo

@[simp]
theorem card_Icc : (icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]
#align fin.card_Icc Fin.card_Icc

@[simp]
theorem card_Ico : (ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]
#align fin.card_Ico Fin.card_Ico

@[simp]
theorem card_Ioc : (ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]
#align fin.card_Ioc Fin.card_Ioc

@[simp]
theorem card_Ioo : (ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]
#align fin.card_Ioo Fin.card_Ioo

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_of_finset]
#align fin.card_fintype_Icc Fin.card_fintype_Icc

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_of_finset]
#align fin.card_fintype_Ico Fin.card_fintype_Ico

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_of_finset]
#align fin.card_fintype_Ioc Fin.card_fintype_Ioc

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_of_finset]
#align fin.card_fintype_Ioo Fin.card_fintype_Ioo

theorem Ici_eq_finset_subtype : ici a = (icc (a : ℕ) n).Fin n := by
  ext
  simp
#align fin.Ici_eq_finset_subtype Fin.Ici_eq_finset_subtype

theorem Ioi_eq_finset_subtype : ioi a = (ioc (a : ℕ) n).Fin n := by
  ext
  simp
#align fin.Ioi_eq_finset_subtype Fin.Ioi_eq_finset_subtype

theorem Iic_eq_finset_subtype : iic b = (iic (b : ℕ)).Fin n :=
  rfl
#align fin.Iic_eq_finset_subtype Fin.Iic_eq_finset_subtype

theorem Iio_eq_finset_subtype : iio b = (iio (b : ℕ)).Fin n :=
  rfl
#align fin.Iio_eq_finset_subtype Fin.Iio_eq_finset_subtype

@[simp]
theorem map_subtype_embedding_Ici : (ici a).map Fin.coeEmbedding = icc a (n - 1) := by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ici Fin.map_subtype_embedding_Ici

@[simp]
theorem map_subtype_embedding_Ioi : (ioi a).map Fin.coeEmbedding = ioc a (n - 1) := by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ioi Fin.map_subtype_embedding_Ioi

@[simp]
theorem map_subtype_embedding_Iic : (iic b).map Fin.coeEmbedding = iic b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Iic Fin.map_subtype_embedding_Iic

@[simp]
theorem map_subtype_embedding_Iio : (iio b).map Fin.coeEmbedding = iio b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Iio Fin.map_subtype_embedding_Iio

@[simp]
theorem card_Ici : (ici a).card = n - a := by 
  cases n
  · exact Fin.elim0 a
  rw [← card_map, map_subtype_embedding_Ici, Nat.card_Icc]
  rfl
#align fin.card_Ici Fin.card_Ici

@[simp]
theorem card_Ioi : (ioi a).card = n - 1 - a := by
  rw [← card_map, map_subtype_embedding_Ioi, Nat.card_Ioc]
#align fin.card_Ioi Fin.card_Ioi

@[simp]
theorem card_Iic : (iic b).card = b + 1 := by
  rw [← Nat.card_Iic b, ← map_subtype_embedding_Iic, card_map]
#align fin.card_Iic Fin.card_Iic

@[simp]
theorem card_Iio : (iio b).card = b := by
  rw [← Nat.card_Iio b, ← map_subtype_embedding_Iio, card_map]
#align fin.card_Iio Fin.card_Iio

@[simp]
theorem card_fintype_Ici : Fintype.card (Set.ici a) = n - a := by
  rw [Fintype.card_of_finset, card_Ici]
#align fin.card_fintype_Ici Fin.card_fintype_Ici

@[simp]
theorem card_fintype_Ioi : Fintype.card (Set.ioi a) = n - 1 - a := by
  rw [Fintype.card_of_finset, card_Ioi]
#align fin.card_fintype_Ioi Fin.card_fintype_Ioi

@[simp]
theorem card_fintype_Iic : Fintype.card (Set.iic b) = b + 1 := by
  rw [Fintype.card_of_finset, card_Iic]
#align fin.card_fintype_Iic Fin.card_fintype_Iic

@[simp]
theorem card_fintype_Iio : Fintype.card (Set.iio b) = b := by rw [Fintype.card_of_finset, card_Iio]
#align fin.card_fintype_Iio Fin.card_fintype_Iio

end Fin

