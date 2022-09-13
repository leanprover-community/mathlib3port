/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals in `fin n`

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Finₓ Function

open BigOperators

variable (n : ℕ)

instance : LocallyFiniteOrder (Finₓ n) :=
  OrderIso.locallyFiniteOrder Finₓ.orderIsoSubtype

instance : LocallyFiniteOrderBot (Finₓ n) :=
  OrderIso.locallyFiniteOrderBot Finₓ.orderIsoSubtype

instance : ∀ n, LocallyFiniteOrderTop (Finₓ n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | n + 1 => inferInstance

namespace Finₓ

variable {n} (a b : Finₓ n)

theorem Icc_eq_finset_subtype : icc a b = (icc (a : ℕ) b).Fin n :=
  rfl

theorem Ico_eq_finset_subtype : ico a b = (ico (a : ℕ) b).Fin n :=
  rfl

theorem Ioc_eq_finset_subtype : ioc a b = (ioc (a : ℕ) b).Fin n :=
  rfl

theorem Ioo_eq_finset_subtype : ioo a b = (ioo (a : ℕ) b).Fin n :=
  rfl

@[simp]
theorem map_subtype_embedding_Icc : (icc a b).map Finₓ.coeEmbedding = icc a b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]

@[simp]
theorem map_subtype_embedding_Ico : (ico a b).map Finₓ.coeEmbedding = ico a b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem map_subtype_embedding_Ioc : (ioc a b).map Finₓ.coeEmbedding = ioc a b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]

@[simp]
theorem map_subtype_embedding_Ioo : (ioo a b).map Finₓ.coeEmbedding = ioo a b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem card_Icc : (icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]

@[simp]
theorem card_Ico : (ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]

@[simp]
theorem card_Ioc : (ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]

@[simp]
theorem card_Ioo : (ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_of_finset]

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_of_finset]

theorem Ici_eq_finset_subtype : ici a = (icc (a : ℕ) n).Fin n := by
  ext
  simp

theorem Ioi_eq_finset_subtype : ioi a = (ioc (a : ℕ) n).Fin n := by
  ext
  simp

theorem Iic_eq_finset_subtype : iic b = (iic (b : ℕ)).Fin n :=
  rfl

theorem Iio_eq_finset_subtype : iio b = (iio (b : ℕ)).Fin n :=
  rfl

@[simp]
theorem map_subtype_embedding_Ici : (ici a).map Finₓ.coeEmbedding = icc a (n - 1) := by
  ext x
  simp only [exists_propₓ, embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
    
  cases n
  · exact Finₓ.elim0 a
    
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iffₓ.2 hx.2⟩, hx.1, rfl⟩
    

@[simp]
theorem map_subtype_embedding_Ioi : (ioi a).map Finₓ.coeEmbedding = ioc a (n - 1) := by
  ext x
  simp only [exists_propₓ, embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
    
  cases n
  · exact Finₓ.elim0 a
    
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iffₓ.2 hx.2⟩, hx.1, rfl⟩
    

@[simp]
theorem map_subtype_embedding_Iic : (iic b).map Finₓ.coeEmbedding = iic b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]

@[simp]
theorem map_subtype_embedding_Iio : (iio b).map Finₓ.coeEmbedding = iio b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]

@[simp]
theorem card_Ici : (ici a).card = n - a := by
  cases n
  · exact Finₓ.elim0 a
    
  rw [← card_map, map_subtype_embedding_Ici, Nat.card_Icc]
  rfl

@[simp]
theorem card_Ioi : (ioi a).card = n - 1 - a := by
  rw [← card_map, map_subtype_embedding_Ioi, Nat.card_Ioc]

@[simp]
theorem card_Iic : (iic b).card = b + 1 := by
  rw [← Nat.card_Iic b, ← map_subtype_embedding_Iic, card_map]

@[simp]
theorem card_Iio : (iio b).card = b := by
  rw [← Nat.card_Iio b, ← map_subtype_embedding_Iio, card_map]

@[simp]
theorem card_fintype_Ici : Fintype.card (Set.Ici a) = n - a := by
  rw [Fintype.card_of_finset, card_Ici]

@[simp]
theorem card_fintype_Ioi : Fintype.card (Set.Ioi a) = n - 1 - a := by
  rw [Fintype.card_of_finset, card_Ioi]

@[simp]
theorem card_fintype_Iic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_of_finset, card_Iic]

@[simp]
theorem card_fintype_Iio : Fintype.card (Set.Iio b) = b := by
  rw [Fintype.card_of_finset, card_Iio]

end Finₓ

