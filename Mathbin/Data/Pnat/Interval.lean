/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Pnat.Defs

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Pnat

instance : LocallyFiniteOrder ℕ+ :=
  Subtype.locallyFiniteOrder _

namespace Pnat

variable (a b : ℕ+)

theorem Icc_eq_finset_subtype : icc a b = (icc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Icc_eq_finset_subtype Pnat.Icc_eq_finset_subtype

theorem Ico_eq_finset_subtype : ico a b = (ico (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ico_eq_finset_subtype Pnat.Ico_eq_finset_subtype

theorem Ioc_eq_finset_subtype : ioc a b = (ioc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioc_eq_finset_subtype Pnat.Ioc_eq_finset_subtype

theorem Ioo_eq_finset_subtype : ioo a b = (ioo (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioo_eq_finset_subtype Pnat.Ioo_eq_finset_subtype

theorem map_subtype_embedding_Icc : (icc a b).map (Function.Embedding.subtype _) = icc (a : ℕ) b :=
  map_subtype_embedding_Icc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Icc Pnat.map_subtype_embedding_Icc

theorem map_subtype_embedding_Ico : (ico a b).map (Function.Embedding.subtype _) = ico (a : ℕ) b :=
  map_subtype_embedding_Ico _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ico Pnat.map_subtype_embedding_Ico

theorem map_subtype_embedding_Ioc : (ioc a b).map (Function.Embedding.subtype _) = ioc (a : ℕ) b :=
  map_subtype_embedding_Ioc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioc Pnat.map_subtype_embedding_Ioc

theorem map_subtype_embedding_Ioo : (ioo a b).map (Function.Embedding.subtype _) = ioo (a : ℕ) b :=
  map_subtype_embedding_Ioo _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioo Pnat.map_subtype_embedding_Ioo

@[simp]
theorem card_Icc : (icc a b).card = b + 1 - a := by rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]
#align pnat.card_Icc Pnat.card_Icc

@[simp]
theorem card_Ico : (ico a b).card = b - a := by rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]
#align pnat.card_Ico Pnat.card_Ico

@[simp]
theorem card_Ioc : (ioc a b).card = b - a := by rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]
#align pnat.card_Ioc Pnat.card_Ioc

@[simp]
theorem card_Ioo : (ioo a b).card = b - a - 1 := by rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]
#align pnat.card_Ioo Pnat.card_Ioo

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.IccCat a b) = b + 1 - a := by rw [← card_Icc, Fintype.card_of_finset]
#align pnat.card_fintype_Icc Pnat.card_fintype_Icc

@[simp]
theorem card_fintype_Ico : Fintype.card (Set.IcoCat a b) = b - a := by rw [← card_Ico, Fintype.card_of_finset]
#align pnat.card_fintype_Ico Pnat.card_fintype_Ico

@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.IocCat a b) = b - a := by rw [← card_Ioc, Fintype.card_of_finset]
#align pnat.card_fintype_Ioc Pnat.card_fintype_Ioc

@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.IooCat a b) = b - a - 1 := by rw [← card_Ioo, Fintype.card_of_finset]
#align pnat.card_fintype_Ioo Pnat.card_fintype_Ioo

end Pnat

