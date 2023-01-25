/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.pnat.interval
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Pnat.Defs

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset PNat

instance : LocallyFiniteOrder ℕ+ :=
  Subtype.locallyFiniteOrder _

namespace PNat

variable (a b : ℕ+)

theorem icc_eq_finset_subtype : icc a b = (icc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Icc_eq_finset_subtype PNat.icc_eq_finset_subtype

theorem ico_eq_finset_subtype : ico a b = (ico (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ico_eq_finset_subtype PNat.ico_eq_finset_subtype

theorem ioc_eq_finset_subtype : ioc a b = (ioc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioc_eq_finset_subtype PNat.ioc_eq_finset_subtype

theorem ioo_eq_finset_subtype : ioo a b = (ioo (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioo_eq_finset_subtype PNat.ioo_eq_finset_subtype

theorem map_subtype_embedding_icc : (icc a b).map (Function.Embedding.subtype _) = icc (a : ℕ) b :=
  map_subtype_embedding_icc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Icc PNat.map_subtype_embedding_icc

theorem map_subtype_embedding_ico : (ico a b).map (Function.Embedding.subtype _) = ico (a : ℕ) b :=
  map_subtype_embedding_ico _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ico PNat.map_subtype_embedding_ico

theorem map_subtype_embedding_ioc : (ioc a b).map (Function.Embedding.subtype _) = ioc (a : ℕ) b :=
  map_subtype_embedding_ioc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioc PNat.map_subtype_embedding_ioc

theorem map_subtype_embedding_ioo : (ioo a b).map (Function.Embedding.subtype _) = ioo (a : ℕ) b :=
  map_subtype_embedding_ioo _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioo PNat.map_subtype_embedding_ioo

@[simp]
theorem card_icc : (icc a b).card = b + 1 - a := by
  rw [← Nat.card_icc, ← map_subtype_embedding_Icc, card_map]
#align pnat.card_Icc PNat.card_icc

@[simp]
theorem card_ico : (ico a b).card = b - a := by
  rw [← Nat.card_ico, ← map_subtype_embedding_Ico, card_map]
#align pnat.card_Ico PNat.card_ico

@[simp]
theorem card_ioc : (ioc a b).card = b - a := by
  rw [← Nat.card_ioc, ← map_subtype_embedding_Ioc, card_map]
#align pnat.card_Ioc PNat.card_ioc

@[simp]
theorem card_ioo : (ioo a b).card = b - a - 1 := by
  rw [← Nat.card_ioo, ← map_subtype_embedding_Ioo, card_map]
#align pnat.card_Ioo PNat.card_ioo

@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align pnat.card_fintype_Icc PNat.card_fintypeIcc

@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align pnat.card_fintype_Ico PNat.card_fintypeIco

@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioc PNat.card_fintypeIoc

@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioo PNat.card_fintypeIoo

end PNat

