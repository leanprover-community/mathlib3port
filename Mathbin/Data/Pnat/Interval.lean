import Mathbin.Data.Nat.Interval
import Mathbin.Data.Pnat.Basic

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

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl

theorem map_subtype_embedding_Icc : (Icc a b).map (Function.Embedding.subtype _) = Icc (a : ℕ) b :=
  map_subtype_embedding_Icc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ico : (Ico a b).map (Function.Embedding.subtype _) = Ico (a : ℕ) b :=
  map_subtype_embedding_Ico _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Function.Embedding.subtype _) = Ioc (a : ℕ) b :=
  map_subtype_embedding_Ioc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Function.Embedding.subtype _) = Ioo (a : ℕ) b :=
  map_subtype_embedding_Ioo _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx

@[simp]
theorem card_Icc : (Icc a b).card = (b+1) - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]

@[simp]
theorem card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]

@[simp]
theorem card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]

@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]

@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = (b+1) - a := by
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

end Pnat

