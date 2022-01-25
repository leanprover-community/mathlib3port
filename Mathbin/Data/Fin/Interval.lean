import Mathbin.Data.Nat.Interval

/-!
# Finite intervals in `fin n`

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Finₓ

open_locale BigOperators

variable (n : ℕ)

instance : LocallyFiniteOrder (Finₓ n) :=
  Subtype.locallyFiniteOrder _

namespace Finₓ

section Bounded

variable {n} (a b : Finₓ n)

theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).Subtype fun x => x < n :=
  rfl

theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).Subtype fun x => x < n :=
  rfl

theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).Subtype fun x => x < n :=
  rfl

theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).Subtype fun x => x < n :=
  rfl

@[simp]
theorem map_subtype_embedding_Icc : (Icc a b).map (Function.Embedding.subtype _) = Icc (a : ℕ) b :=
  map_subtype_embedding_Icc _ _ _ fun _ c x _ hx _ => hx.trans_lt

@[simp]
theorem map_subtype_embedding_Ico : (Ico a b).map (Function.Embedding.subtype _) = Ico (a : ℕ) b :=
  map_subtype_embedding_Ico _ _ _ fun _ c x _ hx _ => hx.trans_lt

@[simp]
theorem map_subtype_embedding_Ioc : (Ioc a b).map (Function.Embedding.subtype _) = Ioc (a : ℕ) b :=
  map_subtype_embedding_Ioc _ _ _ fun _ c x _ hx _ => hx.trans_lt

@[simp]
theorem map_subtype_embedding_Ioo : (Ioo a b).map (Function.Embedding.subtype _) = Ioo (a : ℕ) b :=
  map_subtype_embedding_Ioo _ _ _ fun _ c x _ hx _ => hx.trans_lt

@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a := by
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

end Bounded

section Unbounded

variable {n} (a b : Finₓ (n + 1))

theorem Ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) (n + 1)).Subtype fun x => x < n + 1 := by
  ext x
  simp only [mem_subtype, mem_Ici, mem_Icc, coe_fin_le, iff_self_and]
  exact fun _ => x.2.le

theorem Ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) (n + 1)).Subtype fun x => x < n + 1 := by
  ext x
  simp only [mem_subtype, mem_Ioi, mem_Ioc, coe_fin_lt, iff_self_and]
  exact fun _ => x.2.le

theorem Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).Subtype fun x => x < n + 1 :=
  rfl

theorem Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).Subtype fun x => x < n + 1 :=
  rfl

@[simp]
theorem map_subtype_embedding_Ici : (Ici a).map (Function.Embedding.subtype _) = Icc a n := by
  ext x
  simp only [exists_prop, Function.Embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, Nat.lt_succ_iffₓ.1 x.2⟩
    
  · rintro hx
    exact ⟨⟨x, Nat.lt_succ_iffₓ.2 hx.2⟩, hx.1, rfl⟩
    

@[simp]
theorem map_subtype_embedding_Ioi : (Ioi a).map (Function.Embedding.subtype _) = Ioc a n := by
  ext x
  simp only [exists_prop, Function.Embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  refine' ⟨_, fun hx => ⟨⟨x, Nat.lt_succ_iffₓ.2 hx.2⟩, hx.1, rfl⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨hx, Nat.lt_succ_iffₓ.1 x.2⟩

@[simp]
theorem map_subtype_embedding_Iic : (Iic b).map (Function.Embedding.subtype _) = Iic b := by
  ext x
  simp only [exists_prop, Function.Embedding.coe_subtype, mem_Iic, mem_map]
  refine' ⟨_, fun hx => ⟨⟨x, hx.trans_lt b.2⟩, hx, rfl⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact hx

@[simp]
theorem map_subtype_embedding_Iio : (Iio b).map (Function.Embedding.subtype _) = Iio b := by
  ext x
  simp only [exists_prop, Function.Embedding.coe_subtype, mem_Iio, mem_map]
  refine' ⟨_, fun hx => ⟨⟨x, hx.trans b.2⟩, hx, rfl⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact hx

@[simp]
theorem card_Ici : (Ici a).card = n + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Ici, card_map]

@[simp]
theorem card_Ioi : (Ioi a).card = n - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioi, card_map]

@[simp]
theorem card_Iic : (Iic b).card = b + 1 := by
  rw [← Nat.card_Iic b, ← map_subtype_embedding_Iic, card_map]

@[simp]
theorem card_Iio : (Iio b).card = b := by
  rw [← Nat.card_Iio b, ← map_subtype_embedding_Iio, card_map]

@[simp]
theorem card_fintype_Ici : Fintype.card (Set.Ici a) = n + 1 - a := by
  rw [Fintype.card_of_finset, card_Ici]

@[simp]
theorem card_fintype_Ioi : Fintype.card (Set.Ioi a) = n - a := by
  rw [Fintype.card_of_finset, card_Ioi]

@[simp]
theorem card_fintype_Iic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_of_finset, card_Iic]

@[simp]
theorem card_fintype_Iio : Fintype.card (Set.Iio b) = b := by
  rw [Fintype.card_of_finset, card_Iio]

end Unbounded

section Filter

variable {n} (a b : Finₓ n)

@[simp]
theorem card_filter_lt : (Finset.univ.filter fun j => a < j).card = n - a - 1 := by
  cases n
  · simp
    
  · rw [filter_lt_eq_Ioi, card_Ioi, tsub_tsub]
    exact (add_tsub_add_eq_tsub_right _ 1 _).symm
    

@[simp]
theorem card_filter_le : (univ.filter fun j => a ≤ j).card = n - a := by
  cases n
  · simp
    
  · rw [filter_le_eq_Ici, card_Ici]
    

@[simp]
theorem card_filter_gt : (Finset.univ.filter fun j => j < a).card = a := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_gt_eq_Iio, card_Iio]
    

@[simp]
theorem card_filter_ge : (Finset.univ.filter fun j => j ≤ a).card = a + 1 := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_ge_eq_Iic, card_Iic]
    

@[simp]
theorem card_filter_lt_lt : (Finset.univ.filter fun j => a < j ∧ j < b).card = b - a - 1 := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_lt_lt_eq_Ioo, card_Ioo]
    

@[simp]
theorem card_filter_lt_le : (Finset.univ.filter fun j => a < j ∧ j ≤ b).card = b - a := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_lt_le_eq_Ioc, card_Ioc]
    

@[simp]
theorem card_filter_le_lt : (Finset.univ.filter fun j => a ≤ j ∧ j < b).card = b - a := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_le_lt_eq_Ico, card_Ico]
    

@[simp]
theorem card_filter_le_le : (Finset.univ.filter fun j => a ≤ j ∧ j ≤ b).card = b + 1 - a := by
  cases n
  · exact Finₓ.elim0 a
    
  · rw [filter_le_le_eq_Icc, card_Icc]
    

theorem prod_filter_lt_mul_neg_eq_prod_off_diag {R : Type _} [CommMonoidₓ R] {n : ℕ} {f : Finₓ n → Finₓ n → R} :
    (∏ i, ∏ j in univ.filter fun j => i < j, f j i * f i j) = ∏ i, ∏ j in univ.filter fun j => i ≠ j, f j i := by
  simp_rw [ne_iff_lt_or_gtₓ, Or.comm, filter_or, prod_mul_distrib]
  have : ∀ i : Finₓ n, Disjoint (filter (Gt i) univ) (filter (LT.lt i) univ) := by
    simp_rw [disjoint_filter]
    intro i x y
    apply lt_asymmₓ
  simp only [prod_union, this, prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine' prod_bij' (fun i hi => ⟨i.2, i.1⟩) _ _ (fun i hi => ⟨i.2, i.1⟩) _ _ _ <;> simp

end Filter

end Finₓ

