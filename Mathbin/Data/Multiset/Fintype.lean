/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.BigOperators.Default

/-!
# Multiset coercion to type

This module defines a `has_coe_to_sort` instance for multisets and gives it a `fintype` instance.
It also defines `multiset.to_enum_finset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`finset` theory.

## Main definitions

* A coercion from `m : multiset α` to a `Type*`. For `x : m`, then there is a coercion `↑x : α`,
  and `x.2` is a term of `fin (m.count x)`. The second component is what ensures each term appears
  with the correct multiplicity. Note that this coercion requires `decidable_eq α` due to
  `multiset.count`.
* `multiset.to_enum_finset` is a `finset` version of this.
* `multiset.coe_embedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `multiset.coe_equiv` is the equivalence `m ≃ m.to_enum_finset`.

## Tags

multiset enumeration
-/


open BigOperators

variable {α : Type _} [DecidableEq α] {m : Multiset α}

/-- Auxiliary definition for the `has_coe_to_sort` instance. This prevents the `has_coe m α`
instance from inadverently applying to other sigma types. One should not use this definition
directly. -/
@[nolint has_nonempty_instance]
def Multiset.ToType (m : Multiset α) : Type _ :=
  Σx : α, Finₓ (m.count x)

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times with different values of `i`. -/
instance : CoeSort (Multiset α) (Type _) :=
  ⟨Multiset.ToType⟩

@[simp]
theorem Multiset.coe_sort_eq : m.ToType = m :=
  rfl

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, matchPattern]
def Multiset.mkToType (m : Multiset α) (x : α) (i : Finₓ (m.count x)) : m :=
  ⟨x, i⟩

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance Multiset.hasCoeToSort.hasCoe : Coe m α :=
  ⟨fun x => x.1⟩

@[simp]
theorem Multiset.fst_coe_eq_coe {x : m} : x.1 = x :=
  rfl

@[simp]
theorem Multiset.coe_eq {x y : m} : (x : α) = (y : α) ↔ x.1 = y.1 := by
  cases x
  cases y
  rfl

@[simp]
theorem Multiset.coe_mk {x : α} {i : Finₓ (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl

@[simp]
theorem Multiset.coe_mem {x : m} : ↑x ∈ m :=
  Multiset.count_pos.mp (pos_of_gt x.2.2)

@[simp]
protected theorem Multiset.forall_coe (p : m → Prop) : (∀ x : m, p x) ↔ ∀ (x : α) (i : Finₓ (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall

@[simp]
protected theorem Multiset.exists_coe (p : m → Prop) : (∃ x : m, p x) ↔ ∃ (x : α)(i : Finₓ (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists

instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset (m.toFinset.bUnion fun x => (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩)
    (by
      rintro ⟨x, i⟩
      simp only [← Finset.mem_bUnion, ← Multiset.mem_to_finset, ← Finset.mem_map, ← Finset.mem_range, ←
        Function.Embedding.coe_fn_mk, ← Prod.mk.inj_iff, ← exists_prop, ← exists_eq_right_rightₓ, ← Set.mem_set_of_eq, ←
        and_iff_right_iff_imp]
      exact fun h => multiset.count_pos.mp (pos_of_gt h))

/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `finset`. -/
def Multiset.toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset

@[simp]
theorem Multiset.mem_to_enum_finset (m : Multiset α) (p : α × ℕ) : p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_to_finset

theorem Multiset.mem_of_mem_to_enum_finset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  Multiset.count_pos.mp <| pos_of_gt <| (m.mem_to_enum_finset p).mp h

@[mono]
theorem Multiset.to_enum_finset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) : m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  simp only [← Multiset.mem_to_enum_finset]
  exact gt_of_ge_of_gtₓ (multiset.le_iff_count.mp h p.1)

@[simp]
theorem Multiset.to_enum_finset_subset_iff {m₁ m₂ : Multiset α} : m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ := by
  refine' ⟨fun h => _, Multiset.to_enum_finset_mono⟩
  rw [Multiset.le_iff_count]
  intro x
  by_cases' hx : x ∈ m₁
  · apply Nat.le_of_pred_lt
    have : (x, m₁.count x - 1) ∈ m₁.to_enum_finset := by
      rw [Multiset.mem_to_enum_finset]
      exact Nat.pred_ltₓ (ne_of_gtₓ (multiset.count_pos.mpr hx))
    simpa only [← Multiset.mem_to_enum_finset] using h this
    
  · simp [← hx]
    

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.

If you are looking for the function `m → α`, that would be plain `coe`. -/
@[simps]
def Multiset.coeEmbedding (m : Multiset α) : m ↪ α × ℕ where
  toFun := fun x => (x, x.2)
  inj' := by
    rintro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    simp only [← Prod.mk.inj_iff, ← Sigma.mk.inj_iff, ← and_imp, ← Multiset.coe_eq, ← Finₓ.coe_mk]
    rintro rfl rfl
    exact ⟨rfl, HEq.rfl⟩

/-- Another way to coerce a `multiset` to a type is to go through `m.to_enum_finset` and coerce
that `finset` to a type. -/
@[simps]
def Multiset.coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where
  toFun := fun x =>
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_to_enum_finset]
      exact x.2.2⟩
  invFun := fun x =>
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_to_enum_finset]
      exact x.2⟩
  left_inv := by
    rintro ⟨x, i, h⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, i⟩, h⟩
    rfl

@[simp]
theorem Multiset.to_embedding_coe_equiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by
  ext <;> simp

instance Multiset.fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

theorem Multiset.map_univ_coe_embedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  simp only [← Finₓ.exists_iff, ← Finset.mem_map, ← Finset.mem_univ, ← Multiset.coe_embedding_apply, ← Prod.mk.inj_iff,
    ← exists_true_left, ← Multiset.exists_coe, ← Multiset.coe_mk, ← Finₓ.coe_mk, ← exists_prop, ←
    exists_eq_right_rightₓ, ← exists_eq_right, ← Multiset.mem_to_enum_finset, ← iff_selfₓ, ← true_andₓ]

theorem Multiset.to_enum_finset_filter_eq (m : Multiset α) (x : α) :
    (m.toEnumFinset.filter fun p => x = p.1) = (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩ := by
  ext ⟨y, i⟩
  simp only [← eq_comm, ← Finset.mem_filter, ← Multiset.mem_to_enum_finset, ← Finset.mem_map, ← Finset.mem_range, ←
    Function.Embedding.coe_fn_mk, ← Prod.mk.inj_iff, ← exists_prop, ← exists_eq_right_right'ₓ, ← And.congr_left_iff]
  rintro rfl
  rfl

@[simp]
theorem Multiset.map_to_enum_finset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m := by
  ext x
  simp only [← Multiset.count_map, Finset.filter_val, ← Multiset.to_enum_finset_filter_eq, ← Finset.map_val, ←
    Finset.range_coe, ← Multiset.card_map, ← Multiset.card_range]

@[simp]
theorem Multiset.image_to_enum_finset_fst (m : Multiset α) : m.toEnumFinset.Image Prod.fst = m.toFinset := by
  rw [Finset.image, Multiset.map_to_enum_finset_fst]

@[simp]
theorem Multiset.map_univ_coe (m : Multiset α) : (Finset.univ : Finset m).val.map coe = m := by
  have := m.map_to_enum_finset_fst
  rw [← m.map_univ_coe_embedding] at this
  simpa only [← Finset.map_val, ← Multiset.coe_embedding_apply, ← Multiset.map_map, ← Function.comp_app] using this

@[simp]
theorem Multiset.map_univ {β : Type _} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun x => f x) = m.map f := by
  rw [← Multiset.map_map, Multiset.map_univ_coe]

@[simp]
theorem Multiset.card_to_enum_finset (m : Multiset α) : m.toEnumFinset.card = m.card := by
  change Multiset.card _ = _
  convert_to (m.to_enum_finset.val.map Prod.fst).card = _
  · rw [Multiset.card_map]
    
  · rw [m.map_to_enum_finset_fst]
    

@[simp]
theorem Multiset.card_coe (m : Multiset α) : Fintype.card m = m.card := by
  rw [Fintype.card_congr m.coe_equiv]
  simp

@[to_additive]
theorem Multiset.prod_eq_prod_coe [CommMonoidₓ α] (m : Multiset α) : m.Prod = ∏ x : m, x := by
  congr
  simp

@[to_additive]
theorem Multiset.prod_eq_prod_to_enum_finset [CommMonoidₓ α] (m : Multiset α) : m.Prod = ∏ x in m.toEnumFinset, x.1 :=
  by
  congr
  simp

@[to_additive]
theorem Multiset.prod_to_enum_finset {β : Type _} [CommMonoidₓ β] (m : Multiset α) (f : α → ℕ → β) :
    (∏ x in m.toEnumFinset, f x.1 x.2) = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coe_equiv (fun x => f x x.2) fun x => f x.1.1 x.1.2]
  · rw [← m.to_enum_finset.prod_coe_sort fun x => f x.1 x.2]
    simp
    
  · simp
    

