/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.multiset.fintype
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Prod.Lex

/-!
# Multiset coercion to type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Multiset.ToType /-
/-- Auxiliary definition for the `has_coe_to_sort` instance. This prevents the `has_coe m α`
instance from inadverently applying to other sigma types. One should not use this definition
directly. -/
@[nolint has_nonempty_instance]
def Multiset.ToType (m : Multiset α) : Type _ :=
  Σx : α, Fin (m.count x)
#align multiset.to_type Multiset.ToType
-/

/-- Create a type that has the same number of elements as the multiset.
Terms of this type are triples `⟨x, ⟨i, h⟩⟩` where `x : α`, `i : ℕ`, and `h : i < m.count x`.
This way repeated elements of a multiset appear multiple times with different values of `i`. -/
instance : CoeSort (Multiset α) (Type _) :=
  ⟨Multiset.ToType⟩

/- warning: multiset.coe_sort_eq clashes with [anonymous] -> [anonymous]
warning: multiset.coe_sort_eq -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DecidableEq.{succ u_1} α] {m : Multiset.{u_1} α}, Eq.{succ (succ u_1)} Type.{u_1} (Multiset.ToType.{u_1} α (fun (a : α) (b : α) => _inst_1 a b) m) (coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m)
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align multiset.coe_sort_eq [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] : m.to_type = m :=
  rfl
#align multiset.coe_sort_eq [anonymous]

#print Multiset.mkToType /-
/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
def Multiset.mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩
#align multiset.mk_to_type Multiset.mkToType
-/

/-- As a convenience, there is a coercion from `m : Type*` to `α` by projecting onto the first
component. -/
instance instCoeSortMultisetType.instCoeOutToType : Coe m α :=
  ⟨fun x => x.1⟩
#align multiset.has_coe_to_sort.has_coe instCoeSortMultisetType.instCoeOutToTypeₓ

/- warning: multiset.fst_coe_eq_coe clashes with [anonymous] -> [anonymous]
warning: multiset.fst_coe_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DecidableEq.{succ u_1} α] {m : Multiset.{u_1} α} {x : coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m}, Eq.{succ u_1} α (Sigma.fst.{u_1, 0} α (fun (x : α) => Fin (Multiset.count.{u_1} α (fun (a : α) (b : α) => (fun (a : α) (b : α) => (fun (a : α) (b : α) => _inst_1 a b) a b) a b) x m)) x) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m) α (HasLiftT.mk.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m) α (CoeTCₓ.coe.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m) α (coeBase.{succ u_1, succ u_1} (coeSort.{succ u_1, succ (succ u_1)} (Multiset.{u_1} α) Type.{u_1} (Multiset.hasCoeToSort.{u_1} α (fun (a : α) (b : α) => _inst_1 a b)) m) α (instCoeSortMultisetType.instCoeOutToTypeₓ.{u_1} α (fun (a : α) (b : α) => _inst_1 a b) m)))) x)
but is expected to have type
  forall {α : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> α -> _inst_1) -> Nat -> (List.{u} α) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align multiset.fst_coe_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {x : m} : x.1 = x :=
  rfl
#align multiset.fst_coe_eq_coe [anonymous]

#print Multiset.coe_eq /-
@[simp]
theorem Multiset.coe_eq {x y : m} : (x : α) = (y : α) ↔ x.1 = y.1 :=
  by
  cases x
  cases y
  rfl
#align multiset.coe_eq Multiset.coe_eq
-/

#print Multiset.coe_mk /-
@[simp]
theorem Multiset.coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl
#align multiset.coe_mk Multiset.coe_mk
-/

#print Multiset.coe_mem /-
@[simp]
theorem Multiset.coe_mem {x : m} : ↑x ∈ m :=
  Multiset.count_pos.mp (pos_of_gt x.2.2)
#align multiset.coe_mem Multiset.coe_mem
-/

#print Multiset.forall_coe /-
@[simp]
protected theorem Multiset.forall_coe (p : m → Prop) :
    (∀ x : m, p x) ↔ ∀ (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall
#align multiset.forall_coe Multiset.forall_coe
-/

#print Multiset.exists_coe /-
@[simp]
protected theorem Multiset.exists_coe (p : m → Prop) :
    (∃ x : m, p x) ↔ ∃ (x : α)(i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists
#align multiset.exists_coe Multiset.exists_coe
-/

instance : Fintype { p : α × ℕ | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.bunionᵢ fun x => (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩)
    (by
      rintro ⟨x, i⟩
      simp only [Finset.mem_bunionᵢ, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk.inj_iff, exists_prop, exists_eq_right_right,
        Set.mem_setOf_eq, and_iff_right_iff_imp]
      exact fun h => multiset.count_pos.mp (pos_of_gt h))

#print Multiset.toEnumFinset /-
/-- Construct a finset whose elements enumerate the elements of the multiset `m`.
The `ℕ` component is used to differentiate between equal elements: if `x` appears `n` times
then `(x, 0)`, ..., and `(x, n-1)` appear in the `finset`. -/
def Multiset.toEnumFinset (m : Multiset α) : Finset (α × ℕ) :=
  { p : α × ℕ | p.2 < m.count p.1 }.toFinset
#align multiset.to_enum_finset Multiset.toEnumFinset
-/

#print Multiset.mem_toEnumFinset /-
@[simp]
theorem Multiset.mem_toEnumFinset (m : Multiset α) (p : α × ℕ) :
    p ∈ m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset
#align multiset.mem_to_enum_finset Multiset.mem_toEnumFinset
-/

#print Multiset.mem_of_mem_toEnumFinset /-
theorem Multiset.mem_of_mem_toEnumFinset {p : α × ℕ} (h : p ∈ m.toEnumFinset) : p.1 ∈ m :=
  Multiset.count_pos.mp <| pos_of_gt <| (m.mem_toEnumFinset p).mp h
#align multiset.mem_of_mem_to_enum_finset Multiset.mem_of_mem_toEnumFinset
-/

/- warning: multiset.to_enum_finset_mono -> Multiset.toEnumFinset_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m₁ : Multiset.{u1} α} {m₂ : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) m₁ m₂) -> (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} α Nat)) (Finset.hasSubset.{u1} (Prod.{u1, 0} α Nat)) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₁) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m₁ : Multiset.{u1} α} {m₂ : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) m₁ m₂) -> (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} α Nat)) (Finset.instHasSubsetFinset.{u1} (Prod.{u1, 0} α Nat)) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₁) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₂))
Case conversion may be inaccurate. Consider using '#align multiset.to_enum_finset_mono Multiset.toEnumFinset_monoₓ'. -/
@[mono]
theorem Multiset.toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ ≤ m₂) :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset := by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact gt_of_ge_of_gt (multiset.le_iff_count.mp h p.1)
#align multiset.to_enum_finset_mono Multiset.toEnumFinset_mono

/- warning: multiset.to_enum_finset_subset_iff -> Multiset.toEnumFinset_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m₁ : Multiset.{u1} α} {m₂ : Multiset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} α Nat)) (Finset.hasSubset.{u1} (Prod.{u1, 0} α Nat)) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₁) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₂)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) m₁ m₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m₁ : Multiset.{u1} α} {m₂ : Multiset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} α Nat)) (Finset.instHasSubsetFinset.{u1} (Prod.{u1, 0} α Nat)) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₁) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m₂)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align multiset.to_enum_finset_subset_iff Multiset.toEnumFinset_subset_iffₓ'. -/
@[simp]
theorem Multiset.toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset ⊆ m₂.toEnumFinset ↔ m₁ ≤ m₂ :=
  by
  refine' ⟨fun h => _, Multiset.toEnumFinset_mono⟩
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ m₁
  · apply Nat.le_of_pred_lt
    have : (x, m₁.count x - 1) ∈ m₁.to_enum_finset :=
      by
      rw [Multiset.mem_toEnumFinset]
      exact Nat.pred_lt (ne_of_gt (multiset.count_pos.mpr hx))
    simpa only [Multiset.mem_toEnumFinset] using h this
  · simp [hx]
#align multiset.to_enum_finset_subset_iff Multiset.toEnumFinset_subset_iff

#print Multiset.coeEmbedding /-
/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.

If you are looking for the function `m → α`, that would be plain `coe`. -/
@[simps]
def Multiset.coeEmbedding (m : Multiset α) : m ↪ α × ℕ
    where
  toFun x := (x, x.2)
  inj' := by
    rintro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    simp only [Prod.mk.inj_iff, Sigma.mk.inj_iff, and_imp, Multiset.coe_eq, Fin.val_mk]
    rintro rfl rfl
    exact ⟨rfl, HEq.rfl⟩
#align multiset.coe_embedding Multiset.coeEmbedding
-/

#print Multiset.coeEquiv /-
/-- Another way to coerce a `multiset` to a type is to go through `m.to_enum_finset` and coerce
that `finset` to a type. -/
@[simps]
def Multiset.coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset
    where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩
  left_inv := by
    rintro ⟨x, i, h⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, i⟩, h⟩
    rfl
#align multiset.coe_equiv Multiset.coeEquiv
-/

#print Multiset.toEmbedding_coeEquiv_trans /-
@[simp]
theorem Multiset.toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> simp
#align multiset.to_embedding_coe_equiv_trans Multiset.toEmbedding_coeEquiv_trans
-/

#print Multiset.fintypeCoe /-
instance Multiset.fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm
#align multiset.fintype_coe Multiset.fintypeCoe
-/

#print Multiset.map_univ_coeEmbedding /-
theorem Multiset.map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset :=
  by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk.inj_iff, exists_true_left, Multiset.exists_coe, Multiset.coe_mk, Fin.val_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, iff_self_iff,
    true_and_iff]
#align multiset.map_univ_coe_embedding Multiset.map_univ_coeEmbedding
-/

#print Multiset.toEnumFinset_filter_eq /-
theorem Multiset.toEnumFinset_filter_eq (m : Multiset α) (x : α) :
    (m.toEnumFinset.filterₓ fun p => x = p.1) =
      (Finset.range (m.count x)).map ⟨Prod.mk x, Prod.mk.inj_left x⟩ :=
  by
  ext ⟨y, i⟩
  simp only [eq_comm, Finset.mem_filter, Multiset.mem_toEnumFinset, Finset.mem_map,
    Finset.mem_range, Function.Embedding.coeFn_mk, Prod.mk.inj_iff, exists_prop,
    exists_eq_right_right', and_congr_left_iff]
  rintro rfl
  rfl
#align multiset.to_enum_finset_filter_eq Multiset.toEnumFinset_filter_eq
-/

#print Multiset.map_toEnumFinset_fst /-
@[simp]
theorem Multiset.map_toEnumFinset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m :=
  by
  ext x
  simp only [Multiset.count_map, ← Finset.filter_val, Multiset.toEnumFinset_filter_eq,
    Finset.map_val, Finset.range_val, Multiset.card_map, Multiset.card_range]
#align multiset.map_to_enum_finset_fst Multiset.map_toEnumFinset_fst
-/

#print Multiset.image_toEnumFinset_fst /-
@[simp]
theorem Multiset.image_toEnumFinset_fst (m : Multiset α) :
    m.toEnumFinset.image Prod.fst = m.toFinset := by
  rw [Finset.image, Multiset.map_toEnumFinset_fst]
#align multiset.image_to_enum_finset_fst Multiset.image_toEnumFinset_fst
-/

#print Multiset.map_univ_coe /-
@[simp]
theorem Multiset.map_univ_coe (m : Multiset α) : (Finset.univ : Finset m).val.map coe = m :=
  by
  have := m.map_to_enum_finset_fst
  rw [← m.map_univ_coe_embedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this
#align multiset.map_univ_coe Multiset.map_univ_coe
-/

#print Multiset.map_univ /-
@[simp]
theorem Multiset.map_univ {β : Type _} (m : Multiset α) (f : α → β) :
    ((Finset.univ : Finset m).val.map fun x => f x) = m.map f := by
  rw [← Multiset.map_map, Multiset.map_univ_coe]
#align multiset.map_univ Multiset.map_univ
-/

/- warning: multiset.card_to_enum_finset -> Multiset.card_toEnumFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Prod.{u1, 0} α Nat) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Prod.{u1, 0} α Nat) (Multiset.toEnumFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m)
Case conversion may be inaccurate. Consider using '#align multiset.card_to_enum_finset Multiset.card_toEnumFinsetₓ'. -/
@[simp]
theorem Multiset.card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = m.card :=
  by
  change Multiset.card _ = _
  convert_to (m.to_enum_finset.val.map Prod.fst).card = _
  · rw [Multiset.card_map]
  · rw [m.map_to_enum_finset_fst]
#align multiset.card_to_enum_finset Multiset.card_toEnumFinset

/- warning: multiset.card_coe -> Multiset.card_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Multiset.{u1} α) Type.{u1} (Multiset.hasCoeToSort.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) m) (Multiset.fintypeCoe.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (m : Multiset.{u1} α), Eq.{1} Nat (Fintype.card.{u1} (Multiset.ToType.{u1} α (fun (a : α) (b : α) => (fun (a : α) (b : α) => _inst_1 a b) a b) m) (Multiset.fintypeCoe.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) m)
Case conversion may be inaccurate. Consider using '#align multiset.card_coe Multiset.card_coeₓ'. -/
@[simp]
theorem Multiset.card_coe (m : Multiset α) : Fintype.card m = m.card :=
  by
  rw [Fintype.card_congr m.coe_equiv]
  simp
#align multiset.card_coe Multiset.card_coe

#print Multiset.prod_eq_prod_coe /-
@[to_additive]
theorem Multiset.prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.Prod = ∏ x : m, x :=
  by
  congr
  simp
#align multiset.prod_eq_prod_coe Multiset.prod_eq_prod_coe
#align multiset.sum_eq_sum_coe Multiset.sum_eq_sum_coe
-/

#print Multiset.prod_eq_prod_toEnumFinset /-
@[to_additive]
theorem Multiset.prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.Prod = ∏ x in m.toEnumFinset, x.1 := by
  congr
  simp
#align multiset.prod_eq_prod_to_enum_finset Multiset.prod_eq_prod_toEnumFinset
#align multiset.sum_eq_sum_to_enum_finset Multiset.sum_eq_sum_toEnumFinset
-/

#print Multiset.prod_toEnumFinset /-
@[to_additive]
theorem Multiset.prod_toEnumFinset {β : Type _} [CommMonoid β] (m : Multiset α) (f : α → ℕ → β) :
    (∏ x in m.toEnumFinset, f x.1 x.2) = ∏ x : m, f x x.2 :=
  by
  rw [Fintype.prod_equiv m.coe_equiv (fun x => f x x.2) fun x => f x.1.1 x.1.2]
  · rw [← m.to_enum_finset.prod_coe_sort fun x => f x.1 x.2]
    simp
  · simp
#align multiset.prod_to_enum_finset Multiset.prod_toEnumFinset
#align multiset.sum_to_enum_finset Multiset.sum_toEnumFinset
-/

