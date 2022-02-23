/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.BigOperators.Basic

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/


variable {α β : Type _} (f : α → β → β) (op : α → α → α)

namespace Multiset

/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀ b, f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val) (fun ⟨x, hx⟩ ⟨y, hy⟩ => comm x hx y hy) b

@[simp]
theorem noncomm_foldr_coe (l : List α)
    (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀ b, f x (f y b) = f y (f x b)) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b := by
  simp only [noncomm_foldr, coe_foldr, coe_attach, List.attach]
  rw [← List.foldr_map]
  simp [List.map_pmap, List.pmap_eq_map]

@[simp]
theorem noncomm_foldr_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀ b, f x (f y b) = f y (f x b))
    (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl

theorem noncomm_foldr_cons (s : Multiset α) (a : α)
    (h : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀ b, f x (f y b) = f y (f x b))
    (h' : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀ b, f x (f y b) = f y (f x b)) (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) := by
  induction s using Quotientₓ.induction_on
  simp

theorem noncomm_foldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
    noncommFoldr f s (fun x _ y _ => h x y) b = foldr f h b s := by
  induction s using Quotientₓ.induction_on
  simp

variable [assoc : IsAssociative α op]

include assoc

/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, op x y = op y x) (a : α) : α :=
  noncommFoldr op s
    (fun x hx y hy b => by
      rw [← assoc.assoc, comm _ hx _ hy, assoc.assoc])
    a

@[simp]
theorem noncomm_fold_coe (l : List α) (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀, op x y = op y x)
    (a : α) : noncommFold op (l : Multiset α) comm a = l.foldr op a := by
  simp [noncomm_fold]

@[simp]
theorem noncomm_fold_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀, op x y = op y x) (a : α) :
    noncommFold op (0 : Multiset α) h a = a :=
  rfl

theorem noncomm_fold_cons (s : Multiset α) (a : α) (h : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, op x y = op y x)
    (h' : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, op x y = op y x) (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) := by
  induction s using Quotientₓ.induction_on
  simp

theorem noncomm_fold_eq_fold (s : Multiset α) [IsCommutative α op] (a : α) :
    noncommFold op s (fun x _ y _ => IsCommutative.comm x y) a = fold op a s := by
  induction s using Quotientₓ.induction_on
  simp

omit assoc

variable [Monoidₓ α]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes\non all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute x y) : α :=
  s.noncommFold (· * ·) comm 1

@[simp, to_additive]
theorem noncomm_prod_coe (l : List α) (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀, Commute x y) :
    noncommProd (l : Multiset α) comm = l.Prod := by
  rw [noncomm_prod]
  simp only [noncomm_fold_coe]
  induction' l with hd tl hl
  · simp
    
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm x (List.mem_cons_of_memₓ _ hx) y (List.mem_cons_of_memₓ _ hy)
    

@[simp, to_additive]
theorem noncomm_prod_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀, Commute x y) :
    noncommProd (0 : Multiset α) h = 1 :=
  rfl

@[simp, to_additive]
theorem noncomm_prod_cons (s : Multiset α) (a : α) (comm : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, Commute x y) :
    noncommProd (a ::ₘ s) comm =
      a * noncommProd s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy) :=
  by
  induction s using Quotientₓ.induction_on
  simp

@[to_additive]
theorem noncomm_prod_cons' (s : Multiset α) (a : α) (comm : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, Commute x y) :
    noncommProd (a ::ₘ s) comm =
      (noncommProd s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) * a :=
  by
  induction' s using Quotientₓ.induction_on with s
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, List.prod_cons]
  induction' s with hd tl IH
  · simp
    
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm <;> simp
      
    · intro x hx y hy
      simp only [quot_mk_to_coe, List.mem_cons_iff, mem_coe, cons_coe] at hx hy
      apply comm
      · cases hx <;> simp [hx]
        
      · cases hy <;> simp [hy]
        
      
    

@[to_additive]
theorem noncomm_prod_eq_prod {α : Type _} [CommMonoidₓ α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ => Commute.all _ _) = prod s := by
  induction s using Quotientₓ.induction_on
  simp

end Multiset

namespace Finset

variable [Monoidₓ β]

/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,\ngiven a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y)) : β :=
  (s.1.map f).noncommProd
    (by
      simpa [Multiset.mem_map, ← Finset.mem_def] using comm)

@[simp, to_additive]
theorem noncomm_prod_to_finset [DecidableEq α] (l : List α) (f : α → β)
    (comm : ∀, ∀ x ∈ l.toFinset, ∀, ∀ y ∈ l.toFinset, ∀, Commute (f x) (f y)) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).Prod := by
  rw [← List.dedup_eq_self] at hl
  simp [noncomm_prod, hl]

@[simp, to_additive]
theorem noncomm_prod_empty (f : α → β) (h : ∀, ∀ x ∈ (∅ : Finset α), ∀, ∀ y ∈ (∅ : Finset α), ∀, Commute (f x) (f y)) :
    noncommProd (∅ : Finset α) f h = 1 :=
  rfl

@[simp, to_additive]
theorem noncomm_prod_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
    (comm : ∀, ∀ x ∈ insert a s, ∀, ∀ y ∈ insert a s, ∀, Commute (f x) (f y)) (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy) :=
  by
  simp [insert_val_of_not_mem ha, noncomm_prod]

@[to_additive]
theorem noncomm_prod_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
    (comm : ∀, ∀ x ∈ insert a s, ∀, ∀ y ∈ insert a s, ∀, Commute (f x) (f y)) (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      (noncommProd s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) * f a :=
  by
  simp [noncomm_prod, insert_val_of_not_mem ha, Multiset.noncomm_prod_cons']

@[simp, to_additive]
theorem noncomm_prod_singleton (a : α) (f : α → β) :
    (noncommProd ({a} : Finset α) f fun x hx y hy => by
        rw [mem_singleton.mp hx, mem_singleton.mp hy]) =
      f a :=
  by
  simp [noncomm_prod, Multiset.singleton_eq_cons]

@[to_additive]
theorem noncomm_prod_eq_prod {β : Type _} [CommMonoidₓ β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ => Commute.all _ _) = s.Prod f := by
  classical
  induction' s using Finset.induction_on with a s ha IH
  · simp
    
  · simp [ha, IH]
    

-- The non-commutative version of `finset.prod_union`
@[to_additive " The non-commutative version of `finset.sum_union` "]
theorem noncomm_prod_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t) (f : α → β)
    (comm : ∀, ∀ x ∈ s ∪ t, ∀, ∀ y ∈ s ∪ t, ∀, Commute (f x) (f y))
    (scomm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y) := fun _ hx _ hy =>
      comm _ (mem_union_left _ hx) _ (mem_union_left _ hy))
    (tcomm : ∀, ∀ x ∈ t, ∀, ∀ y ∈ t, ∀, Commute (f x) (f y) := fun _ hx _ hy =>
      comm _ (mem_union_right _ hx) _ (mem_union_right _ hy)) :
    noncommProd (s ∪ t) f comm = noncommProd s f scomm * noncommProd t f tcomm := by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_to_finset_iff_disjoint] at h
  simp [sl', tl', noncomm_prod_to_finset, ← List.prod_append, ← List.to_finset_append,
    List.nodup_append_of_nodup sl' tl' h]

end Finset

