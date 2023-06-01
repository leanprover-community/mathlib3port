/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.finset.noncomm_prod
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.Hom.Commute
import Mathbin.Algebra.BigOperators.Basic

/-!
# Products (respectively, sums) over a finset or a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


variable {F ι α β γ : Type _} (f : α → β → β) (op : α → α → α)

namespace Multiset

#print Multiset.noncommFoldr /-
/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise fun x y => ∀ b, f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val)
    (fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      haveI : IsRefl α fun x y => ∀ b, f x (f y b) = f y (f x b) := ⟨fun x b => rfl⟩
      comm.of_refl hx hy)
    b
#align multiset.noncomm_foldr Multiset.noncommFoldr
-/

@[simp]
theorem noncommFoldr_coe (l : List α) (comm) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b :=
  by
  simp only [noncomm_foldr, coe_foldr, coe_attach, List.attach]
  rw [← List.foldr_map]
  simp [List.map_pmap, List.pmap_eq_map]
#align multiset.noncomm_foldr_coe Multiset.noncommFoldr_coe

@[simp]
theorem noncommFoldr_empty (h) (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl
#align multiset.noncomm_foldr_empty Multiset.noncommFoldr_empty

theorem noncommFoldr_cons (s : Multiset α) (a : α) (h h') (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_cons Multiset.noncommFoldr_cons

theorem noncommFoldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
    noncommFoldr f s (fun x _ y _ _ => h x y) b = foldr f h b s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_eq_foldr Multiset.noncommFoldr_eq_foldr

variable [assoc : IsAssociative α op]

include assoc

#print Multiset.noncommFold /-
/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : { x | x ∈ s }.Pairwise fun x y => op x y = op y x) :
    α → α :=
  noncommFoldr op s fun x hx y hy h b => by rw [← assoc.assoc, comm hx hy h, assoc.assoc]
#align multiset.noncomm_fold Multiset.noncommFold
-/

#print Multiset.noncommFold_coe /-
@[simp]
theorem noncommFold_coe (l : List α) (comm) (a : α) :
    noncommFold op (l : Multiset α) comm a = l.foldr op a := by simp [noncomm_fold]
#align multiset.noncomm_fold_coe Multiset.noncommFold_coe
-/

#print Multiset.noncommFold_empty /-
@[simp]
theorem noncommFold_empty (h) (a : α) : noncommFold op (0 : Multiset α) h a = a :=
  rfl
#align multiset.noncomm_fold_empty Multiset.noncommFold_empty
-/

#print Multiset.noncommFold_cons /-
theorem noncommFold_cons (s : Multiset α) (a : α) (h h') (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_cons Multiset.noncommFold_cons
-/

#print Multiset.noncommFold_eq_fold /-
theorem noncommFold_eq_fold (s : Multiset α) [IsCommutative α op] (a : α) :
    noncommFold op s (fun x _ y _ _ => IsCommutative.comm x y) a = fold op a s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_eq_fold Multiset.noncommFold_eq_fold
-/

omit assoc

variable [Monoid α] [Monoid β]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes\non all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : { x | x ∈ s }.Pairwise Commute) : α :=
  s.noncommFold (· * ·) comm 1
#align multiset.noncomm_prod Multiset.noncommProd
#align multiset.noncomm_sum Multiset.noncommSum

@[simp, to_additive]
theorem noncommProd_coe (l : List α) (comm) : noncommProd (l : Multiset α) comm = l.Prod :=
  by
  rw [noncomm_prod]
  simp only [noncomm_fold_coe]
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
#align multiset.noncomm_prod_coe Multiset.noncommProd_coe
#align multiset.noncomm_sum_coe Multiset.noncommSum_coe

@[simp, to_additive]
theorem noncommProd_empty (h) : noncommProd (0 : Multiset α) h = 1 :=
  rfl
#align multiset.noncomm_prod_empty Multiset.noncommProd_empty
#align multiset.noncomm_sum_empty Multiset.noncommSum_empty

@[simp, to_additive]
theorem noncommProd_cons (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = a * noncommProd s (comm.mono fun _ => mem_cons_of_mem) := by
  induction s using Quotient.inductionOn; simp
#align multiset.noncomm_prod_cons Multiset.noncommProd_cons
#align multiset.noncomm_sum_cons Multiset.noncommSum_cons

@[to_additive]
theorem noncommProd_cons' (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = noncommProd s (comm.mono fun _ => mem_cons_of_mem) * a :=
  by
  induction' s using Quotient.inductionOn with s
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, List.prod_cons]
  induction' s with hd tl IH
  · simp
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm.of_refl <;> simp
    · intro x hx y hy
      simp only [quot_mk_to_coe, List.mem_cons, mem_coe, cons_coe] at hx hy 
      apply comm
      · cases hx <;> simp [hx]
      · cases hy <;> simp [hy]
#align multiset.noncomm_prod_cons' Multiset.noncommProd_cons'
#align multiset.noncomm_sum_cons' Multiset.noncommSum_cons'

@[to_additive]
theorem noncommProd_add (s t : Multiset α) (comm) :
    noncommProd (s + t) comm =
      noncommProd s (comm.mono <| subset_of_le <| s.le_add_right t) *
        noncommProd t (comm.mono <| subset_of_le <| t.le_add_left s) :=
  by rcases s with ⟨⟩; rcases t with ⟨⟩; simp
#align multiset.noncomm_prod_add Multiset.noncommProd_add
#align multiset.noncomm_sum_add Multiset.noncommSum_add

@[protected, to_additive]
theorem noncommProd_map_aux [MonoidHomClass F α β] (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise Commute) (f : F) : { x | x ∈ s.map f }.Pairwise Commute :=
  by
  simp only [Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
  exact (comm.of_refl hx hy).map f
#align multiset.noncomm_prod_map_aux Multiset.noncommProd_map_aux
#align multiset.noncomm_sum_map_aux Multiset.noncommSum_map_aux

@[to_additive]
theorem noncommProd_map [MonoidHomClass F α β] (s : Multiset α) (comm) (f : F) :
    f (s.noncommProd comm) = (s.map f).noncommProd (noncommProd_map_aux s comm f) :=
  by
  induction s using Quotient.inductionOn
  simpa using map_list_prod f _
#align multiset.noncomm_prod_map Multiset.noncommProd_map
#align multiset.noncomm_sum_map Multiset.noncommSum_map

@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Multiset α) (comm) (m : α) (h : ∀ x ∈ s, x = m) :
    s.noncommProd comm = m ^ s.card :=
  by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncomm_prod_coe, coe_card, mem_coe] at *
  exact List.prod_eq_pow_card _ m h
#align multiset.noncomm_prod_eq_pow_card Multiset.noncommProd_eq_pow_card
#align multiset.noncomm_sum_eq_card_nsmul Multiset.noncommSum_eq_card_nsmul

#print Multiset.noncommProd_eq_prod /-
@[to_additive]
theorem noncommProd_eq_prod {α : Type _} [CommMonoid α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ _ => Commute.all _ _) = prod s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_prod_eq_prod Multiset.noncommProd_eq_prod
#align multiset.noncomm_sum_eq_sum Multiset.noncommSum_eq_sum
-/

@[to_additive noncomm_sum_add_commute]
theorem noncommProd_commute (s : Multiset α) (comm) (y : α) (h : ∀ x ∈ s, Commute y x) :
    Commute y (s.noncommProd comm) :=
  by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncomm_prod_coe]
  exact Commute.list_prod_right _ _ h
#align multiset.noncomm_prod_commute Multiset.noncommProd_commute
#align multiset.noncomm_sum_add_commute Multiset.noncommSum_addCommute

end Multiset

namespace Finset

variable [Monoid β] [Monoid γ]

/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,\ngiven a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise fun a b => Commute (f a) (f b)) : β :=
  (s.1.map f).noncommProd <| by simp_rw [Multiset.mem_map]; rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _;
    exact comm.of_refl ha hb
#align finset.noncomm_prod Finset.noncommProd
#align finset.noncomm_sum Finset.noncommSum

@[congr, to_additive]
theorem noncommProd_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x)
    (comm) :
    noncommProd s₁ f comm =
      noncommProd s₂ g fun x hx y hy h => by rw [← h₂ _ hx, ← h₂ _ hy]; subst h₁;
        exact comm hx hy h :=
  by simp_rw [noncomm_prod, Multiset.map_congr (congr_arg _ h₁) h₂]
#align finset.noncomm_prod_congr Finset.noncommProd_congr
#align finset.noncomm_sum_congr Finset.noncommSum_congr

@[simp, to_additive]
theorem noncommProd_toFinset [DecidableEq α] (l : List α) (f : α → β) (comm) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).Prod :=
  by
  rw [← List.dedup_eq_self] at hl 
  simp [noncomm_prod, hl]
#align finset.noncomm_prod_to_finset Finset.noncommProd_toFinset
#align finset.noncomm_sum_to_finset Finset.noncommSum_toFinset

@[simp, to_additive]
theorem noncommProd_empty (f : α → β) (h) : noncommProd (∅ : Finset α) f h = 1 :=
  rfl
#align finset.noncomm_prod_empty Finset.noncommProd_empty
#align finset.noncomm_sum_empty Finset.noncommSum_empty

@[simp, to_additive]
theorem noncommProd_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f (comm.mono fun _ => mem_insert_of_mem) :=
  by simp [insert_val_of_not_mem ha, noncomm_prod]
#align finset.noncomm_prod_insert_of_not_mem Finset.noncommProd_insert_of_not_mem
#align finset.noncomm_sum_insert_of_not_mem Finset.noncommSum_insert_of_not_mem

@[to_additive]
theorem noncommProd_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      noncommProd s f (comm.mono fun _ => mem_insert_of_mem) * f a :=
  by simp [noncomm_prod, insert_val_of_not_mem ha, Multiset.noncommProd_cons']
#align finset.noncomm_prod_insert_of_not_mem' Finset.noncommProd_insert_of_not_mem'
#align finset.noncomm_sum_insert_of_not_mem' Finset.noncommSum_insert_of_not_mem'

#print Finset.noncommProd_singleton /-
@[simp, to_additive]
theorem noncommProd_singleton (a : α) (f : α → β) :
    noncommProd ({a} : Finset α) f (by norm_cast; exact Set.pairwise_singleton _ _) = f a := by
  simp [noncomm_prod, ← Multiset.cons_zero]
#align finset.noncomm_prod_singleton Finset.noncommProd_singleton
#align finset.noncomm_sum_singleton Finset.noncommSum_singleton
-/

@[to_additive]
theorem noncommProd_map [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (comm) (g : F) :
    g (s.noncommProd f comm) =
      s.noncommProd (fun i => g (f i)) fun x hx y hy h => (comm.of_refl hx hy).map g :=
  by simp [noncomm_prod, Multiset.noncommProd_map]
#align finset.noncomm_prod_map Finset.noncommProd_map
#align finset.noncomm_sum_map Finset.noncommSum_map

@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Finset α) (f : α → β) (comm) (m : β) (h : ∀ x ∈ s, f x = m) :
    s.noncommProd f comm = m ^ s.card :=
  by
  rw [noncomm_prod, Multiset.noncommProd_eq_pow_card _ _ m]
  simp only [Finset.card_def, Multiset.card_map]
  simpa using h
#align finset.noncomm_prod_eq_pow_card Finset.noncommProd_eq_pow_card
#align finset.noncomm_sum_eq_card_nsmul Finset.noncommSum_eq_card_nsmul

@[to_additive noncomm_sum_add_commute]
theorem noncommProd_commute (s : Finset α) (f : α → β) (comm) (y : β)
    (h : ∀ x ∈ s, Commute y (f x)) : Commute y (s.noncommProd f comm) :=
  by
  apply Multiset.noncommProd_commute
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx
#align finset.noncomm_prod_commute Finset.noncommProd_commute
#align finset.noncomm_sum_add_commute Finset.noncommSum_addCommute

#print Finset.noncommProd_eq_prod /-
@[to_additive]
theorem noncommProd_eq_prod {β : Type _} [CommMonoid β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ _ => Commute.all _ _) = s.Prod f := by
  classical
    induction' s using Finset.induction_on with a s ha IH
    · simp
    · simp [ha, IH]
#align finset.noncomm_prod_eq_prod Finset.noncommProd_eq_prod
#align finset.noncomm_sum_eq_sum Finset.noncommSum_eq_sum
-/

/-- The non-commutative version of `finset.prod_union` -/
@[to_additive "The non-commutative version of `finset.sum_union`"]
theorem noncommProd_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t)
    (f : α → β) (comm : { x | x ∈ s ∪ t }.Pairwise fun a b => Commute (f a) (f b)) :
    noncommProd (s ∪ t) f comm =
      noncommProd s f (comm.mono <| coe_subset.2 <| subset_union_left _ _) *
        noncommProd t f (comm.mono <| coe_subset.2 <| subset_union_right _ _) :=
  by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_toFinset_iff_disjoint] at h 
  simp [sl', tl', noncomm_prod_to_finset, ← List.prod_append, ← List.toFinset_append,
    sl'.append tl' h]
#align finset.noncomm_prod_union_of_disjoint Finset.noncommProd_union_of_disjoint
#align finset.noncomm_sum_union_of_disjoint Finset.noncommSum_union_of_disjoint

@[protected, to_additive]
theorem noncommProd_mul_distrib_aux {s : Finset α} {f : α → β} {g : α → β}
    (comm_ff : (s : Set α).Pairwise fun x y => Commute (f x) (f y))
    (comm_gg : (s : Set α).Pairwise fun x y => Commute (g x) (g y))
    (comm_gf : (s : Set α).Pairwise fun x y => Commute (g x) (f y)) :
    (s : Set α).Pairwise fun x y => Commute ((f * g) x) ((f * g) y) :=
  by
  intro x hx y hy h
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact comm_ff.of_refl hx hy
  · exact (comm_gf hy hx h.symm).symm
  · exact comm_gf hx hy h
  · exact comm_gg.of_refl hx hy
#align finset.noncomm_prod_mul_distrib_aux Finset.noncommProd_mul_distrib_aux
#align finset.noncomm_sum_add_distrib_aux Finset.noncommSum_add_distrib_aux

/-- The non-commutative version of `finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `finset.sum_add_distrib`"]
theorem noncommProd_mul_distrib {s : Finset α} (f : α → β) (g : α → β) (comm_ff comm_gg comm_gf) :
    noncommProd s (f * g) (noncommProd_mul_distrib_aux comm_ff comm_gg comm_gf) =
      noncommProd s f comm_ff * noncommProd s g comm_gg :=
  by
  classical
    induction' s using Finset.induction_on with x s hnmem ih
    · simp
    simp only [Finset.noncommProd_insert_of_not_mem _ _ _ _ hnmem]
    specialize
      ih (comm_ff.mono fun _ => mem_insert_of_mem) (comm_gg.mono fun _ => mem_insert_of_mem)
        (comm_gf.mono fun _ => mem_insert_of_mem)
    rw [ih, Pi.mul_apply]
    simp only [mul_assoc]
    congr 1
    simp only [← mul_assoc]
    congr 1
    refine' noncomm_prod_commute _ _ _ _ fun y hy => _
    exact comm_gf (mem_insert_self x s) (mem_insert_of_mem hy) (ne_of_mem_of_not_mem hy hnmem).symm
#align finset.noncomm_prod_mul_distrib Finset.noncommProd_mul_distrib
#align finset.noncomm_sum_add_distrib Finset.noncommSum_add_distrib

section FinitePi

variable {M : ι → Type _} [∀ i, Monoid (M i)]

@[to_additive]
theorem noncommProd_mul_single [Fintype ι] [DecidableEq ι] (x : ∀ i, M i) :
    (univ.noncommProd (fun i => Pi.mulSingle i (x i)) fun i _ j _ _ =>
        Pi.mulSingle_apply_commute x i j) =
      x :=
  by
  ext i
  apply (univ.noncomm_prod_map (fun i => MonoidHom.single M i (x i)) _ (Pi.evalMonoidHom M i)).trans
  rw [← insert_erase (mem_univ i), noncomm_prod_insert_of_not_mem' _ _ _ _ (not_mem_erase _ _),
    noncomm_prod_eq_pow_card, one_pow]
  · simp
  · intro i h; simp at h ; simp [h]
#align finset.noncomm_prod_mul_single Finset.noncommProd_mul_single
#align finset.noncomm_sum_single Finset.noncommSum_single

@[to_additive]
theorem MonoidHom.pi_ext [Finite ι] [DecidableEq ι] {f g : (∀ i, M i) →* γ}
    (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g :=
  by
  cases nonempty_fintype ι
  ext x
  rw [← noncomm_prod_mul_single x, univ.noncomm_prod_map, univ.noncomm_prod_map]
  congr 1 with i; exact h i (x i)
#align monoid_hom.pi_ext MonoidHom.pi_ext
#align add_monoid_hom.pi_ext AddMonoidHom.pi_ext

end FinitePi

end Finset

