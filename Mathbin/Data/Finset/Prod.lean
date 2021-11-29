import Mathbin.Data.Finset.Basic

/-!
# Finsets in product types

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`finset.prod` operation which computes the multiplicative product.

## Main declarations

* `finset.product`: Turns `s : finset α`, `t : finset β` into their product in `finset (α × β)`.
* `finset.diag`: For `s : finset α`, `s.diag` is the `finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `finset.off_diag`: For `s : finset α`, `s.off_diag` is the `finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/


open Multiset

variable {α β γ : Type _}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, nodup_product s.2 t.2⟩

@[simp]
theorem product_val : (s.product t).1 = s.1.product t.1 :=
  rfl

@[simp]
theorem mem_product {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  mem_product

theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
  s ⊆ (s.image Prod.fst).product (s.image Prod.snd) :=
  fun p hp => mem_product.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

theorem product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s.product t ⊆ s'.product t' :=
  fun ⟨x, y⟩ h => mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩

theorem product_subset_product_left (hs : s ⊆ s') : s.product t ⊆ s'.product t :=
  product_subset_product hs (subset.refl _)

theorem product_subset_product_right (ht : t ⊆ t') : s.product t ⊆ s.product t' :=
  product_subset_product (subset.refl _) ht

theorem product_eq_bUnion [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
  s.product t = s.bUnion fun a => t.image$ fun b => (a, b) :=
  ext$
    fun ⟨x, y⟩ =>
      by 
        simp only [mem_product, mem_bUnion, mem_image, exists_prop, Prod.mk.inj_iffₓ, And.left_comm,
          exists_and_distrib_left, exists_eq_right, exists_eq_left]

@[simp]
theorem product_bUnion [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β → Finset γ) :
  (s.product t).bUnion f = s.bUnion fun a => t.bUnion fun b => f (a, b) :=
  by 
    classical 
    simpRw [product_eq_bUnion, bUnion_bUnion, image_bUnion]

@[simp]
theorem card_product (s : Finset α) (t : Finset β) : card (s.product t) = card s*card t :=
  Multiset.card_product _ _

theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
  ((s.product t).filter fun x : α × β => p x.1 ∧ q x.2) = (s.filter p).product (t.filter q) :=
  by 
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product]
    finish

theorem filter_product_card (s : Finset α) (t : Finset β) (p : α → Prop) (q : β → Prop) [DecidablePred p]
  [DecidablePred q] :
  ((s.product t).filter fun x : α × β => p x.1 ↔ q x.2).card =
    ((s.filter p).card*(t.filter q).card)+(s.filter (Not ∘ p)).card*(t.filter (Not ∘ q)).card :=
  by 
    classical 
    rw [←card_product, ←card_product, ←filter_product, ←filter_product, ←card_union_eq]
    ·
      apply congr_argₓ 
      ext ⟨a, b⟩
      simp only [filter_union_right, mem_filter, mem_product]
      split  <;> intros  <;> finish
    ·
      rw [disjoint_iff]
      change _ ∩ _ = ∅
      ext ⟨a, b⟩
      rw [mem_inter]
      finish

theorem empty_product (t : Finset β) : (∅ : Finset α).product t = ∅ :=
  rfl

theorem product_empty (s : Finset α) : s.product (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_not_mem fun x h => (Finset.mem_product.1 h).2

theorem nonempty.product (hs : s.nonempty) (ht : t.nonempty) : (s.product t).Nonempty :=
  let ⟨x, hx⟩ := hs 
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

theorem nonempty.fst (h : (s.product t).Nonempty) : s.nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩

theorem nonempty.snd (h : (s.product t).Nonempty) : t.nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp]
theorem nonempty_product : (s.product t).Nonempty ↔ s.nonempty ∧ t.nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩

@[simp]
theorem union_product [DecidableEq α] [DecidableEq β] : (s ∪ s').product t = s.product t ∪ s'.product t :=
  by 
    ext ⟨x, y⟩
    simp only [or_and_distrib_right, mem_union, mem_product]

@[simp]
theorem product_union [DecidableEq α] [DecidableEq β] : s.product (t ∪ t') = s.product t ∪ s.product t' :=
  by 
    ext ⟨x, y⟩
    simp only [and_or_distrib_left, mem_union, mem_product]

end Prod

section Diag

variable (s : Finset α) [DecidableEq α]

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag :=
  (s.product s).filter fun a : α × α => a.fst = a.snd

/-- Given a finite set `s`, the off-diagonal, `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def off_diag :=
  (s.product s).filter fun a : α × α => a.fst ≠ a.snd

@[simp]
theorem mem_diag (x : α × α) : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 :=
  by 
    simp only [diag, mem_filter, mem_product]
    split  <;> intros  <;> finish

@[simp]
theorem mem_off_diag (x : α × α) : x ∈ s.off_diag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  by 
    simp only [off_diag, mem_filter, mem_product]
    split  <;> intros  <;> finish

@[simp]
theorem diag_card : (diag s).card = s.card :=
  by 
    suffices  : diag s = s.image fun a => (a, a)
    ·
      rw [this]
      apply card_image_of_inj_on 
      finish 
    ext ⟨a₁, a₂⟩
    rw [mem_diag]
    split  <;> intros  <;> finish

@[simp]
theorem off_diag_card : (off_diag s).card = (s.card*s.card) - s.card :=
  by 
    suffices  : ((diag s).card+(off_diag s).card) = s.card*s.card
    ·
      nthRw 2[←s.diag_card]
      finish 
    rw [←card_product]
    apply filter_card_add_filter_neg_card_eq_card

@[simp]
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl

@[simp]
theorem off_diag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl

end Diag

end Finset

