/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.nodup
! leanprover-community/mathlib commit f2f413b9d4be3a02840d0663dace76e8fe3da053
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Nodup
import Mathbin.Data.Multiset.Bind
import Mathbin.Data.Multiset.Range

/-!
# The `nodup` predicate for multisets without duplicate elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

open Function List

variable {α β γ : Type _} {r : α → α → Prop} {s t : Multiset α} {a : α}

#print Multiset.Nodup /-
-- nodup
/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s Nodup fun s t p => propext p.nodup_iff
#align multiset.nodup Multiset.Nodup
-/

#print Multiset.coe_nodup /-
@[simp]
theorem coe_nodup {l : List α} : @Nodup α l ↔ l.Nodup :=
  Iff.rfl
#align multiset.coe_nodup Multiset.coe_nodup
-/

#print Multiset.nodup_zero /-
@[simp]
theorem nodup_zero : @Nodup α 0 :=
  Pairwise.nil
#align multiset.nodup_zero Multiset.nodup_zero
-/

#print Multiset.nodup_cons /-
@[simp]
theorem nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s :=
  Quot.inductionOn s fun l => nodup_cons
#align multiset.nodup_cons Multiset.nodup_cons
-/

#print Multiset.Nodup.cons /-
theorem Nodup.cons (m : a ∉ s) (n : Nodup s) : Nodup (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩
#align multiset.nodup.cons Multiset.Nodup.cons
-/

#print Multiset.nodup_singleton /-
@[simp]
theorem nodup_singleton : ∀ a : α, Nodup ({a} : Multiset α) :=
  nodup_singleton
#align multiset.nodup_singleton Multiset.nodup_singleton
-/

#print Multiset.Nodup.of_cons /-
theorem Nodup.of_cons (h : Nodup (a ::ₘ s)) : Nodup s :=
  (nodup_cons.1 h).2
#align multiset.nodup.of_cons Multiset.Nodup.of_cons
-/

#print Multiset.Nodup.not_mem /-
theorem Nodup.not_mem (h : Nodup (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1
#align multiset.nodup.not_mem Multiset.Nodup.not_mem
-/

#print Multiset.nodup_of_le /-
theorem nodup_of_le {s t : Multiset α} (h : s ≤ t) : Nodup t → Nodup s :=
  leInductionOn h fun l₁ l₂ => Nodup.sublist
#align multiset.nodup_of_le Multiset.nodup_of_le
-/

#print Multiset.not_nodup_pair /-
theorem not_nodup_pair : ∀ a : α, ¬Nodup (a ::ₘ a ::ₘ 0) :=
  not_nodup_pair
#align multiset.not_nodup_pair Multiset.not_nodup_pair
-/

#print Multiset.nodup_iff_le /-
theorem nodup_iff_le {s : Multiset α} : Nodup s ↔ ∀ a : α, ¬a ::ₘ a ::ₘ 0 ≤ s :=
  Quot.inductionOn s fun l =>
    nodup_iff_sublist.trans <| forall_congr' fun a => (@replicate_le_coe _ a 2 _).symm.Not
#align multiset.nodup_iff_le Multiset.nodup_iff_le
-/

#print Multiset.nodup_iff_ne_cons_cons /-
theorem nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ ∀ a t, s ≠ a ::ₘ a ::ₘ t :=
  nodup_iff_le.trans
    ⟨fun h a t s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, zero_add] at s_eq )⟩
#align multiset.nodup_iff_ne_cons_cons Multiset.nodup_iff_ne_cons_cons
-/

#print Multiset.nodup_iff_count_le_one /-
theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ ∀ a, count a s ≤ 1 :=
  Quot.inductionOn s fun l => nodup_iff_count_le_one
#align multiset.nodup_iff_count_le_one Multiset.nodup_iff_count_le_one
-/

#print Multiset.count_eq_one_of_mem /-
@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a ∈ s) :
    count a s = 1 :=
  le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)
#align multiset.count_eq_one_of_mem Multiset.count_eq_one_of_mem
-/

#print Multiset.count_eq_of_nodup /-
theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
    count a s = if a ∈ s then 1 else 0 :=
  by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_not_mem h
#align multiset.count_eq_of_nodup Multiset.count_eq_of_nodup
-/

#print Multiset.nodup_iff_pairwise /-
theorem nodup_iff_pairwise {α} {s : Multiset α} : Nodup s ↔ Pairwise (· ≠ ·) s :=
  Quotient.inductionOn s fun l => (pairwise_coe_iff_pairwise fun a b => Ne.symm).symm
#align multiset.nodup_iff_pairwise Multiset.nodup_iff_pairwise
-/

#print Multiset.Nodup.pairwise /-
protected theorem Nodup.pairwise : (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → Nodup s → Pairwise r s :=
  Quotient.inductionOn s fun l h hl => ⟨l, rfl, hl.imp_of_mem fun a b ha hb => h a ha b hb⟩
#align multiset.nodup.pairwise Multiset.Nodup.pairwise
-/

#print Multiset.Pairwise.forall /-
theorem Pairwise.forall (H : Symmetric r) (hs : Pairwise r s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  let ⟨l, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall H
#align multiset.pairwise.forall Multiset.Pairwise.forall
-/

#print Multiset.nodup_add /-
theorem nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => nodup_append
#align multiset.nodup_add Multiset.nodup_add
-/

#print Multiset.disjoint_of_nodup_add /-
theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2
#align multiset.disjoint_of_nodup_add Multiset.disjoint_of_nodup_add
-/

#print Multiset.Nodup.add_iff /-
theorem Nodup.add_iff (d₁ : Nodup s) (d₂ : Nodup t) : Nodup (s + t) ↔ Disjoint s t := by
  simp [nodup_add, d₁, d₂]
#align multiset.nodup.add_iff Multiset.Nodup.add_iff
-/

#print Multiset.Nodup.of_map /-
theorem Nodup.of_map (f : α → β) : Nodup (map f s) → Nodup s :=
  Quot.inductionOn s fun l => Nodup.of_map f
#align multiset.nodup.of_map Multiset.Nodup.of_map
-/

#print Multiset.Nodup.map_on /-
theorem Nodup.map_on {f : α → β} :
    (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → Nodup s → Nodup (map f s) :=
  Quot.inductionOn s fun l => Nodup.map_on
#align multiset.nodup.map_on Multiset.Nodup.map_on
-/

#print Multiset.Nodup.map /-
theorem Nodup.map {f : α → β} {s : Multiset α} (hf : Injective f) : Nodup s → Nodup (map f s) :=
  Nodup.map_on fun x _ y _ h => hf h
#align multiset.nodup.map Multiset.Nodup.map
-/

#print Multiset.inj_on_of_nodup_map /-
theorem inj_on_of_nodup_map {f : α → β} {s : Multiset α} :
    Nodup (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  Quot.inductionOn s fun l => inj_on_of_nodup_map
#align multiset.inj_on_of_nodup_map Multiset.inj_on_of_nodup_map
-/

#print Multiset.nodup_map_iff_inj_on /-
theorem nodup_map_iff_inj_on {f : α → β} {s : Multiset α} (d : Nodup s) :
    Nodup (map f s) ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_onₓ h⟩
#align multiset.nodup_map_iff_inj_on Multiset.nodup_map_iff_inj_on
-/

#print Multiset.Nodup.filter /-
theorem Nodup.filter (p : α → Prop) [DecidablePred p] {s} : Nodup s → Nodup (filter p s) :=
  Quot.inductionOn s fun l => Nodup.filter p
#align multiset.nodup.filter Multiset.Nodup.filter
-/

#print Multiset.nodup_attach /-
@[simp]
theorem nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s :=
  Quot.inductionOn s fun l => nodup_attach
#align multiset.nodup_attach Multiset.nodup_attach
-/

#print Multiset.Nodup.pmap /-
theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : Nodup s → Nodup (pmap f s H) :=
  Quot.inductionOn s (fun l H => Nodup.pmap hf) H
#align multiset.nodup.pmap Multiset.Nodup.pmap
-/

#print Multiset.nodupDecidable /-
instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodup s) :=
  Quotient.recOnSubsingleton s fun l => l.nodupDecidable
#align multiset.nodup_decidable Multiset.nodupDecidable
-/

#print Multiset.Nodup.erase_eq_filter /-
theorem Nodup.erase_eq_filter [DecidableEq α] (a : α) {s} :
    Nodup s → s.eraseₓ a = filter (· ≠ a) s :=
  Quot.inductionOn s fun l d => congr_arg coe <| d.erase_eq_filter a
#align multiset.nodup.erase_eq_filter Multiset.Nodup.erase_eq_filter
-/

#print Multiset.Nodup.erase /-
theorem Nodup.erase [DecidableEq α] (a : α) {l} : Nodup l → Nodup (l.eraseₓ a) :=
  nodup_of_le (erase_le _ _)
#align multiset.nodup.erase Multiset.Nodup.erase
-/

#print Multiset.Nodup.mem_erase_iff /-
theorem Nodup.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodup l) :
    a ∈ l.eraseₓ b ↔ a ≠ b ∧ a ∈ l := by rw [d.erase_eq_filter b, mem_filter, and_comm']
#align multiset.nodup.mem_erase_iff Multiset.Nodup.mem_erase_iff
-/

#print Multiset.Nodup.not_mem_erase /-
theorem Nodup.not_mem_erase [DecidableEq α] {a : α} {s} (h : Nodup s) : a ∉ s.eraseₓ a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl
#align multiset.nodup.not_mem_erase Multiset.Nodup.not_mem_erase
-/

#print Multiset.Nodup.product /-
protected theorem Nodup.product {t : Multiset β} : Nodup s → Nodup t → Nodup (product s t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ d₁ d₂ => by simp [d₁.product d₂]
#align multiset.nodup.product Multiset.Nodup.product
-/

#print Multiset.Nodup.sigma /-
protected theorem Nodup.sigma {σ : α → Type _} {t : ∀ a, Multiset (σ a)} :
    Nodup s → (∀ a, Nodup (t a)) → Nodup (s.Sigma t) :=
  Quot.inductionOn s fun l₁ =>
    by
    choose f hf using fun a => Quotient.exists_rep (t a)
    rw [show t = fun a => f a from Eq.symm <| funext fun a => hf a]
    simpa using nodup.sigma
#align multiset.nodup.sigma Multiset.Nodup.sigma
-/

#print Multiset.Nodup.filterMap /-
protected theorem Nodup.filterMap (f : α → Option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup s → Nodup (filterMap f s) :=
  Quot.inductionOn s fun l => Nodup.filterMap H
#align multiset.nodup.filter_map Multiset.Nodup.filterMap
-/

#print Multiset.nodup_range /-
theorem nodup_range (n : ℕ) : Nodup (range n) :=
  nodup_range _
#align multiset.nodup_range Multiset.nodup_range
-/

#print Multiset.Nodup.inter_left /-
theorem Nodup.inter_left [DecidableEq α] (t) : Nodup s → Nodup (s ∩ t) :=
  nodup_of_le <| inter_le_left _ _
#align multiset.nodup.inter_left Multiset.Nodup.inter_left
-/

#print Multiset.Nodup.inter_right /-
theorem Nodup.inter_right [DecidableEq α] (s) : Nodup t → Nodup (s ∩ t) :=
  nodup_of_le <| inter_le_right _ _
#align multiset.nodup.inter_right Multiset.Nodup.inter_right
-/

#print Multiset.nodup_union /-
@[simp]
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s ∪ t) ↔ Nodup s ∧ Nodup t :=
  ⟨fun h => ⟨nodup_of_le (le_union_left _ _) h, nodup_of_le (le_union_right _ _) h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union] <;>
        exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩
#align multiset.nodup_union Multiset.nodup_union
-/

#print Multiset.nodup_bind /-
@[simp]
theorem nodup_bind {s : Multiset α} {t : α → Multiset β} :
    Nodup (bind s t) ↔ (∀ a ∈ s, Nodup (t a)) ∧ s.Pairwise fun a b => Disjoint (t a) (t b) :=
  have h₁ : ∀ a, ∃ l : List β, t a = l := fun a => Quot.inductionOn (t a) fun l => ⟨l, rfl⟩
  let ⟨t', h'⟩ := Classical.axiom_of_choice h₁
  have : t = fun a => t' a := funext h'
  have hd : Symmetric fun a b => List.Disjoint (t' a) (t' b) := fun a b h => h.symm
  Quot.inductionOn s <| by simp [this, List.nodup_bind, pairwise_coe_iff_pairwise hd]
#align multiset.nodup_bind Multiset.nodup_bind
-/

#print Multiset.Nodup.ext /-
theorem Nodup.ext {s t : Multiset α} : Nodup s → Nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ d₁ d₂ => Quotient.eq'.trans <| perm_ext d₁ d₂
#align multiset.nodup.ext Multiset.Nodup.ext
-/

#print Multiset.le_iff_subset /-
theorem le_iff_subset {s t : Multiset α} : Nodup s → (s ≤ t ↔ s ⊆ t) :=
  Quotient.induction_on₂ s t fun l₁ l₂ d => ⟨subset_of_le, d.Subperm⟩
#align multiset.le_iff_subset Multiset.le_iff_subset
-/

#print Multiset.range_le /-
theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
  (le_iff_subset (nodup_range _)).trans range_subset
#align multiset.range_le Multiset.range_le
-/

#print Multiset.mem_sub_of_nodup /-
theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) :
    a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le tsub_le_self h, fun h' => by
      refine' count_eq_zero.1 _ h <;> rw [count_sub a s t, tsub_eq_zero_iff_le] <;>
        exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le le_tsub_add h₁) h₂⟩
#align multiset.mem_sub_of_nodup Multiset.mem_sub_of_nodup
-/

#print Multiset.map_eq_map_of_bij_of_nodup /-
theorem map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : Multiset α} {t : Multiset β}
    (hs : s.Nodup) (ht : t.Nodup) (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (h : ∀ a ha, f a = g (i a ha)) (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : s.map f = t.map g :=
  have : t = s.attach.map fun x => i x x.2 :=
    (ht.ext <|
          (nodup_attach.2 hs).map <|
            show Injective fun x : { x // x ∈ s } => i x x.2 from fun x y hxy =>
              Subtype.ext <| i_inj x y x.2 y.2 hxy).2
      fun x => by
      simp only [mem_map, true_and_iff, Subtype.exists, eq_comm, mem_attach] <;>
        exact ⟨i_surj _, fun ⟨y, hy⟩ => hy.snd.symm ▸ hi _ _⟩
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map] <;> exact map_congr rfl fun x _ => h _ _
#align multiset.map_eq_map_of_bij_of_nodup Multiset.map_eq_map_of_bij_of_nodup
-/

end Multiset

