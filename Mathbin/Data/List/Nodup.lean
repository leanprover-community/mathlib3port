/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import Data.List.Lattice
import Data.List.Pairwise
import Data.List.Forall2
import Data.Set.Pairwise.Basic

#align_import data.list.nodup from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Lists with no duplicates

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/


universe u v

open Nat Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α → α → Prop} {a b : α}

namespace List

#print List.forall_mem_ne /-
@[simp]
theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h a' m e => h (e.symm ▸ m)⟩
#align list.forall_mem_ne List.forall_mem_ne
-/

#print List.nodup_nil /-
@[simp]
theorem nodup_nil : @Nodup α [] :=
  Pairwise.nil
#align list.nodup_nil List.nodup_nil
-/

#print List.nodup_cons /-
@[simp]
theorem nodup_cons {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [nodup, pairwise_cons, forall_mem_ne]
#align list.nodup_cons List.nodup_cons
-/

#print List.Pairwise.nodup /-
protected theorem Pairwise.nodup {l : List α} {r : α → α → Prop} [IsIrrefl α r] (h : Pairwise r l) :
    Nodup l :=
  h.imp fun a b => ne_of_irrefl
#align list.pairwise.nodup List.Pairwise.nodup
-/

#print List.rel_nodup /-
theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, forall₂.nil => by simp only [nodup_nil]
  | _, _, forall₂.cons hab h => by
    simpa only [nodup_cons] using Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup h)
#align list.rel_nodup List.rel_nodup
-/

#print List.Nodup.cons /-
protected theorem Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩
#align list.nodup.cons List.Nodup.cons
-/

#print List.nodup_singleton /-
theorem nodup_singleton (a : α) : Nodup [a] :=
  pairwise_singleton _ _
#align list.nodup_singleton List.nodup_singleton
-/

#print List.Nodup.of_cons /-
theorem Nodup.of_cons (h : Nodup (a :: l)) : Nodup l :=
  (nodup_cons.1 h).2
#align list.nodup.of_cons List.Nodup.of_cons
-/

#print List.Nodup.not_mem /-
theorem Nodup.not_mem (h : (a :: l).Nodup) : a ∉ l :=
  (nodup_cons.1 h).1
#align list.nodup.not_mem List.Nodup.not_mem
-/

#print List.not_nodup_cons_of_mem /-
theorem not_nodup_cons_of_mem : a ∈ l → ¬Nodup (a :: l) :=
  imp_not_comm.1 Nodup.not_mem
#align list.not_nodup_cons_of_mem List.not_nodup_cons_of_mem
-/

#print List.Nodup.sublist /-
protected theorem Nodup.sublist : l₁ <+ l₂ → Nodup l₂ → Nodup l₁ :=
  Pairwise.sublist
#align list.nodup.sublist List.Nodup.sublist
-/

#print List.not_nodup_pair /-
theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
  not_nodup_cons_of_mem <| mem_singleton_self _
#align list.not_nodup_pair List.not_nodup_pair
-/

#print List.nodup_iff_sublist /-
theorem nodup_iff_sublist {l : List α} : Nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.Sublist h),
    by
    induction' l with a l IH <;> intro h; · exact nodup_nil
    exact
      (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons fun al =>
        h a <| (singleton_sublist.2 al).cons_cons _⟩
#align list.nodup_iff_sublist List.nodup_iff_sublist
-/

#print List.nodup_iff_nthLe_inj /-
theorem nodup_iff_nthLe_inj {l : List α} :
    Nodup l ↔ ∀ i j h₁ h₂, nthLe l i h₁ = nthLe l j h₂ → i = j :=
  pairwise_iff_nthLe.trans
    ⟨fun H i j h₁ h₂ h =>
      ((lt_trichotomy _ _).resolve_left fun h' => H _ _ h₂ h' h).resolve_right fun h' =>
        H _ _ h₁ h' h.symm,
      fun H i j h₁ h₂ h => ne_of_lt h₂ (H _ _ _ _ h)⟩
#align list.nodup_iff_nth_le_inj List.nodup_iff_nthLe_inj
-/

#print List.Nodup.nthLe_inj_iff /-
theorem Nodup.nthLe_inj_iff {l : List α} (h : Nodup l) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : l.nthLe i hi = l.nthLe j hj ↔ i = j :=
  ⟨nodup_iff_nthLe_inj.mp h _ _ _ _, by simp (config := { contextual := true })⟩
#align list.nodup.nth_le_inj_iff List.Nodup.nthLe_inj_iff
-/

#print List.nodup_iff_get?_ne_get? /-
theorem nodup_iff_get?_ne_get? {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l.get? i ≠ l.get? j :=
  by
  rw [nodup_iff_nth_le_inj]
  simp only [nth_le_eq_iff, some_nth_le_eq]
  constructor <;> rintro h i j h₁ h₂
  · exact mt (h i j (h₁.trans h₂) h₂) (ne_of_lt h₁)
  · intro h₃
    by_contra h₄
    cases' lt_or_gt_of_ne h₄ with h₅ h₅
    · exact h i j h₅ h₂ h₃
    · exact h j i h₅ h₁ h₃.symm
#align list.nodup_iff_nth_ne_nth List.nodup_iff_get?_ne_get?
-/

#print List.Nodup.ne_singleton_iff /-
theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
  by
  induction' l with hd tl hl
  · simp
  · specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne.def, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · have : tl ≠ [] := ne_nil_of_mem hy
        suffices ∃ (y : α) (H : y ∈ hd :: tl), y ≠ x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩
#align list.nodup.ne_singleton_iff List.Nodup.ne_singleton_iff
-/

#print List.nthLe_eq_of_ne_imp_not_nodup /-
theorem nthLe_eq_of_ne_imp_not_nodup (xs : List α) (n m : ℕ) (hn : n < xs.length)
    (hm : m < xs.length) (h : xs.nthLe n hn = xs.nthLe m hm) (hne : n ≠ m) : ¬Nodup xs :=
  by
  rw [nodup_iff_nth_le_inj]
  simp only [exists_prop, exists_and_right, Classical.not_forall]
  exact ⟨n, m, ⟨hn, hm, h⟩, hne⟩
#align list.nth_le_eq_of_ne_imp_not_nodup List.nthLe_eq_of_ne_imp_not_nodup
-/

#print List.nthLe_index_of /-
@[simp]
theorem nthLe_index_of [DecidableEq α] {l : List α} (H : Nodup l) (n h) :
    indexOf (nthLe l n h) l = n :=
  nodup_iff_nthLe_inj.1 H _ _ _ h <| indexOf_nthLe <| indexOf_lt_length.2 <| nthLe_mem _ _ _
#align list.nth_le_index_of List.nthLe_index_of
-/

#print List.nodup_iff_count_le_one /-
theorem nodup_iff_count_le_one [DecidableEq α] {l : List α} : Nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans <|
    forall_congr' fun a =>
      have : [a, a] <+ l ↔ 1 < count a l := (@le_count_iff_replicate_sublist _ _ a l 2).symm
      (not_congr this).trans not_lt
#align list.nodup_iff_count_le_one List.nodup_iff_count_le_one
-/

#print List.nodup_replicate /-
theorem nodup_replicate (a : α) : ∀ {n : ℕ}, Nodup (replicate n a) ↔ n ≤ 1
  | 0 => by simp [Nat.zero_le]
  | 1 => by simp
  | n + 2 =>
    iff_of_false
      (fun H => nodup_iff_sublist.1 H a ((replicate_sublist_replicate _).2 (Nat.le_add_left 2 n)))
      (not_le_of_lt <| Nat.le_add_left 2 n)
#align list.nodup_replicate List.nodup_replicate
-/

#print List.count_eq_one_of_mem /-
@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {l : List α} (d : Nodup l) (h : a ∈ l) :
    count a l = 1 :=
  le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos_iff_mem.2 h)
#align list.count_eq_one_of_mem List.count_eq_one_of_mem
-/

#print List.count_eq_of_nodup /-
theorem count_eq_of_nodup [DecidableEq α] {a : α} {l : List α} (d : Nodup l) :
    count a l = if a ∈ l then 1 else 0 :=
  by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_not_mem h
#align list.count_eq_of_nodup List.count_eq_of_nodup
-/

#print List.Nodup.of_append_left /-
theorem Nodup.of_append_left : Nodup (l₁ ++ l₂) → Nodup l₁ :=
  Nodup.sublist (sublist_append_left l₁ l₂)
#align list.nodup.of_append_left List.Nodup.of_append_left
-/

#print List.Nodup.of_append_right /-
theorem Nodup.of_append_right : Nodup (l₁ ++ l₂) → Nodup l₂ :=
  Nodup.sublist (sublist_append_right l₁ l₂)
#align list.nodup.of_append_right List.Nodup.of_append_right
-/

#print List.nodup_append /-
theorem nodup_append {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ :=
  by simp only [nodup, pairwise_append, disjoint_iff_ne]
#align list.nodup_append List.nodup_append
-/

#print List.disjoint_of_nodup_append /-
theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append.1 d).2.2
#align list.disjoint_of_nodup_append List.disjoint_of_nodup_append
-/

#print List.Nodup.append /-
theorem Nodup.append (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂) :=
  nodup_append.2 ⟨d₁, d₂, dj⟩
#align list.nodup.append List.Nodup.append
-/

#print List.nodup_append_comm /-
theorem nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁) := by
  simp only [nodup_append, and_left_comm, disjoint_comm]
#align list.nodup_append_comm List.nodup_append_comm
-/

#print List.nodup_middle /-
theorem nodup_middle {a : α} {l₁ l₂ : List α} : Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) :=
  by
  simp only [nodup_append, not_or, and_left_comm, and_assoc', nodup_cons, mem_append,
    disjoint_cons_right]
#align list.nodup_middle List.nodup_middle
-/

theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  Pairwise.of_map f fun a b => mt <| congr_arg f
#align list.nodup.of_map List.Nodup.of_mapₓ

theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)
#align list.nodup.map_on List.Nodup.map_onₓ

#print List.inj_on_of_nodup_map /-
theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : Nodup (map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y :=
  by
  induction' l with hd tl ih
  · simp
  · simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.def] at d
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃
#align list.inj_on_of_nodup_map List.inj_on_of_nodup_map
-/

#print List.nodup_map_iff_inj_on /-
theorem nodup_map_iff_inj_on {f : α → β} {l : List α} (d : Nodup l) :
    Nodup (map f l) ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_onₓ h⟩
#align list.nodup_map_iff_inj_on List.nodup_map_iff_inj_on
-/

#print List.Nodup.map /-
protected theorem Nodup.map {f : α → β} (hf : Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun x _ y _ h => hf h
#align list.nodup.map List.Nodup.map
-/

#print List.nodup_map_iff /-
theorem nodup_map_iff {f : α → β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩
#align list.nodup_map_iff List.nodup_map_iff
-/

#print List.nodup_attach /-
@[simp]
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_val l ▸ h.map fun a b => Subtype.eq, fun h =>
    Nodup.of_map Subtype.val ((attach_map_val l).symm ▸ h)⟩
#align list.nodup_attach List.nodup_attach
-/

alias ⟨nodup.of_attach, nodup.attach⟩ := nodup_attach
#align list.nodup.of_attach List.Nodup.of_attach
#align list.nodup.attach List.Nodup.attach

attribute [protected] nodup.attach

#print List.Nodup.pmap /-
theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  rw [pmap_eq_map_attach] <;>
    exact h.attach.map fun ⟨a, ha⟩ ⟨b, hb⟩ h => by congr <;> exact hf a (H _ ha) b (H _ hb) h
#align list.nodup.pmap List.Nodup.pmap
-/

#print List.Nodup.filter /-
theorem Nodup.filter (p : α → Prop) [DecidablePred p] {l} : Nodup l → Nodup (filter p l) :=
  Pairwise.filter p
#align list.nodup.filter List.Nodup.filter
-/

#print List.nodup_reverse /-
@[simp]
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [nodup, Ne.def, eq_comm]
#align list.nodup_reverse List.nodup_reverse
-/

#print List.Nodup.erase_eq_filter /-
theorem Nodup.erase_eq_filter [DecidableEq α] {l} (d : Nodup l) (a : α) :
    l.eraseₓ a = filter (· ≠ a) l :=
  by
  induction' d with b l m d IH; · rfl
  by_cases b = a
  · subst h; rw [erase_cons_head, filter_cons_of_neg]
    symm; rw [filter_eq_self]; simpa only [Ne.def, eq_comm] using m; exact not_not_intro rfl
  · rw [erase_cons_tail _ h, filter_cons_of_pos, IH]; exact h
#align list.nodup.erase_eq_filter List.Nodup.erase_eq_filter
-/

#print List.Nodup.erase /-
theorem Nodup.erase [DecidableEq α] (a : α) : Nodup l → Nodup (l.eraseₓ a) :=
  Nodup.sublist <| erase_sublist _ _
#align list.nodup.erase List.Nodup.erase
-/

#print List.Nodup.diff /-
theorem Nodup.diff [DecidableEq α] : l₁.Nodup → (l₁.diffₓ l₂).Nodup :=
  Nodup.sublist <| diff_sublist _ _
#align list.nodup.diff List.Nodup.diff
-/

#print List.Nodup.mem_erase_iff /-
theorem Nodup.mem_erase_iff [DecidableEq α] (d : Nodup l) : a ∈ l.eraseₓ b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter, mem_filter, and_comm']
#align list.nodup.mem_erase_iff List.Nodup.mem_erase_iff
-/

#print List.Nodup.not_mem_erase /-
theorem Nodup.not_mem_erase [DecidableEq α] (h : Nodup l) : a ∉ l.eraseₓ a := fun H =>
  (h.mem_erase_iff.1 H).1 rfl
#align list.nodup.not_mem_erase List.Nodup.not_mem_erase
-/

#print List.nodup_join /-
theorem nodup_join {L : List (List α)} :
    Nodup (join L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [nodup, pairwise_join, disjoint_left.symm, forall_mem_ne]
#align list.nodup_join List.nodup_join
-/

#print List.nodup_bind /-
theorem nodup_bind {l₁ : List α} {f : α → List β} :
    Nodup (l₁.bind f) ↔
      (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (fun a b : α => Disjoint (f a) (f b)) l₁ :=
  by
  simp only [List.bind, nodup_join, pairwise_map, and_comm', and_left_comm, mem_map, exists_imp,
      and_imp] <;>
    rw [show (∀ (l : List β) (x : α), f x = l → x ∈ l₁ → nodup l) ↔ ∀ x : α, x ∈ l₁ → nodup (f x)
        from forall_swap.trans <| forall_congr' fun _ => forall_eq']
#align list.nodup_bind List.nodup_bind
-/

#print List.Nodup.product /-
protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁.product l₂).Nodup :=
  nodup_bind.2
    ⟨fun a ma => d₂.map <| LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun a₁ a₂ n x h₁ h₂ =>
        by
        rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
#align list.nodup.product List.Nodup.product
-/

#print List.Nodup.sigma /-
theorem Nodup.sigma {σ : α → Type _} {l₂ : ∀ a, List (σ a)} (d₁ : Nodup l₁)
    (d₂ : ∀ a, Nodup (l₂ a)) : (l₁.Sigma l₂).Nodup :=
  nodup_bind.2
    ⟨fun a ma => (d₂ a).map fun b b' h => by injection h with _ h <;> exact eq_of_hEq h,
      d₁.imp fun a₁ a₂ n x h₁ h₂ =>
        by
        rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
#align list.nodup.sigma List.Nodup.sigma
-/

#print List.Nodup.filterMap /-
protected theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup l → Nodup (filterMap f l) :=
  Pairwise.filter_map f fun a a' n b bm b' bm' e => n <| h a a' b' (e ▸ bm) bm'
#align list.nodup.filter_map List.Nodup.filterMap
-/

#print List.Nodup.concat /-
protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.push a).Nodup := by
  rw [concat_eq_append] <;> exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)
#align list.nodup.concat List.Nodup.concat
-/

#print List.Nodup.insert /-
theorem Nodup.insert [DecidableEq α] (h : l.Nodup) : (insert a l).Nodup :=
  if h' : a ∈ l then by rw [insert_of_mem h'] <;> exact h
  else by rw [insert_of_not_mem h', nodup_cons] <;> constructor <;> assumption
#align list.nodup.insert List.Nodup.insert
-/

#print List.Nodup.union /-
theorem Nodup.union [DecidableEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ ∪ l₂).Nodup :=
  by
  induction' l₁ with a l₁ ih generalizing l₂
  · exact h
  · exact (ih h).insert
#align list.nodup.union List.Nodup.union
-/

#print List.Nodup.inter /-
theorem Nodup.inter [DecidableEq α] (l₂ : List α) : Nodup l₁ → Nodup (l₁ ∩ l₂) :=
  Nodup.filter _
#align list.nodup.inter List.Nodup.inter
-/

#print List.Nodup.diff_eq_filter /-
theorem Nodup.diff_eq_filter [DecidableEq α] :
    ∀ {l₁ l₂ : List α} (hl₁ : l₁.Nodup), l₁.diffₓ l₂ = l₁.filterₓ (· ∉ l₂)
  | l₁, [], hl₁ => by simp
  | l₁, a :: l₂, hl₁ =>
    by
    rw [diff_cons, (hl₁.erase _).diff_eq_filter, hl₁.erase_eq_filter, filter_filter]
    simp only [mem_cons_iff, not_or, and_comm]
#align list.nodup.diff_eq_filter List.Nodup.diff_eq_filter
-/

#print List.Nodup.mem_diff_iff /-
theorem Nodup.mem_diff_iff [DecidableEq α] (hl₁ : l₁.Nodup) : a ∈ l₁.diffₓ l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ :=
  by rw [hl₁.diff_eq_filter, mem_filter]
#align list.nodup.mem_diff_iff List.Nodup.mem_diff_iff
-/

#print List.Nodup.set /-
protected theorem Nodup.set :
    ∀ {l : List α} {n : ℕ} {a : α} (hl : l.Nodup) (ha : a ∉ l), (l.set n a).Nodup
  | [], n, a, hl, ha => nodup_nil
  | b :: l, 0, a, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | b :: l, n + 1, a, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self _ _),
        hl.of_cons.set (mt (mem_cons_of_mem _) ha)⟩
#align list.nodup.update_nth List.Nodup.set
-/

#print List.Nodup.map_update /-
theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → β) (x : α) (y : β) :
    l.map (Function.update f x y) = if x ∈ l then (l.map f).set (l.indexOfₓ x) y else l.map f :=
  by
  induction' l with hd tl ihl; · simp
  rw [nodup_cons] at hl
  simp only [mem_cons_iff, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [update_nth, hl.1]
  · simp [Ne.symm H, H, update_nth, ← apply_ite (cons (f hd))]
#align list.nodup.map_update List.Nodup.map_update
-/

#print List.Nodup.pairwise_of_forall_ne /-
theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  classical
  refine' pairwise_of_reflexive_on_dupl_of_forall_ne _ h
  intro x hx
  rw [nodup_iff_count_le_one] at hl
  exact absurd (hl x) hx.not_le
#align list.nodup.pairwise_of_forall_ne List.Nodup.pairwise_of_forall_ne
-/

#print List.Nodup.pairwise_of_set_pairwise /-
theorem Nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : {x | x ∈ l}.Pairwise r) : l.Pairwise r :=
  hl.pairwise_of_forall_ne h
#align list.nodup.pairwise_of_set_pairwise List.Nodup.pairwise_of_set_pairwise
-/

#print List.Nodup.pairwise_coe /-
@[simp]
theorem Nodup.pairwise_coe [IsSymm α r] (hl : l.Nodup) : {a | a ∈ l}.Pairwise r ↔ l.Pairwise r :=
  by
  induction' l with a l ih
  · simp
  rw [List.nodup_cons] at hl
  have : ∀ b ∈ l, ¬a = b → r a b ↔ r a b := fun b hb =>
    imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm
  simp [Set.setOf_or, Set.pairwise_insert_of_symmetric (@symm_of _ r _), ih hl.2, and_comm',
    forall₂_congr this]
#align list.nodup.pairwise_coe List.Nodup.pairwise_coe
-/

end List

#print Option.toList_nodup /-
theorem Option.toList_nodup {α} : ∀ o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
#align option.to_list_nodup Option.toList_nodup
-/

