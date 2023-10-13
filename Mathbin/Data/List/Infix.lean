/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.List.Basic

#align_import data.list.infix from "leanprover-community/mathlib"@"00f4ab49e7d5139216e0b3daad15fffa504897ab"

/-!
# Prefixes, subfixes, infixes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves properties about
* `list.prefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `list.subfix`: `l₁` is a subfix of `l₂` if `l₂` ends with `l₁`.
* `list.infix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some subfix of `l₂`.
* `list.inits`: The list of prefixes of a list.
* `list.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `data.list.defs`.

## Notation

`l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
`l₁ <:+ l₂`: `l₁` is a subfix of `l₂`.
`l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/


open Nat

variable {α β : Type _}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α} {m n : ℕ}

/-! ### prefix, suffix, infix -/


section Fix

#print List.prefix_append /-
@[simp]
theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  ⟨l₂, rfl⟩
#align list.prefix_append List.prefix_append
-/

#print List.suffix_append /-
@[simp]
theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  ⟨l₁, rfl⟩
#align list.suffix_append List.suffix_append
-/

#print List.infix_append /-
theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  ⟨l₁, l₃, rfl⟩
#align list.infix_append List.infix_append
-/

#print List.infix_append' /-
@[simp]
theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) := by
  rw [← List.append_assoc] <;> apply infix_append
#align list.infix_append' List.infix_append'
-/

#print List.IsPrefix.isInfix /-
theorem IsPrefix.isInfix : l₁ <+: l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨[], t, h⟩
#align list.is_prefix.is_infix List.IsPrefix.isInfix
-/

#print List.IsSuffix.isInfix /-
theorem IsSuffix.isInfix : l₁ <:+ l₂ → l₁ <:+: l₂ := fun ⟨t, h⟩ => ⟨t, [], by rw [h, append_nil]⟩
#align list.is_suffix.is_infix List.IsSuffix.isInfix
-/

#print List.nil_prefix /-
theorem nil_prefix (l : List α) : [] <+: l :=
  ⟨l, rfl⟩
#align list.nil_prefix List.nil_prefix
-/

#print List.nil_suffix /-
theorem nil_suffix (l : List α) : [] <:+ l :=
  ⟨l, append_nil _⟩
#align list.nil_suffix List.nil_suffix
-/

#print List.nil_infix /-
theorem nil_infix (l : List α) : [] <:+: l :=
  (nil_prefix _).IsInfix
#align list.nil_infix List.nil_infix
-/

#print List.prefix_refl /-
@[refl]
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], append_nil _⟩
#align list.prefix_refl List.prefix_refl
-/

#print List.suffix_refl /-
@[refl]
theorem suffix_refl (l : List α) : l <:+ l :=
  ⟨[], rfl⟩
#align list.suffix_refl List.suffix_refl
-/

#print List.infix_refl /-
@[refl]
theorem infix_refl (l : List α) : l <:+: l :=
  (prefix_refl l).IsInfix
#align list.infix_refl List.infix_refl
-/

#print List.prefix_rfl /-
theorem prefix_rfl : l <+: l :=
  prefix_refl _
#align list.prefix_rfl List.prefix_rfl
-/

#print List.suffix_rfl /-
theorem suffix_rfl : l <:+ l :=
  suffix_refl _
#align list.suffix_rfl List.suffix_rfl
-/

#print List.infix_rfl /-
theorem infix_rfl : l <:+: l :=
  infix_refl _
#align list.infix_rfl List.infix_rfl
-/

#print List.suffix_cons /-
@[simp]
theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l :=
  suffix_append [a]
#align list.suffix_cons List.suffix_cons
-/

#print List.prefix_concat /-
theorem prefix_concat (a : α) (l) : l <+: concat l a := by simp
#align list.prefix_concat List.prefix_concat
-/

#print List.infix_cons /-
theorem infix_cons : l₁ <:+: l₂ → l₁ <:+: a :: l₂ := fun ⟨L₁, L₂, h⟩ => ⟨a :: L₁, L₂, h ▸ rfl⟩
#align list.infix_cons List.infix_cons
-/

#print List.infix_concat /-
theorem infix_concat : l₁ <:+: l₂ → l₁ <:+: concat l₂ a := fun ⟨L₁, L₂, h⟩ =>
  ⟨L₁, concat L₂ a, by simp_rw [← h, concat_eq_append, append_assoc]⟩
#align list.infix_concat List.infix_concat
-/

#print List.IsPrefix.trans /-
@[trans]
theorem IsPrefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
  | l, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩
#align list.is_prefix.trans List.IsPrefix.trans
-/

#print List.IsSuffix.trans /-
@[trans]
theorem IsSuffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
  | l, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩
#align list.is_suffix.trans List.IsSuffix.trans
-/

#print List.IsInfix.trans /-
@[trans]
theorem IsInfix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
  | l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ => ⟨l₂ ++ l₁, r₁ ++ r₂, by simp only [append_assoc]⟩
#align list.is_infix.trans List.IsInfix.trans
-/

#print List.IsInfix.sublist /-
protected theorem IsInfix.sublist : l₁ <:+: l₂ → l₁ <+ l₂ := fun ⟨s, t, h⟩ => by rw [← h];
  exact (sublist_append_right _ _).trans (sublist_append_left _ _)
#align list.is_infix.sublist List.IsInfix.sublist
-/

#print List.IsInfix.subset /-
protected theorem IsInfix.subset (hl : l₁ <:+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_infix.subset List.IsInfix.subset
-/

#print List.IsPrefix.sublist /-
protected theorem IsPrefix.sublist (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.IsInfix.Sublist
#align list.is_prefix.sublist List.IsPrefix.sublist
-/

#print List.IsPrefix.subset /-
protected theorem IsPrefix.subset (hl : l₁ <+: l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_prefix.subset List.IsPrefix.subset
-/

#print List.IsSuffix.sublist /-
protected theorem IsSuffix.sublist (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.IsInfix.Sublist
#align list.is_suffix.sublist List.IsSuffix.sublist
-/

#print List.IsSuffix.subset /-
protected theorem IsSuffix.subset (hl : l₁ <:+ l₂) : l₁ ⊆ l₂ :=
  hl.Sublist.Subset
#align list.is_suffix.subset List.IsSuffix.subset
-/

#print List.reverse_suffix /-
@[simp]
theorem reverse_suffix : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_reverse l₁, ← reverse_append, e, reverse_reverse]⟩,
    fun ⟨r, e⟩ => ⟨reverse r, by rw [← reverse_append, e]⟩⟩
#align list.reverse_suffix List.reverse_suffix
-/

#print List.reverse_prefix /-
@[simp]
theorem reverse_prefix : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := by
  rw [← reverse_suffix] <;> simp only [reverse_reverse]
#align list.reverse_prefix List.reverse_prefix
-/

#print List.reverse_infix /-
@[simp]
theorem reverse_infix : reverse l₁ <:+: reverse l₂ ↔ l₁ <:+: l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by
      rw [← reverse_reverse l₁, append_assoc, ← reverse_append, ← reverse_append, e,
        reverse_reverse]⟩,
    fun ⟨s, t, e⟩ =>
    ⟨reverse t, reverse s, by rw [append_assoc, ← reverse_append, ← reverse_append, e]⟩⟩
#align list.reverse_infix List.reverse_infix
-/

alias ⟨_, is_suffix.reverse⟩ := reverse_prefix
#align list.is_suffix.reverse List.isSuffix.reverse

alias ⟨_, is_prefix.reverse⟩ := reverse_suffix
#align list.is_prefix.reverse List.isPrefix.reverse

alias ⟨_, is_infix.reverse⟩ := reverse_infix
#align list.is_infix.reverse List.isInfix.reverse

#print List.IsInfix.length_le /-
theorem IsInfix.length_le (h : l₁ <:+: l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_infix.length_le List.IsInfix.length_le
-/

#print List.IsPrefix.length_le /-
theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_prefix.length_le List.IsPrefix.length_le
-/

#print List.IsSuffix.length_le /-
theorem IsSuffix.length_le (h : l₁ <:+ l₂) : l₁.length ≤ l₂.length :=
  h.Sublist.length_le
#align list.is_suffix.length_le List.IsSuffix.length_le
-/

#print List.eq_nil_of_infix_nil /-
theorem eq_nil_of_infix_nil (h : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil h.Sublist
#align list.eq_nil_of_infix_nil List.eq_nil_of_infix_nil
-/

#print List.infix_nil /-
@[simp]
theorem infix_nil : l <:+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_sublist_nil h.Sublist, fun h => h ▸ infix_rfl⟩
#align list.infix_nil_iff List.infix_nil
-/

alias ⟨eq_nil_of_infix_nil, _⟩ := infix_nil_iff
#align list.eq_nil_of_infix_nil List.eq_nil_of_infix_nil

#print List.prefix_nil /-
@[simp]
theorem prefix_nil : l <+: [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.IsInfix, fun h => h ▸ prefix_rfl⟩
#align list.prefix_nil_iff List.prefix_nil
-/

#print List.suffix_nil /-
@[simp]
theorem suffix_nil : l <:+ [] ↔ l = [] :=
  ⟨fun h => eq_nil_of_infix_nil h.IsInfix, fun h => h ▸ suffix_rfl⟩
#align list.suffix_nil_iff List.suffix_nil
-/

alias ⟨eq_nil_of_prefix_nil, _⟩ := prefix_nil_iff
#align list.eq_nil_of_prefix_nil List.eq_nil_of_prefix_nil

alias ⟨eq_nil_of_suffix_nil, _⟩ := suffix_nil_iff
#align list.eq_nil_of_suffix_nil List.eq_nil_of_suffix_nil

#print List.infix_iff_prefix_suffix /-
theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨s, t, e⟩ => ⟨l₁ ++ t, ⟨_, rfl⟩, by rw [← e, append_assoc] <;> exact ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, s, e⟩ => ⟨s, t, by rw [append_assoc] <;> exact e⟩⟩
#align list.infix_iff_prefix_suffix List.infix_iff_prefix_suffix
-/

#print List.eq_of_infix_of_length_eq /-
theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_infix_of_length_eq List.eq_of_infix_of_length_eq
-/

#print List.eq_of_prefix_of_length_eq /-
theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_prefix_of_length_eq List.eq_of_prefix_of_length_eq
-/

#print List.eq_of_suffix_of_length_eq /-
theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.Sublist.eq_of_length
#align list.eq_of_suffix_of_length_eq List.eq_of_suffix_of_length_eq
-/

#print List.prefix_of_prefix_length_le /-
theorem prefix_of_prefix_length_le :
    ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
  | [], l₂, l₃, h₁, h₂, _ => nil_prefix _
  | a :: l₁, b :: l₂, _, ⟨r₁, rfl⟩, ⟨r₂, e⟩, ll =>
    by
    injection e with _ e'; subst b
    rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩ (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩
    exact ⟨r₃, rfl⟩
#align list.prefix_of_prefix_length_le List.prefix_of_prefix_length_le
-/

#print List.prefix_or_prefix_of_prefix /-
theorem prefix_or_prefix_of_prefix (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (le_total (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂)
    (prefix_of_prefix_length_le h₂ h₁)
#align list.prefix_or_prefix_of_prefix List.prefix_or_prefix_of_prefix
-/

#print List.suffix_of_suffix_length_le /-
theorem suffix_of_suffix_length_le (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) :
    l₁ <:+ l₂ :=
  reverse_prefix.1 <|
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂) (by simp [ll])
#align list.suffix_of_suffix_length_le List.suffix_of_suffix_length_le
-/

#print List.suffix_or_suffix_of_suffix /-
theorem suffix_or_suffix_of_suffix (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1
    reverse_prefix.1
#align list.suffix_or_suffix_of_suffix List.suffix_or_suffix_of_suffix
-/

#print List.suffix_cons_iff /-
theorem suffix_cons_iff : l₁ <:+ a :: l₂ ↔ l₁ = a :: l₂ ∨ l₁ <:+ l₂ :=
  by
  constructor
  · rintro ⟨⟨hd, tl⟩, hl₃⟩
    · exact Or.inl hl₃
    · simp only [cons_append] at hl₃ 
      exact Or.inr ⟨_, hl₃.2⟩
  · rintro (rfl | hl₁)
    · exact (a :: l₂).suffix_refl
    · exact hl₁.trans (l₂.suffix_cons _)
#align list.suffix_cons_iff List.suffix_cons_iff
-/

#print List.infix_cons_iff /-
theorem infix_cons_iff : l₁ <:+: a :: l₂ ↔ l₁ <+: a :: l₂ ∨ l₁ <:+: l₂ :=
  by
  constructor
  · rintro ⟨⟨hd, tl⟩, t, hl₃⟩
    · exact Or.inl ⟨t, hl₃⟩
    · simp only [cons_append] at hl₃ 
      exact Or.inr ⟨_, t, hl₃.2⟩
  · rintro (h | hl₁)
    · exact h.is_infix
    · exact infix_cons hl₁
#align list.infix_cons_iff List.infix_cons_iff
-/

#print List.infix_of_mem_join /-
theorem infix_of_mem_join : ∀ {L : List (List α)}, l ∈ L → l <:+: join L
  | _ :: L, Or.inl rfl => infix_append [] _ _
  | l' :: L, Or.inr h => IsInfix.trans (infix_of_mem_join h) <| (suffix_append _ _).IsInfix
#align list.infix_of_mem_join List.infix_of_mem_join
-/

#print List.prefix_append_right_inj /-
theorem prefix_append_right_inj (l) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr fun r => by rw [append_assoc, append_right_inj]
#align list.prefix_append_right_inj List.prefix_append_right_inj
-/

#print List.prefix_cons_inj /-
theorem prefix_cons_inj (a) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]
#align list.prefix_cons_inj List.prefix_cons_inj
-/

#print List.take_prefix /-
theorem take_prefix (n) (l : List α) : take n l <+: l :=
  ⟨_, take_append_drop _ _⟩
#align list.take_prefix List.take_prefix
-/

#print List.drop_suffix /-
theorem drop_suffix (n) (l : List α) : drop n l <:+ l :=
  ⟨_, take_append_drop _ _⟩
#align list.drop_suffix List.drop_suffix
-/

#print List.take_sublist /-
theorem take_sublist (n) (l : List α) : take n l <+ l :=
  (take_prefix n l).Sublist
#align list.take_sublist List.take_sublist
-/

#print List.drop_sublist /-
theorem drop_sublist (n) (l : List α) : drop n l <+ l :=
  (drop_suffix n l).Sublist
#align list.drop_sublist List.drop_sublist
-/

#print List.take_subset /-
theorem take_subset (n) (l : List α) : take n l ⊆ l :=
  (take_sublist n l).Subset
#align list.take_subset List.take_subset
-/

#print List.drop_subset /-
theorem drop_subset (n) (l : List α) : drop n l ⊆ l :=
  (drop_sublist n l).Subset
#align list.drop_subset List.drop_subset
-/

#print List.mem_of_mem_take /-
theorem mem_of_mem_take (h : a ∈ l.take n) : a ∈ l :=
  take_subset n l h
#align list.mem_of_mem_take List.mem_of_mem_take
-/

#print List.mem_of_mem_drop /-
theorem mem_of_mem_drop (h : a ∈ l.drop n) : a ∈ l :=
  drop_subset n l h
#align list.mem_of_mem_drop List.mem_of_mem_drop
-/

#print List.dropSlice_sublist /-
theorem dropSlice_sublist (n m : ℕ) (l : List α) : l.slice n m <+ l :=
  by
  rw [List.dropSlice_eq]
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.append_sublist_append_left, add_comm, List.drop_add]
  exact List.drop_sublist _ _
#align list.slice_sublist List.dropSlice_sublist
-/

#print List.dropSlice_subset /-
theorem dropSlice_subset (n m : ℕ) (l : List α) : l.slice n m ⊆ l :=
  (dropSlice_sublist n m l).Subset
#align list.slice_subset List.dropSlice_subset
-/

#print List.mem_of_mem_dropSlice /-
theorem mem_of_mem_dropSlice {n m : ℕ} {l : List α} {a : α} (h : a ∈ l.slice n m) : a ∈ l :=
  dropSlice_subset n m l h
#align list.mem_of_mem_slice List.mem_of_mem_dropSlice
-/

#print List.takeWhile_prefix /-
theorem takeWhile_prefix (p : α → Prop) [DecidablePred p] : l.takeWhile p <+: l :=
  ⟨l.dropWhileₓ p, takeWhile_append_dropWhile p l⟩
#align list.take_while_prefix List.takeWhile_prefix
-/

#print List.dropWhile_suffix /-
theorem dropWhile_suffix (p : α → Prop) [DecidablePred p] : l.dropWhileₓ p <:+ l :=
  ⟨l.takeWhile p, takeWhile_append_dropWhile p l⟩
#align list.drop_while_suffix List.dropWhile_suffix
-/

#print List.dropLast_prefix /-
theorem dropLast_prefix : ∀ l : List α, l.dropLast <+: l
  | [] => ⟨nil, by rw [init, List.append_nil]⟩
  | a :: l => ⟨_, dropLast_append_getLast (cons_ne_nil a l)⟩
#align list.init_prefix List.dropLast_prefix
-/

#print List.tail_suffix /-
theorem tail_suffix (l : List α) : tail l <:+ l := by rw [← drop_one] <;> apply drop_suffix
#align list.tail_suffix List.tail_suffix
-/

#print List.dropLast_sublist /-
theorem dropLast_sublist (l : List α) : l.dropLast <+ l :=
  (dropLast_prefix l).Sublist
#align list.init_sublist List.dropLast_sublist
-/

#print List.tail_sublist /-
theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).Sublist
#align list.tail_sublist List.tail_sublist
-/

#print List.dropLast_subset /-
theorem dropLast_subset (l : List α) : l.dropLast ⊆ l :=
  (dropLast_sublist l).Subset
#align list.init_subset List.dropLast_subset
-/

#print List.tail_subset /-
theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).Subset
#align list.tail_subset List.tail_subset
-/

#print List.mem_of_mem_dropLast /-
theorem mem_of_mem_dropLast (h : a ∈ l.dropLast) : a ∈ l :=
  dropLast_subset l h
#align list.mem_of_mem_init List.mem_of_mem_dropLast
-/

#print List.mem_of_mem_tail /-
theorem mem_of_mem_tail (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h
#align list.mem_of_mem_tail List.mem_of_mem_tail
-/

#print List.prefix_iff_eq_append /-
theorem prefix_iff_eq_append : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩ <;> rw [drop_left], fun e => ⟨_, e⟩⟩
#align list.prefix_iff_eq_append List.prefix_iff_eq_append
-/

#print List.suffix_iff_eq_append /-
theorem suffix_iff_eq_append : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by rintro ⟨r, rfl⟩ <;> simp only [length_append, add_tsub_cancel_right, take_left], fun e =>
    ⟨_, e⟩⟩
#align list.suffix_iff_eq_append List.suffix_iff_eq_append
-/

#print List.prefix_iff_eq_take /-
theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_right_cancel <| (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩
#align list.prefix_iff_eq_take List.prefix_iff_eq_take
-/

#print List.suffix_iff_eq_drop /-
theorem suffix_iff_eq_drop : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel <| (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩
#align list.suffix_iff_eq_drop List.suffix_iff_eq_drop
-/

#print List.decidablePrefix /-
instance decidablePrefix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+: l₂)
  | [], l₂ => isTrue ⟨l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨t, te⟩ => List.noConfusion te
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      decidable_of_decidable_of_iff (decidable_prefix l₁ l₂) (by rw [← h, prefix_cons_inj])
    else isFalse fun ⟨t, te⟩ => h <| by injection te
#align list.decidable_prefix List.decidablePrefix
-/

#print List.decidableSuffix /-
-- Alternatively, use mem_tails
instance decidableSuffix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+ l₂)
  | [], l₂ => isTrue ⟨l₂, append_nil _⟩
  | a :: l₁, [] => isFalse <| mt (Sublist.length_le ∘ IsSuffix.sublist) (by decide)
  | l₁, b :: l₂ =>
    decidable_of_decidable_of_iff (@Or.decidable _ _ _ (l₁.decidableSuffix l₂)) suffix_cons_iff.symm
#align list.decidable_suffix List.decidableSuffix
-/

#print List.decidableInfix /-
instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te  <;> exact te
  | l₁, b :: l₂ =>
    decidable_of_decidable_of_iff
      (@Or.decidable _ _ (l₁.decidablePrefix (b :: l₂)) (l₁.decidableInfix l₂)) infix_cons_iff.symm
#align list.decidable_infix List.decidableInfix
-/

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:570:6: unsupported: specialize @hyp -/
#print List.prefix_take_le_iff /-
theorem prefix_take_le_iff {L : List (List (Option α))} (hm : m < L.length) :
    L.take m <+: L.take n ↔ m ≤ n :=
  by
  simp only [prefix_iff_eq_take, length_take]
  induction' m with m IH generalizing L n
  · simp only [min_eq_left, eq_self_iff_true, Nat.zero_le, take]
  cases' L with l ls
  · exact (not_lt_bot hm).elim
  cases n
  · refine' iff_of_false _ (zero_lt_succ _).not_le
    rw [take_zero, take_nil]
    simp only [take]
    exact not_false
  · simp only [length] at hm 
    specialize IH ls n (Nat.lt_of_succ_lt_succ hm)
    simp only [le_of_lt (Nat.lt_of_succ_lt_succ hm), min_eq_left] at IH 
    simp only [le_of_lt hm, IH, true_and_iff, min_eq_left, eq_self_iff_true, length, take]
    exact ⟨Nat.succ_le_succ, Nat.le_of_succ_le_succ⟩
#align list.prefix_take_le_iff List.prefix_take_le_iff
-/

#print List.cons_prefix_iff /-
theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ :=
  by
  constructor
  · rintro ⟨L, hL⟩
    simp only [cons_append] at hL 
    exact ⟨hL.left, ⟨L, hL.right⟩⟩
  · rintro ⟨rfl, h⟩
    rwa [prefix_cons_inj]
#align list.cons_prefix_iff List.cons_prefix_iff
-/

#print List.IsPrefix.map /-
theorem IsPrefix.map (h : l₁ <+: l₂) (f : α → β) : l₁.map f <+: l₂.map f :=
  by
  induction' l₁ with hd tl hl generalizing l₂
  · simp only [nil_prefix, map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h 
      simp only [h, prefix_cons_inj, hl, map]
#align list.is_prefix.map List.IsPrefix.map
-/

#print List.IsPrefix.filter_map /-
theorem IsPrefix.filter_map (h : l₁ <+: l₂) (f : α → Option β) :
    l₁.filterMap f <+: l₂.filterMap f :=
  by
  induction' l₁ with hd₁ tl₁ hl generalizing l₂
  · simp only [nil_prefix, filter_map_nil]
  · cases' l₂ with hd₂ tl₂
    · simpa only using eq_nil_of_prefix_nil h
    · rw [cons_prefix_iff] at h 
      rw [← @singleton_append _ hd₁ _, ← @singleton_append _ hd₂ _, filter_map_append,
        filter_map_append, h.left, prefix_append_right_inj]
      exact hl h.right
#align list.is_prefix.filter_map List.IsPrefix.filter_map
-/

#print List.IsPrefix.reduceOption /-
theorem IsPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id
#align list.is_prefix.reduce_option List.IsPrefix.reduceOption
-/

#print List.IsPrefix.filter /-
theorem IsPrefix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <+: l₂) :
    l₁.filterₓ p <+: l₂.filterₓ p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact prefix_append _ _
#align list.is_prefix.filter List.IsPrefix.filter
-/

#print List.IsSuffix.filter /-
theorem IsSuffix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+ l₂) :
    l₁.filterₓ p <:+ l₂.filterₓ p := by
  obtain ⟨xs, rfl⟩ := h
  rw [filter_append]
  exact suffix_append _ _
#align list.is_suffix.filter List.IsSuffix.filter
-/

#print List.IsInfix.filter /-
theorem IsInfix.filter (p : α → Prop) [DecidablePred p] ⦃l₁ l₂ : List α⦄ (h : l₁ <:+: l₂) :
    l₁.filterₓ p <:+: l₂.filterₓ p :=
  by
  obtain ⟨xs, ys, rfl⟩ := h
  rw [filter_append, filter_append]
  exact infix_append _ _ _
#align list.is_infix.filter List.IsInfix.filter
-/

instance : IsPartialOrder (List α) (· <+: ·)
    where
  refl := prefix_refl
  trans _ _ _ := IsPrefix.trans
  antisymm _ _ h₁ h₂ := eq_of_prefix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·)
    where
  refl := suffix_refl
  trans _ _ _ := IsSuffix.trans
  antisymm _ _ h₁ h₂ := eq_of_suffix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·)
    where
  refl := infix_refl
  trans _ _ _ := IsInfix.trans
  antisymm _ _ h₁ h₂ := eq_of_infix_of_length_eq h₁ <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

#print List.mem_inits /-
@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_refl [], eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht] <;> exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        List.noConfusion hr fun ba (st : s ++ r = t) =>
          Or.inr <| by rw [ba] <;> exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩
#align list.mem_inits List.mem_inits
-/

#print List.mem_tails /-
@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton] <;>
      exact ⟨fun h => by rw [h] <;> exact suffix_refl [], eq_nil_of_suffix_nil⟩
  | s, a :: t => by
    simp only [tails, mem_cons_iff, mem_tails s t] <;>
      exact
        show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
          ⟨fun o =>
            match s, t, o with
            | _, t, Or.inl rfl => suffix_rfl
            | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
            fun e =>
            match s, t, e with
            | _, t, ⟨[], rfl⟩ => Or.inl rfl
            | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun ab lt => Or.inr ⟨l, lt⟩⟩
#align list.mem_tails List.mem_tails
-/

#print List.inits_cons /-
theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp
#align list.inits_cons List.inits_cons
-/

#print List.tails_cons /-
theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp
#align list.tails_cons List.tails_cons
-/

#print List.inits_append /-
@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [inits_append s t]
#align list.inits_append List.inits_append
-/

#print List.tails_append /-
@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]
#align list.tails_append List.tails_append
-/

#print List.inits_eq_tails /-
-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_eq_map_iff]
#align list.inits_eq_tails List.inits_eq_tails
-/

#print List.tails_eq_inits /-
theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l, append_left_inj]
#align list.tails_eq_inits List.tails_eq_inits
-/

#print List.inits_reverse /-
theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]; simp [reverse_involutive.comp_self]
#align list.inits_reverse List.inits_reverse
-/

#print List.tails_reverse /-
theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]; simp [reverse_involutive.comp_self]
#align list.tails_reverse List.tails_reverse
-/

#print List.map_reverse_inits /-
theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]; simp [reverse_involutive.comp_self]
#align list.map_reverse_inits List.map_reverse_inits
-/

#print List.map_reverse_tails /-
theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]; simp [reverse_involutive.comp_self]
#align list.map_reverse_tails List.map_reverse_tails
-/

#print List.length_tails /-
@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 :=
  by
  induction' l with x l IH
  · simp
  · simpa using IH
#align list.length_tails List.length_tails
-/

#print List.length_inits /-
@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]
#align list.length_inits List.length_inits
-/

#print List.nth_le_tails /-
@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) :
    nthLe (tails l) n hn = l.drop n :=
  by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp
    · simpa using IH n _
#align list.nth_le_tails List.nth_le_tails
-/

#print List.nth_le_inits /-
@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) :
    nthLe (inits l) n hn = l.take n :=
  by
  induction' l with x l IH generalizing n
  · simp
  · cases n
    · simp
    · simpa using IH n _
#align list.nth_le_inits List.nth_le_inits
-/

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

#print List.insert_nil /-
@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl
#align list.insert_nil List.insert_nil
-/

#print List.insert.def /-
theorem insert.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl
#align list.insert.def List.insert.def
-/

#print List.insert_of_mem /-
@[simp]
theorem insert_of_mem (h : a ∈ l) : insert a l = l := by simp only [insert.def, if_pos h]
#align list.insert_of_mem List.insert_of_mem
-/

#print List.insert_of_not_mem /-
@[simp]
theorem insert_of_not_mem (h : a ∉ l) : insert a l = a :: l := by
  simp only [insert.def, if_neg h] <;> constructor <;> rfl
#align list.insert_of_not_mem List.insert_of_not_mem
-/

#print List.mem_insert_iff /-
@[simp]
theorem mem_insert_iff : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
  by
  by_cases h' : b ∈ l
  · simp only [insert_of_mem h']
    apply (or_iff_right_of_imp _).symm
    exact fun e => e.symm ▸ h'
  · simp only [insert_of_not_mem h', mem_cons_iff]
#align list.mem_insert_iff List.mem_insert_iff
-/

#print List.suffix_insert /-
@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ insert a l := by
  by_cases a ∈ l <;> [simp only [insert_of_mem h]; simp only [insert_of_not_mem h, suffix_cons]]
#align list.suffix_insert List.suffix_insert
-/

#print List.infix_insert /-
theorem infix_insert (a : α) (l : List α) : l <:+: insert a l :=
  (suffix_insert a l).IsInfix
#align list.infix_insert List.infix_insert
-/

#print List.sublist_insert /-
theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).Sublist
#align list.sublist_insert List.sublist_insert
-/

#print List.subset_insert /-
theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).Subset
#align list.subset_insert List.subset_insert
-/

#print List.mem_insert_self /-
@[simp]
theorem mem_insert_self (a : α) (l : List α) : a ∈ l.insert a :=
  mem_insert_iff.2 <| Or.inl rfl
#align list.mem_insert_self List.mem_insert_self
-/

#print List.mem_insert_of_mem /-
theorem mem_insert_of_mem (h : a ∈ l) : a ∈ insert b l :=
  mem_insert_iff.2 (Or.inr h)
#align list.mem_insert_of_mem List.mem_insert_of_mem
-/

#print List.eq_or_mem_of_mem_insert /-
theorem eq_or_mem_of_mem_insert (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
  mem_insert_iff.1 h
#align list.eq_or_mem_of_mem_insert List.eq_or_mem_of_mem_insert
-/

#print List.length_insert_of_mem /-
@[simp]
theorem length_insert_of_mem (h : a ∈ l) : (insert a l).length = l.length :=
  congr_arg _ <| insert_of_mem h
#align list.length_insert_of_mem List.length_insert_of_mem
-/

#print List.length_insert_of_not_mem /-
@[simp]
theorem length_insert_of_not_mem (h : a ∉ l) : (insert a l).length = l.length + 1 :=
  congr_arg _ <| insert_of_not_mem h
#align list.length_insert_of_not_mem List.length_insert_of_not_mem
-/

end Insert

#print List.mem_of_mem_suffix /-
theorem mem_of_mem_suffix (hx : a ∈ l₁) (hl : l₁ <:+ l₂) : a ∈ l₂ :=
  hl.Subset hx
#align list.mem_of_mem_suffix List.mem_of_mem_suffix
-/

end List

