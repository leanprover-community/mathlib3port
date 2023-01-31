/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Order.Basic

/-!
# Basic properties of lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open Nat hiding one_pos

assert_not_exists Set.range

namespace List

universe u v w x

variable {ι : Type _} {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {l₁ l₂ : List α}

attribute [inline] List.headI

#print List.uniqueOfIsEmpty /-
/-- There is only one list of an empty type -/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { List.inhabited α with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: l => isEmptyElim a }
#align list.unique_of_is_empty List.uniqueOfIsEmpty
-/

instance : IsLeftId (List α) Append.append [] :=
  ⟨nil_append⟩

instance : IsRightId (List α) Append.append [] :=
  ⟨append_nil⟩

instance : IsAssociative (List α) Append.append :=
  ⟨append_assoc⟩

#print List.cons_ne_nil /-
theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] :=
  fun.
#align list.cons_ne_nil List.cons_ne_nil
-/

#print List.cons_ne_self /-
theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l :=
  mt (congr_arg length) (Nat.succ_ne_self _)
#align list.cons_ne_self List.cons_ne_self
-/

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → h₁ = h₂ :=
  fun Peq => List.noConfusion Peq fun Pheq Pteq => Pheq
#align list.head_eq_of_cons_eq List.head_eq_of_cons_eqₓ

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → t₁ = t₂ :=
  fun Peq => List.noConfusion Peq fun Pheq Pteq => Pteq
#align list.tail_eq_of_cons_eq List.tail_eq_of_cons_eqₓ

#print List.cons_injective /-
@[simp]
theorem cons_injective {a : α} : Injective (cons a) := fun l₁ l₂ => fun Pe => tail_eq_of_cons_eq Pe
#align list.cons_injective List.cons_injective
-/

#print List.cons_inj /-
theorem cons_inj (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  cons_injective.eq_iff
#align list.cons_inj List.cons_inj
-/

#print List.cons_eq_cons /-
theorem cons_eq_cons {a b : α} {l l' : List α} : a :: l = b :: l' ↔ a = b ∧ l = l' :=
  ⟨List.cons.inj, fun h => h.1 ▸ h.2 ▸ rfl⟩
#align list.cons_eq_cons List.cons_eq_cons
-/

#print List.singleton_injective /-
theorem singleton_injective : Injective fun a : α => [a] := fun a b h => (cons_eq_cons.1 h).1
#align list.singleton_injective List.singleton_injective
-/

#print List.singleton_inj /-
theorem singleton_inj {a b : α} : [a] = [b] ↔ a = b :=
  singleton_injective.eq_iff
#align list.singleton_inj List.singleton_inj
-/

#print List.exists_cons_of_ne_nil /-
theorem exists_cons_of_ne_nil {l : List α} (h : l ≠ nil) : ∃ b L, l = b :: L :=
  by
  induction' l with c l'
  contradiction
  use c, l'
#align list.exists_cons_of_ne_nil List.exists_cons_of_ne_nil
-/

#print List.set_of_mem_cons /-
theorem set_of_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
  rfl
#align list.set_of_mem_cons List.set_of_mem_cons
-/

/-! ### mem -/


#print List.mem_singleton_self /-
theorem mem_singleton_self (a : α) : a ∈ [a] :=
  mem_cons_self _ _
#align list.mem_singleton_self List.mem_singleton_self
-/

#print List.eq_of_mem_singleton /-
theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b := fun this : a ∈ [b] =>
  Or.elim (eq_or_mem_of_mem_cons this) (fun this : a = b => this) fun this : a ∈ [] =>
    absurd this (not_mem_nil a)
#align list.eq_of_mem_singleton List.eq_of_mem_singleton
-/

#print List.mem_singleton /-
@[simp]
theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, Or.inl⟩
#align list.mem_singleton List.mem_singleton
-/

#print List.mem_of_mem_cons_of_mem /-
theorem mem_of_mem_cons_of_mem {a b : α} {l : List α} : a ∈ b :: l → b ∈ l → a ∈ l :=
  fun ainbl binl =>
  Or.elim (eq_or_mem_of_mem_cons ainbl) (fun this : a = b => by subst a; exact binl)
    fun this : a ∈ l => this
#align list.mem_of_mem_cons_of_mem List.mem_of_mem_cons_of_mem
-/

#print Decidable.List.eq_or_ne_mem_of_mem /-
theorem Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α] {a b : α} {l : List α} (h : a ∈ b :: l) :
    a = b ∨ a ≠ b ∧ a ∈ l :=
  Decidable.byCases Or.inl fun this : a ≠ b => h.elim Or.inl fun h => Or.inr ⟨this, h⟩
#align decidable.list.eq_or_ne_mem_of_mem Decidable.List.eq_or_ne_mem_of_mem
-/

#print List.eq_or_ne_mem_of_mem /-
theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} : a ∈ b :: l → a = b ∨ a ≠ b ∧ a ∈ l := by
  classical exact Decidable.List.eq_or_ne_mem_of_mem
#align list.eq_or_ne_mem_of_mem List.eq_or_ne_mem_of_mem
-/

#print List.not_mem_append /-
theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1 <| not_or.2 ⟨h₁, h₂⟩
#align list.not_mem_append List.not_mem_append
-/

#print List.ne_nil_of_mem /-
theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  intro e <;> rw [e] at h <;> cases h
#align list.ne_nil_of_mem List.ne_nil_of_mem
-/

#print List.mem_split /-
theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t :=
  by
  induction' l with b l ih; · cases h; rcases h with (rfl | h)
  · exact ⟨[], l, rfl⟩
  · rcases ih h with ⟨s, t, rfl⟩
    exact ⟨b :: s, t, rfl⟩
#align list.mem_split List.mem_split
-/

#print List.mem_of_ne_of_mem /-
theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  Or.elim (eq_or_mem_of_mem_cons h₂) (fun e => absurd e h₁) fun r => r
#align list.mem_of_ne_of_mem List.mem_of_ne_of_mem
-/

#print List.ne_of_not_mem_cons /-
theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ≠ b := fun nin aeqb =>
  absurd (Or.inl aeqb) nin
#align list.ne_of_not_mem_cons List.ne_of_not_mem_cons
-/

#print List.not_mem_of_not_mem_cons /-
theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ∉ l := fun nin nainl =>
  absurd (Or.inr nainl) nin
#align list.not_mem_of_not_mem_cons List.not_mem_of_not_mem_cons
-/

#print List.not_mem_cons_of_ne_of_not_mem /-
theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y :: l :=
  fun p1 p2 => Not.intro fun Pain => absurd (eq_or_mem_of_mem_cons Pain) (not_or_of_not p1 p2)
#align list.not_mem_cons_of_ne_of_not_mem List.not_mem_cons_of_ne_of_not_mem
-/

#print List.ne_and_not_mem_of_not_mem_cons /-
theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y :: l → a ≠ y ∧ a ∉ l :=
  fun p => And.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)
#align list.ne_and_not_mem_of_not_mem_cons List.ne_and_not_mem_of_not_mem_cons
-/

#print List.mem_map' /-
@[simp]
theorem mem_map' {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  by
  -- This proof uses no axioms, that's why it's longer that `induction`; simp [...]
  induction' l with a l ihl
  · constructor
    · rintro ⟨_⟩
    · rintro ⟨a, ⟨_⟩, _⟩
  · refine' (or_congr eq_comm ihl).trans _
    constructor
    · rintro (h | ⟨c, hcl, h⟩)
      exacts[⟨a, Or.inl rfl, h⟩, ⟨c, Or.inr hcl, h⟩]
    · rintro ⟨c, hc | hc, h⟩
      exacts[Or.inl <| (congr_arg f hc.symm).trans h, Or.inr ⟨c, hc, h⟩]
#align list.mem_map List.mem_map'
-/

alias mem_map ↔ exists_of_mem_map _
#align list.exists_of_mem_map List.exists_of_mem_map'

theorem mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l :=
  mem_map'.2 ⟨a, h, rfl⟩
#align list.mem_map_of_mem List.mem_map_of_memₓ

#print List.mem_map_of_injective /-
theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m =>
    let ⟨a', m', e⟩ := exists_of_mem_map' m
    H e ▸ m',
    mem_map_of_mem _⟩
#align list.mem_map_of_injective List.mem_map_of_injective
-/

#print Function.Involutive.exists_mem_and_apply_eq_iff /-
@[simp]
theorem Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α} (hf : Function.Involutive f)
    (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by
    rintro ⟨y, h, rfl⟩
    rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
#align function.involutive.exists_mem_and_apply_eq_iff Function.Involutive.exists_mem_and_apply_eq_iff
-/

#print List.mem_map_of_involutive /-
theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]
#align list.mem_map_of_involutive List.mem_map_of_involutive
-/

theorem forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
    (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) :=
  by
  constructor
  · intro H j hj
    exact H (f j) (mem_map_of_mem f hj)
  · intro H i hi
    rcases mem_map.1 hi with ⟨j, hj, ji⟩
    rw [← ji]
    exact H j hj
#align list.forall_mem_map_iff List.forall_mem_map_iffₓ

@[simp]
theorem map_eq_nil {f : α → β} {l : List α} : List.map f l = [] ↔ l = [] :=
  ⟨by cases l <;> simp only [forall_prop_of_true, map, forall_prop_of_false, not_false_iff],
    fun h => h.symm ▸ rfl⟩
#align list.map_eq_nil List.map_eq_nilₓ

#print List.mem_join /-
@[simp]
theorem mem_join {a : α} : ∀ {L : List (List α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
  | [] => ⟨False.elim, fun ⟨_, h, _⟩ => False.elim h⟩
  | c :: L => by
    simp only [join, mem_append, @mem_join L, mem_cons_iff, or_and_right, exists_or, exists_eq_left]
#align list.mem_join List.mem_join
-/

#print List.exists_of_mem_join /-
theorem exists_of_mem_join {a : α} {L : List (List α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
  mem_join.1
#align list.exists_of_mem_join List.exists_of_mem_join
-/

theorem mem_join_of_mem {a : α} {L : List (List α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
  mem_join.2 ⟨l, lL, al⟩
#align list.mem_join_of_mem List.mem_join_of_memₓ

@[simp]
theorem mem_bind {b : β} {l : List α} {f : α → List β} : b ∈ List.bind l f ↔ ∃ a ∈ l, b ∈ f a :=
  Iff.trans mem_join
    ⟨fun ⟨l', h1, h2⟩ =>
      let ⟨a, al, fa⟩ := exists_of_mem_map' h1
      ⟨a, al, fa.symm ▸ h2⟩,
      fun ⟨a, al, bfa⟩ => ⟨f a, mem_map_of_mem _ al, bfa⟩⟩
#align list.mem_bind List.mem_bindₓ

theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} :
    b ∈ List.bind l f → ∃ a ∈ l, b ∈ f a :=
  mem_bind.1
#align list.exists_of_mem_bind List.exists_of_mem_bindₓ

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) :
    b ∈ List.bind l f :=
  mem_bind.2 ⟨a, al, h⟩
#align list.mem_bind_of_mem List.mem_bind_of_memₓ

theorem bind_map {g : α → List β} {f : β → γ} :
    ∀ l : List α, List.map f (l.bind g) = l.bind fun a => (g a).map f
  | [] => rfl
  | a :: l => by simp only [cons_bind, map_append, bind_map l]
#align list.bind_map List.bind_mapₓ

#print List.map_bind /-
theorem map_bind (g : β → List γ) (f : α → β) :
    ∀ l : List α, (List.map f l).bind g = l.bind fun a => g (f a)
  | [] => rfl
  | a :: l => by simp only [cons_bind, map_cons, map_bind l]
#align list.map_bind List.map_bind
-/

/-! ### length -/


#print List.length_eq_zero /-
theorem length_eq_zero {l : List α} : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h.symm ▸ rfl⟩
#align list.length_eq_zero List.length_eq_zero
-/

#print List.length_singleton /-
@[simp]
theorem length_singleton (a : α) : length [a] = 1 :=
  rfl
#align list.length_singleton List.length_singleton
-/

#print List.length_pos_of_mem /-
theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
  | b :: l, _ => zero_lt_succ _
#align list.length_pos_of_mem List.length_pos_of_mem
-/

#print List.exists_mem_of_length_pos /-
theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
  | b :: l, _ => ⟨b, mem_cons_self _ _⟩
#align list.exists_mem_of_length_pos List.exists_mem_of_length_pos
-/

#print List.length_pos_iff_exists_mem /-
theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨a, h⟩ => length_pos_of_mem h⟩
#align list.length_pos_iff_exists_mem List.length_pos_iff_exists_mem
-/

#print List.ne_nil_of_length_pos /-
theorem ne_nil_of_length_pos {l : List α} : 0 < length l → l ≠ [] := fun h1 h2 =>
  lt_irrefl 0 ((length_eq_zero.2 h2).subst h1)
#align list.ne_nil_of_length_pos List.ne_nil_of_length_pos
-/

#print List.length_pos_of_ne_nil /-
theorem length_pos_of_ne_nil {l : List α} : l ≠ [] → 0 < length l := fun h =>
  pos_iff_ne_zero.2 fun h0 => h <| length_eq_zero.1 h0
#align list.length_pos_of_ne_nil List.length_pos_of_ne_nil
-/

#print List.length_pos_iff_ne_nil /-
theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩
#align list.length_pos_iff_ne_nil List.length_pos_iff_ne_nil
-/

#print List.exists_mem_of_ne_nil /-
theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos_of_ne_nil h)
#align list.exists_mem_of_ne_nil List.exists_mem_of_ne_nil
-/

#print List.length_eq_one /-
theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨match l with
    | [a], _ => ⟨a, rfl⟩,
    fun ⟨a, e⟩ => e.symm ▸ rfl⟩
#align list.length_eq_one List.length_eq_one
-/

#print List.exists_of_length_succ /-
theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, H => ⟨h, t, rfl⟩
#align list.exists_of_length_succ List.exists_of_length_succ
-/

#print List.length_injective_iff /-
@[simp]
theorem length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α :=
  by
  constructor
  · intro h
    refine' ⟨fun x y => _⟩
    suffices [x] = [y] by simpa using this
    apply h
    rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    congr
    exact Subsingleton.elim _ _
    apply l1_ih
    simpa using hl
#align list.length_injective_iff List.length_injective_iff
-/

#print List.length_injective /-
@[simp]
theorem length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr <| by infer_instance
#align list.length_injective List.length_injective
-/

#print List.length_eq_two /-
theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨match l with
    | [a, b], _ => ⟨a, b, rfl⟩,
    fun ⟨a, b, e⟩ => e.symm ▸ rfl⟩
#align list.length_eq_two List.length_eq_two
-/

#print List.length_eq_three /-
theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨match l with
    | [a, b, c], _ => ⟨a, b, c, rfl⟩,
    fun ⟨a, b, c, e⟩ => e.symm ▸ rfl⟩
#align list.length_eq_three List.length_eq_three
-/

alias length_le_of_sublist ← sublist.length_le
#align list.sublist.length_le List.Sublist.length_le

/-! ### set-theoretic notation of lists -/


#print List.empty_eq /-
theorem empty_eq : (∅ : List α) = [] := by rfl
#align list.empty_eq List.empty_eq
-/

#print List.singleton_eq /-
theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl
#align list.singleton_eq List.singleton_eq
-/

#print List.insert_neg /-
theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) : Insert.insert x l = x :: l :=
  if_neg h
#align list.insert_neg List.insert_neg
-/

#print List.insert_pos /-
theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : Insert.insert x l = l :=
  if_pos h
#align list.insert_pos List.insert_pos
-/

#print List.doubleton_eq /-
theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] :=
  by
  rw [insert_neg, singleton_eq]
  rwa [singleton_eq, mem_singleton]
#align list.doubleton_eq List.doubleton_eq
-/

/-! ### bounded quantifiers over lists -/


#print List.forall_mem_nil /-
theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x :=
  fun.
#align list.forall_mem_nil List.forall_mem_nil
-/

#print List.forall_mem_cons /-
theorem forall_mem_cons :
    ∀ {p : α → Prop} {a : α} {l : List α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
  ball_cons
#align list.forall_mem_cons List.forall_mem_cons
-/

#print List.forall_mem_of_forall_mem_cons /-
theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x ∈ a :: l, p x) :
    ∀ x ∈ l, p x :=
  (forall_mem_cons.1 h).2
#align list.forall_mem_of_forall_mem_cons List.forall_mem_of_forall_mem_cons
-/

#print List.forall_mem_singleton /-
theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a := by
  simp only [mem_singleton, forall_eq]
#align list.forall_mem_singleton List.forall_mem_singleton
-/

#print List.forall_mem_append /-
theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
    (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x := by
  simp only [mem_append, or_imp, forall_and]
#align list.forall_mem_append List.forall_mem_append
-/

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun.
#align list.not_exists_mem_nil List.not_exists_mem_nilₓ

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  BEx.intro a (mem_cons_self _ _) h
#align list.exists_mem_cons_of List.exists_mem_cons_ofₓ

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} (h : ∃ x ∈ l, p x) :
    ∃ x ∈ a :: l, p x :=
  BEx.elim h fun x xl px => BEx.intro x (mem_cons_of_mem _ xl) px
#align list.exists_mem_cons_of_exists List.exists_mem_cons_of_existsₓ

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∃ x ∈ a :: l, p x) :
    p a ∨ ∃ x ∈ l, p x :=
  BEx.elim h fun x xal px =>
    Or.elim (eq_or_mem_of_mem_cons xal) (fun this : x = a => by rw [← this]; left; exact px)
      fun this : x ∈ l => Or.inr (BEx.intro x this px)
#align list.or_exists_of_exists_mem_cons List.or_exists_of_exists_mem_consₓ

/- warning: list.exists_mem_cons_iff -> List.exists_mem_cons_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (a : α) (l : List.{u1} α), Iff (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x (List.cons.{u1} α a l)) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x (List.cons.{u1} α a l)) => p x))) (Or (p a) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) => p x))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) (a : α) (l : List.{u1} α), Iff (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x (List.cons.{u1} α a l)) (p x))) (Or (p a) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) (p x))))
Case conversion may be inaccurate. Consider using '#align list.exists_mem_cons_iff List.exists_mem_cons_iffₓ'. -/
theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h =>
    Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists
#align list.exists_mem_cons_iff List.exists_mem_cons_iff

/-! ### list subset -/


instance : IsTrans (List α) (· ⊆ ·) :=
  ⟨fun _ _ _ => List.Subset.trans⟩

#print List.subset_def /-
theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ :=
  Iff.rfl
#align list.subset_def List.subset_def
-/

#print List.subset_append_of_subset_left /-
theorem subset_append_of_subset_left (l l₁ l₂ : List α) : l ⊆ l₁ → l ⊆ l₁ ++ l₂ := fun s =>
  Subset.trans s <| subset_append_left _ _
#align list.subset_append_of_subset_left List.subset_append_of_subset_left
-/

#print List.subset_append_of_subset_right' /-
theorem subset_append_of_subset_right' (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ := fun s =>
  Subset.trans s <| subset_append_right _ _
#align list.subset_append_of_subset_right List.subset_append_of_subset_right'
-/

#print List.cons_subset /-
@[simp]
theorem cons_subset {a : α} {l m : List α} : a :: l ⊆ m ↔ a ∈ m ∧ l ⊆ m := by
  simp only [subset_def, mem_cons_iff, or_imp, forall_and, forall_eq]
#align list.cons_subset List.cons_subset
-/

#print List.cons_subset_of_subset_of_mem /-
theorem cons_subset_of_subset_of_mem {a : α} {l m : List α} (ainm : a ∈ m) (lsubm : l ⊆ m) :
    a :: l ⊆ m :=
  cons_subset.2 ⟨ainm, lsubm⟩
#align list.cons_subset_of_subset_of_mem List.cons_subset_of_subset_of_mem
-/

#print List.append_subset_of_subset_of_subset /-
theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
    l₁ ++ l₂ ⊆ l := fun a h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)
#align list.append_subset_of_subset_of_subset List.append_subset_of_subset_of_subset
-/

#print List.append_subset /-
@[simp]
theorem append_subset {l₁ l₂ l : List α} : l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l :=
  by
  constructor
  · intro h
    simp only [subset_def] at *
    constructor <;> intros <;> simp [*]
  · rintro ⟨h1, h2⟩
    apply append_subset_of_subset_of_subset h1 h2
#align list.append_subset_iff List.append_subset
-/

#print List.eq_nil_of_subset_nil /-
theorem eq_nil_of_subset_nil : ∀ {l : List α}, l ⊆ [] → l = []
  | [], s => rfl
  | a :: l, s => False.elim <| s <| mem_cons_self a l
#align list.eq_nil_of_subset_nil List.eq_nil_of_subset_nil
-/

#print List.eq_nil_iff_forall_not_mem /-
theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l :=
  show l = [] ↔ l ⊆ [] from ⟨fun e => e ▸ Subset.refl _, eq_nil_of_subset_nil⟩
#align list.eq_nil_iff_forall_not_mem List.eq_nil_iff_forall_not_mem
-/

/- warning: list.map_subset -> List.map_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l₁ : List.{u1} α} {l₂ : List.{u1} α} (f : α -> β), (HasSubset.Subset.{u1} (List.{u1} α) (List.hasSubset.{u1} α) l₁ l₂) -> (HasSubset.Subset.{u2} (List.{u2} β) (List.hasSubset.{u2} β) (List.map.{u1, u2} α β f l₁) (List.map.{u1, u2} α β f l₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l₁ : List.{u2} α} {l₂ : List.{u2} α} (f : α -> β), (HasSubset.Subset.{u2} (List.{u2} α) (List.instHasSubsetList.{u2} α) l₁ l₂) -> (HasSubset.Subset.{u1} (List.{u1} β) (List.instHasSubsetList.{u1} β) (List.map.{u2, u1} α β f l₁) (List.map.{u2, u1} α β f l₂))
Case conversion may be inaccurate. Consider using '#align list.map_subset List.map_subsetₓ'. -/
theorem map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ := fun x => by
  simp only [mem_map, not_and, exists_imp, and_imp] <;> exact fun a h e => ⟨a, H h, e⟩
#align list.map_subset List.map_subset

#print List.map_subset_iff /-
theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
  by
  refine' ⟨_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'
#align list.map_subset_iff List.map_subset_iff
-/

/-! ### append -/


#print List.append_eq_has_append /-
theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl
#align list.append_eq_has_append List.append_eq_has_append
-/

#print List.singleton_append /-
@[simp]
theorem singleton_append {x : α} {l : List α} : [x] ++ l = x :: l :=
  rfl
#align list.singleton_append List.singleton_append
-/

#print List.append_ne_nil_of_ne_nil_left /-
theorem append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] := by
  induction s <;> intros <;> contradiction
#align list.append_ne_nil_of_ne_nil_left List.append_ne_nil_of_ne_nil_left
-/

#print List.append_ne_nil_of_ne_nil_right /-
theorem append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] := by
  induction s <;> intros <;> contradiction
#align list.append_ne_nil_of_ne_nil_right List.append_ne_nil_of_ne_nil_right
-/

#print List.append_eq_nil /-
@[simp]
theorem append_eq_nil {p q : List α} : p ++ q = [] ↔ p = [] ∧ q = [] := by
  cases p <;> simp only [nil_append, cons_append, eq_self_iff_true, true_and_iff, false_and_iff]
#align list.append_eq_nil List.append_eq_nil
-/

#print List.nil_eq_append /-
@[simp]
theorem nil_eq_append {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] := by
  rw [eq_comm, append_eq_nil]
#align list.nil_eq_append_iff List.nil_eq_append
-/

#print List.append_eq_cons_iff /-
theorem append_eq_cons_iff {a b c : List α} {x : α} :
    a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  cases a <;>
    simp only [and_assoc', @eq_comm _ c, nil_append, cons_append, eq_self_iff_true, true_and_iff,
      false_and_iff, exists_false, false_or_iff, or_false_iff, exists_and_left, exists_eq_left']
#align list.append_eq_cons_iff List.append_eq_cons_iff
-/

#print List.cons_eq_append_iff /-
theorem cons_eq_append_iff {a b c : List α} {x : α} :
    (x :: c : List α) = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b := by
  rw [eq_comm, append_eq_cons_iff]
#align list.cons_eq_append_iff List.cons_eq_append_iff
-/

#print List.append_eq_append_iff /-
theorem append_eq_append_iff {a b c d : List α} :
    a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b :=
  by
  induction a generalizing c
  case nil =>
    rw [nil_append]; constructor
    · rintro rfl
      left
      exact ⟨_, rfl, rfl⟩
    · rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩)
      · rfl
      · rw [← append_assoc, ← H]
        rfl
  case cons a as ih =>
    cases c
    · simp only [cons_append, nil_append, false_and_iff, exists_false, false_or_iff,
        exists_eq_left']
      exact eq_comm
    · simp only [cons_append, @eq_comm _ a, ih, and_assoc', and_or_left, exists_and_left]
#align list.append_eq_append_iff List.append_eq_append_iff
-/

#print List.take_append_drop /-
@[simp]
theorem take_append_drop : ∀ (n : ℕ) (l : List α), take n l ++ drop n l = l
  | 0, a => rfl
  | succ n, [] => rfl
  | succ n, x :: xs => congr_arg (cons x) <| take_append_drop n xs
#align list.take_append_drop List.take_append_drop
-/

#print List.append_inj /-
-- TODO(Leo): cleanup proof after arith dec proc
theorem append_inj :
    ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
  | [], [], t₁, t₂, h, hl => ⟨rfl, h⟩
  | a :: s₁, [], t₁, t₂, h, hl => List.noConfusion <| eq_nil_of_length_eq_zero hl
  | [], b :: s₂, t₁, t₂, h, hl => List.noConfusion <| eq_nil_of_length_eq_zero hl.symm
  | a :: s₁, b :: s₂, t₁, t₂, h, hl =>
    List.noConfusion h fun ab hap =>
      by
      let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl)
      rw [ab, e1, e2] <;> exact ⟨rfl, rfl⟩
#align list.append_inj List.append_inj
-/

theorem append_inj_right {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right
#align list.append_inj_right List.append_inj_rightₓ

theorem append_inj_left {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left
#align list.append_inj_left List.append_inj_leftₓ

theorem append_inj' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
    s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h <|
    @Nat.add_right_cancel _ (length t₁) _ <|
      by
      let hap := congr_arg length h
      simp only [length_append] at hap <;> rwa [← hl] at hap
#align list.append_inj' List.append_inj'ₓ

theorem append_inj_right' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right
#align list.append_inj_right' List.append_inj_right'ₓ

theorem append_inj_left' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂)
    (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left
#align list.append_inj_left' List.append_inj_left'ₓ

#print List.append_left_cancel /-
theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  append_inj_right h rfl
#align list.append_left_cancel List.append_left_cancel
-/

#print List.append_right_cancel /-
theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  append_inj_left' h rfl
#align list.append_right_cancel List.append_right_cancel
-/

#print List.append_right_injective /-
theorem append_right_injective (s : List α) : Injective fun t => s ++ t := fun t₁ t₂ =>
  append_left_cancel
#align list.append_right_injective List.append_right_injective
-/

#print List.append_right_inj /-
theorem append_right_inj {t₁ t₂ : List α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  (append_right_injective s).eq_iff
#align list.append_right_inj List.append_right_inj
-/

#print List.append_left_injective /-
theorem append_left_injective (t : List α) : Injective fun s => s ++ t := fun s₁ s₂ =>
  append_right_cancel
#align list.append_left_injective List.append_left_injective
-/

#print List.append_left_inj /-
theorem append_left_inj {s₁ s₂ : List α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  (append_left_injective t).eq_iff
#align list.append_left_inj List.append_left_inj
-/

/- warning: list.map_eq_append_split -> List.map_eq_append_split is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {l : List.{u1} α} {s₁ : List.{u2} β} {s₂ : List.{u2} β}, (Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f l) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) s₁ s₂)) -> (Exists.{succ u1} (List.{u1} α) (fun (l₁ : List.{u1} α) => Exists.{succ u1} (List.{u1} α) (fun (l₂ : List.{u1} α) => And (Eq.{succ u1} (List.{u1} α) l (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (And (Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f l₁) s₁) (Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f l₂) s₂)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {l : List.{u2} α} {s₁ : List.{u1} β} {s₂ : List.{u1} β}, (Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f l) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) s₁ s₂)) -> (Exists.{succ u2} (List.{u2} α) (fun (l₁ : List.{u2} α) => Exists.{succ u2} (List.{u2} α) (fun (l₂ : List.{u2} α) => And (Eq.{succ u2} (List.{u2} α) l (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) (And (Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f l₁) s₁) (Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f l₂) s₂)))))
Case conversion may be inaccurate. Consider using '#align list.map_eq_append_split List.map_eq_append_splitₓ'. -/
theorem map_eq_append_split {f : α → β} {l : List α} {s₁ s₂ : List β} (h : map f l = s₁ ++ s₂) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
  by
  have := h; rw [← take_append_drop (length s₁) l] at this⊢
  rw [map_append] at this
  refine' ⟨_, _, rfl, append_inj this _⟩
  rw [length_map, length_take, min_eq_left]
  rw [← length_map f l, h, length_append]
  apply Nat.le_add_right
#align list.map_eq_append_split List.map_eq_append_split

/-! ### replicate -/


#print List.replicate_zero /-
@[simp]
theorem replicate_zero (a : α) : replicate 0 a = [] :=
  rfl
#align list.replicate_zero List.replicate_zero
-/

#print List.replicate_succ /-
@[simp]
theorem replicate_succ (a : α) (n) : replicate (n + 1) a = a :: replicate n a :=
  rfl
#align list.replicate_succ List.replicate_succ
-/

#print List.replicate_one /-
theorem replicate_one (a : α) : replicate 1 a = [a] :=
  rfl
#align list.replicate_one List.replicate_one
-/

#print List.length_replicate /-
@[simp]
theorem length_replicate : ∀ (n) (a : α), length (replicate n a) = n
  | 0, a => rfl
  | n + 1, a => congr_arg Nat.succ (length_replicate n a)
#align list.length_replicate List.length_replicate
-/

#print List.mem_replicate /-
theorem mem_replicate {a b : α} : ∀ {n}, b ∈ replicate n a ↔ n ≠ 0 ∧ b = a
  | 0 => by simp
  | n + 1 => by simp [mem_replicate]
#align list.mem_replicate List.mem_replicate
-/

#print List.eq_of_mem_replicate /-
theorem eq_of_mem_replicate {a b : α} {n} (h : b ∈ replicate n a) : b = a :=
  (mem_replicate.1 h).2
#align list.eq_of_mem_replicate List.eq_of_mem_replicate
-/

#print List.eq_replicate_length /-
theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
  | b :: l => by simp [eq_replicate_length]
#align list.eq_replicate_length List.eq_replicate_length
-/

alias eq_replicate_length ↔ _ eq_replicate_of_mem
#align list.eq_replicate_of_mem List.eq_replicate_of_mem

#print List.eq_replicate /-
theorem eq_replicate {a : α} {n} {l : List α} : l = replicate n a ↔ length l = n ∧ ∀ b ∈ l, b = a :=
  ⟨fun h => h.symm ▸ ⟨length_replicate _ _, fun b => eq_of_mem_replicate⟩, fun ⟨e, al⟩ =>
    e ▸ eq_replicate_of_mem al⟩
#align list.eq_replicate List.eq_replicate
-/

#print List.replicate_add /-
theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  induction m <;> simp only [*, zero_add, succ_add, replicate] <;> rfl
#align list.replicate_add List.replicate_add
-/

#print List.replicate_succ' /-
theorem replicate_succ' (n) (a : α) : replicate (n + 1) a = replicate n a ++ [a] :=
  replicate_add n 1 a
#align list.replicate_succ' List.replicate_succ'
-/

#print List.replicate_subset_singleton /-
theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun b h =>
  mem_singleton.2 (eq_of_mem_replicate h)
#align list.replicate_subset_singleton List.replicate_subset_singleton
-/

#print List.subset_singleton_iff /-
theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate, subset_def, mem_singleton, exists_eq_left']
#align list.subset_singleton_iff List.subset_singleton_iff
-/

#print List.map_replicate /-
@[simp]
theorem map_replicate (f : α → β) (n a) : map f (replicate n a) = replicate n (f a) := by
  induction n <;> [rfl, simp only [*, replicate, map]] <;> constructor <;> rfl
#align list.map_replicate List.map_replicate
-/

/- warning: list.tail_replicate -> List.tail_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : Nat) (a : α), Eq.{succ u1} (List.{u1} α) (List.tail.{u1} α (List.replicate.{u1} α n a)) (List.replicate.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a)
but is expected to have type
  forall {α : Type.{u1}} (n : α) (a : Nat), Eq.{succ u1} (List.{u1} α) (List.tail.{u1} α (List.replicate.{u1} α a n)) (List.replicate.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) a (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n)
Case conversion may be inaccurate. Consider using '#align list.tail_replicate List.tail_replicateₓ'. -/
@[simp]
theorem tail_replicate (n) (a : α) : tail (replicate n a) = replicate (n - 1) a := by
  cases n <;> rfl
#align list.tail_replicate List.tail_replicate

#print List.join_replicate_nil /-
@[simp]
theorem join_replicate_nil (n : ℕ) : join (replicate n []) = @nil α := by
  induction n <;> [rfl, simp only [*, replicate, join, append_nil]]
#align list.join_replicate_nil List.join_replicate_nil
-/

#print List.replicate_right_injective /-
theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (replicate n : α → List α) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩
#align list.replicate_right_injective List.replicate_right_injective
-/

#print List.replicate_right_inj /-
theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff
#align list.replicate_right_inj List.replicate_right_inj
-/

#print List.replicate_right_inj' /-
@[simp]
theorem replicate_right_inj' {a b : α} : ∀ {n}, replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 =>
    (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or_iff]
#align list.replicate_right_inj' List.replicate_right_inj'
-/

#print List.replicate_left_injective /-
theorem replicate_left_injective (a : α) : Injective fun n => replicate n a :=
  LeftInverse.injective fun n => length_replicate n a
#align list.replicate_left_injective List.replicate_left_injective
-/

#print List.replicate_left_inj /-
@[simp]
theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff
#align list.replicate_left_inj List.replicate_left_inj
-/

/-! ### pure -/


/- warning: list.mem_pure -> List.mem_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (y : α), Iff (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x (Pure.pure.{u1, u1} List.{u1} (Applicative.toHasPure.{u1, u1} List.{u1} (Monad.toApplicative.{u1, u1} List.{u1} List.monad.{u1})) α y)) (Eq.{succ u1} α x y)
but is expected to have type
  forall {α : Type.{u1}} (x : α) (y : α), Iff (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x (Pure.pure.{u1, u1} List.{u1} (Applicative.toPure.{u1, u1} List.{u1} (Monad.toApplicative.{u1, u1} List.{u1} List.instMonadList.{u1})) α y)) (Eq.{succ u1} α x y)
Case conversion may be inaccurate. Consider using '#align list.mem_pure List.mem_pureₓ'. -/
@[simp]
theorem mem_pure {α} (x y : α) : x ∈ (pure y : List α) ↔ x = y := by simp! [pure, List.ret]
#align list.mem_pure List.mem_pure

/-! ### bind -/


/- warning: list.bind_eq_bind -> List.bind_eq_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (List.{u1} β)) (l : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Bind.bind.{u1, u1} List.{u1} (Monad.toHasBind.{u1, u1} List.{u1} List.monad.{u1}) α β l f) (List.bind.{u1, u1} α β l f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> (List.{u1} β)) (l : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Bind.bind.{u1, u1} List.{u1} (Monad.toBind.{u1, u1} List.{u1} List.instMonadList.{u1}) α β l f) (List.bind.{u1, u1} α β l f)
Case conversion may be inaccurate. Consider using '#align list.bind_eq_bind List.bind_eq_bindₓ'. -/
@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl
#align list.bind_eq_bind List.bind_eq_bind

#print List.bind_append /-
-- TODO: duplicate of a lemma in core
theorem bind_append (f : α → List β) (l₁ l₂ : List α) :
    (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
  append_bind _ _ _
#align list.bind_append List.bind_append
-/

#print List.bind_singleton /-
@[simp]
theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)
#align list.bind_singleton List.bind_singleton
-/

#print List.bind_singleton' /-
@[simp]
theorem bind_singleton' (l : List α) : (l.bind fun x => [x]) = l :=
  bind_pure l
#align list.bind_singleton' List.bind_singleton'
-/

/- warning: list.map_eq_bind -> List.map_eq_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f l) (List.bind.{u1, u2} α β l (fun (x : α) => List.cons.{u2} β (f x) (List.nil.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (l : List.{u2} α), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f l) (List.bind.{u2, u1} α β l (fun (x : α) => List.cons.{u1} β (f x) (List.nil.{u1} β)))
Case conversion may be inaccurate. Consider using '#align list.map_eq_bind List.map_eq_bindₓ'. -/
theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind fun x => [f x] :=
  by
  trans
  rw [← bind_singleton' l, bind_map]
  rfl
#align list.map_eq_bind List.map_eq_bind

/- warning: list.bind_assoc -> List.bind_assoc is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} (l : List.{u2} α) (f : α -> (List.{u3} β)) (g : β -> (List.{u1} γ)), Eq.{succ u1} (List.{u1} γ) (List.bind.{u3, u1} β γ (List.bind.{u2, u3} α β l f) g) (List.bind.{u2, u1} α γ l (fun (x : α) => List.bind.{u3, u1} β γ (f x) g))
but is expected to have type
  forall {γ : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : α -> (List.{u1} β)) (g : β -> (List.{u3} γ)), Eq.{succ u3} (List.{u3} γ) (List.bind.{u1, u3} β γ (List.bind.{u2, u1} α β l f) g) (List.bind.{u2, u3} α γ l (fun (x : α) => List.bind.{u1, u3} β γ (f x) g))
Case conversion may be inaccurate. Consider using '#align list.bind_assoc List.bind_assocₓ'. -/
theorem bind_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.bind f).bind g = l.bind fun x => (f x).bind g := by induction l <;> simp [*]
#align list.bind_assoc List.bind_assoc

/-! ### concat -/


#print List.concat_nil /-
theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl
#align list.concat_nil List.concat_nil
-/

#print List.concat_cons /-
theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl
#align list.concat_cons List.concat_cons
-/

#print List.concat_eq_append' /-
@[simp]
theorem concat_eq_append' (a : α) (l : List α) : concat l a = l ++ [a] := by
  induction l <;> simp only [*, concat] <;> constructor <;> rfl
#align list.concat_eq_append List.concat_eq_append'
-/

#print List.init_eq_of_concat_eq /-
theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ :=
  by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact append_right_cancel h
#align list.init_eq_of_concat_eq List.init_eq_of_concat_eq
-/

#print List.last_eq_of_concat_eq /-
theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b :=
  by
  intro h
  rw [concat_eq_append, concat_eq_append] at h
  exact head_eq_of_cons_eq (append_left_cancel h)
#align list.last_eq_of_concat_eq List.last_eq_of_concat_eq
-/

#print List.concat_ne_nil /-
theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] := by simp
#align list.concat_ne_nil List.concat_ne_nil
-/

#print List.concat_append /-
theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := by simp
#align list.concat_append List.concat_append
-/

#print List.length_concat' /-
theorem length_concat' (a : α) (l : List α) : length (concat l a) = succ (length l) := by
  simp only [concat_eq_append, length_append, length]
#align list.length_concat List.length_concat'
-/

#print List.append_concat /-
theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := by simp
#align list.append_concat List.append_concat
-/

/-! ### reverse -/


#print List.reverse_nil /-
@[simp]
theorem reverse_nil : reverse (@nil α) = [] :=
  rfl
#align list.reverse_nil List.reverse_nil
-/

attribute [local simp] reverse_core

#print List.reverse_cons /-
@[simp]
theorem reverse_cons (a : α) (l : List α) : reverse (a :: l) = reverse l ++ [a] :=
  have aux : ∀ l₁ l₂, reverseAux l₁ l₂ ++ [a] = reverseAux l₁ (l₂ ++ [a]) := by
    intro l₁ <;> induction l₁ <;> intros <;> [rfl, simp only [*, reverse_core, cons_append]]
  (aux l nil).symm
#align list.reverse_cons List.reverse_cons
-/

#print List.reverseAux_eq /-
theorem reverseAux_eq (l₁ l₂ : List α) : reverseAux l₁ l₂ = reverse l₁ ++ l₂ := by
  induction l₁ generalizing l₂ <;> [rfl,
      simp only [*, reverse_core, reverse_cons, append_assoc]] <;>
    rfl
#align list.reverse_core_eq List.reverseAux_eq
-/

#print List.reverse_cons' /-
theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]
#align list.reverse_cons' List.reverse_cons'
-/

#print List.reverse_singleton /-
@[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl
#align list.reverse_singleton List.reverse_singleton
-/

#print List.reverse_append /-
@[simp]
theorem reverse_append (s t : List α) : reverse (s ++ t) = reverse t ++ reverse s := by
  induction s <;> [rw [nil_append, reverse_nil, append_nil],
    simp only [*, cons_append, reverse_cons, append_assoc]]
#align list.reverse_append List.reverse_append
-/

#print List.reverse_concat /-
theorem reverse_concat (l : List α) (a : α) : reverse (concat l a) = a :: reverse l := by
  rw [concat_eq_append, reverse_append, reverse_singleton, singleton_append]
#align list.reverse_concat List.reverse_concat
-/

#print List.reverse_reverse /-
@[simp]
theorem reverse_reverse (l : List α) : reverse (reverse l) = l := by
  induction l <;> [rfl, simp only [*, reverse_cons, reverse_append]] <;> rfl
#align list.reverse_reverse List.reverse_reverse
-/

#print List.reverse_involutive /-
@[simp]
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse
#align list.reverse_involutive List.reverse_involutive
-/

#print List.reverse_injective /-
@[simp]
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.Injective
#align list.reverse_injective List.reverse_injective
-/

#print List.reverse_surjective /-
theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.Surjective
#align list.reverse_surjective List.reverse_surjective
-/

#print List.reverse_bijective /-
theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.Bijective
#align list.reverse_bijective List.reverse_bijective
-/

#print List.reverse_inj /-
@[simp]
theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  reverse_injective.eq_iff
#align list.reverse_inj List.reverse_inj
-/

#print List.reverse_eq_iff /-
theorem reverse_eq_iff {l l' : List α} : l.reverse = l' ↔ l = l'.reverse :=
  reverse_involutive.eq_iff
#align list.reverse_eq_iff List.reverse_eq_iff
-/

#print List.reverse_eq_nil /-
@[simp]
theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] :=
  @reverse_inj _ l []
#align list.reverse_eq_nil List.reverse_eq_nil
-/

#print List.concat_eq_reverse_cons /-
theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  simp only [concat_eq_append, reverse_cons, reverse_reverse]
#align list.concat_eq_reverse_cons List.concat_eq_reverse_cons
-/

#print List.length_reverse /-
@[simp]
theorem length_reverse (l : List α) : length (reverse l) = length l := by
  induction l <;> [rfl, simp only [*, reverse_cons, length_append, length]]
#align list.length_reverse List.length_reverse
-/

#print List.map_reverse /-
@[simp]
theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) := by
  induction l <;> [rfl, simp only [*, map, reverse_cons, map_append]]
#align list.map_reverse List.map_reverse
-/

#print List.map_reverseAux /-
theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverse_core_eq, map_append, map_reverse]
#align list.map_reverse_core List.map_reverseAux
-/

#print List.mem_reverse' /-
@[simp]
theorem mem_reverse' {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l := by
  induction l <;> [rfl,
    simp only [*, reverse_cons, mem_append, mem_singleton, mem_cons_iff, not_mem_nil, false_or_iff,
      or_false_iff, or_comm']]
#align list.mem_reverse List.mem_reverse'
-/

#print List.reverse_replicate /-
@[simp]
theorem reverse_replicate (n) (a : α) : reverse (replicate n a) = replicate n a :=
  eq_replicate.2
    ⟨by rw [length_reverse, length_replicate], fun b h => eq_of_mem_replicate (mem_reverse'.1 h)⟩
#align list.reverse_replicate List.reverse_replicate
-/

/-! ### empty -/


attribute [simp] List.isEmpty

#print List.isEmpty_iff_eq_nil /-
theorem isEmpty_iff_eq_nil {l : List α} : l.Empty ↔ l = [] :=
  List.casesOn l (by simp) (by simp)
#align list.empty_iff_eq_nil List.isEmpty_iff_eq_nil
-/

/-! ### init -/


#print List.length_dropLast /-
@[simp]
theorem length_dropLast : ∀ l : List α, length (dropLast l) = length l - 1
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    rw [init]
    simp only [add_left_inj, length, succ_add_sub_one]
    exact length_init (b :: l)
#align list.length_init List.length_dropLast
-/

/-! ### last -/


#print List.getLast_cons /-
@[simp]
theorem getLast_cons {a : α} {l : List α} :
    ∀ h : l ≠ nil, getLast (a :: l) (cons_ne_nil a l) = getLast l h :=
  by
  induction l <;> intros
  contradiction
  rfl
#align list.last_cons List.getLast_cons
-/

#print List.getLast_append_singleton /-
@[simp]
theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_ne_nil_right l _ (cons_ne_nil a _)) = a := by
  induction l <;> [rfl,
    simp only [cons_append, last_cons fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2, *]]
#align list.last_append_singleton List.getLast_append_singleton
-/

#print List.getLast_append' /-
theorem getLast_append' (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_ne_nil_right l₁ l₂ h) = getLast l₂ h :=
  by
  induction' l₁ with _ _ ih
  · simp
  · simp only [cons_append]
    rw [List.getLast_cons]
    exact ih
#align list.last_append List.getLast_append'
-/

#print List.getLast_concat' /-
theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (concat_ne_nil a l) = a := by
  simp only [concat_eq_append, last_append_singleton]
#align list.last_concat List.getLast_concat'
-/

#print List.getLast_singleton' /-
@[simp]
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a :=
  rfl
#align list.last_singleton List.getLast_singleton'
-/

#print List.getLast_cons_cons /-
@[simp]
theorem getLast_cons_cons (a₁ a₂ : α) (l : List α) :
    getLast (a₁ :: a₂ :: l) (cons_ne_nil _ _) = getLast (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl
#align list.last_cons_cons List.getLast_cons_cons
-/

#print List.dropLast_append_getLast /-
theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [a], h => rfl
  | a :: b :: l, h => by
    rw [init, cons_append, last_cons (cons_ne_nil _ _)]
    congr
    exact init_append_last (cons_ne_nil b l)
#align list.init_append_last List.dropLast_append_getLast
-/

#print List.getLast_congr /-
theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁
#align list.last_congr List.getLast_congr
-/

#print List.getLast_mem /-
theorem getLast_mem : ∀ {l : List α} (h : l ≠ []), getLast l h ∈ l
  | [], h => absurd rfl h
  | [a], h => Or.inl rfl
  | a :: b :: l, h =>
    Or.inr <| by
      rw [last_cons_cons]
      exact last_mem (cons_ne_nil b l)
#align list.last_mem List.getLast_mem
-/

#print List.getLast_replicate_succ /-
theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).last (ne_nil_of_length_eq_succ (length_replicate (m + 1) a)) = a :=
  by
  simp only [replicate_succ']
  exact last_append_singleton _
#align list.last_replicate_succ List.getLast_replicate_succ
-/

/-! ### last' -/


#print List.getLast?_isNone /-
@[simp]
theorem getLast?_isNone : ∀ {l : List α}, (getLast? l).isNone ↔ l = []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@last'_is_none (b :: l)]
#align list.last'_is_none List.getLast?_isNone
-/

#print List.getLast?_isSome /-
@[simp]
theorem getLast?_isSome : ∀ {l : List α}, l.last'.isSome ↔ l ≠ []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@last'_is_some (b :: l)]
#align list.last'_is_some List.getLast?_isSome
-/

#print List.mem_getLast?_eq_getLast /-
theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.last' → ∃ h, x = getLast l h
  | [], x, hx => False.elim <| by simpa using hx
  | [a], x, hx =>
    have : a = x := by simpa using hx
    this ▸ ⟨cons_ne_nil a [], rfl⟩
  | a :: b :: l, x, hx => by
    rw [last'] at hx
    rcases mem_last'_eq_last hx with ⟨h₁, h₂⟩
    use cons_ne_nil _ _
    rwa [last_cons]
#align list.mem_last'_eq_last List.mem_getLast?_eq_getLast
-/

#print List.getLast?_eq_getLast_of_ne_nil /-
theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.last' = some (l.last h)
  | [], h => (h rfl).elim
  | [a], _ => by
    unfold last
    unfold last'
  | a :: b :: l, _ => @last'_eq_last_of_ne_nil (b :: l) (cons_ne_nil _ _)
#align list.last'_eq_last_of_ne_nil List.getLast?_eq_getLast_of_ne_nil
-/

#print List.mem_getLast?_cons /-
theorem mem_getLast?_cons {x y : α} : ∀ {l : List α} (h : x ∈ l.last'), x ∈ (y :: l).last'
  | [], _ => by contradiction
  | a :: l, h => h
#align list.mem_last'_cons List.mem_getLast?_cons
-/

#print List.mem_of_mem_getLast? /-
theorem mem_of_mem_getLast? {l : List α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
  let ⟨h₁, h₂⟩ := mem_getLast?_eq_getLast ha
  h₂.symm ▸ getLast_mem _
#align list.mem_of_mem_last' List.mem_of_mem_getLast?
-/

#print List.dropLast_append_getLast? /-
theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.last', dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [last'] at hc
    rw [init, cons_append, init_append_last' _ hc]
#align list.init_append_last' List.dropLast_append_getLast?
-/

#print List.getLastI_eq_getLast? /-
theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.ilast = l.last'.iget
  | [] => by simp [ilast, Inhabited.default]
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | a :: b :: c :: l => by simp [ilast, ilast_eq_last' (c :: l)]
#align list.ilast_eq_last' List.getLastI_eq_getLast?
-/

#print List.getLast?_append_cons /-
@[simp]
theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, last', ← cons_append, last'_append_cons]
#align list.last'_append_cons List.getLast?_append_cons
-/

#print List.getLast?_cons_cons /-
@[simp]
theorem getLast?_cons_cons (x y : α) (l : List α) : getLast? (x :: y :: l) = getLast? (y :: l) :=
  rfl
#align list.last'_cons_cons List.getLast?_cons_cons
-/

#print List.getLast?_append_of_ne_nil /-
theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (hl₂ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂
#align list.last'_append_of_ne_nil List.getLast?_append_of_ne_nil
-/

#print List.getLast?_append /-
theorem getLast?_append {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.last') : x ∈ (l₁ ++ l₂).last' :=
  by
  cases l₂
  · contradiction
  · rw [List.getLast?_append_cons]
    exact h
#align list.last'_append List.getLast?_append
-/

/-! ### head(') and tail -/


#print List.head!_eq_head? /-
theorem head!_eq_head? [Inhabited α] (l : List α) : headI l = (head? l).iget := by cases l <;> rfl
#align list.head_eq_head' List.head!_eq_head?
-/

#print List.surjective_head /-
theorem surjective_head [Inhabited α] : Surjective (@headI α _) := fun x => ⟨[x], rfl⟩
#align list.surjective_head List.surjective_head
-/

#print List.surjective_head' /-
theorem surjective_head' : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩
#align list.surjective_head' List.surjective_head'
-/

#print List.surjective_tail /-
theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩
#align list.surjective_tail List.surjective_tail
-/

#print List.eq_cons_of_mem_head? /-
theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head' → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head', Option.mem_def] at h
    exact h ▸ rfl
#align list.eq_cons_of_mem_head' List.eq_cons_of_mem_head?
-/

#print List.mem_of_mem_head? /-
theorem mem_of_mem_head? {x : α} {l : List α} (h : x ∈ l.head') : x ∈ l :=
  (eq_cons_of_mem_head? h).symm ▸ mem_cons_self _ _
#align list.mem_of_mem_head' List.mem_of_mem_head?
-/

#print List.head!_cons /-
@[simp]
theorem head!_cons [Inhabited α] (a : α) (l : List α) : headI (a :: l) = a :=
  rfl
#align list.head_cons List.head!_cons
-/

#print List.tail_nil /-
@[simp]
theorem tail_nil : tail (@nil α) = [] :=
  rfl
#align list.tail_nil List.tail_nil
-/

#print List.tail_cons /-
@[simp]
theorem tail_cons (a : α) (l : List α) : tail (a :: l) = l :=
  rfl
#align list.tail_cons List.tail_cons
-/

#print List.head!_append /-
@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    headI (s ++ t) = headI s := by
  induction s
  contradiction
  rfl
#align list.head_append List.head!_append
-/

#print List.head?_append /-
theorem head?_append {s t : List α} {x : α} (h : x ∈ s.head') : x ∈ (s ++ t).head' :=
  by
  cases s
  contradiction
  exact h
#align list.head'_append List.head?_append
-/

#print List.head?_append_of_ne_nil /-
theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (hl₁ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | [], _, hl₁ => by contradiction
  | x :: l₁, _, _ => rfl
#align list.head'_append_of_ne_nil List.head?_append_of_ne_nil
-/

#print List.tail_append_singleton_of_ne_nil /-
theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by
  induction l
  contradiction
  rw [tail, cons_append, tail]
#align list.tail_append_singleton_of_ne_nil List.tail_append_singleton_of_ne_nil
-/

#print List.cons_head?_tail /-
theorem cons_head?_tail : ∀ {l : List α} {a : α} (h : a ∈ head? l), a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    simp at h
    simp [h]
#align list.cons_head'_tail List.cons_head?_tail
-/

#print List.head!_mem_head? /-
theorem head!_mem_head? [Inhabited α] : ∀ {l : List α} (h : l ≠ []), headI l ∈ head? l
  | [], h => by contradiction
  | a :: l, h => rfl
#align list.head_mem_head' List.head!_mem_head?
-/

#print List.cons_head!_tail /-
theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : headI l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)
#align list.cons_head_tail List.cons_head!_tail
-/

#print List.head!_mem_self /-
theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head ∈ l :=
  by
  have h' := mem_cons_self l.head l.tail
  rwa [cons_head_tail h] at h'
#align list.head_mem_self List.head!_mem_self
-/

#print List.head?_map /-
@[simp]
theorem head?_map (f : α → β) (l) : head? (map f l) = (head? l).map f := by cases l <;> rfl
#align list.head'_map List.head?_map
-/

#print List.tail_append_of_ne_nil /-
theorem tail_append_of_ne_nil (l l' : List α) (h : l ≠ []) : (l ++ l').tail = l.tail ++ l' :=
  by
  cases l
  · contradiction
  · simp
#align list.tail_append_of_ne_nil List.tail_append_of_ne_nil
-/

#print List.nthLe_tail /-
@[simp]
theorem nthLe_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simpa [← lt_tsub_iff_right] using h)) :
    l.tail.nthLe i h = l.nthLe (i + 1) h' := by
  cases l
  · cases h
  · simpa
#align list.nth_le_tail List.nthLe_tail
-/

#print List.nthLe_cons_aux /-
theorem nthLe_cons_aux {l : List α} {a : α} {n} (hn : n ≠ 0) (h : n < (a :: l).length) :
    n - 1 < l.length := by
  contrapose! h
  rw [length_cons]
  convert succ_le_succ h
  exact (Nat.succ_pred_eq_of_pos hn.bot_lt).symm
#align list.nth_le_cons_aux List.nthLe_cons_aux
-/

/- warning: list.nth_le_cons -> List.nthLe_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {n : Nat} (hl : LT.lt.{0} Nat Nat.hasLt n (List.length.{u1} α (List.cons.{u1} α a l))), Eq.{succ u1} α (List.nthLe.{u1} α (List.cons.{u1} α a l) n hl) (dite.{succ u1} α (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Nat.decidableEq n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (hn : Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => a) (fun (hn : Not (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) => List.nthLe.{u1} α l (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (List.nthLe_cons_aux.{u1} α l a n hn hl)))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {n : Nat} (hl : LT.lt.{0} Nat instLTNat n (List.length.{u1} α (List.cons.{u1} α a l))), Eq.{succ u1} α (List.nthLe.{u1} α (List.cons.{u1} α a l) n hl) (dite.{succ u1} α (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (instDecidableEqNat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (hn : Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => a) (fun (hn : Not (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) => List.nthLe.{u1} α l (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.nthLe_cons_aux.{u1} α l a n hn hl)))
Case conversion may be inaccurate. Consider using '#align list.nth_le_cons List.nthLe_consₓ'. -/
theorem nthLe_cons {l : List α} {a : α} {n} (hl) :
    (a :: l).nthLe n hl = if hn : n = 0 then a else l.nthLe (n - 1) (nthLe_cons_aux hn hl) :=
  by
  split_ifs
  · simp [nth_le, h]
  cases l
  · rw [length_singleton, lt_succ_iff, nonpos_iff_eq_zero] at hl
    contradiction
  cases n
  · contradiction
  rfl
#align list.nth_le_cons List.nthLe_cons

#print List.modifyHead_modifyHead /-
@[simp]
theorem modifyHead_modifyHead (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp
#align list.modify_head_modify_head List.modifyHead_modifyHead
-/

/-! ### Induction from the right -/


#print List.reverseRecOn /-
/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {C : List α → Sort _} (l : List α) (H0 : C [])
    (H1 : ∀ (l : List α) (a : α), C l → C (l ++ [a])) : C l :=
  by
  rw [← reverse_reverse l]
  induction reverse l
  · exact H0
  · rw [reverse_cons]
    exact H1 _ _ ih
#align list.reverse_rec_on List.reverseRecOn
-/

/- warning: list.bidirectional_rec -> List.bidirectionalRecₓ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (List.{u1} α) -> Sort.{u2}}, (C (List.nil.{u1} α)) -> (forall (a : α), C (List.cons.{u1} α a (List.nil.{u1} α))) -> (forall (a : α) (l : List.{u1} α) (b : α), (C l) -> (C (List.cons.{u1} α a (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l (List.cons.{u1} α b (List.nil.{u1} α)))))) -> (forall (l : List.{u1} α), C l)
but is expected to have type
  forall {α : Type.{u2}} {C : (List.{u2} α) -> Sort.{u1}}, (C (List.nil.{u2} α)) -> (forall (a : α), C (List.cons.{u2} α a (List.nil.{u2} α))) -> (forall (a : α) (l : List.{u2} α) (b : α), (C l) -> (C (List.cons.{u2} α a (Append.append.{u2} (List.{u2} α) (List.hasAppend.{u2} α) l (List.cons.{u2} α b (List.nil.{u2} α)))))) -> (forall (l : List.{u2} α), C l)
Case conversion may be inaccurate. Consider using '#align list.bidirectional_rec List.bidirectionalRecₓₓ'. -/
/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectionalRec {C : List α → Sort _} (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
  | [] => H0
  | [a] => H1 a
  | a :: b :: l => by
    let l' := dropLast (b :: l)
    let b' := getLast (b :: l) (cons_ne_nil _ _)
    have : length l' < length (a :: b :: l) :=
      by
      change _ < length l + 2
      simp
    rw [← init_append_last (cons_ne_nil b l)]
    have : C l' := bidirectional_rec l'
    exact Hn a l' b' ‹C l'›termination_by' ⟨_, measure_wf List.length⟩
#align list.bidirectional_rec List.bidirectionalRecₓ

#print List.bidirectionalRecOn /-
/-- Like `bidirectional_rec`, but with the list parameter placed first. -/
@[elab_as_elim]
def bidirectionalRecOn {C : List α → Sort _} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l
#align list.bidirectional_rec_on List.bidirectionalRecOn
-/

/-! ### sublists -/


#print List.nil_sublist /-
@[simp]
theorem nil_sublist : ∀ l : List α, [] <+ l
  | [] => Sublist.slnil
  | a :: l => Sublist.cons _ _ a (nil_sublist l)
#align list.nil_sublist List.nil_sublist
-/

#print List.Sublist.refl /-
@[refl, simp]
theorem Sublist.refl : ∀ l : List α, l <+ l
  | [] => Sublist.slnil
  | a :: l => Sublist.cons₂ _ _ a (sublist.refl l)
#align list.sublist.refl List.Sublist.refl
-/

#print List.Sublist.trans /-
@[trans]
theorem Sublist.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
  Sublist.rec_on h₂ (fun _ s => s) (fun l₂ l₃ a h₂ IH l₁ h₁ => Sublist.cons _ _ _ (IH l₁ h₁))
    (fun l₂ l₃ a h₂ IH l₁ h₁ =>
      @Sublist.cases_on _ (fun l₁ l₂' => l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
        (fun _ => nil_sublist _)
        (fun l₁ l₂' a' h₁' e =>
          match a', l₂', e, h₁' with
          | _, _, rfl, h₁ => Sublist.cons _ _ _ (IH _ h₁))
        (fun l₁ l₂' a' h₁' e =>
          match a', l₂', e, h₁' with
          | _, _, rfl, h₁ => Sublist.cons₂ _ _ _ (IH _ h₁))
        rfl)
    l₁ h₁
#align list.sublist.trans List.Sublist.trans
-/

#print List.sublist_cons /-
@[simp]
theorem sublist_cons (a : α) (l : List α) : l <+ a :: l :=
  Sublist.cons _ _ _ (Sublist.refl l)
#align list.sublist_cons List.sublist_cons
-/

#print List.sublist_of_cons_sublist /-
theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : List α} : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  Sublist.trans (sublist_cons a l₁)
#align list.sublist_of_cons_sublist List.sublist_of_cons_sublist
-/

#print List.Sublist.cons_cons /-
theorem Sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  Sublist.cons₂ _ _ _ s
#align list.sublist.cons_cons List.Sublist.cons_cons
-/

#print List.sublist_append_left /-
@[simp]
theorem sublist_append_left : ∀ l₁ l₂ : List α, l₁ <+ l₁ ++ l₂
  | [], l₂ => nil_sublist _
  | a :: l₁, l₂ => (sublist_append_left l₁ l₂).cons_cons _
#align list.sublist_append_left List.sublist_append_left
-/

#print List.sublist_append_right /-
@[simp]
theorem sublist_append_right : ∀ l₁ l₂ : List α, l₂ <+ l₁ ++ l₂
  | [], l₂ => Sublist.refl _
  | a :: l₁, l₂ => Sublist.cons _ _ _ (sublist_append_right l₁ l₂)
#align list.sublist_append_right List.sublist_append_right
-/

#print List.sublist_cons_of_sublist /-
theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+ a :: l₂ :=
  Sublist.cons _ _ _
#align list.sublist_cons_of_sublist List.sublist_cons_of_sublist
-/

#print List.sublist_append_of_sublist_left /-
theorem sublist_append_of_sublist_left {l l₁ l₂ : List α} (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_left _ _
#align list.sublist_append_of_sublist_left List.sublist_append_of_sublist_left
-/

/- warning: list.sublist_append_of_sublist_right -> List.sublist_append_of_sublist_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l l₂) -> (List.Sublist.{u1} α l (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l l₁) -> (List.Sublist.{u1} α l (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₂ l₁))
Case conversion may be inaccurate. Consider using '#align list.sublist_append_of_sublist_right List.sublist_append_of_sublist_rightₓ'. -/
theorem sublist_append_of_sublist_right {l l₁ l₂ : List α} (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  s.trans <| sublist_append_right _ _
#align list.sublist_append_of_sublist_right List.sublist_append_of_sublist_right

#print List.sublist_of_cons_sublist_cons /-
theorem sublist_of_cons_sublist_cons {l₁ l₂ : List α} : ∀ {a : α}, a :: l₁ <+ a :: l₂ → l₁ <+ l₂
  | _, sublist.cons _ _ a s => sublist_of_cons_sublist s
  | _, sublist.cons2 _ _ a s => s
#align list.sublist_of_cons_sublist_cons List.sublist_of_cons_sublist_cons
-/

#print List.cons_sublist_cons_iff /-
theorem cons_sublist_cons_iff {l₁ l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨sublist_of_cons_sublist_cons, Sublist.cons_cons _⟩
#align list.cons_sublist_cons_iff List.cons_sublist_cons_iff
-/

#print List.append_sublist_append_left /-
@[simp]
theorem append_sublist_append_left {l₁ l₂ : List α} : ∀ l, l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂
  | [] => Iff.rfl
  | a :: l => cons_sublist_cons_iff.trans (append_sublist_append_left l)
#align list.append_sublist_append_left List.append_sublist_append_left
-/

#print List.Sublist.append_right /-
theorem Sublist.append_right {l₁ l₂ : List α} (h : l₁ <+ l₂) (l) : l₁ ++ l <+ l₂ ++ l :=
  by
  induction' h with _ _ a _ ih _ _ a _ ih
  · rfl
  · apply sublist_cons_of_sublist a ih
  · apply ih.cons_cons a
#align list.sublist.append_right List.Sublist.append_right
-/

/- warning: list.sublist_or_mem_of_sublist -> List.sublist_or_mem_of_sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {l₁ : List.{u1} α} {l₂ : List.{u1} α} {a : α}, (List.Sublist.{u1} α l (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ (List.cons.{u1} α a l₂))) -> (Or (List.Sublist.{u1} α l (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {l₁ : List.{u1} α} {l₂ : α} {a : List.{u1} α}, (List.Sublist.{u1} α l (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₁ (List.cons.{u1} α l₂ a))) -> (Or (List.Sublist.{u1} α l (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₁ a)) (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l₂ l))
Case conversion may be inaccurate. Consider using '#align list.sublist_or_mem_of_sublist List.sublist_or_mem_of_sublistₓ'. -/
theorem sublist_or_mem_of_sublist {l l₁ l₂ : List α} {a : α} (h : l <+ l₁ ++ a :: l₂) :
    l <+ l₁ ++ l₂ ∨ a ∈ l := by
  induction' l₁ with b l₁ IH generalizing l
  · cases h
    · left
      exact ‹l <+ l₂›
    · right
      apply mem_cons_self
  · cases' h with _ _ _ h _ _ _ h
    · exact Or.imp_left (sublist_cons_of_sublist _) (IH h)
    · exact (IH h).imp (sublist.cons_cons _) (mem_cons_of_mem _)
#align list.sublist_or_mem_of_sublist List.sublist_or_mem_of_sublist

#print List.Sublist.reverse /-
theorem Sublist.reverse {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse :=
  by
  induction' h with _ _ _ _ ih _ _ a _ ih; · rfl
  · rw [reverse_cons]
    exact sublist_append_of_sublist_left ih
  · rw [reverse_cons, reverse_cons]
    exact ih.append_right [a]
#align list.sublist.reverse List.Sublist.reverse
-/

#print List.reverse_sublist /-
@[simp]
theorem reverse_sublist {l₁ l₂ : List α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, Sublist.reverse⟩
#align list.reverse_sublist_iff List.reverse_sublist
-/

#print List.append_sublist_append_right /-
@[simp]
theorem append_sublist_append_right {l₁ l₂ : List α} (l) : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ :=
  ⟨fun h => by
    simpa only [reverse_append, append_sublist_append_left, reverse_sublist_iff] using h.reverse,
    fun h => h.append_right l⟩
#align list.append_sublist_append_right List.append_sublist_append_right
-/

#print List.Sublist.append /-
theorem Sublist.append {l₁ l₂ r₁ r₂ : List α} (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) :
    l₁ ++ r₁ <+ l₂ ++ r₂ :=
  (hl.append_right _).trans ((append_sublist_append_left _).2 hr)
#align list.sublist.append List.Sublist.append
-/

#print List.Sublist.subset /-
theorem Sublist.subset : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → l₁ ⊆ l₂
  | _, _, sublist.slnil, b, h => h
  | _, _, sublist.cons l₁ l₂ a s, b, h => mem_cons_of_mem _ (sublist.subset s h)
  | _, _, sublist.cons2 l₁ l₂ a s, b, h =>
    match eq_or_mem_of_mem_cons h with
    | Or.inl h => h ▸ mem_cons_self _ _
    | Or.inr h => mem_cons_of_mem _ (sublist.subset s h)
#align list.sublist.subset List.Sublist.subset
-/

#print List.singleton_sublist /-
@[simp]
theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
  ⟨fun h => h.Subset (mem_singleton_self _), fun h =>
    let ⟨s, t, e⟩ := mem_split h
    e.symm ▸ ((nil_sublist _).cons_cons _).trans (sublist_append_right _ _)⟩
#align list.singleton_sublist List.singleton_sublist
-/

#print List.eq_nil_of_sublist_nil /-
theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil <| s.Subset
#align list.eq_nil_of_sublist_nil List.eq_nil_of_sublist_nil
-/

#print List.sublist_nil_iff_eq_nil /-
@[simp]
theorem sublist_nil_iff_eq_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨eq_nil_of_sublist_nil, fun H => H ▸ Sublist.refl _⟩
#align list.sublist_nil_iff_eq_nil List.sublist_nil_iff_eq_nil
-/

/- warning: list.replicate_sublist_replicate -> List.replicate_sublist_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) {m : Nat} {n : Nat}, Iff (List.Sublist.{u1} α (List.replicate.{u1} α m a) (List.replicate.{u1} α n a)) (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall {α : Type.{u1}} {a : Nat} {m : Nat} (n : α), Iff (List.Sublist.{u1} α (List.replicate.{u1} α a n) (List.replicate.{u1} α m n)) (LE.le.{0} Nat instLENat a m)
Case conversion may be inaccurate. Consider using '#align list.replicate_sublist_replicate List.replicate_sublist_replicateₓ'. -/
@[simp]
theorem replicate_sublist_replicate (a : α) {m n} : replicate m a <+ replicate n a ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_replicate] using h.length_le, fun h => by
    induction h <;> [rfl, simp only [*, replicate_succ, sublist.cons]]⟩
#align list.replicate_sublist_replicate List.replicate_sublist_replicate

/- warning: list.sublist_replicate_iff -> List.sublist_replicate_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {n : Nat}, Iff (List.Sublist.{u1} α l (List.replicate.{u1} α n a)) (Exists.{1} Nat (fun (k : Nat) => Exists.{0} (LE.le.{0} Nat Nat.hasLe k n) (fun (H : LE.le.{0} Nat Nat.hasLe k n) => Eq.{succ u1} (List.{u1} α) l (List.replicate.{u1} α k a))))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {a : α} {n : Nat}, Iff (List.Sublist.{u1} α l (List.replicate.{u1} α n a)) (Exists.{1} Nat (fun (k : Nat) => And (LE.le.{0} Nat instLENat k n) (Eq.{succ u1} (List.{u1} α) l (List.replicate.{u1} α k a))))
Case conversion may be inaccurate. Consider using '#align list.sublist_replicate_iff List.sublist_replicate_iffₓ'. -/
theorem sublist_replicate_iff {l : List α} {a : α} {n : ℕ} :
    l <+ replicate n a ↔ ∃ k ≤ n, l = replicate k a :=
  ⟨fun h =>
    ⟨l.length, h.length_le.trans (length_replicate _ _).le,
      eq_replicate_length.mpr fun b hb => eq_of_mem_replicate (h.Subset hb)⟩,
    by
    rintro ⟨k, h, rfl⟩
    exact (replicate_sublist_replicate _).mpr h⟩
#align list.sublist_replicate_iff List.sublist_replicate_iff

#print List.Sublist.eq_of_length /-
theorem Sublist.eq_of_length : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
  | _, _, sublist.slnil, h => rfl
  | _, _, sublist.cons l₁ l₂ a s, h => by
    cases s.length_le.not_lt (by rw [h] <;> apply lt_succ_self)
  | _, _, sublist.cons2 l₁ l₂ a s, h => by
    rw [length, length] at h <;> injection h with h <;> rw [s.eq_of_length h]
#align list.sublist.eq_of_length List.Sublist.eq_of_length
-/

#print List.Sublist.eq_of_length_le /-
theorem Sublist.eq_of_length_le (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  s.eq_of_length <| s.length_le.antisymm h
#align list.sublist.eq_of_length_le List.Sublist.eq_of_length_le
-/

#print List.Sublist.antisymm /-
theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le
#align list.sublist.antisymm List.Sublist.antisymm
-/

#print List.decidableSublist /-
instance decidableSublist [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+ l₂)
  | [], l₂ => is_true <| nil_sublist _
  | a :: l₁, [] => is_false fun h => List.noConfusion <| eq_nil_of_sublist_nil h
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      decidable_of_decidable_of_iff (decidable_sublist l₁ l₂) <| by
        rw [← h] <;> exact ⟨sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
    else
      decidable_of_decidable_of_iff (decidable_sublist (a :: l₁) l₂)
        ⟨sublist_cons_of_sublist _, fun s =>
          match a, l₁, s, h with
          | a, l₁, sublist.cons _ _ _ s', h => s'
          | _, _, sublist.cons2 t _ _ s', h => absurd rfl h⟩
#align list.decidable_sublist List.decidableSublist
-/

/-! ### index_of -/


section IndexOf

variable [DecidableEq α]

#print List.indexOf_nil /-
@[simp]
theorem indexOf_nil (a : α) : indexOf a [] = 0 :=
  rfl
#align list.index_of_nil List.indexOf_nil
-/

#print List.indexOf_cons /-
theorem indexOf_cons (a b : α) (l : List α) :
    indexOf a (b :: l) = if a = b then 0 else succ (indexOf a l) :=
  rfl
#align list.index_of_cons List.indexOf_cons
-/

#print List.indexOf_cons_eq /-
theorem indexOf_cons_eq {a b : α} (l : List α) : a = b → indexOf a (b :: l) = 0 := fun e => if_pos e
#align list.index_of_cons_eq List.indexOf_cons_eq
-/

#print List.indexOf_cons_self /-
@[simp]
theorem indexOf_cons_self (a : α) (l : List α) : indexOf a (a :: l) = 0 :=
  indexOf_cons_eq _ rfl
#align list.index_of_cons_self List.indexOf_cons_self
-/

#print List.indexOf_cons_ne /-
@[simp]
theorem indexOf_cons_ne {a b : α} (l : List α) : a ≠ b → indexOf a (b :: l) = succ (indexOf a l) :=
  fun n => if_neg n
#align list.index_of_cons_ne List.indexOf_cons_ne
-/

#print List.indexOf_eq_length /-
theorem indexOf_eq_length {a : α} {l : List α} : indexOf a l = length l ↔ a ∉ l :=
  by
  induction' l with b l ih
  · exact iff_of_true rfl (not_mem_nil _)
  simp only [length, mem_cons_iff, index_of_cons]; split_ifs
  · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h
  · simp only [h, false_or_iff]
    rw [← ih]
    exact succ_inj'
#align list.index_of_eq_length List.indexOf_eq_length
-/

#print List.indexOf_of_not_mem /-
@[simp]
theorem indexOf_of_not_mem {l : List α} {a : α} : a ∉ l → indexOf a l = length l :=
  indexOf_eq_length.2
#align list.index_of_of_not_mem List.indexOf_of_not_mem
-/

#print List.indexOf_le_length /-
theorem indexOf_le_length {a : α} {l : List α} : indexOf a l ≤ length l :=
  by
  induction' l with b l ih; · rfl
  simp only [length, index_of_cons]
  by_cases h : a = b;
  · rw [if_pos h]
    exact Nat.zero_le _
  rw [if_neg h]; exact succ_le_succ ih
#align list.index_of_le_length List.indexOf_le_length
-/

#print List.indexOf_lt_length /-
theorem indexOf_lt_length {a} {l : List α} : indexOf a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction fun al => ne_of_lt h <| indexOf_eq_length.2 al, fun al =>
    lt_of_le_of_ne indexOf_le_length fun h => indexOf_eq_length.1 h al⟩
#align list.index_of_lt_length List.indexOf_lt_length
-/

#print List.indexOf_append_of_mem /-
theorem indexOf_append_of_mem {a : α} (h : a ∈ l₁) : indexOf a (l₁ ++ l₂) = indexOf a l₁ :=
  by
  induction' l₁ with d₁ t₁ ih
  · exfalso
    exact not_mem_nil a h
  rw [List.cons_append]
  by_cases hh : a = d₁
  · iterate 2 rw [index_of_cons_eq _ hh]
  rw [index_of_cons_ne _ hh, index_of_cons_ne _ hh, ih (mem_of_ne_of_mem hh h)]
#align list.index_of_append_of_mem List.indexOf_append_of_mem
-/

#print List.indexOf_append_of_not_mem /-
theorem indexOf_append_of_not_mem {a : α} (h : a ∉ l₁) :
    indexOf a (l₁ ++ l₂) = l₁.length + indexOf a l₂ :=
  by
  induction' l₁ with d₁ t₁ ih
  · rw [List.nil_append, List.length, zero_add]
  rw [List.cons_append, index_of_cons_ne _ (ne_of_not_mem_cons h), List.length,
    ih (not_mem_of_not_mem_cons h), Nat.succ_add]
#align list.index_of_append_of_not_mem List.indexOf_append_of_not_mem
-/

end IndexOf

/-! ### nth element -/


#print List.nthLe_of_mem /-
theorem nthLe_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n h, nthLe l n h = a
  | a, _ :: l, Or.inl rfl => ⟨0, succ_pos _, rfl⟩
  | a, b :: l, Or.inr m =>
    let ⟨n, h, e⟩ := nth_le_of_mem m
    ⟨n + 1, succ_lt_succ h, e⟩
#align list.nth_le_of_mem List.nthLe_of_mem
-/

#print List.nthLe_get? /-
theorem nthLe_get? : ∀ {l : List α} {n} (h), get? l n = some (nthLe l n h)
  | a :: l, 0, h => rfl
  | a :: l, n + 1, h => @nth_le_nth l n _
#align list.nth_le_nth List.nthLe_get?
-/

#print List.get?_len_le /-
theorem get?_len_le : ∀ {l : List α} {n}, length l ≤ n → get? l n = none
  | [], n, h => rfl
  | a :: l, n + 1, h => nth_len_le (le_of_succ_le_succ h)
#align list.nth_len_le List.get?_len_le
-/

#print List.get?_length /-
@[simp]
theorem get?_length (l : List α) : l.nth l.length = none :=
  get?_len_le le_rfl
#align list.nth_length List.get?_length
-/

#print List.get?_eq_some' /-
theorem get?_eq_some' {l : List α} {n a} : get? l n = some a ↔ ∃ h, nthLe l n h = a :=
  ⟨fun e =>
    have h : n < length l := lt_of_not_ge fun hn => by rw [nth_len_le hn] at e <;> contradiction
    ⟨h, by rw [nth_le_nth h] at e <;> injection e with e <;> apply nth_le_mem⟩,
    fun ⟨h, e⟩ => e ▸ nthLe_get? _⟩
#align list.nth_eq_some List.get?_eq_some'
-/

#print List.get?_eq_none /-
@[simp]
theorem get?_eq_none : ∀ {l : List α} {n}, get? l n = none ↔ length l ≤ n :=
  by
  intros ; constructor
  · intro h
    by_contra h'
    have h₂ : ∃ h, l.nth_le n h = l.nth_le n (lt_of_not_ge h') := ⟨lt_of_not_ge h', rfl⟩
    rw [← nth_eq_some, h] at h₂
    cases h₂
  · solve_by_elim [nth_len_le]
#align list.nth_eq_none_iff List.get?_eq_none
-/

#print List.get?_of_mem /-
theorem get?_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, get? l n = some a :=
  let ⟨n, h, e⟩ := nthLe_of_mem h
  ⟨n, by rw [nth_le_nth, e]⟩
#align list.nth_of_mem List.get?_of_mem
-/

#print List.nthLe_mem /-
theorem nthLe_mem : ∀ (l : List α) (n h), nthLe l n h ∈ l
  | a :: l, 0, h => mem_cons_self _ _
  | a :: l, n + 1, h => mem_cons_of_mem _ (nth_le_mem l _ _)
#align list.nth_le_mem List.nthLe_mem
-/

#print List.get?_mem /-
theorem get?_mem {l : List α} {n a} (e : get? l n = some a) : a ∈ l :=
  let ⟨h, e⟩ := get?_eq_some'.1 e
  e ▸ nthLe_mem _ _ _
#align list.nth_mem List.get?_mem
-/

#print List.mem_iff_nthLe /-
theorem mem_iff_nthLe {a} {l : List α} : a ∈ l ↔ ∃ n h, nthLe l n h = a :=
  ⟨nthLe_of_mem, fun ⟨n, h, e⟩ => e ▸ nthLe_mem _ _ _⟩
#align list.mem_iff_nth_le List.mem_iff_nthLe
-/

#print List.mem_iff_get? /-
theorem mem_iff_get? {a} {l : List α} : a ∈ l ↔ ∃ n, get? l n = some a :=
  mem_iff_nthLe.trans <| exists_congr fun n => get?_eq_some'.symm
#align list.mem_iff_nth List.mem_iff_get?
-/

#print List.get?_zero /-
theorem get?_zero (l : List α) : l.nth 0 = l.head' := by cases l <;> rfl
#align list.nth_zero List.get?_zero
-/

#print List.get?_injective /-
theorem get?_injective {α : Type u} {xs : List α} {i j : ℕ} (h₀ : i < xs.length) (h₁ : Nodup xs)
    (h₂ : xs.nth i = xs.nth j) : i = j :=
  by
  induction' xs with x xs generalizing i j
  · cases h₀
  · cases i <;> cases j
    case zero.zero => rfl
    case succ.succ =>
      congr ; cases h₁
      apply xs_ih <;> solve_by_elim [lt_of_succ_lt_succ]
    iterate 2 
      dsimp at h₂
      cases' h₁ with _ _ h h'
      cases h x _ rfl
      rw [mem_iff_nth]
      first |exact ⟨_, h₂.symm⟩|exact ⟨_, h₂⟩
#align list.nth_injective List.get?_injective
-/

/- warning: list.nth_map -> List.get?_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (l : List.{u1} α) (n : Nat), Eq.{succ u2} (Option.{u2} β) (List.get?.{u2} β (List.map.{u1, u2} α β f l) n) (Option.map.{u1, u2} α β f (List.get?.{u1} α l n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (l : List.{u2} α) (n : Nat), Eq.{succ u1} (Option.{u1} β) (List.get?.{u1} β (List.map.{u2, u1} α β f l) n) (Option.map.{u2, u1} α β f (List.get?.{u2} α l n))
Case conversion may be inaccurate. Consider using '#align list.nth_map List.get?_mapₓ'. -/
@[simp]
theorem get?_map (f : α → β) : ∀ l n, get? (map f l) n = (get? l n).map f
  | [], n => rfl
  | a :: l, 0 => rfl
  | a :: l, n + 1 => nth_map l n
#align list.nth_map List.get?_map

#print List.nthLe_map /-
theorem nthLe_map (f : α → β) {l n} (H1 H2) : nthLe (map f l) n H1 = f (nthLe l n H2) :=
  Option.some.inj <| by rw [← nth_le_nth, nth_map, nth_le_nth] <;> rfl
#align list.nth_le_map List.nthLe_map
-/

#print List.nthLe_map_rev /-
/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nthLe_map_rev (f : α → β) {l n} (H) :
    f (nthLe l n H) = nthLe (map f l) n ((length_map f l).symm ▸ H) :=
  (nthLe_map f _ _).symm
#align list.nth_le_map_rev List.nthLe_map_rev
-/

#print List.nthLe_map' /-
@[simp]
theorem nthLe_map' (f : α → β) {l n} (H) :
    nthLe (map f l) n H = f (nthLe l n (length_map f l ▸ H)) :=
  nthLe_map f _ _
#align list.nth_le_map' List.nthLe_map'
-/

#print List.nthLe_of_eq /-
/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
theorem nthLe_of_eq {L L' : List α} (h : L = L') {i : ℕ} (hi : i < L.length) :
    nthLe L i hi = nthLe L' i (h ▸ hi) := by
  congr
  exact h
#align list.nth_le_of_eq List.nthLe_of_eq
-/

#print List.nthLe_singleton /-
@[simp]
theorem nthLe_singleton (a : α) {n : ℕ} (hn : n < 1) : nthLe [a] n hn = a :=
  by
  have hn0 : n = 0 := Nat.eq_zero_of_le_zero (le_of_lt_succ hn)
  subst hn0 <;> rfl
#align list.nth_le_singleton List.nthLe_singleton
-/

#print List.nthLe_zero /-
theorem nthLe_zero [Inhabited α] {L : List α} (h : 0 < L.length) : L.nthLe 0 h = L.head :=
  by
  cases L
  cases h
  simp
#align list.nth_le_zero List.nthLe_zero
-/

#print List.nthLe_append /-
theorem nthLe_append :
    ∀ {l₁ l₂ : List α} {n : ℕ} (hn₁) (hn₂), (l₁ ++ l₂).nthLe n hn₁ = l₁.nthLe n hn₂
  | [], _, n, hn₁, hn₂ => (Nat.not_lt_zero _ hn₂).elim
  | a :: l, _, 0, hn₁, hn₂ => rfl
  | a :: l, _, n + 1, hn₁, hn₂ => by simp only [nth_le, cons_append] <;> exact nth_le_append _ _
#align list.nth_le_append List.nthLe_append
-/

#print List.get_append_right_aux /-
theorem get_append_right_aux {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n)
    (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length :=
  by
  rw [List.length_append] at h₂
  apply lt_of_add_lt_add_right
  rwa [Nat.sub_add_cancel h₁, Nat.add_comm]
#align list.nth_le_append_right_aux List.get_append_right_aux
-/

#print List.nthLe_append_right /-
theorem nthLe_append_right :
    ∀ {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂),
      (l₁ ++ l₂).nthLe n h₂ = l₂.nthLe (n - l₁.length) (get_append_right_aux h₁ h₂)
  | [], _, n, h₁, h₂ => rfl
  | a :: l, _, n + 1, h₁, h₂ => by
    dsimp
    conv =>
      rhs
      congr
      skip
      rw [Nat.add_sub_add_right]
    rw [nth_le_append_right (nat.lt_succ_iff.mp h₁)]
#align list.nth_le_append_right List.nthLe_append_right
-/

#print List.nthLe_replicate /-
@[simp]
theorem nthLe_replicate (a : α) {n m : ℕ} (h : m < (List.replicate n a).length) :
    (List.replicate n a).nthLe m h = a :=
  eq_of_mem_replicate (nthLe_mem _ _ _)
#align list.nth_le_replicate List.nthLe_replicate
-/

#print List.get?_append /-
theorem get?_append {l₁ l₂ : List α} {n : ℕ} (hn : n < l₁.length) : (l₁ ++ l₂).nth n = l₁.nth n :=
  by
  have hn' : n < (l₁ ++ l₂).length :=
    lt_of_lt_of_le hn (by rw [length_append] <;> exact Nat.le_add_right _ _)
  rw [nth_le_nth hn, nth_le_nth hn', nth_le_append]
#align list.nth_append List.get?_append
-/

#print List.get?_append_right /-
theorem get?_append_right {l₁ l₂ : List α} {n : ℕ} (hn : l₁.length ≤ n) :
    (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) :=
  by
  by_cases hl : n < (l₁ ++ l₂).length
  · rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn]
  · rw [nth_len_le (le_of_not_lt hl), nth_len_le]
    rw [not_lt, length_append] at hl
    exact le_tsub_of_add_le_left hl
#align list.nth_append_right List.get?_append_right
-/

#print List.getLast_eq_nthLe /-
theorem getLast_eq_nthLe :
    ∀ (l : List α) (h : l ≠ []),
      getLast l h = l.nthLe (l.length - 1) (Nat.sub_lt (length_pos_of_ne_nil h) one_pos)
  | [], h => rfl
  | [a], h => by rw [last_singleton, nth_le_singleton]
  | a :: b :: l, h => by
    rw [last_cons, last_eq_nth_le (b :: l)]
    rfl
    exact cons_ne_nil b l
#align list.last_eq_nth_le List.getLast_eq_nthLe
-/

#print List.nthLe_length_sub_one /-
theorem nthLe_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.nthLe (l.length - 1) h =
      l.last
        (by
          rintro rfl
          exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_nthLe l _).symm
#align list.nth_le_length_sub_one List.nthLe_length_sub_one
-/

#print List.get?_concat_length /-
@[simp]
theorem get?_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).nth l.length = some a
  | [], a => rfl
  | b :: l, a => by rw [cons_append, length_cons, nth, nth_concat_length]
#align list.nth_concat_length List.get?_concat_length
-/

#print List.nthLe_cons_length /-
theorem nthLe_cons_length (x : α) (xs : List α) (n : ℕ) (h : n = xs.length) :
    (x :: xs).nthLe n (by simp [h]) = (x :: xs).last (cons_ne_nil x xs) :=
  by
  rw [last_eq_nth_le]
  congr
  simp [h]
#align list.nth_le_cons_length List.nthLe_cons_length
-/

#print List.take_one_drop_eq_of_lt_length' /-
theorem take_one_drop_eq_of_lt_length' {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.nthLe n h] :=
  by
  induction' l with x l ih generalizing n
  · cases h
  · by_cases h₁ : l = []
    · subst h₁
      rw [nth_le_singleton]
      simp [lt_succ_iff] at h
      subst h
      simp
    have h₂ := h
    rw [length_cons, Nat.lt_succ_iff, le_iff_eq_or_lt] at h₂
    cases n
    · simp
    rw [drop, nth_le]
    apply ih
#align list.take_one_drop_eq_of_lt_length List.take_one_drop_eq_of_lt_length'
-/

#print List.ext /-
@[ext]
theorem ext : ∀ {l₁ l₂ : List α}, (∀ n, get? l₁ n = get? l₂ n) → l₁ = l₂
  | [], [], h => rfl
  | a :: l₁, [], h => by have h0 := h 0 <;> contradiction
  | [], a' :: l₂, h => by have h0 := h 0 <;> contradiction
  | a :: l₁, a' :: l₂, h => by
    have h0 : some a = some a' := h 0 <;> injection h0 with aa <;>
          simp only [aa, ext fun n => h (n + 1)] <;>
        constructor <;>
      rfl
#align list.ext List.ext
-/

#print List.ext_nthLe /-
theorem ext_nthLe {l₁ l₂ : List α} (hl : length l₁ = length l₂)
    (h : ∀ n h₁ h₂, nthLe l₁ n h₁ = nthLe l₂ n h₂) : l₁ = l₂ :=
  ext fun n =>
    if h₁ : n < length l₁ then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
    else by
      let h₁ := le_of_not_gt h₁
      rw [nth_len_le h₁, nth_len_le]
      rwa [← hl]
#align list.ext_le List.ext_nthLe
-/

#print List.indexOf_nthLe /-
@[simp]
theorem indexOf_nthLe [DecidableEq α] {a : α} : ∀ {l : List α} (h), nthLe l (indexOf a l) h = a
  | b :: l, h => by
    by_cases h' : a = b <;>
      simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]
#align list.index_of_nth_le List.indexOf_nthLe
-/

#print List.indexOf_get? /-
@[simp]
theorem indexOf_get? [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    get? l (indexOf a l) = some a := by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]
#align list.index_of_nth List.indexOf_get?
-/

#print List.get_reverse_aux₁ /-
theorem get_reverse_aux₁ :
    ∀ (l r : List α) (i h1 h2), nthLe (reverseAux l r) (i + length l) h1 = nthLe r i h2
  | [], r, i => fun h1 h2 => rfl
  | a :: l, r, i => by
    rw [show i + length (a :: l) = i + 1 + length l from add_right_comm i (length l) 1] <;>
      exact fun h1 h2 => nth_le_reverse_aux1 l (a :: r) (i + 1) h1 (succ_lt_succ h2)
#align list.nth_le_reverse_aux1 List.get_reverse_aux₁
-/

#print List.indexOf_inj /-
theorem indexOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    indexOf x l = indexOf y l ↔ x = y :=
  ⟨fun h =>
    by
    have :
      nthLe l (indexOf x l) (indexOf_lt_length.2 hx) =
        nthLe l (indexOf y l) (indexOf_lt_length.2 hy) :=
      by simp only [h]
    simpa only [index_of_nth_le] , fun h => by subst h⟩
#align list.index_of_inj List.indexOf_inj
-/

#print List.get_reverse_aux₂ /-
theorem get_reverse_aux₂ :
    ∀ (l r : List α) (i : Nat) (h1) (h2),
      nthLe (reverseAux l r) (length l - 1 - i) h1 = nthLe l i h2
  | [], r, i, h1, h2 => absurd h2 (Nat.not_lt_zero _)
  | a :: l, r, 0, h1, h2 => by
    have aux := nth_le_reverse_aux1 l (a :: r) 0
    rw [zero_add] at aux
    exact aux _ (zero_lt_succ _)
  | a :: l, r, i + 1, h1, h2 =>
    by
    have aux := nth_le_reverse_aux2 l (a :: r) i
    have heq :=
      calc
        length (a :: l) - 1 - (i + 1) = length l - (1 + i) := by rw [add_comm] <;> rfl
        _ = length l - 1 - i := by rw [← tsub_add_eq_tsub_tsub]
        
    rw [← HEq] at aux
    apply aux
#align list.nth_le_reverse_aux2 List.get_reverse_aux₂
-/

#print List.nthLe_reverse /-
@[simp]
theorem nthLe_reverse (l : List α) (i : Nat) (h1 h2) :
    nthLe (reverse l) (length l - 1 - i) h1 = nthLe l i h2 :=
  get_reverse_aux₂ _ _ _ _ _
#align list.nth_le_reverse List.nthLe_reverse
-/

#print List.nthLe_reverse' /-
theorem nthLe_reverse' (l : List α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
    l.reverse.nthLe n hn = l.nthLe (l.length - 1 - n) hn' :=
  by
  rw [eq_comm]
  convert nth_le_reverse l.reverse _ _ _ using 1
  · simp
  · simpa
#align list.nth_le_reverse' List.nthLe_reverse'
-/

#print List.eq_cons_of_length_one /-
theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) :
    l = [l.nthLe 0 (h.symm ▸ zero_lt_one)] :=
  by
  refine' ext_le (by convert h) fun n h₁ h₂ => _
  simp only [nth_le_singleton]
  congr
  exact eq_bot_iff.mpr (nat.lt_succ_iff.mp h₂)
#align list.eq_cons_of_length_one List.eq_cons_of_length_one
-/

#print List.nthLe_eq_iff /-
theorem nthLe_eq_iff {l : List α} {n : ℕ} {x : α} {h} : l.nthLe n h = x ↔ l.nth n = some x :=
  by
  rw [nth_eq_some]
  tauto
#align list.nth_le_eq_iff List.nthLe_eq_iff
-/

#print List.some_nthLe_eq /-
theorem some_nthLe_eq {l : List α} {n : ℕ} {h} : some (l.nthLe n h) = l.nth n :=
  by
  symm
  rw [nth_eq_some]
  tauto
#align list.some_nth_le_eq List.some_nthLe_eq
-/

#print List.modifyNthTail_modifyNthTail /-
theorem modifyNthTail_modifyNthTail {f g : List α → List α} (m : ℕ) :
    ∀ (n) (l : List α),
      (l.modifyNthTail f n).modifyNthTail g (m + n) =
        l.modifyNthTail (fun l => (f l).modifyNthTail g m) n
  | 0, l => rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modify_nth_tail_modify_nth_tail n l)
#align list.modify_nth_tail_modify_nth_tail List.modifyNthTail_modifyNthTail
-/

#print List.modifyNthTail_modifyNthTail_le /-
theorem modifyNthTail_modifyNthTail_le {f g : List α → List α} (m n : ℕ) (l : List α) (h : n ≤ m) :
    (l.modifyNthTail f n).modifyNthTail g m =
      l.modifyNthTail (fun l => (f l).modifyNthTail g (m - n)) n :=
  by
  rcases exists_add_of_le h with ⟨m, rfl⟩
  rw [add_tsub_cancel_left, add_comm, modify_nth_tail_modify_nth_tail]
#align list.modify_nth_tail_modify_nth_tail_le List.modifyNthTail_modifyNthTail_le
-/

#print List.modifyNthTail_modifyNthTail_same /-
theorem modifyNthTail_modifyNthTail_same {f g : List α → List α} (n : ℕ) (l : List α) :
    (l.modifyNthTail f n).modifyNthTail g n = l.modifyNthTail (g ∘ f) n := by
  rw [modify_nth_tail_modify_nth_tail_le n n l (le_refl n), tsub_self] <;> rfl
#align list.modify_nth_tail_modify_nth_tail_same List.modifyNthTail_modifyNthTail_same
-/

#print List.modifyNthTail_id /-
theorem modifyNthTail_id : ∀ (n) (l : List α), l.modifyNthTail id n = l
  | 0, l => rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modify_nth_tail_id n l)
#align list.modify_nth_tail_id List.modifyNthTail_id
-/

#print List.removeNth_eq_nthTail /-
theorem removeNth_eq_nthTail : ∀ (n) (l : List α), removeNth l n = modifyNthTail tail n l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, a :: l => congr_arg (cons _) (remove_nth_eq_nth_tail _ _)
#align list.remove_nth_eq_nth_tail List.removeNth_eq_nthTail
-/

#print List.set_eq_modifyNth /-
theorem set_eq_modifyNth (a : α) : ∀ (n) (l : List α), set l n a = modifyNth (fun _ => a) n l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, b :: l => congr_arg (cons _) (update_nth_eq_modify_nth _ _)
#align list.update_nth_eq_modify_nth List.set_eq_modifyNth
-/

/- warning: list.modify_nth_eq_update_nth -> List.modifyNth_eq_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.modifyNth.{u1} α f n l) (Option.getD.{u1} (List.{u1} α) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α (List.{u1} α) (fun (a : α) => List.set.{u1} α l n (f a)) (List.get?.{u1} α l n)) l)
but is expected to have type
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.modifyNth.{u1} α f n l) (Option.getD.{u1} (List.{u1} α) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α (List.{u1} α) (fun (a : α) => List.set.{u1} α l n (f a)) (List.get?.{u1} α l n)) l)
Case conversion may be inaccurate. Consider using '#align list.modify_nth_eq_update_nth List.modifyNth_eq_setₓ'. -/
theorem modifyNth_eq_set (f : α → α) :
    ∀ (n) (l : List α), modifyNth f n l = ((fun a => set l n (f a)) <$> get? l n).getOrElse l
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, b :: l =>
    (congr_arg (cons b) (modify_nth_eq_update_nth n l)).trans <| by cases nth l n <;> rfl
#align list.modify_nth_eq_update_nth List.modifyNth_eq_set

/- warning: list.nth_modify_nth -> List.get?_modifyNth is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α) (m : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.modifyNth.{u1} α f n l) m) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α α (fun (a : α) => ite.{succ u1} α (Eq.{1} Nat n m) (Nat.decidableEq n m) (f a) a) (List.get?.{u1} α l m))
but is expected to have type
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α) (m : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.modifyNth.{u1} α f n l) m) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α α (fun (a : α) => ite.{succ u1} α (Eq.{1} Nat n m) (instDecidableEqNat n m) (f a) a) (List.get?.{u1} α l m))
Case conversion may be inaccurate. Consider using '#align list.nth_modify_nth List.get?_modifyNthₓ'. -/
theorem get?_modifyNth (f : α → α) :
    ∀ (n) (l : List α) (m),
      get? (modifyNth f n l) m = (fun a => if n = m then f a else a) <$> get? l m
  | n, l, 0 => by cases l <;> cases n <;> rfl
  | n, [], m + 1 => by cases n <;> rfl
  | 0, a :: l, m + 1 => by cases nth l m <;> rfl
  | n + 1, a :: l, m + 1 =>
    (nth_modify_nth n l m).trans <| by
      cases' nth l m with b <;> by_cases n = m <;>
        simp only [h, if_pos, if_true, if_false, Option.map_none, Option.map_some, mt succ.inj,
          not_false_iff]
#align list.nth_modify_nth List.get?_modifyNth

#print List.length_modifyNthTail /-
theorem length_modifyNthTail (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, l => H _
  | n + 1, [] => rfl
  | n + 1, a :: l => @congr_arg _ _ _ _ (· + 1) (modify_nth_tail_length _ _)
#align list.modify_nth_tail_length List.length_modifyNthTail
-/

#print List.length_modifyNth /-
@[simp]
theorem length_modifyNth (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  length_modifyNthTail _ fun l => by cases l <;> rfl
#align list.modify_nth_length List.length_modifyNth
-/

#print List.length_set /-
@[simp]
theorem length_set (l : List α) (n) (a : α) : length (set l n a) = length l := by
  simp only [update_nth_eq_modify_nth, modify_nth_length]
#align list.update_nth_length List.length_set
-/

/- warning: list.nth_modify_nth_eq -> List.get?_modifyNth_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.modifyNth.{u1} α f n l) n) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α α f (List.get?.{u1} α l n))
but is expected to have type
  forall {α : Type.{u1}} (f : α -> α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.modifyNth.{u1} α f n l) n) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α α f (List.get?.{u1} α l n))
Case conversion may be inaccurate. Consider using '#align list.nth_modify_nth_eq List.get?_modifyNth_eqₓ'. -/
@[simp]
theorem get?_modifyNth_eq (f : α → α) (n) (l : List α) :
    get? (modifyNth f n l) n = f <$> get? l n := by simp only [nth_modify_nth, if_pos]
#align list.nth_modify_nth_eq List.get?_modifyNth_eq

#print List.get?_modifyNth_ne /-
@[simp]
theorem get?_modifyNth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) :
    get? (modifyNth f m l) n = get? l n := by simp only [nth_modify_nth, if_neg h, id_map']
#align list.nth_modify_nth_ne List.get?_modifyNth_ne
-/

/- warning: list.nth_update_nth_eq -> List.get?_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.set.{u1} α l n a) n) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α α (fun (_x : α) => a) (List.get?.{u1} α l n))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (n : Nat) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α (List.set.{u1} α l n a) n) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α α (fun (_x : α) => a) (List.get?.{u1} α l n))
Case conversion may be inaccurate. Consider using '#align list.nth_update_nth_eq List.get?_set_eqₓ'. -/
theorem get?_set_eq (a : α) (n) (l : List α) : get? (set l n a) n = (fun _ => a) <$> get? l n := by
  simp only [update_nth_eq_modify_nth, nth_modify_nth_eq]
#align list.nth_update_nth_eq List.get?_set_eq

#print List.get?_set_eq_of_lt /-
theorem get?_set_eq_of_lt (a : α) {n} {l : List α} (h : n < length l) :
    get? (set l n a) n = some a := by rw [nth_update_nth_eq, nth_le_nth h] <;> rfl
#align list.nth_update_nth_of_lt List.get?_set_eq_of_lt
-/

#print List.get?_set_ne /-
theorem get?_set_ne (a : α) {m n} (l : List α) (h : m ≠ n) : get? (set l m a) n = get? l n := by
  simp only [update_nth_eq_modify_nth, nth_modify_nth_ne _ _ h]
#align list.nth_update_nth_ne List.get?_set_ne
-/

#print List.set_nil /-
@[simp]
theorem set_nil (n : ℕ) (a : α) : [].updateNth n a = [] :=
  rfl
#align list.update_nth_nil List.set_nil
-/

#print List.set_succ /-
@[simp]
theorem set_succ (x : α) (xs : List α) (n : ℕ) (a : α) :
    (x :: xs).updateNth n.succ a = x :: xs.updateNth n a :=
  rfl
#align list.update_nth_succ List.set_succ
-/

#print List.set_comm /-
theorem set_comm (a b : α) :
    ∀ {n m : ℕ} (l : List α) (h : n ≠ m),
      (l.updateNth n a).updateNth m b = (l.updateNth m b).updateNth n a
  | _, _, [], _ => by simp
  | 0, 0, x :: t, h => absurd rfl h
  | n + 1, 0, x :: t, h => by simp [List.set]
  | 0, m + 1, x :: t, h => by simp [List.set]
  | n + 1, m + 1, x :: t, h =>
    by
    simp only [update_nth, true_and_iff, eq_self_iff_true]
    exact update_nth_comm t fun h' => h <| nat.succ_inj'.mpr h'
#align list.update_nth_comm List.set_comm
-/

#print List.nthLe_set_eq /-
@[simp]
theorem nthLe_set_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.updateNth i a).length) :
    (l.updateNth i a).nthLe i h = a := by
  rw [← Option.some_inj, ← nth_le_nth, nth_update_nth_eq, nth_le_nth] <;> simp_all
#align list.nth_le_update_nth_eq List.nthLe_set_eq
-/

#print List.nthLe_set_of_ne /-
@[simp]
theorem nthLe_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.updateNth i a).length) :
    (l.updateNth i a).nthLe j hj = l.nthLe j (by simpa using hj) := by
  rw [← Option.some_inj, ← List.nthLe_get?, List.get?_set_ne _ _ h, List.nthLe_get?]
#align list.nth_le_update_nth_of_ne List.nthLe_set_of_ne
-/

#print List.mem_or_eq_of_mem_set /-
theorem mem_or_eq_of_mem_set :
    ∀ {l : List α} {n : ℕ} {a b : α} (h : a ∈ l.updateNth n b), a ∈ l ∨ a = b
  | [], n, a, b, h => False.elim h
  | c :: l, 0, a, b, h => ((mem_cons _ _ _).1 h).elim Or.inr (Or.inl ∘ mem_cons_of_mem _)
  | c :: l, n + 1, a, b, h =>
    ((mem_cons _ _ _).1 h).elim (fun h => h ▸ Or.inl (mem_cons_self _ _)) fun h =>
      (mem_or_eq_of_mem_update_nth h).elim (Or.inl ∘ mem_cons_of_mem _) Or.inr
#align list.mem_or_eq_of_mem_update_nth List.mem_or_eq_of_mem_set
-/

section InsertNth

variable {a : α}

#print List.insertNth_zero /-
@[simp]
theorem insertNth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl
#align list.insert_nth_zero List.insertNth_zero
-/

#print List.insertNth_succ_nil /-
@[simp]
theorem insertNth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl
#align list.insert_nth_succ_nil List.insertNth_succ_nil
-/

#print List.insertNth_succ_cons /-
@[simp]
theorem insertNth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl
#align list.insert_nth_succ_cons List.insertNth_succ_cons
-/

#print List.length_insertNth /-
theorem length_insertNth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, as, h => rfl
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => congr_arg Nat.succ <| length_insert_nth n as (Nat.le_of_succ_le_succ h)
#align list.length_insert_nth List.length_insertNth
-/

#print List.removeNth_insertNth /-
theorem removeNth_insertNth (n : ℕ) (l : List α) : (l.insertNth n a).removeNth n = l := by
  rw [remove_nth_eq_nth_tail, insert_nth, modify_nth_tail_modify_nth_tail_same] <;>
    exact modify_nth_tail_id _ _
#align list.remove_nth_insert_nth List.removeNth_insertNth
-/

#print List.insertNth_removeNth_of_ge /-
theorem insertNth_removeNth_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertNth m a (as.removeNth n) = (as.insertNth (m + 1) a).removeNth n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, a :: as, has, hmn => by simp [remove_nth, insert_nth]
  | 0, m + 1, a :: as, has, hmn => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insert_nth_remove_nth_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_ge List.insertNth_removeNth_of_ge
-/

#print List.insertNth_removeNth_of_le /-
theorem insertNth_removeNth_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.removeNth n) = (as.insertNth m a).removeNth (n + 1)
  | n, 0, a :: as, has, hmn => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insert_nth_remove_nth_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_le List.insertNth_removeNth_of_le
-/

#print List.insertNth_comm /-
theorem insertNth_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (h : i ≤ j) (hj : j ≤ length l),
      (l.insertNth i a).insertNth (j + 1) b = (l.insertNth j b).insertNth i a
  | 0, j, l => by simp [insert_nth]
  | i + 1, 0, l => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp [insert_nth] <;>
      exact insert_nth_comm i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)
#align list.insert_nth_comm List.insertNth_comm
-/

#print List.mem_insertNth /-
theorem mem_insertNth {a b : α} :
    ∀ {n : ℕ} {l : List α} (hi : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, h => Iff.rfl
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    dsimp [List.insertNth]
    erw [mem_insert_nth (Nat.le_of_succ_le_succ h), ← or_assoc, or_comm' (a = a'), or_assoc]
#align list.mem_insert_nth List.mem_insertNth
-/

#print List.insertNth_of_length_lt /-
theorem insertNth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertNth n x l = l := by
  induction' l with hd tl IH generalizing n
  · cases n
    · simpa using h
    · simp
  · cases n
    · simpa using h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using IH _ h
#align list.insert_nth_of_length_lt List.insertNth_of_length_lt
-/

#print List.insertNth_length_self /-
@[simp]
theorem insertNth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] :=
  by
  induction' l with hd tl IH
  · simp
  · simpa using IH
#align list.insert_nth_length_self List.insertNth_length_self
-/

#print List.length_le_length_insertNth /-
theorem length_le_length_insertNth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length :=
  by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insert_nth _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insert_nth_of_length_lt _ _ _ hn]
#align list.length_le_length_insert_nth List.length_le_length_insertNth
-/

#print List.length_insertNth_le_succ /-
theorem length_insertNth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 :=
  by
  cases' le_or_lt n l.length with hn hn
  · rw [length_insert_nth _ _ hn]
  · rw [insert_nth_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le
#align list.length_insert_nth_le_succ List.length_insertNth_le_succ
-/

#print List.nthLe_insertNth_of_lt /-
theorem nthLe_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l).nthLe k hk' = l.nthLe k hk :=
  by
  induction' n with n IH generalizing k l
  · simpa using hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _
#align list.nth_le_insert_nth_of_lt List.nthLe_insertNth_of_lt
-/

#print List.nthLe_insertNth_self /-
@[simp]
theorem nthLe_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insert_nth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).nthLe n hn' = x :=
  by
  induction' l with hd tl IH generalizing n
  · simp only [length, nonpos_iff_eq_zero] at hn
    simp [hn]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn
#align list.nth_le_insert_nth_self List.nthLe_insertNth_self
-/

#print List.nthLe_insertNth_add_succ /-
theorem nthLe_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length :=
      (by rwa [length_insert_nth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff])) :
    (insertNth n x l).nthLe (n + k + 1) hk = nthLe l (n + k) hk' :=
  by
  induction' l with hd tl IH generalizing n k
  · simpa using hk'
  · cases n
    · simpa
    · simpa [succ_add] using IH _ _ _
#align list.nth_le_insert_nth_add_succ List.nthLe_insertNth_add_succ
-/

#print List.insertNth_injective /-
theorem insertNth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) :=
  by
  induction' n with n IH
  · have : insert_nth 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> first |simpa [IH.eq_iff] using h|rfl
#align list.insert_nth_injective List.insertNth_injective
-/

end InsertNth

/-! ### map -/


/- warning: list.map_nil -> List.map_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.nil.{u1} α)) (List.nil.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (List.nil.{u2} α)) (List.nil.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.map_nil List.map_nilₓ'. -/
@[simp]
theorem map_nil (f : α → β) : map f [] = [] :=
  rfl
#align list.map_nil List.map_nil

#print List.map_eq_foldr /-
theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l := by
  induction l <;> simp [*]
#align list.map_eq_foldr List.map_eq_foldr
-/

#print List.map_congr /-
theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → map f l = map g l
  | [], _ => rfl
  | a :: l, h => by
    let ⟨h₁, h₂⟩ := forall_mem_cons.1 h
    rw [map, map, h₁, map_congr h₂]
#align list.map_congr List.map_congr
-/

#print List.map_eq_map_iff /-
theorem map_eq_map_iff {f g : α → β} {l : List α} : map f l = map g l ↔ ∀ x ∈ l, f x = g x :=
  by
  refine' ⟨_, map_congr⟩; intro h x hx
  rw [mem_iff_nth_le] at hx; rcases hx with ⟨n, hn, rfl⟩
  rw [nth_le_map_rev f, nth_le_map_rev g]; congr ; exact h
#align list.map_eq_map_iff List.map_eq_map_iff
-/

#print List.map_concat /-
theorem map_concat (f : α → β) (a : α) (l : List α) : map f (concat l a) = concat (map f l) (f a) :=
  by
  induction l <;> [rfl, simp only [*, concat_eq_append, cons_append, map, map_append]] <;>
      constructor <;>
    rfl
#align list.map_concat List.map_concat
-/

#print List.map_id'' /-
@[simp]
theorem map_id'' (l : List α) : map (fun x => x) l = l :=
  map_id _
#align list.map_id'' List.map_id''
-/

#print List.map_id' /-
theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l := by
  simp [show f = id from funext h]
#align list.map_id' List.map_id'
-/

#print List.eq_nil_of_map_eq_nil /-
theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = nil) : l = nil :=
  eq_nil_of_length_eq_zero <| by rw [← length_map f l, h] <;> rfl
#align list.eq_nil_of_map_eq_nil List.eq_nil_of_map_eq_nil
-/

#print List.map_join /-
@[simp]
theorem map_join (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) := by
  induction L <;> [rfl, simp only [*, join, map, map_append]]
#align list.map_join List.map_join
-/

#print List.bind_ret_eq_map /-
theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l := by
  unfold List.bind <;> induction l <;>
        simp only [map, join, List.ret, cons_append, nil_append, *] <;>
      constructor <;>
    rfl
#align list.bind_ret_eq_map List.bind_ret_eq_map
-/

#print List.bind_congr /-
theorem bind_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    List.bind l f = List.bind l g :=
  (congr_arg List.join <| map_congr h : _)
#align list.bind_congr List.bind_congr
-/

/- warning: list.map_eq_map -> List.map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (l : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => List.{u1} α) (Traversable.toFunctor.{u1} (fun {α : Type.{u1}} => List.{u1} α) List.traversable.{u1}) α β f l) (List.map.{u1, u1} α β f l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (l : List.{u1} α), Eq.{succ u1} (List.{u1} β) (Functor.map.{u1, u1} List.{u1} List.instFunctorList.{u1} α β f l) (List.map.{u1, u1} α β f l)
Case conversion may be inaccurate. Consider using '#align list.map_eq_map List.map_eq_mapₓ'. -/
@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl
#align list.map_eq_map List.map_eq_map

#print List.map_tail /-
@[simp]
theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) := by cases l <;> rfl
#align list.map_tail List.map_tail
-/

#print List.map_injective_iff /-
@[simp]
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f :=
  by
  constructor <;> intro h x y hxy
  · suffices [x] = [y] by simpa using this
    apply h
    simp [hxy]
  · induction y generalizing x
    simpa using hxy
    cases x
    simpa using hxy
    simp at hxy
    simp [y_ih hxy.2, h hxy.1]
#align list.map_injective_iff List.map_injective_iff
-/

#print List.comp_map /-
/-- A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm
#align list.comp_map List.comp_map
-/

#print List.map_comp_map /-
/-- Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) :=
  by
  ext l
  rw [comp_map]
#align list.map_comp_map List.map_comp_map
-/

/- warning: list.map_filter_eq_foldr -> List.map_filter_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (as : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) as)) (List.foldr.{u1, u2} α (List.{u2} β) (fun (a : α) (bs : List.{u2} β) => ite.{succ u2} (List.{u2} β) (p a) (_inst_1 a) (List.cons.{u2} β (f a) bs) bs) (List.nil.{u2} β) as)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.filter.{u1} α p _inst_1)) (List.foldr.{u1, u2} α (List.{u2} β) (fun (a : α) (bs : List.{u2} β) => cond.{u2} (List.{u2} β) (p a) (List.cons.{u2} β (f a) bs) bs) (List.nil.{u2} β) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.map_filter_eq_foldr List.map_filter_eq_foldrₓ'. -/
theorem map_filter_eq_foldr (f : α → β) (p : α → Prop) [DecidablePred p] (as : List α) :
    map f (filter p as) = foldr (fun a bs => if p a then f a :: bs else bs) [] as :=
  by
  induction as
  · rfl
  · simp! [*, apply_ite (map f)]
#align list.map_filter_eq_foldr List.map_filter_eq_foldr

#print List.getLast_map /-
theorem getLast_map (f : α → β) {l : List α} (hl : l ≠ []) :
    (l.map f).last (mt eq_nil_of_map_eq_nil hl) = f (l.last hl) :=
  by
  induction' l with l_hd l_tl l_ih
  · apply (hl rfl).elim
  · cases l_tl
    · simp
    · simpa using l_ih
#align list.last_map List.getLast_map
-/

#print List.map_eq_replicate_iff /-
theorem map_eq_replicate_iff {l : List α} {f : α → β} {b : β} :
    l.map f = replicate l.length b ↔ ∀ x ∈ l, f x = b := by simp [eq_replicate]
#align list.map_eq_replicate_iff List.map_eq_replicate_iff
-/

#print List.map_const /-
@[simp]
theorem map_const (l : List α) (b : β) : map (const α b) l = replicate l.length b :=
  map_eq_replicate_iff.mpr fun x _ => rfl
#align list.map_const List.map_const
-/

#print List.map_const' /-
-- Not a `simp` lemma because `function.const` is reducible in Lean 3
theorem map_const' (l : List α) (b : β) : map (fun _ => b) l = replicate l.length b :=
  map_const l b
#align list.map_const' List.map_const'
-/

#print List.eq_of_mem_map_const /-
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (const α b₂) l) : b₁ = b₂ := by
  rw [map_const] at h <;> exact eq_of_mem_replicate h
#align list.eq_of_mem_map_const List.eq_of_mem_map_const
-/

/-! ### map₂ -/


#print List.nil_zipWith /-
theorem nil_zipWith (f : α → β → γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl
#align list.nil_map₂ List.nil_zipWith
-/

#print List.zipWith_nil /-
theorem zipWith_nil (f : α → β → γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl
#align list.map₂_nil List.zipWith_nil
-/

#print List.zipWith_flip /-
@[simp]
theorem zipWith_flip (f : α → β → γ) : ∀ as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], b :: bs => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => by
    simp! [map₂_flip]
    rfl
#align list.map₂_flip List.zipWith_flip
-/

/-! ### take, drop -/


#print List.take_zero /-
@[simp]
theorem take_zero (l : List α) : take 0 l = [] :=
  rfl
#align list.take_zero List.take_zero
-/

#print List.take_nil /-
@[simp]
theorem take_nil : ∀ n, take n [] = ([] : List α)
  | 0 => rfl
  | n + 1 => rfl
#align list.take_nil List.take_nil
-/

#print List.take_cons /-
theorem take_cons (n) (a : α) (l : List α) : take (succ n) (a :: l) = a :: take n l :=
  rfl
#align list.take_cons List.take_cons
-/

#print List.take_length /-
@[simp]
theorem take_length : ∀ l : List α, take (length l) l = l
  | [] => rfl
  | a :: l => by change a :: take (length l) l = a :: l; rw [take_length]
#align list.take_length List.take_length
-/

#print List.take_all_of_le /-
theorem take_all_of_le : ∀ {n} {l : List α}, length l ≤ n → take n l = l
  | 0, [], h => rfl
  | 0, a :: l, h => absurd h (not_le_of_gt (zero_lt_succ _))
  | n + 1, [], h => rfl
  | n + 1, a :: l, h => by
    change a :: take n l = a :: l
    rw [take_all_of_le (le_of_succ_le_succ h)]
#align list.take_all_of_le List.take_all_of_le
-/

#print List.take_left /-
@[simp]
theorem take_left : ∀ l₁ l₂ : List α, take (length l₁) (l₁ ++ l₂) = l₁
  | [], l₂ => rfl
  | a :: l₁, l₂ => congr_arg (cons a) (take_left l₁ l₂)
#align list.take_left List.take_left
-/

#print List.take_left' /-
theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ := by
  rw [← h] <;> apply take_left
#align list.take_left' List.take_left'
-/

/- warning: list.take_take -> List.take_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : Nat) (m : Nat) (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.take.{u1} α n (List.take.{u1} α m l)) (List.take.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder n m) l)
but is expected to have type
  forall {α : Type.{u1}} (n : Nat) (m : Nat) (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.take.{u1} α n (List.take.{u1} α m l)) (List.take.{u1} α (Min.min.{0} Nat instMinNat n m) l)
Case conversion may be inaccurate. Consider using '#align list.take_take List.take_takeₓ'. -/
theorem take_take : ∀ (n m) (l : List α), take n (take m l) = take (min n m) l
  | n, 0, l => by rw [min_zero, take_zero, take_nil]
  | 0, m, l => by rw [zero_min, take_zero, take_zero]
  | succ n, succ m, nil => by simp only [take_nil]
  | succ n, succ m, a :: l => by
    simp only [take, min_succ_succ, take_take n m l] <;> constructor <;> rfl
#align list.take_take List.take_take

/- warning: list.take_replicate -> List.take_replicate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (n : Nat) (m : Nat), Eq.{succ u1} (List.{u1} α) (List.take.{u1} α n (List.replicate.{u1} α m a)) (List.replicate.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder n m) a)
but is expected to have type
  forall {α : Type.{u1}} (a : α) (n : Nat) (m : Nat), Eq.{succ u1} (List.{u1} α) (List.take.{u1} α n (List.replicate.{u1} α m a)) (List.replicate.{u1} α (Min.min.{0} Nat instMinNat n m) a)
Case conversion may be inaccurate. Consider using '#align list.take_replicate List.take_replicateₓ'. -/
theorem take_replicate (a : α) : ∀ n m : ℕ, take n (replicate m a) = replicate (min n m) a
  | n, 0 => by simp
  | 0, m => by simp
  | succ n, succ m => by simp [min_succ_succ, take_replicate]
#align list.take_replicate List.take_replicate

/- warning: list.map_take -> List.map_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (L : List.{u1} α) (i : Nat), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.take.{u1} α i L)) (List.take.{u2} β i (List.map.{u1, u2} α β f L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (L : List.{u2} α) (i : Nat), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (List.take.{u2} α i L)) (List.take.{u1} β i (List.map.{u2, u1} α β f L))
Case conversion may be inaccurate. Consider using '#align list.map_take List.map_takeₓ'. -/
theorem map_take {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.take i).map f = (L.map f).take i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_take]
#align list.map_take List.map_take

#print List.take_append_eq_append_take /-
/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : ℕ} :
    take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ :=
  by
  induction l₁ generalizing n; · simp
  cases n; · simp; simp [*]
#align list.take_append_eq_append_take List.take_append_eq_append_take
-/

#print List.take_append_of_le_length /-
theorem take_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).take n = l₁.take n := by simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]
#align list.take_append_of_le_length List.take_append_of_le_length
-/

#print List.take_append /-
/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : ℕ) : take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ take i l₂ :=
  by simp [take_append_eq_append_take, take_all_of_le le_self_add]
#align list.take_append List.take_append
-/

#print List.nthLe_take /-
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem nthLe_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
    nthLe L i hi =
      nthLe (L.take j) i
        (by
          rw [length_take]
          exact lt_min hj hi) :=
  by
  rw [nth_le_of_eq (take_append_drop j L).symm hi]
  exact nth_le_append _ _
#align list.nth_le_take List.nthLe_take
-/

#print List.nthLe_take' /-
/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem nthLe_take' (L : List α) {i j : ℕ} (hi : i < (L.take j).length) :
    nthLe (L.take j) i hi = nthLe L i (lt_of_lt_of_le hi (by simp [le_refl])) :=
  by
  simp at hi
  rw [nth_le_take L _ hi.1]
#align list.nth_le_take' List.nthLe_take'
-/

#print List.get?_take /-
theorem get?_take {l : List α} {n m : ℕ} (h : m < n) : (l.take n).nth m = l.nth m :=
  by
  induction' n with n hn generalizing l m
  · simp only [Nat.zero_eq] at h
    exact absurd h (not_lt_of_le m.zero_le)
  · cases' l with hd tl
    · simp only [take_nil]
    · cases m
      · simp only [nth, take]
      · simpa only using hn (Nat.lt_of_succ_lt_succ h)
#align list.nth_take List.get?_take
-/

#print List.nth_take_of_succ /-
@[simp]
theorem nth_take_of_succ {l : List α} {n : ℕ} : (l.take (n + 1)).nth n = l.nth n :=
  get?_take (Nat.lt_succ_self n)
#align list.nth_take_of_succ List.nth_take_of_succ
-/

#print List.take_succ /-
theorem take_succ {l : List α} {n : ℕ} : l.take (n + 1) = l.take n ++ (l.nth n).toList :=
  by
  induction' l with hd tl hl generalizing n
  · simp only [Option.toList, nth, take_nil, append_nil]
  · cases n
    · simp only [Option.toList, nth, eq_self_iff_true, and_self_iff, take, nil_append]
    · simp only [hl, cons_append, nth, eq_self_iff_true, and_self_iff, take]
#align list.take_succ List.take_succ
-/

#print List.take_eq_nil_iff /-
@[simp]
theorem take_eq_nil_iff {l : List α} {k : ℕ} : l.take k = [] ↔ l = [] ∨ k = 0 := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]
#align list.take_eq_nil_iff List.take_eq_nil_iff
-/

/- warning: list.take_eq_take -> List.take_eq_take is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {m : Nat} {n : Nat}, Iff (Eq.{succ u1} (List.{u1} α) (List.take.{u1} α m l) (List.take.{u1} α n l)) (Eq.{1} Nat (LinearOrder.min.{0} Nat Nat.linearOrder m (List.length.{u1} α l)) (LinearOrder.min.{0} Nat Nat.linearOrder n (List.length.{u1} α l)))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {m : Nat} {n : Nat}, Iff (Eq.{succ u1} (List.{u1} α) (List.take.{u1} α m l) (List.take.{u1} α n l)) (Eq.{1} Nat (Min.min.{0} Nat instMinNat m (List.length.{u1} α l)) (Min.min.{0} Nat instMinNat n (List.length.{u1} α l)))
Case conversion may be inaccurate. Consider using '#align list.take_eq_take List.take_eq_takeₓ'. -/
theorem take_eq_take :
    ∀ {l : List α} {m n : ℕ}, l.take m = l.take n ↔ min m l.length = min n l.length
  | [], m, n => by simp
  | x :: xs, 0, 0 => by simp
  | x :: xs, m + 1, 0 => by simp
  | x :: xs, 0, n + 1 => by simp [@eq_comm ℕ 0]
  | x :: xs, m + 1, n + 1 => by simp [Nat.min_succ_succ, take_eq_take]
#align list.take_eq_take List.take_eq_take

#print List.take_add /-
theorem take_add (l : List α) (m n : ℕ) : l.take (m + n) = l.take m ++ (l.drop m).take n :=
  by
  convert_to take (m + n) (take m l ++ drop m l) = take m l ++ take n (drop m l)
  · rw [take_append_drop]
  rw [take_append_eq_append_take, take_all_of_le, append_right_inj]; swap
  · trans m
    · apply length_take_le
    · simp
  simp only [take_eq_take, length_take, length_drop]
  generalize l.length = k; by_cases h : m ≤ k
  · simp [min_eq_left_iff.mpr h]
  · push_neg  at h
    simp [Nat.sub_eq_zero_of_le (le_of_lt h)]
#align list.take_add List.take_add
-/

#print List.dropLast_eq_take /-
theorem dropLast_eq_take (l : List α) : l.init = l.take l.length.pred :=
  by
  cases' l with x l
  · simp [init]
  · induction' l with hd tl hl generalizing x
    · simp [init]
    · simp [init, hl]
#align list.init_eq_take List.dropLast_eq_take
-/

#print List.dropLast_take /-
theorem dropLast_take {n : ℕ} {l : List α} (h : n < l.length) : (l.take n).init = l.take n.pred :=
  by simp [init_eq_take, min_eq_left_of_lt h, take_take, pred_le]
#align list.init_take List.dropLast_take
-/

#print List.dropLast_cons_of_ne_nil /-
@[simp]
theorem dropLast_cons_of_ne_nil {α : Type _} {x : α} :
    ∀ {l : List α} (h : l ≠ []), (x :: l).init = x :: l.init
  | [], h => False.elim (h rfl)
  | a :: l, _ => by simp [init]
#align list.init_cons_of_ne_nil List.dropLast_cons_of_ne_nil
-/

#print List.dropLast_append_of_ne_nil /-
@[simp]
theorem dropLast_append_of_ne_nil {α : Type _} {l : List α} :
    ∀ (l' : List α) (h : l ≠ []), (l' ++ l).init = l' ++ l.init
  | [], _ => by simp only [nil_append]
  | a :: l', h => by simp [append_ne_nil_of_ne_nil_right l' l h, init_append_of_ne_nil l' h]
#align list.init_append_of_ne_nil List.dropLast_append_of_ne_nil
-/

#print List.drop_eq_nil_of_le /-
@[simp]
theorem drop_eq_nil_of_le {l : List α} {k : ℕ} (h : l.length ≤ k) : l.drop k = [] := by
  simpa [← length_eq_zero] using tsub_eq_zero_iff_le.mpr h
#align list.drop_eq_nil_of_le List.drop_eq_nil_of_le
-/

#print List.drop_eq_nil_iff_le /-
theorem drop_eq_nil_iff_le {l : List α} {k : ℕ} : l.drop k = [] ↔ l.length ≤ k :=
  by
  refine' ⟨fun h => _, drop_eq_nil_of_le⟩
  induction' k with k hk generalizing l
  · simp only [drop] at h
    simp [h]
  · cases l
    · simp
    · simp only [drop] at h
      simpa [Nat.succ_le_succ_iff] using hk h
#align list.drop_eq_nil_iff_le List.drop_eq_nil_iff_le
-/

#print List.tail_drop /-
theorem tail_drop (l : List α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) :=
  by
  induction' l with hd tl hl generalizing n
  · simp
  · cases n
    · simp
    · simp [hl]
#align list.tail_drop List.tail_drop
-/

#print List.cons_nthLe_drop_succ /-
theorem cons_nthLe_drop_succ {l : List α} {n : ℕ} (hn : n < l.length) :
    l.nthLe n hn :: l.drop (n + 1) = l.drop n :=
  by
  induction' l with hd tl hl generalizing n
  · exact absurd n.zero_le (not_le_of_lt (by simpa using hn))
  · cases n
    · simp
    · simp only [Nat.succ_lt_succ_iff, List.length] at hn
      simpa [List.nthLe, List.drop] using hl hn
#align list.cons_nth_le_drop_succ List.cons_nthLe_drop_succ
-/

#print List.drop_nil /-
theorem drop_nil : ∀ n, drop n [] = ([] : List α) := fun _ => drop_eq_nil_of_le (Nat.zero_le _)
#align list.drop_nil List.drop_nil
-/

#print List.drop_one /-
@[simp]
theorem drop_one : ∀ l : List α, drop 1 l = tail l
  | [] => rfl
  | a :: l => rfl
#align list.drop_one List.drop_one
-/

#print List.drop_add /-
theorem drop_add : ∀ (m n) (l : List α), drop (m + n) l = drop m (drop n l)
  | m, 0, l => rfl
  | m, n + 1, [] => (drop_nil _).symm
  | m, n + 1, a :: l => drop_add m n _
#align list.drop_add List.drop_add
-/

#print List.drop_left /-
@[simp]
theorem drop_left : ∀ l₁ l₂ : List α, drop (length l₁) (l₁ ++ l₂) = l₂
  | [], l₂ => rfl
  | a :: l₁, l₂ => drop_left l₁ l₂
#align list.drop_left List.drop_left
-/

#print List.drop_left' /-
theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ := by
  rw [← h] <;> apply drop_left
#align list.drop_left' List.drop_left'
-/

theorem drop_eq_get_cons : ∀ {n} {l : List α} (h), drop n l = nthLe l n h :: drop (n + 1) l
  | 0, a :: l, h => rfl
  | n + 1, a :: l, h => @drop_eq_nth_le_cons n _ _
#align list.drop_eq_nth_le_cons List.drop_eq_get_consₓ

#print List.drop_length /-
@[simp]
theorem drop_length (l : List α) : l.drop l.length = [] :=
  calc
    l.drop l.length = (l ++ []).drop l.length := by simp
    _ = [] := drop_left _ _
    
#align list.drop_length List.drop_length
-/

#print List.drop_length_cons /-
theorem drop_length_cons {l : List α} (h : l ≠ []) (a : α) : (a :: l).drop l.length = [l.last h] :=
  by
  induction' l with y l ih generalizing a
  · cases h rfl
  · simp only [drop, length]
    by_cases h₁ : l = []
    · simp [h₁]
    rw [last_cons h₁]
    exact ih h₁ y
#align list.drop_length_cons List.drop_length_cons
-/

#print List.drop_append_eq_append_drop /-
/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : ℕ} :
    drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ :=
  by
  induction l₁ generalizing n; · simp
  cases n; · simp; simp [*]
#align list.drop_append_eq_append_drop List.drop_append_eq_append_drop
-/

#print List.drop_append_of_le_length /-
theorem drop_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) :
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]
#align list.drop_append_of_le_length List.drop_append_of_le_length
-/

#print List.drop_append /-
/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {l₁ l₂ : List α} (i : ℕ) : drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ := by
  simp [drop_append_eq_append_drop, take_all_of_le le_self_add]
#align list.drop_append List.drop_append
-/

/- warning: list.drop_sizeof_le -> List.drop_sizeOf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] (l : List.{u1} α) (n : Nat), LE.le.{0} Nat Nat.hasLe (List.sizeof.{u1} α _inst_1 (List.drop.{u1} α n l)) (List.sizeof.{u1} α _inst_1 l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] (l : List.{u1} α) (n : Nat), LE.le.{0} Nat instLENat (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List._sizeOf_inst.{u1} α _inst_1) (List.drop.{u1} α n l)) (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List._sizeOf_inst.{u1} α _inst_1) l)
Case conversion may be inaccurate. Consider using '#align list.drop_sizeof_le List.drop_sizeOf_leₓ'. -/
theorem drop_sizeOf_le [SizeOf α] (l : List α) : ∀ n : ℕ, (l.drop n).sizeof ≤ l.sizeof :=
  by
  induction' l with _ _ lih <;> intro n
  · rw [drop_nil]
  · induction' n with n nih
    · rfl
    · exact trans (lih _) le_add_self
#align list.drop_sizeof_le List.drop_sizeOf_le

#print List.nthLe_drop /-
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem nthLe_drop (L : List α) {i j : ℕ} (h : i + j < L.length) :
    nthLe L (i + j) h =
      nthLe (L.drop i) j
        (by
          have A : i < L.length := lt_of_le_of_lt (Nat.le.intro rfl) h
          rw [(take_append_drop i L).symm] at h
          simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take,
            length_append] using h) :=
  by
  have A : length (take i L) = i := by simp [le_of_lt (lt_of_le_of_lt (Nat.le.intro rfl) h)]
  rw [nth_le_of_eq (take_append_drop i L).symm h, nth_le_append_right] <;> simp [A]
#align list.nth_le_drop List.nthLe_drop
-/

/- warning: list.nth_le_drop' -> List.nthLe_drop' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (L : List.{u1} α) {i : Nat} {j : Nat} (h : LT.lt.{0} Nat Nat.hasLt j (List.length.{u1} α (List.drop.{u1} α i L))), Eq.{succ u1} α (List.nthLe.{u1} α (List.drop.{u1} α i L) j h) (List.nthLe.{u1} α L (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i j) (Iff.mp (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder))))) j (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (List.length.{u1} α L) i)) (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat (AddCommSemigroup.toAddSemigroup.{0} Nat Nat.addCommSemigroup))) i j) (List.length.{u1} α L)) (lt_tsub_iff_left.{0} Nat j (List.length.{u1} α L) i Nat.linearOrder Nat.addCommSemigroup Nat.hasSub Nat.hasOrderedSub) (Eq.subst.{1} Nat (fun (_x : Nat) => LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder))))) j _x) (List.length.{u1} α (List.drop.{u1} α i L)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (List.length.{u1} α L) i) (List.length_drop.{u1} α i L) h)))
but is expected to have type
  forall {α : Type.{u1}} (L : List.{u1} α) {i : Nat} {j : Nat} (h : LT.lt.{0} Nat instLTNat j (List.length.{u1} α (List.drop.{u1} α i L))), Eq.{succ u1} α (List.nthLe.{u1} α (List.drop.{u1} α i L) j h) (List.nthLe.{u1} α L (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i j) (Iff.mp (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat (instDistribLattice.{0} Nat Nat.linearOrder)))))) j (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (List.length.{u1} α L) i)) (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat (instDistribLattice.{0} Nat Nat.linearOrder)))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat (AddCommSemigroup.toAddSemigroup.{0} Nat Nat.addCommSemigroup))) i j) (List.length.{u1} α L)) (lt_tsub_iff_left.{0} Nat j (List.length.{u1} α L) i Nat.linearOrder Nat.addCommSemigroup instSubNat Nat.instOrderedSubNatInstLENatInstAddNatInstSubNat) (Eq.rec.{0, 1} Nat (List.length.{u1} α (List.drop.{u1} α i L)) (fun (x._@.Mathlib.Data.List.Basic._hyg.25582 : Nat) (h._@.Mathlib.Data.List.Basic._hyg.25583 : Eq.{1} Nat (List.length.{u1} α (List.drop.{u1} α i L)) x._@.Mathlib.Data.List.Basic._hyg.25582) => LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat (instDistribLattice.{0} Nat Nat.linearOrder)))))) j x._@.Mathlib.Data.List.Basic._hyg.25582) h (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (List.length.{u1} α L) i) (List.length_drop.{u1} α i L))))
Case conversion may be inaccurate. Consider using '#align list.nth_le_drop' List.nthLe_drop'ₓ'. -/
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem nthLe_drop' (L : List α) {i j : ℕ} (h : j < (L.drop i).length) :
    nthLe (L.drop i) j h = nthLe L (i + j) (lt_tsub_iff_left.mp (length_drop i L ▸ h)) := by
  rw [nth_le_drop]
#align list.nth_le_drop' List.nthLe_drop'

#print List.get?_drop /-
theorem get?_drop (L : List α) (i j : ℕ) : get? (L.drop i) j = get? L (i + j) :=
  by
  ext
  simp only [nth_eq_some, nth_le_drop', Option.mem_def]
  constructor <;> exact fun ⟨h, ha⟩ => ⟨by simpa [lt_tsub_iff_left] using h, ha⟩
#align list.nth_drop List.get?_drop
-/

#print List.drop_drop /-
@[simp]
theorem drop_drop (n : ℕ) : ∀ (m) (l : List α), drop n (drop m l) = drop (n + m) l
  | m, [] => by simp
  | 0, l => by simp
  | m + 1, a :: l =>
    calc
      drop n (drop (m + 1) (a :: l)) = drop n (drop m l) := rfl
      _ = drop (n + m) l := drop_drop m l
      _ = drop (n + (m + 1)) (a :: l) := rfl
      
#align list.drop_drop List.drop_drop
-/

#print List.drop_take /-
theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : List α), drop m (take (m + n) l) = take n (drop m l)
  | 0, n, _ => by simp
  | m + 1, n, nil => by simp
  | m + 1, n, _ :: l => by
    have h : m + 1 + n = m + n + 1 := by ac_rfl
    simpa [take_cons, h] using drop_take m n l
#align list.drop_take List.drop_take
-/

/- warning: list.map_drop -> List.map_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (L : List.{u1} α) (i : Nat), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.drop.{u1} α i L)) (List.drop.{u2} β i (List.map.{u1, u2} α β f L))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (L : List.{u2} α) (i : Nat), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β f (List.drop.{u2} α i L)) (List.drop.{u1} β i (List.map.{u2, u1} α β f L))
Case conversion may be inaccurate. Consider using '#align list.map_drop List.map_dropₓ'. -/
theorem map_drop {α β : Type _} (f : α → β) :
    ∀ (L : List α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
  | [], i => by simp
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [map_drop]
#align list.map_drop List.map_drop

#print List.modifyNthTail_eq_take_drop /-
theorem modifyNthTail_eq_take_drop (f : List α → List α) (H : f [] = []) :
    ∀ n l, modifyNthTail f n l = take n l ++ f (drop n l)
  | 0, l => rfl
  | n + 1, [] => H.symm
  | n + 1, b :: l => congr_arg (cons b) (modify_nth_tail_eq_take_drop n l)
#align list.modify_nth_tail_eq_take_drop List.modifyNthTail_eq_take_drop
-/

#print List.modifyNth_eq_take_drop /-
theorem modifyNth_eq_take_drop (f : α → α) :
    ∀ n l, modifyNth f n l = take n l ++ modifyHead f (drop n l) :=
  modifyNthTail_eq_take_drop _ rfl
#align list.modify_nth_eq_take_drop List.modifyNth_eq_take_drop
-/

#print List.modifyNth_eq_take_cons_drop /-
theorem modifyNth_eq_take_cons_drop (f : α → α) {n l} (h) :
    modifyNth f n l = take n l ++ f (nthLe l n h) :: drop (n + 1) l := by
  rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h] <;> rfl
#align list.modify_nth_eq_take_cons_drop List.modifyNth_eq_take_cons_drop
-/

#print List.set_eq_take_cons_drop /-
theorem set_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
    set l n a = take n l ++ a :: drop (n + 1) l := by
  rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]
#align list.update_nth_eq_take_cons_drop List.set_eq_take_cons_drop
-/

#print List.reverse_take /-
theorem reverse_take {α} {xs : List α} (n : ℕ) (h : n ≤ xs.length) :
    xs.reverse.take n = (xs.drop (xs.length - n)).reverse :=
  by
  induction xs generalizing n <;>
    simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil]
  cases' h.lt_or_eq_dec with h' h'
  · replace h' := le_of_succ_le_succ h'
    rwa [take_append_of_le_length, xs_ih _ h']
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n) from _, drop]
    · rwa [succ_eq_add_one, ← tsub_add_eq_add_tsub]
    · rwa [length_reverse]
  · subst h'
    rw [length, tsub_self, drop]
    suffices xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length by
      rw [this, take_length, reverse_cons]
    rw [length_append, length_reverse]
    rfl
#align list.reverse_take List.reverse_take
-/

#print List.set_eq_nil /-
@[simp]
theorem set_eq_nil (l : List α) (n : ℕ) (a : α) : l.updateNth n a = [] ↔ l = [] := by
  cases l <;> cases n <;> simp only [update_nth]
#align list.update_nth_eq_nil List.set_eq_nil
-/

section Take'

variable [Inhabited α]

#print List.takeI_length /-
@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, l => rfl
  | n + 1, l => congr_arg succ (take'_length _ _)
#align list.take'_length List.takeI_length
-/

#print List.takeI_nil /-
@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | n + 1 => congr_arg (cons _) (take'_nil _)
#align list.take'_nil List.takeI_nil
-/

#print List.takeI_eq_take /-
theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, l, h => rfl
  | n + 1, a :: l, h => congr_arg (cons _) <| take'_eq_take <| le_of_succ_le_succ h
#align list.take'_eq_take List.takeI_eq_take
-/

#print List.takeI_left /-
@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)
#align list.take'_left List.takeI_left
-/

#print List.takeI_left' /-
theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h] <;> apply take'_left
#align list.take'_left' List.takeI_left'
-/

end Take'

/-! ### foldl, foldr -/


#print List.foldl_ext /-
theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l :=
  by
  induction' l with hd tl ih generalizing a; · rfl
  unfold foldl
  rw [ih fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]
#align list.foldl_ext List.foldl_ext
-/

#print List.foldr_ext /-
theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction' l with hd tl ih; · rfl
  simp only [mem_cons_iff, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]
#align list.foldr_ext List.foldr_ext
-/

#print List.foldl_nil /-
@[simp]
theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a :=
  rfl
#align list.foldl_nil List.foldl_nil
-/

#print List.foldl_cons /-
@[simp]
theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) :
    foldl f a (b :: l) = foldl f (f a b) l :=
  rfl
#align list.foldl_cons List.foldl_cons
-/

#print List.foldr_nil /-
@[simp]
theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b :=
  rfl
#align list.foldr_nil List.foldr_nil
-/

#print List.foldr_cons /-
@[simp]
theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    foldr f b (a :: l) = f a (foldr f b l) :=
  rfl
#align list.foldr_cons List.foldr_cons
-/

/- warning: list.foldl_append -> List.foldl_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> α) (a : α) (l₁ : List.{u2} β) (l₂ : List.{u2} β), Eq.{succ u1} α (List.foldl.{u1, u2} α β f a (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) l₁ l₂)) (List.foldl.{u1, u2} α β f (List.foldl.{u1, u2} α β f a l₁) l₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (a : β) (l₁ : List.{u2} α) (l₂ : List.{u2} α), Eq.{succ u1} β (List.foldl.{u1, u2} β α f a (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) (List.foldl.{u1, u2} β α f (List.foldl.{u1, u2} β α f a l₁) l₂)
Case conversion may be inaccurate. Consider using '#align list.foldl_append List.foldl_appendₓ'. -/
@[simp]
theorem foldl_append (f : α → β → α) :
    ∀ (a : α) (l₁ l₂ : List β), foldl f a (l₁ ++ l₂) = foldl f (foldl f a l₁) l₂
  | a, [], l₂ => rfl
  | a, b :: l₁, l₂ => by simp only [cons_append, foldl_cons, foldl_append (f a b) l₁ l₂]
#align list.foldl_append List.foldl_append

/- warning: list.foldr_append -> List.foldr_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (b : β) (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u2} β (List.foldr.{u1, u2} α β f b (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (List.foldr.{u1, u2} α β f (List.foldr.{u1, u2} α β f b l₂) l₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (b : β) (l₁ : List.{u2} α) (l₂ : List.{u2} α), Eq.{succ u1} β (List.foldr.{u2, u1} α β f b (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) (List.foldr.{u2, u1} α β f (List.foldr.{u2, u1} α β f b l₂) l₁)
Case conversion may be inaccurate. Consider using '#align list.foldr_append List.foldr_appendₓ'. -/
@[simp]
theorem foldr_append (f : α → β → β) :
    ∀ (b : β) (l₁ l₂ : List α), foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁
  | b, [], l₂ => rfl
  | b, a :: l₁, l₂ => by simp only [cons_append, foldr_cons, foldr_append b l₁ l₂]
#align list.foldr_append List.foldr_append

#print List.foldl_fixed' /-
theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' l]
#align list.foldl_fixed' List.foldl_fixed'
-/

#print List.foldr_fixed' /-
theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' l, hf a]
#align list.foldr_fixed' List.foldr_fixed'
-/

#print List.foldl_fixed /-
@[simp]
theorem foldl_fixed {a : α} : ∀ l : List β, foldl (fun a b => a) a l = a :=
  foldl_fixed' fun _ => rfl
#align list.foldl_fixed List.foldl_fixed
-/

#print List.foldr_fixed /-
@[simp]
theorem foldr_fixed {b : β} : ∀ l : List α, foldr (fun a b => b) b l = b :=
  foldr_fixed' fun _ => rfl
#align list.foldr_fixed List.foldr_fixed
-/

#print List.foldl_join /-
@[simp]
theorem foldl_join (f : α → β → α) :
    ∀ (a : α) (L : List (List β)), foldl f a (join L) = foldl (foldl f) a L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldl_append, foldl_cons, foldl_join (foldl f a l) L]
#align list.foldl_join List.foldl_join
-/

#print List.foldr_join /-
@[simp]
theorem foldr_join (f : α → β → β) :
    ∀ (b : β) (L : List (List α)), foldr f b (join L) = foldr (fun l b => foldr f b l) b L
  | a, [] => rfl
  | a, l :: L => by simp only [join, foldr_append, foldr_join a L, foldr_cons]
#align list.foldr_join List.foldr_join
-/

/- warning: list.foldl_reverse -> List.foldl_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> α) (a : α) (l : List.{u2} β), Eq.{succ u1} α (List.foldl.{u1, u2} α β f a (List.reverse.{u2} β l)) (List.foldr.{u2, u1} β α (fun (x : β) (y : α) => f y x) a l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : List.{u2} α) (a : β -> α -> β) (l : β), Eq.{succ u1} β (List.foldl.{u1, u2} β α a l (List.reverse.{u2} α f)) (List.foldr.{u2, u1} α β (fun (x : α) (y : β) => a y x) l f)
Case conversion may be inaccurate. Consider using '#align list.foldl_reverse List.foldl_reverseₓ'. -/
theorem foldl_reverse (f : α → β → α) (a : α) (l : List β) :
    foldl f a (reverse l) = foldr (fun x y => f y x) a l := by
  induction l <;> [rfl, simp only [*, reverse_cons, foldl_append, foldl_cons, foldl_nil, foldr]]
#align list.foldl_reverse List.foldl_reverse

/- warning: list.foldr_reverse -> List.foldr_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (a : β) (l : List.{u1} α), Eq.{succ u2} β (List.foldr.{u1, u2} α β f a (List.reverse.{u1} α l)) (List.foldl.{u2, u1} β α (fun (x : β) (y : α) => f y x) a l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : List.{u2} α) (a : α -> β -> β) (l : β), Eq.{succ u1} β (List.foldr.{u2, u1} α β a l (List.reverse.{u2} α f)) (List.foldl.{u1, u2} β α (fun (x : β) (y : α) => a y x) l f)
Case conversion may be inaccurate. Consider using '#align list.foldr_reverse List.foldr_reverseₓ'. -/
theorem foldr_reverse (f : α → β → β) (a : β) (l : List α) :
    foldr f a (reverse l) = foldl (fun x y => f y x) a l :=
  by
  let t := foldl_reverse (fun x y => f y x) a (reverse l)
  rw [reverse_reverse l] at t <;> rwa [t]
#align list.foldr_reverse List.foldr_reverse

#print List.foldr_eta /-
@[simp]
theorem foldr_eta : ∀ l : List α, foldr cons [] l = l
  | [] => rfl
  | x :: l => by simp only [foldr_cons, foldr_eta l] <;> constructor <;> rfl
#align list.foldr_eta List.foldr_eta
-/

#print List.reverse_foldl /-
@[simp]
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  rw [← foldr_reverse] <;> simp
#align list.reverse_foldl List.reverse_foldl
-/

/- warning: list.foldl_map -> List.foldl_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> γ -> α) (a : α) (l : List.{u2} β), Eq.{succ u1} α (List.foldl.{u1, u3} α γ f a (List.map.{u2, u3} β γ g l)) (List.foldl.{u1, u2} α β (fun (x : α) (y : β) => f x (g y)) a l)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (g : α -> β) (f : γ -> β -> γ) (a : List.{u3} α) (l : γ), Eq.{succ u1} γ (List.foldl.{u1, u2} γ β f l (List.map.{u3, u2} α β g a)) (List.foldl.{u1, u3} γ α (fun (x : γ) (y : α) => f x (g y)) l a)
Case conversion may be inaccurate. Consider using '#align list.foldl_map List.foldl_mapₓ'. -/
@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : List β) :
    foldl f a (map g l) = foldl (fun x y => f x (g y)) a l := by
  revert a <;> induction l <;> intros <;> [rfl, simp only [*, map, foldl]]
#align list.foldl_map List.foldl_map

/- warning: list.foldr_map -> List.foldr_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : γ -> α -> α) (a : α) (l : List.{u2} β), Eq.{succ u1} α (List.foldr.{u3, u1} γ α f a (List.map.{u2, u3} β γ g l)) (List.foldr.{u2, u1} β α (Function.comp.{succ u2, succ u3, succ u1} β γ (α -> α) f g) a l)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (g : α -> β) (f : β -> γ -> γ) (a : List.{u3} α) (l : γ), Eq.{succ u1} γ (List.foldr.{u2, u1} β γ f l (List.map.{u3, u2} α β g a)) (List.foldr.{u3, u1} α γ (fun (x : α) (y : γ) => f (g x) y) l a)
Case conversion may be inaccurate. Consider using '#align list.foldr_map List.foldr_mapₓ'. -/
@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : List β) :
    foldr f a (map g l) = foldr (f ∘ g) a l := by
  revert a <;> induction l <;> intros <;> [rfl, simp only [*, map, foldr]]
#align list.foldr_map List.foldr_map

#print List.foldl_map' /-
theorem foldl_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldl f' (g a) (l.map g) = g (List.foldl f a l) :=
  by
  induction l generalizing a
  · simp; · simp [l_ih, h]
#align list.foldl_map' List.foldl_map'
-/

#print List.foldr_map' /-
theorem foldr_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
    (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
    List.foldr f' (g a) (l.map g) = g (List.foldr f a l) :=
  by
  induction l generalizing a
  · simp; · simp [l_ih, h]
#align list.foldr_map' List.foldr_map'
-/

/- warning: list.foldl_hom -> List.foldl_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (l : List.{u3} γ) (f : α -> β) (op : α -> γ -> α) (op' : β -> γ -> β) (a : α), (forall (a : α) (x : γ), Eq.{succ u2} β (f (op a x)) (op' (f a) x)) -> (Eq.{succ u2} β (List.foldl.{u2, u3} β γ op' (f a) l) (f (List.foldl.{u1, u3} α γ op a l)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (l : α -> β) (f : α -> γ -> α) (op : β -> γ -> β) (op' : List.{u1} γ) (a : α), (forall (a : α) (x : γ), Eq.{succ u2} β (op (l a) x) (l (f a x))) -> (Eq.{succ u2} β (List.foldl.{u2, u1} β γ op (l a) op') (l (List.foldl.{u3, u1} α γ f a op')))
Case conversion may be inaccurate. Consider using '#align list.foldl_hom List.foldl_homₓ'. -/
theorem foldl_hom (l : List γ) (f : α → β) (op : α → γ → α) (op' : β → γ → β) (a : α)
    (h : ∀ a x, f (op a x) = op' (f a) x) : foldl op' (f a) l = f (foldl op a l) :=
  Eq.symm <| by
    revert a
    induction l <;> intros <;> [rfl, simp only [*, foldl]]
#align list.foldl_hom List.foldl_hom

/- warning: list.foldr_hom -> List.foldr_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (l : List.{u3} γ) (f : α -> β) (op : γ -> α -> α) (op' : γ -> β -> β) (a : α), (forall (x : γ) (a : α), Eq.{succ u2} β (f (op x a)) (op' x (f a))) -> (Eq.{succ u2} β (List.foldr.{u3, u2} γ β op' (f a) l) (f (List.foldr.{u3, u1} γ α op a l)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (l : α -> β) (f : γ -> α -> α) (op : γ -> β -> β) (op' : List.{u1} γ) (a : α), (forall (x : γ) (a : α), Eq.{succ u2} β (op x (l a)) (l (f x a))) -> (Eq.{succ u2} β (List.foldr.{u1, u2} γ β op (l a) op') (l (List.foldr.{u1, u3} γ α f a op')))
Case conversion may be inaccurate. Consider using '#align list.foldr_hom List.foldr_homₓ'. -/
theorem foldr_hom (l : List γ) (f : α → β) (op : γ → α → α) (op' : γ → β → β) (a : α)
    (h : ∀ x a, f (op x a) = op' x (f a)) : foldr op' (f a) l = f (foldr op a l) :=
  by
  revert a
  induction l <;> intros <;> [rfl, simp only [*, foldr]]
#align list.foldr_hom List.foldr_hom

/- warning: list.foldl_hom₂ -> List.foldl_hom₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (l : List.{u4} ι) (f : α -> β -> γ) (op₁ : α -> ι -> α) (op₂ : β -> ι -> β) (op₃ : γ -> ι -> γ) (a : α) (b : β), (forall (a : α) (b : β) (i : ι), Eq.{succ u3} γ (f (op₁ a i) (op₂ b i)) (op₃ (f a b) i)) -> (Eq.{succ u3} γ (List.foldl.{u3, u4} γ ι op₃ (f a b) l) (f (List.foldl.{u1, u4} α ι op₁ a l) (List.foldl.{u2, u4} β ι op₂ b l)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} (l : List.{u1} ι) (f : α -> β -> γ) (op₁ : α -> ι -> α) (op₂ : β -> ι -> β) (op₃ : γ -> ι -> γ) (a : α) (b : β), (forall (a : α) (b : β) (i : ι), Eq.{succ u4} γ (f (op₁ a i) (op₂ b i)) (op₃ (f a b) i)) -> (Eq.{succ u4} γ (List.foldl.{u4, u1} γ ι op₃ (f a b) l) (f (List.foldl.{u2, u1} α ι op₁ a l) (List.foldl.{u3, u1} β ι op₂ b l)))
Case conversion may be inaccurate. Consider using '#align list.foldl_hom₂ List.foldl_hom₂ₓ'. -/
theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    induction l <;> intros <;> [rfl, simp only [*, foldl]]
#align list.foldl_hom₂ List.foldl_hom₂

/- warning: list.foldr_hom₂ -> List.foldr_hom₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u4}} {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (l : List.{u4} ι) (f : α -> β -> γ) (op₁ : ι -> α -> α) (op₂ : ι -> β -> β) (op₃ : ι -> γ -> γ) (a : α) (b : β), (forall (a : α) (b : β) (i : ι), Eq.{succ u3} γ (f (op₁ i a) (op₂ i b)) (op₃ i (f a b))) -> (Eq.{succ u3} γ (List.foldr.{u4, u3} ι γ op₃ (f a b) l) (f (List.foldr.{u4, u1} ι α op₁ a l) (List.foldr.{u4, u2} ι β op₂ b l)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} (l : List.{u1} ι) (f : α -> β -> γ) (op₁ : ι -> α -> α) (op₂ : ι -> β -> β) (op₃ : ι -> γ -> γ) (a : α) (b : β), (forall (a : α) (b : β) (i : ι), Eq.{succ u4} γ (f (op₁ i a) (op₂ i b)) (op₃ i (f a b))) -> (Eq.{succ u4} γ (List.foldr.{u1, u4} ι γ op₃ (f a b) l) (f (List.foldr.{u1, u2} ι α op₁ a l) (List.foldr.{u1, u3} ι β op₂ b l)))
Case conversion may be inaccurate. Consider using '#align list.foldr_hom₂ List.foldr_hom₂ₓ'. -/
theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) :=
  by
  revert a
  induction l <;> intros <;> [rfl, simp only [*, foldr]]
#align list.foldr_hom₂ List.foldr_hom₂

#print List.injective_foldl_comp /-
theorem injective_foldl_comp {α : Type _} {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) :=
  by
  induction l generalizing f
  · exact hf
  · apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ (List.mem_cons_self _ _)
#align list.injective_foldl_comp List.injective_foldl_comp
-/

#print List.foldrRecOn /-
/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldrRecOn {C : β → Sort _} (l : List α) (op : α → β → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op a b)) : C (foldr op b l) :=
  by
  induction' l with hd tl IH
  · exact hb
  · refine' hl _ _ hd (mem_cons_self hd tl)
    refine' IH _
    intro y hy x hx
    exact hl y hy x (mem_cons_of_mem hd hx)
#align list.foldr_rec_on List.foldrRecOn
-/

#print List.foldlRecOn /-
/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldlRecOn {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op b a)) : C (foldl op b l) :=
  by
  induction' l with hd tl IH generalizing b
  · exact hb
  · refine' IH _ _ _
    · intro y hy x hx
      exact hl y hy x (mem_cons_of_mem hd hx)
    · exact hl b hb hd (mem_cons_self hd tl)
#align list.foldl_rec_on List.foldlRecOn
-/

/- warning: list.foldr_rec_on_nil -> List.foldrRecOn_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Sort.{u3}} (op : α -> β -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.nil.{u1} α)) -> (C (op a b)))), Eq.{u3} (C (List.foldr.{u1, u2} α β op b (List.nil.{u1} α))) (List.foldrRecOn.{u1, u2, u3} α β (fun (b : β) => C b) (List.nil.{u1} α) op b hb hl) hb
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {C : β -> Sort.{u1}} (op : α -> β -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (List.nil.{u2} α)) -> (C (op a b)))), Eq.{u1} (C (List.foldr.{u2, u3} α β op b (List.nil.{u2} α))) (List.foldrRecOn.{u2, u3, u1} α β C (List.nil.{u2} α) op b hb hl) hb
Case conversion may be inaccurate. Consider using '#align list.foldr_rec_on_nil List.foldrRecOn_nilₓ'. -/
@[simp]
theorem foldrRecOn_nil {C : β → Sort _} (op : α → β → β) (b) (hb : C b) (hl) :
    foldrRecOn [] op b hb hl = hb :=
  rfl
#align list.foldr_rec_on_nil List.foldrRecOn_nil

/- warning: list.foldr_rec_on_cons -> List.foldrRecOn_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Sort.{u3}} (x : α) (l : List.{u1} α) (op : α -> β -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.cons.{u1} α x l)) -> (C (op a b)))), Eq.{u3} (C (List.foldr.{u1, u2} α β op b (List.cons.{u1} α x l))) (List.foldrRecOn.{u1, u2, u3} α β (fun (b : β) => C b) (List.cons.{u1} α x l) op b hb hl) (hl (List.foldr.{u1, u2} α β op b l) (List.foldrRecOn.{u1, u2, u3} α β C l op b hb (fun (b : β) (hb : C b) (a : α) (ha : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) => hl b hb a (List.mem_cons_of_mem.{u1} α x a l ha))) x (List.mem_cons_self.{u1} α x l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {C : β -> Sort.{u1}} (x : α) (l : List.{u2} α) (op : α -> β -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (List.cons.{u2} α x l)) -> (C (op a b)))), Eq.{u1} (C (List.foldr.{u2, u3} α β op b (List.cons.{u2} α x l))) (List.foldrRecOn.{u2, u3, u1} α β C (List.cons.{u2} α x l) op b hb hl) (hl (List.foldr.{u2, u3} α β op b l) (List.foldrRecOn.{u2, u3, u1} α β C l op b hb (fun (b : β) (hb : C b) (a : α) (ha : Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) => hl b hb a (List.mem_cons_of_mem.{u2} α x a l ha))) x (List.mem_cons_self.{u2} α x l))
Case conversion may be inaccurate. Consider using '#align list.foldr_rec_on_cons List.foldrRecOn_consₓ'. -/
@[simp]
theorem foldrRecOn_cons {C : β → Sort _} (x : α) (l : List α) (op : α → β → β) (b) (hb : C b)
    (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ x :: l), C (op a b)) :
    foldrRecOn (x :: l) op b hb hl =
      hl _ (foldrRecOn l op b hb fun b hb a ha => hl b hb a (mem_cons_of_mem _ ha)) x
        (mem_cons_self _ _) :=
  rfl
#align list.foldr_rec_on_cons List.foldrRecOn_cons

/- warning: list.foldl_rec_on_nil -> List.foldlRecOn_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {C : β -> Sort.{u3}} (op : β -> α -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.nil.{u1} α)) -> (C (op b a)))), Eq.{u3} (C (List.foldl.{u2, u1} β α op b (List.nil.{u1} α))) (List.foldlRecOn.{u1, u2, u3} α β (fun (b : β) => C b) (List.nil.{u1} α) op b hb hl) hb
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {C : β -> Sort.{u1}} (op : β -> α -> β) (b : β) (hb : C b) (hl : forall (b : β), (C b) -> (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (List.nil.{u2} α)) -> (C (op b a)))), Eq.{u1} (C (List.foldl.{u3, u2} β α op b (List.nil.{u2} α))) (List.foldlRecOn.{u2, u3, u1} α β C (List.nil.{u2} α) op b hb hl) hb
Case conversion may be inaccurate. Consider using '#align list.foldl_rec_on_nil List.foldlRecOn_nilₓ'. -/
@[simp]
theorem foldlRecOn_nil {C : β → Sort _} (op : β → α → β) (b) (hb : C b) (hl) :
    foldlRecOn [] op b hb hl = hb :=
  rfl
#align list.foldl_rec_on_nil List.foldlRecOn_nil

-- scanl
section Scanl

variable {f : β → α → β} {b : β} {a : α} {l : List α}

#print List.length_scanl /-
theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | a, [] => rfl
  | a, x :: l => by erw [length_cons, length_cons, length_scanl]
#align list.length_scanl List.length_scanl
-/

#print List.scanl_nil /-
@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl
#align list.scanl_nil List.scanl_nil
-/

#print List.scanl_cons /-
@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, eq_self_iff_true, singleton_append, and_self_iff]
#align list.scanl_cons List.scanl_cons
-/

#print List.get?_zero_scanl /-
@[simp]
theorem get?_zero_scanl : (scanl f b l).nth 0 = some b :=
  by
  cases l
  · simp only [nth, scanl_nil]
  · simp only [nth, scanl_cons, singleton_append]
#align list.nth_zero_scanl List.get?_zero_scanl
-/

#print List.nthLe_zero_scanl /-
@[simp]
theorem nthLe_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).nthLe 0 h = b :=
  by
  cases l
  · simp only [nth_le, scanl_nil]
  · simp only [nth_le, scanl_cons, singleton_append]
#align list.nth_le_zero_scanl List.nthLe_zero_scanl
-/

#print List.get?_succ_scanl /-
theorem get?_succ_scanl {i : ℕ} :
    (scanl f b l).nth (i + 1) = ((scanl f b l).nth i).bind fun x => (l.nth i).map fun y => f x y :=
  by
  induction' l with hd tl hl generalizing b i
  · symm
    simp only [Option.bind_eq_none', nth, forall₂_true_iff, not_false_iff, Option.map_none',
      scanl_nil, Option.not_mem_none, forall_true_iff]
  · simp only [nth, scanl_cons, singleton_append]
    cases i
    · simp only [Option.map_some', nth_zero_scanl, nth, Option.some_bind']
    · simp only [hl, nth]
#align list.nth_succ_scanl List.get?_succ_scanl
-/

#print List.nthLe_succ_scanl /-
theorem nthLe_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).nthLe (i + 1) h =
      f ((scanl f b l).nthLe i (Nat.lt_of_succ_lt h))
        (l.nthLe i (Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) :=
  by
  induction' i with i hi generalizing b l
  · cases l
    · simp only [length, zero_add, scanl_nil] at h
      exact absurd h (lt_irrefl 1)
    · simp only [scanl_cons, singleton_append, nth_le_zero_scanl, nth_le]
  · cases l
    · simp only [length, add_lt_iff_neg_right, scanl_nil] at h
      exact absurd h (not_lt_of_lt Nat.succ_pos')
    · simp_rw [scanl_cons]
      rw [nth_le_append_right _]
      · simpa only [hi, length, succ_add_sub_one]
      · simp only [length, Nat.zero_le, le_add_iff_nonneg_left]
#align list.nth_le_succ_scanl List.nthLe_succ_scanl
-/

end Scanl

#print List.scanr_nil /-
-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl
#align list.scanr_nil List.scanr_nil
-/

/- warning: list.scanr_aux_cons clashes with [anonymous] -> [anonymous]
warning: list.scanr_aux_cons -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (b : β) (a : α) (l : List.{u1} α), Eq.{succ u2} (Prod.{u2, u2} β (List.{u2} β)) (List.scanrAux.{u1, u2} α β f b (List.cons.{u1} α a l)) (Prod.mk.{u2, u2} β (List.{u2} β) (List.foldr.{u1, u2} α β f b (List.cons.{u1} α a l)) (List.scanr.{u1, u2} α β f b l))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.scanr_aux_cons [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (f : α → β → β) (b : β) :
    ∀ (a : α) (l : List α), scanrAux f b (a :: l) = (foldr f b (a :: l), scanr f b l)
  | a, [] => rfl
  | a, x :: l => by
    let t := scanr_aux_cons x l
    simp only [scanr, scanr_aux, t, foldr_cons]
#align list.scanr_aux_cons [anonymous]

#print List.scanr_cons /-
@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, scanr_aux_cons, foldr_cons] <;> constructor <;> rfl
#align list.scanr_cons List.scanr_cons
-/

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α} (hcomm : Commutative f) (hassoc : Associative f)

include hassoc

#print List.foldl1_eq_foldr1 /-
theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | a, b, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l] <;> rw [hassoc]
#align list.foldl1_eq_foldr1 List.foldl1_eq_foldr1
-/

include hcomm

#print List.foldl_eq_of_comm_of_assoc /-
theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm a b
  | a, b, c :: l => by
    simp only [foldl_cons] <;> rw [← foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc] <;> rfl
#align list.foldl_eq_of_comm_of_assoc List.foldl_eq_of_comm_of_assoc
-/

#print List.foldl_eq_foldr /-
theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
  | a, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc] <;> rw [foldl_eq_foldr a l]
#align list.foldl_eq_foldr List.foldl_eq_foldr
-/

end FoldlEqFoldr

section FoldlEqFoldlr'

variable {f : α → β → α}

variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

include hf

#print List.foldl_eq_of_comm' /-
theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm', foldl, hf]
#align list.foldl_eq_of_comm' List.foldl_eq_of_comm'
-/

#print List.foldl_eq_foldr' /-
theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | a, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr'] <;> rfl
#align list.foldl_eq_foldr' List.foldl_eq_foldr'
-/

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable {f : α → β → β}

variable (hf : ∀ a b c, f a (f b c) = f b (f a c))

include hf

#print List.foldr_eq_of_comm' /-
theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm'] <;> rfl
#align list.foldr_eq_of_comm' List.foldr_eq_of_comm'
-/

end FoldlEqFoldlr'

section

variable {op : α → α → α} [ha : IsAssociative α op] [hc : IsCommutative α op]

-- mathport name: op
local notation a " * " b => op a b

-- mathport name: foldl
local notation l " <*> " a => foldl op a l

include ha

#print List.foldl_assoc /-
theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l <*> a₁ * a₂) = a₁ * l <*> a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ =>
    calc
      ((a :: l) <*> a₁ * a₂) = l <*> a₁ * a₂ * a := by simp only [foldl_cons, ha.assoc]
      _ = a₁ * (a :: l) <*> a₂ := by rw [foldl_assoc, foldl_cons]
      
#align list.foldl_assoc List.foldl_assoc
-/

#print List.foldl_op_eq_op_foldr_assoc /-
theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) * a₂) = a₁ * l.foldr (· * ·) a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc] <;> rw [foldl_op_eq_op_foldr_assoc]
#align list.foldl_op_eq_op_foldr_assoc List.foldl_op_eq_op_foldr_assoc
-/

include hc

#print List.foldl_assoc_comm_cons /-
theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l) <*> a₂) = a₁ * l <*> a₂ := by
  rw [foldl_cons, hc.comm, foldl_assoc]
#align list.foldl_assoc_comm_cons List.foldl_assoc_comm_cons
-/

end

/-! ### mfoldl, mfoldr, mmap -/


section MfoldlMfoldr

variable {m : Type v → Type w} [Monad m]

#print List.foldlM_nil /-
@[simp]
theorem foldlM_nil (f : β → α → m β) {b} : foldlM f b [] = pure b :=
  rfl
#align list.mfoldl_nil List.foldlM_nil
-/

/- warning: list.mfoldr_nil -> List.foldrM_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] (f : α -> β -> (m β)) {b : β}, Eq.{succ u3} (m β) (List.foldrM.{u2, u3, u1} (fun {β : Type.{u2}} => m β) _inst_1 β α f b (List.nil.{u1} α)) (Pure.pure.{u2, u3} m (Applicative.toHasPure.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) β b)
but is expected to have type
  forall {α : Type.{u3} -> Type.{u2}} {β : Type.{u1}} {m : Type.{u3}} [_inst_1 : Monad.{u3, u2} α] (f : β -> m -> (α m)) (b : m), Eq.{succ u2} (α m) (List.foldrM.{u3, u2, u1} α _inst_1 m β f b (List.nil.{u1} β)) (Pure.pure.{u3, u2} α (Applicative.toPure.{u3, u2} α (Monad.toApplicative.{u3, u2} α _inst_1)) m b)
Case conversion may be inaccurate. Consider using '#align list.mfoldr_nil List.foldrM_nilₓ'. -/
@[simp]
theorem foldrM_nil (f : α → β → m β) {b} : foldrM f b [] = pure b :=
  rfl
#align list.mfoldr_nil List.foldrM_nil

#print List.foldlM_cons /-
@[simp]
theorem foldlM_cons {f : β → α → m β} {b a l} :
    foldlM f b (a :: l) = f b a >>= fun b' => foldlM f b' l :=
  rfl
#align list.mfoldl_cons List.foldlM_cons
-/

/- warning: list.mfoldr_cons -> List.foldrM_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] {f : α -> β -> (m β)} {b : β} {a : α} {l : List.{u1} α}, Eq.{succ u3} (m β) (List.foldrM.{u2, u3, u1} (fun {β : Type.{u2}} => m β) _inst_1 β α f b (List.cons.{u1} α a l)) (Bind.bind.{u2, u3} m (Monad.toHasBind.{u2, u3} m _inst_1) β β (List.foldrM.{u2, u3, u1} m _inst_1 β α f b l) (f a))
but is expected to have type
  forall {α : Type.{u3} -> Type.{u2}} {β : Type.{u1}} {m : Type.{u3}} [_inst_1 : Monad.{u3, u2} α] [f : LawfulMonad.{u3, u2} α _inst_1] (b : β) (a : List.{u1} β) (l : β -> m -> (α m)) (b_1 : m), Eq.{succ u2} (α m) (List.foldrM.{u3, u2, u1} α _inst_1 m β l b_1 (List.cons.{u1} β b a)) (Bind.bind.{u3, u2} α (Monad.toBind.{u3, u2} α _inst_1) m m (List.foldrM.{u3, u2, u1} α _inst_1 m β l b_1 a) (l b))
Case conversion may be inaccurate. Consider using '#align list.mfoldr_cons List.foldrM_consₓ'. -/
@[simp]
theorem foldrM_cons {f : α → β → m β} {b a l} : foldrM f b (a :: l) = foldrM f b l >>= f a :=
  rfl
#align list.mfoldr_cons List.foldrM_cons

/- warning: list.mfoldr_eq_foldr -> List.foldrM_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] (f : α -> β -> (m β)) (b : β) (l : List.{u1} α), Eq.{succ u3} (m β) (List.foldrM.{u2, u3, u1} (fun {β : Type.{u2}} => m β) _inst_1 β α f b l) (List.foldr.{u1, u3} α (m β) (fun (a : α) (mb : m β) => Bind.bind.{u2, u3} m (Monad.toHasBind.{u2, u3} m _inst_1) β β mb (f a)) (Pure.pure.{u2, u3} m (Applicative.toHasPure.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) β b) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [f : LawfulMonad.{u2, u3} m _inst_1] (b : α -> β -> (m β)) (l : β) (l_1 : List.{u1} α), Eq.{succ u3} (m β) (List.foldrM.{u2, u3, u1} m _inst_1 β α b l l_1) (List.foldr.{u1, u3} α (m β) (fun (a : α) (mb : m β) => Bind.bind.{u2, u3} m (Monad.toBind.{u2, u3} m _inst_1) β β mb (b a)) (Pure.pure.{u2, u3} m (Applicative.toPure.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) β l) l_1)
Case conversion may be inaccurate. Consider using '#align list.mfoldr_eq_foldr List.foldrM_eq_foldrₓ'. -/
theorem foldrM_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]
#align list.mfoldr_eq_foldr List.foldrM_eq_foldr

attribute [simp] mmap mmap'

variable [LawfulMonad m]

#print List.foldlM_eq_foldl /-
theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l :=
  by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => mfoldl f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
  · simp [← h (pure b)]
  induction l <;> intro
  · simp
  · simp only [mfoldl, foldl, ← l_ih, functor_norm]
#align list.mfoldl_eq_foldl List.foldlM_eq_foldl
-/

/- warning: list.mfoldl_append -> List.foldlM_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [_inst_2 : LawfulMonad.{u2, u3} m _inst_1] {f : β -> α -> (m β)} {b : β} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u3} (m β) (List.foldlM.{u2, u3, u1} (fun {β : Type.{u2}} => m β) _inst_1 β α f b (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Bind.bind.{u2, u3} m (Monad.toHasBind.{u2, u3} m _inst_1) β β (List.foldlM.{u2, u3, u1} m _inst_1 β α f b l₁) (fun (x : β) => List.foldlM.{u2, u3, u1} m _inst_1 β α f x l₂))
but is expected to have type
  forall {α : Type.{u3} -> Type.{u2}} {β : Type.{u3}} {m : Type.{u1}} [_inst_1 : Monad.{u3, u2} α] [_inst_2 : LawfulMonad.{u3, u2} α _inst_1] (f : β -> m -> (α β)) (b : β) (l₁ : List.{u1} m) (l₂ : List.{u1} m), Eq.{succ u2} (α β) (List.foldlM.{u3, u2, u1} α _inst_1 β m f b (HAppend.hAppend.{u1, u1, u1} (List.{u1} m) (List.{u1} m) (List.{u1} m) (instHAppend.{u1} (List.{u1} m) (List.instAppendList.{u1} m)) l₁ l₂)) (Bind.bind.{u3, u2} α (Monad.toBind.{u3, u2} α _inst_1) β β (List.foldlM.{u3, u2, u1} α _inst_1 β m f b l₁) (fun (x : β) => List.foldlM.{u3, u2, u1} α _inst_1 β m f x l₂))
Case conversion may be inaccurate. Consider using '#align list.mfoldl_append List.foldlM_appendₓ'. -/
@[simp]
theorem foldlM_append {f : β → α → m β} :
    ∀ {b l₁ l₂}, foldlM f b (l₁ ++ l₂) = foldlM f b l₁ >>= fun x => foldlM f x l₂
  | _, [], _ => by simp only [nil_append, mfoldl_nil, pure_bind]
  | _, _ :: _, _ => by simp only [cons_append, mfoldl_cons, mfoldl_append, LawfulMonad.bind_assoc]
#align list.mfoldl_append List.foldlM_append

/- warning: list.mfoldr_append -> List.foldrM_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [_inst_2 : LawfulMonad.{u2, u3} m _inst_1] {f : α -> β -> (m β)} {b : β} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u3} (m β) (List.foldrM.{u2, u3, u1} (fun {β : Type.{u2}} => m β) _inst_1 β α f b (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Bind.bind.{u2, u3} m (Monad.toHasBind.{u2, u3} m _inst_1) β β (List.foldrM.{u2, u3, u1} m _inst_1 β α f b l₂) (fun (x : β) => List.foldrM.{u2, u3, u1} m _inst_1 β α f x l₁))
but is expected to have type
  forall {α : Type.{u3} -> Type.{u2}} {β : Type.{u1}} {m : Type.{u3}} [_inst_1 : Monad.{u3, u2} α] [_inst_2 : LawfulMonad.{u3, u2} α _inst_1] (f : β -> m -> (α m)) (b : m) (l₁ : List.{u1} β) (l₂ : List.{u1} β), Eq.{succ u2} (α m) (List.foldrM.{u3, u2, u1} α _inst_1 m β f b (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) l₁ l₂)) (Bind.bind.{u3, u2} α (Monad.toBind.{u3, u2} α _inst_1) m m (List.foldrM.{u3, u2, u1} α _inst_1 m β f b l₂) (fun (x : m) => List.foldrM.{u3, u2, u1} α _inst_1 m β f x l₁))
Case conversion may be inaccurate. Consider using '#align list.mfoldr_append List.foldrM_appendₓ'. -/
@[simp]
theorem foldrM_append {f : α → β → m β} :
    ∀ {b l₁ l₂}, foldrM f b (l₁ ++ l₂) = foldrM f b l₂ >>= fun x => foldrM f x l₁
  | _, [], _ => by simp only [nil_append, mfoldr_nil, bind_pure]
  | _, _ :: _, _ => by simp only [mfoldr_cons, cons_append, mfoldr_append, LawfulMonad.bind_assoc]
#align list.mfoldr_append List.foldrM_append

end MfoldlMfoldr

/-! ### intersperse -/


#print List.intersperse_nil /-
@[simp]
theorem intersperse_nil {α : Type u} (a : α) : intersperse a [] = [] :=
  rfl
#align list.intersperse_nil List.intersperse_nil
-/

#print List.intersperse_singleton /-
@[simp]
theorem intersperse_singleton {α : Type u} (a b : α) : intersperse a [b] = [b] :=
  rfl
#align list.intersperse_singleton List.intersperse_singleton
-/

#print List.intersperse_cons_cons /-
@[simp]
theorem intersperse_cons_cons {α : Type u} (a b c : α) (tl : List α) :
    intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) :=
  rfl
#align list.intersperse_cons_cons List.intersperse_cons_cons
-/

/-! ### split_at and split_on -/


section SplitAtOn

variable (p : α → Prop) [DecidablePred p] (xs ys : List α) (ls : List (List α))
  (f : List α → List α)

#print List.splitAt_eq_take_drop /-
@[simp]
theorem splitAt_eq_take_drop : ∀ (n : ℕ) (l : List α), splitAt n l = (take n l, drop n l)
  | 0, a => rfl
  | succ n, [] => rfl
  | succ n, x :: xs => by simp only [split_at, split_at_eq_take_drop n xs, take, drop]
#align list.split_at_eq_take_drop List.splitAt_eq_take_drop
-/

#print List.splitOn_nil /-
@[simp]
theorem splitOn_nil {α : Type u} [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl
#align list.split_on_nil List.splitOn_nil
-/

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  rfl
#align list.split_on_p_nil List.splitOnP_nilₓ

/- warning: list.split_on_p_aux' clashes with [anonymous] -> [anonymous]
warning: list.split_on_p_aux' -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (P : α -> Prop) [_inst_2 : DecidablePred.{succ u} α P], (List.{u} α) -> (List.{u} α) -> (List.{u} (List.{u} α))
but is expected to have type
  forall {α : Type.{u}} {P : Type.{v}}, (Nat -> α -> P) -> Nat -> (List.{u} α) -> (List.{v} P)
Case conversion may be inaccurate. Consider using '#align list.split_on_p_aux' [anonymous]ₓ'. -/
/-- An auxiliary definition for proving a specification lemma for `split_on_p`.

`split_on_p_aux' P xs ys` splits the list `ys ++ xs` at every element satisfying `P`,
where `ys` is an accumulating parameter for the initial segment of elements not satisfying `P`.
-/
def [anonymous] {α : Type u} (P : α → Prop) [DecidablePred P] : List α → List α → List (List α)
  | [], xs => [xs]
  | h :: t, xs => if P h then xs :: split_on_p_aux' t [] else split_on_p_aux' t (xs ++ [h])
#align list.split_on_p_aux' [anonymous]

/- warning: list.split_on_p_aux_eq clashes with [anonymous] -> [anonymous]
warning: list.split_on_p_aux_eq -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u} α p] (xs : List.{u} α) (ys : List.{u} α), Eq.{succ u} (List.{u} (List.{u} α)) ([anonymous].{u} α p (fun (a : α) => _inst_1 a) xs ys) (List.splitOnPAux.{u} α p (fun (a : α) => _inst_1 a) xs (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) ys))
but is expected to have type
  forall {α : Type.{u}} {p : Type.{v}}, (Nat -> α -> p) -> Nat -> (List.{u} α) -> (List.{v} p)
Case conversion may be inaccurate. Consider using '#align list.split_on_p_aux_eq [anonymous]ₓ'. -/
theorem [anonymous] : [anonymous] p xs ys = splitOnPAux p xs ((· ++ ·) ys) :=
  by
  induction' xs with a t ih generalizing ys <;>
    simp! only [append_nil, eq_self_iff_true, and_self_iff]
  split_ifs <;> rw [ih]
  · refine' ⟨rfl, rfl⟩
  · congr
    ext
    simp
#align list.split_on_p_aux_eq [anonymous]

/- warning: list.split_on_p_aux_nil clashes with [anonymous] -> [anonymous]
warning: list.split_on_p_aux_nil -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u} α p] (xs : List.{u} α), Eq.{succ u} (List.{u} (List.{u} α)) (List.splitOnPAux.{u} α p (fun (a : α) => _inst_1 a) xs (id.{succ u} (List.{u} α))) ([anonymous].{u} α p (fun (a : α) => _inst_1 a) xs (List.nil.{u} α))
but is expected to have type
  forall {α : Type.{u}} {p : Type.{v}}, (Nat -> α -> p) -> Nat -> (List.{u} α) -> (List.{v} p)
Case conversion may be inaccurate. Consider using '#align list.split_on_p_aux_nil [anonymous]ₓ'. -/
theorem [anonymous] : splitOnPAux p xs id = [anonymous] p xs [] :=
  by
  rw [split_on_p_aux_eq]
  rfl
#align list.split_on_p_aux_nil [anonymous]

/-- The original list `L` can be recovered by joining the lists produced by `split_on_p p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    join (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as :=
  by
  rw [split_on_p, split_on_p_aux_nil]
  suffices
    ∀ xs,
      join
          (zip_with (· ++ ·) (split_on_p_aux' p as xs) (((as.filter p).map fun x => [x]) ++ [[]])) =
        xs ++ as
    by
    rw [this]
    rfl
  induction as <;> intro <;> simp! only [split_on_p_aux', append_nil]
  split_ifs <;> simp [zip_with, join, *]
#align list.split_on_p_spec List.splitOnP_specₓ

/- warning: list.split_on_p_aux_ne_nil clashes with [anonymous] -> [anonymous]
warning: list.split_on_p_aux_ne_nil -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u} α p] (xs : List.{u} α) (f : (List.{u} α) -> (List.{u} α)), Ne.{succ u} (List.{u} (List.{u} α)) (List.splitOnPAux.{u} α p (fun (a : α) => _inst_1 a) xs f) (List.nil.{u} (List.{u} α))
but is expected to have type
  forall {α : Type.{u}} {p : Type.{v}}, (Nat -> α -> p) -> Nat -> (List.{u} α) -> (List.{v} p)
Case conversion may be inaccurate. Consider using '#align list.split_on_p_aux_ne_nil [anonymous]ₓ'. -/
theorem [anonymous] : splitOnPAux p xs f ≠ [] :=
  by
  induction' xs with _ _ ih generalizing f; · trivial
  simp only [split_on_p_aux]; split_ifs; · trivial; exact ih _
#align list.split_on_p_aux_ne_nil [anonymous]

/- warning: list.split_on_p_aux_spec clashes with [anonymous] -> [anonymous]
warning: list.split_on_p_aux_spec -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u} α p] (xs : List.{u} α) (f : (List.{u} α) -> (List.{u} α)), Eq.{succ u} (List.{u} (List.{u} α)) (List.splitOnPAux.{u} α p (fun (a : α) => _inst_1 a) xs f) (List.modifyHead.{u} (List.{u} α) f (List.splitOnP.{u} α p (fun (a : α) => _inst_1 a) xs))
but is expected to have type
  forall {α : Type.{u}} {p : Type.{v}}, (Nat -> α -> p) -> Nat -> (List.{u} α) -> (List.{v} p)
Case conversion may be inaccurate. Consider using '#align list.split_on_p_aux_spec [anonymous]ₓ'. -/
theorem [anonymous] : splitOnPAux p xs f = (xs.splitOnP p).modifyHead f :=
  by
  simp only [split_on_p]
  induction' xs with hd tl ih generalizing f; · simp [split_on_p_aux]
  simp only [split_on_p_aux]; split_ifs; · simp
  rw [ih fun l => f (hd :: l), ih fun l => id (hd :: l)]
  simp
#align list.split_on_p_aux_spec [anonymous]

theorem splitOnP_ne_nil : xs.splitOnP p ≠ [] :=
  [anonymous] _ _ id
#align list.split_on_p_ne_nil List.splitOnP_ne_nilₓ

@[simp]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) :=
  by
  simp only [split_on_p, split_on_p_aux]
  split_ifs
  · simp
  rw [split_on_p_aux_spec]
  rfl
#align list.split_on_p_cons List.splitOnP_consₓ

/-- If no element satisfies `p` in the list `xs`, then `xs.split_on_p p = [xs]` -/
theorem splitOnP_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] :=
  by
  induction' xs with hd tl ih
  · rfl
  simp [h hd _, ih fun t ht => h t (Or.inr ht)]
#align list.split_on_p_eq_single List.splitOnP_eq_singleₓ

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p :=
  by
  induction' xs with hd tl ih
  · simp [hsep]
  simp [h hd _, ih fun t ht => h t (Or.inr ht)]
#align list.split_on_p_first List.splitOnP_firstₓ

#print List.intercalate_splitOn /-
/-- `intercalate [x]` is the left inverse of `split_on x`  -/
theorem intercalate_splitOn (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs :=
  by
  simp only [intercalate, split_on]
  induction' xs with hd tl ih; · simp [join]; simp only [split_on_p_cons]
  cases' h' : split_on_p (· = x) tl with hd' tl'; · exact (split_on_p_ne_nil _ tl h').elim
  rw [h'] at ih; split_ifs;
  · subst h
    simp [ih, join]
  cases tl' <;> simpa [join] using ih
#align list.intercalate_split_on List.intercalate_splitOn
-/

#print List.splitOn_intercalate /-
/-- `split_on x` is the left inverse of `intercalate [x]`, on the domain
  consisting of each nonempty list of lists `ls` whose elements do not contain `x`  -/
theorem splitOn_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls :=
  by
  simp only [intercalate]
  induction' ls with hd tl ih; · contradiction
  cases tl
  · suffices hd.split_on x = [hd] by simpa [join]
    refine' split_on_p_eq_single _ _ _
    intro y hy H
    rw [H] at hy
    refine' hx hd _ hy
    simp
  · simp only [intersperse_cons_cons, singleton_append, join]
    specialize ih _ _
    · intro l hl
      apply hx l
      simp at hl⊢
      tauto
    · trivial
    have := split_on_p_first (· = x) hd _ x rfl _
    · simp only [split_on] at ih⊢
      rw [this]
      rw [ih]
    intro y hy H
    rw [H] at hy
    exact hx hd (Or.inl rfl) hy
#align list.split_on_intercalate List.splitOn_intercalate
-/

end SplitAtOn

/-! ### map for partial functions -/


#print List.pmap /-
/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
  | [], H => []
  | a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2
#align list.pmap List.pmap
-/

#print List.attach /-
/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id
#align list.attach List.attach
-/

/- warning: list.sizeof_lt_sizeof_of_mem -> List.sizeOf_lt_sizeOf_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] {x : α} {l : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (LT.lt.{0} Nat Nat.hasLt (SizeOf.sizeOf.{succ u1} α _inst_1 x) (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List.hasSizeof.{u1} α _inst_1) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] {x : α} {l : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (LT.lt.{0} Nat instLTNat (SizeOf.sizeOf.{succ u1} α _inst_1 x) (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List._sizeOf_inst.{u1} α _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.sizeof_lt_sizeof_of_mem List.sizeOf_lt_sizeOf_of_memₓ'. -/
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l :=
  by
  induction' l with h t ih <;> cases hx
  · rw [hx]
    exact lt_add_of_lt_of_nonneg (lt_one_add _) (Nat.zero_le _)
  · exact lt_add_of_pos_of_le (zero_lt_one_add _) (le_of_lt (ih hx))
#align list.sizeof_lt_sizeof_of_mem List.sizeOf_lt_sizeOf_of_mem

#print List.pmap_eq_map /-
@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) (H) :
    @pmap _ _ p (fun a _ => f a) l H = map f l := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.pmap_eq_map List.pmap_eq_map
-/

#print List.pmap_congr /-
theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
    (h : ∀ a ∈ l, ∀ (h₁ h₂), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ :=
  by
  induction' l with _ _ ih
  · rfl
  · rw [pmap, pmap, h _ (mem_cons_self _ _), ih fun a ha => h a (mem_cons_of_mem _ ha)]
#align list.pmap_congr List.pmap_congr
-/

#print List.map_pmap /-
theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (l H) :
    map g (pmap f l H) = pmap (fun a h => g (f a h)) l H := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.map_pmap List.map_pmap
-/

#print List.pmap_map /-
theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (l H) :
    pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) := by
  induction l <;> [rfl, simp only [*, pmap, map]] <;> constructor <;> rfl
#align list.pmap_map List.pmap_map
-/

#print List.pmap_eq_map_attach /-
theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (l H) :
    pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) := by
  rw [attach, map_pmap] <;> exact pmap_congr l fun _ _ _ _ => rfl
#align list.pmap_eq_map_attach List.pmap_eq_map_attach
-/

#print List.attach_map_coe' /-
@[simp]
theorem attach_map_coe' (l : List α) (f : α → β) : (l.attach.map fun i => f i) = l.map f := by
  rw [attach, map_pmap] <;> exact pmap_eq_map _ _ _ _
#align list.attach_map_coe' List.attach_map_coe'
-/

#print List.attach_map_val' /-
theorem attach_map_val' (l : List α) (f : α → β) : (l.attach.map fun i => f i.val) = l.map f :=
  attach_map_coe' _ _
#align list.attach_map_val' List.attach_map_val'
-/

#print List.attach_map_val /-
@[simp]
theorem attach_map_val (l : List α) : l.attach.map (coe : _ → α) = l :=
  (attach_map_coe' _ _).trans l.map_id
#align list.attach_map_coe List.attach_map_val
-/

/- warning: list.attach_map_val clashes with list.attach_map_coe -> List.attach_map_val
Case conversion may be inaccurate. Consider using '#align list.attach_map_val List.attach_map_valₓ'. -/
#print List.attach_map_val /-
theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l :=
  attach_map_val _
#align list.attach_map_val List.attach_map_val
-/

#print List.mem_attach /-
@[simp]
theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach
  | ⟨a, h⟩ => by
    have := mem_map.1 (by rw [attach_map_val] <;> exact h) <;>
      · rcases this with ⟨⟨_, _⟩, m, rfl⟩
        exact m
#align list.mem_attach List.mem_attach
-/

#print List.mem_pmap /-
@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} :
    b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b := by
  simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and_iff, Subtype.exists]
#align list.mem_pmap List.mem_pmap
-/

#print List.length_pmap /-
@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l := by
  induction l <;> [rfl, simp only [*, pmap, length]]
#align list.length_pmap List.length_pmap
-/

#print List.length_attach /-
@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap
#align list.length_attach List.length_attach
-/

#print List.pmap_eq_nil /-
@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] := by
  rw [← length_eq_zero, length_pmap, length_eq_zero]
#align list.pmap_eq_nil List.pmap_eq_nil
-/

#print List.attach_eq_nil /-
@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil
#align list.attach_eq_nil List.attach_eq_nil
-/

/- warning: list.last_pmap -> List.getLast_pmap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) (f : forall (a : α), (p a) -> β) (l : List.{u1} α) (hl₁ : forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a)) (hl₂ : Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)), Eq.{succ u2} β (List.getLast.{u2} β (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l hl₁) (mt (Eq.{succ u2} (List.{u2} β) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l hl₁) (List.nil.{u2} β)) (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) (Iff.mp (Eq.{succ u2} (List.{u2} β) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l hl₁) (List.nil.{u2} β)) (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) (List.pmap_eq_nil.{u1, u2} α β (fun (a : α) => p a) f l hl₁)) hl₂)) (f (List.getLast.{u1} α l hl₂) (hl₁ (List.getLast.{u1} α l hl₂) (List.getLast_mem.{u1} α l hl₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : α -> Prop) (f : forall (a : α), (p a) -> β) (l : List.{u2} α) (hl₁ : forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (p a)) (hl₂ : Ne.{succ u2} (List.{u2} α) l (List.nil.{u2} α)), Eq.{succ u1} β (List.getLast.{u1} β (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l hl₁) (mt (Eq.{succ u1} (List.{u1} β) (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l hl₁) (List.nil.{u1} β)) (Eq.{succ u2} (List.{u2} α) l (List.nil.{u2} α)) (Iff.mp (Eq.{succ u1} (List.{u1} β) (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l hl₁) (List.nil.{u1} β)) (Eq.{succ u2} (List.{u2} α) l (List.nil.{u2} α)) (List.pmap_eq_nil.{u2, u1} α β (fun (a : α) => p a) f l hl₁)) hl₂)) (f (List.getLast.{u2} α l hl₂) (hl₁ (List.getLast.{u2} α l hl₂) (List.getLast_mem.{u2} α l hl₂)))
Case conversion may be inaccurate. Consider using '#align list.last_pmap List.getLast_pmapₓ'. -/
theorem getLast_pmap {α β : Type _} (p : α → Prop) (f : ∀ a, p a → β) (l : List α)
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
    (l.pmap f hl₁).last (mt List.pmap_eq_nil.1 hl₂) =
      f (l.last hl₂) (hl₁ _ (List.getLast_mem hl₂)) :=
  by
  induction' l with l_hd l_tl l_ih
  · apply (hl₂ rfl).elim
  · cases l_tl
    · simp
    · apply l_ih
#align list.last_pmap List.getLast_pmap

#print List.get?_pmap /-
theorem get?_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) (n : ℕ) :
    get? (pmap f l h) n = Option.pmap f (get? l n) fun x H => h x (get?_mem H) :=
  by
  induction' l with hd tl hl generalizing n
  · simp
  · cases n <;> simp [hl]
#align list.nth_pmap List.get?_pmap
-/

#print List.nthLe_pmap /-
theorem nthLe_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a) {n : ℕ}
    (hn : n < (pmap f l h).length) :
    nthLe (pmap f l h) n hn =
      f (nthLe l n (@length_pmap _ _ p f l h ▸ hn))
        (h _ (nthLe_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
  by
  induction' l with hd tl hl generalizing n
  · simp only [length, pmap] at hn
    exact absurd hn (not_lt_of_le n.zero_le)
  · cases n
    · simp
    · simpa [hl]
#align list.nth_le_pmap List.nthLe_pmap
-/

/- warning: list.pmap_append -> List.pmap_append is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : Type.{u1}} {p : ι -> Prop} (f : forall (a : ι), (p a) -> α) (l₁ : List.{u2} ι) (l₂ : List.{u2} ι) (h : forall (a : ι), (Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) a (Append.append.{u2} (List.{u2} ι) (List.hasAppend.{u2} ι) l₁ l₂)) -> (p a)), Eq.{succ u1} (List.{u1} α) (List.pmap.{u2, u1} ι α (fun (a : ι) => p a) f (Append.append.{u2} (List.{u2} ι) (List.hasAppend.{u2} ι) l₁ l₂) h) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) (List.pmap.{u2, u1} ι α (fun (a : ι) => p a) f l₁ (fun (a : ι) (ha : Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) a l₁) => h a (List.mem_append_left.{u2} ι a l₁ l₂ ha))) (List.pmap.{u2, u1} ι α (fun (a : ι) => p a) f l₂ (fun (a : ι) (ha : Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) a l₂) => h a (List.mem_append_right.{u2} ι a l₁ l₂ ha))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {p : ι -> Prop} (f : forall (a : ι), (p a) -> α) (l₁ : List.{u1} ι) (l₂ : List.{u1} ι) (h : forall (a : ι), (Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) a (HAppend.hAppend.{u1, u1, u1} (List.{u1} ι) (List.{u1} ι) (List.{u1} ι) (instHAppend.{u1} (List.{u1} ι) (List.instAppendList.{u1} ι)) l₁ l₂)) -> (p a)), Eq.{succ u2} (List.{u2} α) (List.pmap.{u1, u2} ι α (fun (a : ι) => p a) f (HAppend.hAppend.{u1, u1, u1} (List.{u1} ι) (List.{u1} ι) (List.{u1} ι) (instHAppend.{u1} (List.{u1} ι) (List.instAppendList.{u1} ι)) l₁ l₂) h) (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) (List.pmap.{u1, u2} ι α (fun (a : ι) => p a) f l₁ (fun (a : ι) (ha : Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) a l₁) => h a (List.mem_append_left.{u1} ι a l₁ l₂ ha))) (List.pmap.{u1, u2} ι α (fun (a : ι) => p a) f l₂ (fun (a : ι) (ha : Membership.mem.{u1, u1} ι (List.{u1} ι) (List.instMembershipList.{u1} ι) a l₂) => h a (List.mem_append_right.{u1} ι a l₁ l₂ ha))))
Case conversion may be inaccurate. Consider using '#align list.pmap_append List.pmap_appendₓ'. -/
theorem pmap_append {p : ι → Prop} (f : ∀ a : ι, p a → α) (l₁ l₂ : List ι)
    (h : ∀ a ∈ l₁ ++ l₂, p a) :
    (l₁ ++ l₂).pmap f h =
      (l₁.pmap f fun a ha => h a (mem_append_left l₂ ha)) ++
        l₂.pmap f fun a ha => h a (mem_append_right l₁ ha) :=
  by
  induction' l₁ with _ _ ih
  · rfl
  · dsimp only [pmap, cons_append]
    rw [ih]
#align list.pmap_append List.pmap_append

/- warning: list.pmap_append' -> List.pmap_append' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l₁ : List.{u1} α) (l₂ : List.{u1} α) (h₁ : forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) -> (p a)) (h₂ : forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂) -> (p a)), Eq.{succ u2} (List.{u2} β) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂) (fun (a : α) (ha : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) => Or.elim (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂) (p a) (Iff.mp (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (Or (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂)) (List.mem_append.{u1} α a l₁ l₂) ha) (h₁ a) (h₂ a))) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l₁ h₁) (List.pmap.{u1, u2} α β (fun (a : α) => p a) f l₂ h₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {p : α -> Prop} (f : forall (a : α), (p a) -> β) (l₁ : List.{u2} α) (l₂ : List.{u2} α) (h₁ : forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) -> (p a)) (h₂ : forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₂) -> (p a)), Eq.{succ u1} (List.{u1} β) (List.pmap.{u2, u1} α β (fun (a : α) => p a) f (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂) (fun (a : α) (ha : Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) => Or.elim (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₂) (p a) (Iff.mp (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l₁ l₂)) (Or (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₁) (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l₂)) (List.mem_append.{u2} α a l₁ l₂) ha) (h₁ a) (h₂ a))) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l₁ h₁) (List.pmap.{u2, u1} α β (fun (a : α) => p a) f l₂ h₂))
Case conversion may be inaccurate. Consider using '#align list.pmap_append' List.pmap_append'ₓ'. -/
theorem pmap_append' {α β : Type _} {p : α → Prop} (f : ∀ a : α, p a → β) (l₁ l₂ : List α)
    (h₁ : ∀ a ∈ l₁, p a) (h₂ : ∀ a ∈ l₂, p a) :
    ((l₁ ++ l₂).pmap f fun a ha => (List.mem_append.1 ha).elim (h₁ a) (h₂ a)) =
      l₁.pmap f h₁ ++ l₂.pmap f h₂ :=
  pmap_append f l₁ l₂ _
#align list.pmap_append' List.pmap_append'

/-! ### find -/


section Find

variable {p : α → Prop} [DecidablePred p] {l : List α} {a : α}

/- warning: list.find_nil -> List.find?_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_2 : DecidablePred.{succ u1} α p], Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_2 a) (List.nil.{u1} α)) (Option.none.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool), Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (List.nil.{u1} α)) (Option.none.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.find_nil List.find?_nilₓ'. -/
@[simp]
theorem find?_nil (p : α → Prop) [DecidablePred p] : find? p [] = none :=
  rfl
#align list.find_nil List.find?_nil

/- warning: list.find_cons_of_pos -> List.find?_cons_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} (l : List.{u1} α), (p a) -> (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a l)) (Option.some.{u1} α a))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α} (a : List.{u1} α), (Eq.{1} Bool (p _inst_1) Bool.true) -> (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (List.cons.{u1} α _inst_1 a)) (Option.some.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align list.find_cons_of_pos List.find?_cons_of_posₓ'. -/
@[simp]
theorem find?_cons_of_pos (l) (h : p a) : find? p (a :: l) = some a :=
  if_pos h
#align list.find_cons_of_pos List.find?_cons_of_pos

/- warning: list.find_cons_of_neg -> List.find?_cons_of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} (l : List.{u1} α), (Not (p a)) -> (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a l)) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α} (a : List.{u1} α), (Not (Eq.{1} Bool (p _inst_1) Bool.true)) -> (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (List.cons.{u1} α _inst_1 a)) (List.find?.{u1} α p a))
Case conversion may be inaccurate. Consider using '#align list.find_cons_of_neg List.find?_cons_of_negₓ'. -/
@[simp]
theorem find?_cons_of_neg (l) (h : ¬p a) : find? p (a :: l) = find? p l :=
  if_neg h
#align list.find_cons_of_neg List.find?_cons_of_neg

/- warning: list.find_eq_none -> List.find?_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) l) (Option.none.{u1} α)) (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (Not (p x)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p _inst_1) (Option.none.{u1} α)) (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x _inst_1) -> (Not (Eq.{1} Bool (p x) Bool.true)))
Case conversion may be inaccurate. Consider using '#align list.find_eq_none List.find?_eq_noneₓ'. -/
@[simp]
theorem find?_eq_none : find? p l = none ↔ ∀ x ∈ l, ¬p x :=
  by
  induction' l with a l IH
  · exact iff_of_true rfl (forall_mem_nil _)
  rw [forall_mem_cons]; by_cases h : p a
  · simp only [find_cons_of_pos _ h, h, not_true, false_and_iff]
  · rwa [find_cons_of_neg _ h, iff_true_intro h, true_and_iff]
#align list.find_eq_none List.find?_eq_none

/- warning: list.find_some -> List.find?_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α} {a : α}, (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) l) (Option.some.{u1} α a)) -> (p a)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α} {l : α}, (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p _inst_1) (Option.some.{u1} α l)) -> (Eq.{1} Bool (p l) Bool.true)
Case conversion may be inaccurate. Consider using '#align list.find_some List.find?_someₓ'. -/
theorem find?_some (H : find? p l = some a) : p a :=
  by
  induction' l with b l IH; · contradiction
  by_cases h : p b
  · rw [find_cons_of_pos _ h] at H
    cases H
    exact h
  · rw [find_cons_of_neg _ h] at H
    exact IH H
#align list.find_some List.find?_some

/- warning: list.find_mem -> List.find?_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α} {a : α}, (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p (fun (a : α) => _inst_1 a) l) (Option.some.{u1} α a)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α} {l : α}, (Eq.{succ u1} (Option.{u1} α) (List.find?.{u1} α p _inst_1) (Option.some.{u1} α l)) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l _inst_1)
Case conversion may be inaccurate. Consider using '#align list.find_mem List.find?_memₓ'. -/
@[simp]
theorem find?_mem (H : find? p l = some a) : a ∈ l :=
  by
  induction' l with b l IH; · contradiction
  by_cases h : p b
  · rw [find_cons_of_pos _ h] at H
    cases H
    apply mem_cons_self
  · rw [find_cons_of_neg _ h] at H
    exact mem_cons_of_mem _ (IH H)
#align list.find_mem List.find?_mem

end Find

/-! ### lookmap -/


section Lookmap

variable (f : α → Option α)

#print List.lookmap_nil /-
@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl
#align list.lookmap_nil List.lookmap_nil
-/

#print List.lookmap_cons_none /-
@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by simp [lookmap, h]
#align list.lookmap_cons_none List.lookmap_cons_none
-/

#print List.lookmap_cons_some /-
@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) : (a :: l).lookmap f = b :: l :=
  by simp [lookmap, h]
#align list.lookmap_cons_some List.lookmap_cons_some
-/

#print List.lookmap_some /-
theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | a :: l => rfl
#align list.lookmap_some List.lookmap_some
-/

#print List.lookmap_none /-
theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => congr_arg (cons a) (lookmap_none l)
#align list.lookmap_none List.lookmap_none
-/

#print List.lookmap_congr /-
theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], H => rfl
  | a :: l, H => by
    cases' forall_mem_cons.1 H with H₁ H₂
    cases' h : g a with b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]
#align list.lookmap_congr List.lookmap_congr
-/

#print List.lookmap_of_forall_not /-
theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)
#align list.lookmap_of_forall_not List.lookmap_of_forall_not
-/

#print List.lookmap_map_eq /-
theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    cases' h' : f a with b
    · simp [h', lookmap_map_eq]
    · simp [lookmap_cons_some _ _ h', h _ _ h']
#align list.lookmap_map_eq List.lookmap_map_eq
-/

#print List.lookmap_id' /-
theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id] <;> exact h
#align list.lookmap_id' List.lookmap_id'
-/

#print List.length_lookmap /-
theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map] <;> simp
#align list.length_lookmap List.length_lookmap
-/

end Lookmap

/-! ### filter_map -/


#print List.filterMap_nil /-
@[simp]
theorem filterMap_nil (f : α → Option β) : filterMap f [] = [] :=
  rfl
#align list.filter_map_nil List.filterMap_nil
-/

#print List.filterMap_cons_none /-
@[simp]
theorem filterMap_cons_none {f : α → Option β} (a : α) (l : List α) (h : f a = none) :
    filterMap f (a :: l) = filterMap f l := by simp only [filter_map, h]
#align list.filter_map_cons_none List.filterMap_cons_none
-/

#print List.filterMap_cons_some /-
@[simp]
theorem filterMap_cons_some (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
    filterMap f (a :: l) = b :: filterMap f l := by
  simp only [filter_map, h] <;> constructor <;> rfl
#align list.filter_map_cons_some List.filterMap_cons_some
-/

#print List.filterMap_cons /-
theorem filterMap_cons (f : α → Option β) (a : α) (l : List α) :
    filterMap f (a :: l) = Option.casesOn (f a) (filterMap f l) fun b => b :: filterMap f l :=
  by
  generalize eq : f a = b
  cases b
  · rw [filter_map_cons_none _ _ Eq]
  · rw [filter_map_cons_some _ _ _ Eq]
#align list.filter_map_cons List.filterMap_cons
-/

/- warning: list.filter_map_append -> List.filterMap_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (l' : List.{u1} α) (f : α -> (Option.{u2} β)), Eq.{succ u2} (List.{u2} β) (List.filterMap.{u1, u2} α β f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l l')) (Append.append.{u2} (List.{u2} β) (List.hasAppend.{u2} β) (List.filterMap.{u1, u2} α β f l) (List.filterMap.{u1, u2} α β f l'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (l' : List.{u2} α) (f : α -> (Option.{u1} β)), Eq.{succ u1} (List.{u1} β) (List.filterMap.{u2, u1} α β f (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l l')) (HAppend.hAppend.{u1, u1, u1} (List.{u1} β) (List.{u1} β) (List.{u1} β) (instHAppend.{u1} (List.{u1} β) (List.instAppendList.{u1} β)) (List.filterMap.{u2, u1} α β f l) (List.filterMap.{u2, u1} α β f l'))
Case conversion may be inaccurate. Consider using '#align list.filter_map_append List.filterMap_appendₓ'. -/
theorem filterMap_append {α β : Type _} (l l' : List α) (f : α → Option β) :
    filterMap f (l ++ l') = filterMap f l ++ filterMap f l' :=
  by
  induction' l with hd tl hl generalizing l'
  · simp
  · rw [cons_append, filter_map, filter_map]
    cases f hd <;> simp only [filter_map, hl, cons_append, eq_self_iff_true, and_self_iff]
#align list.filter_map_append List.filterMap_append

#print List.filterMap_eq_map /-
theorem filterMap_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  by
  funext l
  induction' l with a l IH; · rfl
  simp only [filter_map_cons_some (some ∘ f) _ _ rfl, IH, map_cons]; constructor <;> rfl
#align list.filter_map_eq_map List.filterMap_eq_map
-/

/- warning: list.filter_map_eq_filter -> List.filterMap_eq_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{succ u1} ((List.{u1} α) -> (List.{u1} α)) (List.filterMap.{u1, u1} α α (Option.guard.{u1} α p (fun (a : α) => _inst_1 a))) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool), Eq.{succ u1} ((List.{u1} α) -> (List.{u1} α)) (List.filterMap.{u1, u1} α α (Option.guard.{u1} α (fun (x._@.Mathlib.Data.List.Basic._hyg.42152 : α) => Eq.{1} Bool (p x._@.Mathlib.Data.List.Basic._hyg.42152) Bool.true) (fun (a : α) => instDecidableEqBool (p a) Bool.true))) (List.filter.{u1} α p)
Case conversion may be inaccurate. Consider using '#align list.filter_map_eq_filter List.filterMap_eq_filterₓ'. -/
theorem filterMap_eq_filter (p : α → Prop) [DecidablePred p] :
    filterMap (Option.guard p) = filter p := by
  funext l
  induction' l with a l IH; · rfl
  by_cases pa : p a
  · simp only [filter_map, Option.guard, IH, if_pos pa, filter_cons_of_pos _ pa]
    constructor <;> rfl
  · simp only [filter_map, Option.guard, IH, if_neg pa, filter_cons_of_neg _ pa]
#align list.filter_map_eq_filter List.filterMap_eq_filter

#print List.filterMap_filterMap /-
theorem filterMap_filterMap (f : α → Option β) (g : β → Option γ) (l : List α) :
    filterMap g (filterMap f l) = filterMap (fun x => (f x).bind g) l :=
  by
  induction' l with a l IH; · rfl
  cases' h : f a with b
  · rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH]
    simp only [h, Option.none_bind']
  rw [filter_map_cons_some _ _ _ h]
  cases' h' : g b with c <;> [rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
      rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH]] <;>
    simp only [h, h', Option.some_bind']
#align list.filter_map_filter_map List.filterMap_filterMap
-/

#print List.map_filterMap /-
theorem map_filterMap (f : α → Option β) (g : β → γ) (l : List α) :
    map g (filterMap f l) = filterMap (fun x => (f x).map g) l := by
  rw [← filter_map_eq_map, filter_map_filter_map] <;> rfl
#align list.map_filter_map List.map_filterMap
-/

#print List.filterMap_map /-
theorem filterMap_map (f : α → β) (g : β → Option γ) (l : List α) :
    filterMap g (map f l) = filterMap (g ∘ f) l := by
  rw [← filter_map_eq_map, filter_map_filter_map] <;> rfl
#align list.filter_map_map List.filterMap_map
-/

/- warning: list.filter_filter_map -> List.filter_filterMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) (p : β -> Prop) [_inst_1 : DecidablePred.{succ u2} β p] (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.filterₓ.{u2} β p (fun (a : β) => _inst_1 a) (List.filterMap.{u1, u2} α β f l)) (List.filterMap.{u1, u2} α β (fun (x : α) => Option.filter.{u2} β p (fun (a : β) => _inst_1 a) (f x)) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) (p : β -> Bool) (_inst_1 : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.filter.{u2} β p (List.filterMap.{u1, u2} α β f _inst_1)) (List.filterMap.{u1, u2} α β (fun (x : α) => Option.filter.{u2} β p (f x)) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.filter_filter_map List.filter_filterMapₓ'. -/
theorem filter_filterMap (f : α → Option β) (p : β → Prop) [DecidablePred p] (l : List α) :
    filter p (filterMap f l) = filterMap (fun x => (f x).filter p) l := by
  rw [← filter_map_eq_filter, filter_map_filter_map] <;> rfl
#align list.filter_filter_map List.filter_filterMap

/- warning: list.filter_map_filter -> List.filterMap_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (f : α -> (Option.{u2} β)) (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.filterMap.{u1, u2} α β f (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) (List.filterMap.{u1, u2} α β (fun (x : α) => ite.{succ u2} (Option.{u2} β) (p x) (_inst_1 x) (f x) (Option.none.{u2} β)) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Bool) (_inst_1 : α -> (Option.{u2} β)) (f : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.filterMap.{u1, u2} α β _inst_1 (List.filter.{u1} α p f)) (List.filterMap.{u1, u2} α β (fun (x : α) => ite.{succ u2} (Option.{u2} β) (Eq.{1} Bool (p x) Bool.true) (instDecidableEqBool (p x) Bool.true) (_inst_1 x) (Option.none.{u2} β)) f)
Case conversion may be inaccurate. Consider using '#align list.filter_map_filter List.filterMap_filterₓ'. -/
theorem filterMap_filter (p : α → Prop) [DecidablePred p] (f : α → Option β) (l : List α) :
    filterMap f (filter p l) = filterMap (fun x => if p x then f x else none) l :=
  by
  rw [← filter_map_eq_filter, filter_map_filter_map]; congr
  funext x
  show (Option.guard p x).bind f = ite (p x) (f x) none
  by_cases h : p x
  · simp only [Option.guard, if_pos h, Option.some_bind']
  · simp only [Option.guard, if_neg h, Option.none_bind']
#align list.filter_map_filter List.filterMap_filter

#print List.filterMap_some /-
@[simp]
theorem filterMap_some (l : List α) : filterMap some l = l := by
  rw [filter_map_eq_map] <;> apply map_id
#align list.filter_map_some List.filterMap_some
-/

/- warning: list.map_filter_map_some_eq_filter_map_is_some -> List.map_filterMap_some_eq_filter_map_is_some is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) (l : List.{u1} α), Eq.{succ u2} (List.{u2} (Option.{u2} β)) (List.map.{u2, u2} β (Option.{u2} β) (Option.some.{u2} β) (List.filterMap.{u1, u2} α β f l)) (List.filterₓ.{u2} (Option.{u2} β) (fun (b : Option.{u2} β) => coeSort.{1, 1} Bool Prop coeSortBool (Option.isSome.{u2} β b)) (fun (a : Option.{u2} β) => Bool.decidableEq (Option.isSome.{u2} β a) Bool.true) (List.map.{u1, u2} α (Option.{u2} β) f l))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> (Option.{u2} β)) (l : List.{u1} α), Eq.{succ u2} (List.{u2} (Option.{u2} β)) (List.map.{u2, u2} β (Option.{u2} β) (Option.some.{u2} β) (List.filterMap.{u1, u2} α β f l)) (List.filter.{u2} (Option.{u2} β) (fun (a : Option.{u2} β) => Option.isSome.{u2} β a) (List.map.{u1, u2} α (Option.{u2} β) f l))
Case conversion may be inaccurate. Consider using '#align list.map_filter_map_some_eq_filter_map_is_some List.map_filterMap_some_eq_filter_map_is_someₓ'. -/
theorem map_filterMap_some_eq_filter_map_is_some (f : α → Option β) (l : List α) :
    (l.filterMap f).map some = (l.map f).filter fun b => b.isSome :=
  by
  induction' l with x xs ih
  · simp
  · cases h : f x <;> rw [List.filterMap_cons, h] <;> simp [h, ih]
#align list.map_filter_map_some_eq_filter_map_is_some List.map_filterMap_some_eq_filter_map_is_some

#print List.mem_filterMap /-
@[simp]
theorem mem_filterMap (f : α → Option β) (l : List α) {b : β} :
    b ∈ filterMap f l ↔ ∃ a, a ∈ l ∧ f a = some b :=
  by
  induction' l with a l IH
  · constructor
    · intro H
      cases H
    · rintro ⟨_, H, _⟩
      cases H
  cases' h : f a with b'
  · have : f a ≠ some b := by
      rw [h]
      intro
      contradiction
    simp only [filter_map_cons_none _ _ h, IH, mem_cons_iff, or_and_right, exists_or,
      exists_eq_left, this, false_or_iff]
  · have : f a = some b ↔ b = b' := by
      constructor <;> intro t
      · rw [t] at h <;> injection h
      · exact t.symm ▸ h
    simp only [filter_map_cons_some _ _ _ h, IH, mem_cons_iff, or_and_right, exists_or, this,
      exists_eq_left]
#align list.mem_filter_map List.mem_filterMap
-/

#print List.filterMap_join /-
@[simp]
theorem filterMap_join (f : α → Option β) (L : List (List α)) :
    filterMap f (join L) = join (map (filterMap f) L) :=
  by
  induction' L with hd tl ih
  · rfl
  · rw [map, join, join, filter_map_append, ih]
#align list.filter_map_join List.filterMap_join
-/

#print List.map_filterMap_of_inv /-
theorem map_filterMap_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x)
    (l : List α) : map g (filterMap f l) = l := by simp only [map_filter_map, H, filter_map_some]
#align list.map_filter_map_of_inv List.map_filterMap_of_inv
-/

theorem length_filter_le (p : α → Prop) [DecidablePred p] (l : List α) :
    (l.filter p).length ≤ l.length :=
  (List.filter_sublist _).length_le
#align list.length_filter_le List.length_filter_leₓ

#print List.length_filterMap_le /-
theorem length_filterMap_le (f : α → Option β) (l : List α) :
    (List.filterMap f l).length ≤ l.length :=
  by
  rw [← List.length_map some, List.map_filterMap_some_eq_filter_map_is_some, ← List.length_map f]
  apply List.length_filter_le
#align list.length_filter_map_le List.length_filterMap_le
-/

#print List.Sublist.filterMap /-
theorem Sublist.filterMap (f : α → Option β) {l₁ l₂ : List α} (s : l₁ <+ l₂) :
    filterMap f l₁ <+ filterMap f l₂ := by
  induction' s with l₁ l₂ a s IH l₁ l₂ a s IH <;> simp only [filter_map] <;> cases' f a with b <;>
    simp only [filter_map, IH, sublist.cons, sublist.cons2]
#align list.sublist.filter_map List.Sublist.filterMap
-/

#print List.Sublist.map /-
theorem Sublist.map (f : α → β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filterMap_eq_map f ▸ s.filterMap _
#align list.sublist.map List.Sublist.map
-/

/-! ### reduce_option -/


#print List.reduceOption_cons_of_some /-
@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_self_iff]
#align list.reduce_option_cons_of_some List.reduceOption_cons_of_some
-/

#print List.reduceOption_cons_of_none /-
@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduce_option, filter_map, id.def]
#align list.reduce_option_cons_of_none List.reduceOption_cons_of_none
-/

#print List.reduceOption_nil /-
@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl
#align list.reduce_option_nil List.reduceOption_nil
-/

#print List.reduceOption_map /-
@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) :=
  by
  induction' l with hd tl hl
  · simp only [reduce_option_nil, map_nil]
  ·
    cases hd <;>
      simpa only [true_and_iff, Option.map_some', map, eq_self_iff_true,
        reduce_option_cons_of_some] using hl
#align list.reduce_option_map List.reduceOption_map
-/

#print List.reduceOption_append /-
theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id
#align list.reduce_option_append List.reduceOption_append
-/

#print List.reduceOption_length_le /-
theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length :=
  by
  induction' l with hd tl hl
  · simp only [reduce_option_nil, length]
  · cases hd
    · exact Nat.le_succ_of_le hl
    · simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl
#align list.reduce_option_length_le List.reduceOption_length_le
-/

#print List.reduceOption_length_eq_iff /-
theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x :=
  by
  induction' l with hd tl hl
  ·
    simp only [forall_const, reduce_option_nil, not_mem_nil, forall_prop_of_false, eq_self_iff_true,
      length, not_false_iff]
  · cases hd
    · simp only [mem_cons_iff, forall_eq_or_imp, Bool.coeSort_false, false_and_iff,
        reduce_option_cons_of_none, length, Option.isSome_none, iff_false_iff]
      intro H
      have := reduce_option_length_le tl
      rw [H] at this
      exact absurd (Nat.lt_succ_self _) (not_lt_of_le this)
    ·
      simp only [hl, true_and_iff, mem_cons_iff, forall_eq_or_imp, add_left_inj, Bool.coeSort_true,
        length, Option.isSome_some, reduce_option_cons_of_some]
#align list.reduce_option_length_eq_iff List.reduceOption_length_eq_iff
-/

#print List.reduceOption_length_lt_iff /-
theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l :=
  by
  rw [(reduce_option_length_le l).lt_iff_ne, Ne, reduce_option_length_eq_iff]
  induction l <;> simp [*]
  rw [eq_comm, ← Option.not_isSome_iff_eq_none, Decidable.imp_iff_not_or]
#align list.reduce_option_length_lt_iff List.reduceOption_length_lt_iff
-/

#print List.reduceOption_singleton /-
theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
#align list.reduce_option_singleton List.reduceOption_singleton
-/

#print List.reduceOption_concat /-
theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList :=
  by
  induction' l with hd tl hl generalizing x
  · cases x <;> simp [Option.toList]
  · simp only [concat_eq_append, reduce_option_append] at hl
    cases hd <;> simp [hl, reduce_option_append]
#align list.reduce_option_concat List.reduceOption_concat
-/

#print List.reduceOption_concat_of_some /-
theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]
#align list.reduce_option_concat_of_some List.reduceOption_concat_of_some
-/

#print List.reduceOption_mem_iff /-
theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduce_option, id.def, mem_filter_map, exists_eq_right]
#align list.reduce_option_mem_iff List.reduceOption_mem_iff
-/

#print List.reduceOption_get?_iff /-
theorem reduceOption_get?_iff {l : List (Option α)} {x : α} :
    (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduceOption.nth i = some x := by
  rw [← mem_iff_nth, ← mem_iff_nth, reduce_option_mem_iff]
#align list.reduce_option_nth_iff List.reduceOption_get?_iff
-/

/-! ### filter -/


section Filter

variable {p : α → Prop} [DecidablePred p]

/- warning: list.filter_singleton -> List.filter_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α}, Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a (List.nil.{u1} α))) (ite.{succ u1} (List.{u1} α) (p a) (_inst_1 a) (List.cons.{u1} α a (List.nil.{u1} α)) (List.nil.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α}, Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p (List.cons.{u1} α _inst_1 (List.nil.{u1} α))) (cond.{u1} (List.{u1} α) (p _inst_1) (List.cons.{u1} α _inst_1 (List.nil.{u1} α)) (List.nil.{u1} α))
Case conversion may be inaccurate. Consider using '#align list.filter_singleton List.filter_singletonₓ'. -/
theorem filter_singleton {a : α} : [a].filter p = if p a then [a] else [] :=
  rfl
#align list.filter_singleton List.filter_singleton

/- warning: list.filter_eq_foldr -> List.filter_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_2 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l) (List.foldr.{u1, u1} α (List.{u1} α) (fun (a : α) (out : List.{u1} α) => ite.{succ u1} (List.{u1} α) (p a) (_inst_2 a) (List.cons.{u1} α a out) out) (List.nil.{u1} α) l)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_2 : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p _inst_2) (List.foldr.{u1, u1} α (List.{u1} α) (fun (a : α) (out : List.{u1} α) => cond.{u1} (List.{u1} α) (p a) (List.cons.{u1} α a out) out) (List.nil.{u1} α) _inst_2)
Case conversion may be inaccurate. Consider using '#align list.filter_eq_foldr List.filter_eq_foldrₓ'. -/
theorem filter_eq_foldr (p : α → Prop) [DecidablePred p] (l : List α) :
    filter p l = foldr (fun a out => if p a then a :: out else out) [] l := by
  induction l <;> simp [*, Filter]
#align list.filter_eq_foldr List.filter_eq_foldr

/- warning: list.filter_congr' -> List.filter_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : DecidablePred.{succ u1} α q] {l : List.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (Iff (p x) (q x))) -> (Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l) (List.filterₓ.{u1} α q (fun (a : α) => _inst_3 a) l))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {q : α -> Bool} {_inst_2 : List.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x _inst_2) -> (Iff (Eq.{1} Bool (p x) Bool.true) (Eq.{1} Bool (q x) Bool.true))) -> (Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p _inst_2) (List.filter.{u1} α q _inst_2))
Case conversion may be inaccurate. Consider using '#align list.filter_congr' List.filter_congr'ₓ'. -/
theorem filter_congr' {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ {l : List α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
  | [], _ => rfl
  | a :: l, h => by
    rw [forall_mem_cons] at h <;> by_cases pa : p a <;>
          [simp only [filter_cons_of_pos _ pa, filter_cons_of_pos _ (h.1.1 pa), filter_congr' h.2],
          simp only [filter_cons_of_neg _ pa, filter_cons_of_neg _ (mt h.1.2 pa),
            filter_congr' h.2]] <;>
        constructor <;>
      rfl
#align list.filter_congr' List.filter_congr'

/- warning: list.filter_subset -> List.filter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), HasSubset.Subset.{u1} (List.{u1} α) (List.hasSubset.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l) l
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} (_inst_1 : List.{u1} α), HasSubset.Subset.{u1} (List.{u1} α) (List.instHasSubsetList.{u1} α) (List.filter.{u1} α p _inst_1) _inst_1
Case conversion may be inaccurate. Consider using '#align list.filter_subset List.filter_subsetₓ'. -/
@[simp]
theorem filter_subset (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).Subset
#align list.filter_subset List.filter_subset

/- warning: list.of_mem_filter -> List.of_mem_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} {l : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) -> (p a)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α} {a : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) _inst_1 (List.filter.{u1} α p a)) -> (Eq.{1} Bool (p _inst_1) Bool.true)
Case conversion may be inaccurate. Consider using '#align list.of_mem_filter List.of_mem_filterₓ'. -/
theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
  | b :: l, ain =>
    if pb : p b then
      have : a ∈ b :: filter p l := by simpa only [filter_cons_of_pos _ pb] using ain
      Or.elim (eq_or_mem_of_mem_cons this) (fun this : a = b => by rw [← this] at pb; exact pb)
        fun this : a ∈ filter p l => of_mem_filter this
    else by simp only [filter_cons_of_neg _ pb] at ain; exact of_mem_filter ain
#align list.of_mem_filter List.of_mem_filter

/- warning: list.mem_of_mem_filter -> List.mem_of_mem_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} {l : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α} {a : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) _inst_1 (List.filter.{u1} α p a)) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) _inst_1 a)
Case conversion may be inaccurate. Consider using '#align list.mem_of_mem_filter List.mem_of_mem_filterₓ'. -/
theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h
#align list.mem_of_mem_filter List.mem_of_mem_filter

/- warning: list.mem_filter_of_mem -> List.mem_filter_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} {l : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : α} {a : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) _inst_1 a) -> (Eq.{1} Bool (p _inst_1) Bool.true) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) _inst_1 (List.filter.{u1} α p a))
Case conversion may be inaccurate. Consider using '#align list.mem_filter_of_mem List.mem_filter_of_memₓ'. -/
theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
  | _ :: l, Or.inl rfl, pa => by rw [filter_cons_of_pos _ pa] <;> apply mem_cons_self
  | b :: l, Or.inr ain, pa =>
    if pb : p b then by
      rw [filter_cons_of_pos _ pb] <;> apply mem_cons_of_mem <;> apply mem_filter_of_mem ain pa
    else by rw [filter_cons_of_neg _ pb] <;> apply mem_filter_of_mem ain pa
#align list.mem_filter_of_mem List.mem_filter_of_mem

/- warning: list.mem_filter -> List.mem_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {a : α} {l : List.{u1} α}, Iff (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : α} {_inst_1 : α -> Bool} {a : List.{u1} α}, Iff (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) p (List.filter.{u1} α _inst_1 a)) (And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) p a) (Eq.{1} Bool (_inst_1 p) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.mem_filter List.mem_filterₓ'. -/
@[simp]
theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
  ⟨fun h => ⟨mem_of_mem_filter h, of_mem_filter h⟩, fun ⟨h₁, h₂⟩ => mem_filter_of_mem h₁ h₂⟩
#align list.mem_filter List.mem_filter

/- warning: list.monotone_filter_left -> List.monotone_filter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_2 : DecidablePred.{succ u1} α p] {{l : List.{u1} α}} {{l' : List.{u1} α}}, (HasSubset.Subset.{u1} (List.{u1} α) (List.hasSubset.{u1} α) l l') -> (HasSubset.Subset.{u1} (List.{u1} α) (List.hasSubset.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l) (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l'))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) {{_inst_2 : List.{u1} α}} {{l : List.{u1} α}}, (HasSubset.Subset.{u1} (List.{u1} α) (List.instHasSubsetList.{u1} α) _inst_2 l) -> (HasSubset.Subset.{u1} (List.{u1} α) (List.instHasSubsetList.{u1} α) (List.filter.{u1} α p _inst_2) (List.filter.{u1} α p l))
Case conversion may be inaccurate. Consider using '#align list.monotone_filter_left List.monotone_filter_leftₓ'. -/
theorem monotone_filter_left (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l ⊆ l') :
    filter p l ⊆ filter p l' := by
  intro x hx
  rw [mem_filter] at hx⊢
  exact ⟨h hx.left, hx.right⟩
#align list.monotone_filter_left List.monotone_filter_left

/- warning: list.filter_eq_self -> List.filter_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l) l) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p _inst_1) _inst_1) (forall (a : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Eq.{1} Bool (p a) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.filter_eq_self List.filter_eq_selfₓ'. -/
theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a :=
  by
  induction' l with a l ih
  · exact iff_of_true rfl (forall_mem_nil _)
  rw [forall_mem_cons]; by_cases p a
  · rw [filter_cons_of_pos _ h, cons_inj, ih, and_iff_right h]
  · refine' iff_of_false (fun hl => h <| of_mem_filter (_ : a ∈ Filter p (a :: l))) (mt And.left h)
    rw [hl]
    exact mem_cons_self _ _
#align list.filter_eq_self List.filter_eq_self

/- warning: list.filter_length_eq_length -> List.filter_length_eq_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{1} Nat (List.length.{u1} α (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) (List.length.{u1} α l)) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{1} Nat (List.length.{u1} α (List.filter.{u1} α p _inst_1)) (List.length.{u1} α _inst_1)) (forall (a : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Eq.{1} Bool (p a) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.filter_length_eq_length List.filter_length_eq_lengthₓ'. -/
theorem filter_length_eq_length {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a :=
  Iff.trans ⟨l.filter_sublist.eq_of_length, congr_arg List.length⟩ filter_eq_self
#align list.filter_length_eq_length List.filter_length_eq_length

/- warning: list.filter_eq_nil -> List.filter_eq_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (List.nil.{u1} α)) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Not (p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p _inst_1) (List.nil.{u1} α)) (forall (a : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a _inst_1) -> (Not (Eq.{1} Bool (p a) Bool.true)))
Case conversion may be inaccurate. Consider using '#align list.filter_eq_nil List.filter_eq_nilₓ'. -/
theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a := by
  simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]
#align list.filter_eq_nil List.filter_eq_nil

variable (p)

/- warning: list.sublist.filter -> List.Sublist.filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Sublist.{u1} α (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l₁) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l₂))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) {_inst_1 : List.{u1} α} {l₁ : List.{u1} α}, (List.Sublist.{u1} α _inst_1 l₁) -> (List.Sublist.{u1} α (List.filter.{u1} α p _inst_1) (List.filter.{u1} α p l₁))
Case conversion may be inaccurate. Consider using '#align list.sublist.filter List.Sublist.filterₓ'. -/
theorem Sublist.filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
  filterMap_eq_filter p ▸ s.filterMap _
#align list.sublist.filter List.Sublist.filter

/- warning: list.monotone_filter_right -> List.monotone_filter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α) {{p : α -> Prop}} {{q : α -> Prop}} [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : DecidablePred.{succ u1} α q], (LE.le.{u1} (α -> Prop) (Pi.hasLe.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.le)) p q) -> (List.Sublist.{u1} α (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l) (List.filterₓ.{u1} α q (fun (a : α) => _inst_3 a) l))
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α) {{p : α -> Bool}} {{q : α -> Bool}}, (forall (a : α), (Eq.{1} Bool (p a) Bool.true) -> (Eq.{1} Bool (q a) Bool.true)) -> (List.Sublist.{u1} α (List.filter.{u1} α p l) (List.filter.{u1} α q l))
Case conversion may be inaccurate. Consider using '#align list.monotone_filter_right List.monotone_filter_rightₓ'. -/
theorem monotone_filter_right (l : List α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : l.filter p <+ l.filter q :=
  by
  induction' l with hd tl IH
  · rfl
  · by_cases hp : p hd
    · rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)]
      exact IH.cons_cons hd
    · rw [filter_cons_of_neg _ hp]
      by_cases hq : q hd
      · rw [filter_cons_of_pos _ hq]
        exact sublist_cons_of_sublist hd IH
      · rw [filter_cons_of_neg _ hq]
        exact IH
#align list.monotone_filter_right List.monotone_filter_right

/- warning: list.map_filter -> List.map_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (f : β -> α) (l : List.{u2} β), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) (List.map.{u2, u1} β α f l)) (List.map.{u2, u1} β α f (List.filterₓ.{u2} β (Function.comp.{succ u2, succ u1, 1} β α Prop p f) (fun (a : β) => _inst_1 (f a)) l))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : α -> Bool) (_inst_1 : β -> α) (f : List.{u2} β), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p (List.map.{u2, u1} β α _inst_1 f)) (List.map.{u2, u1} β α _inst_1 (List.filter.{u2} β (Function.comp.{succ u2, succ u1, 1} β α Bool p _inst_1) f))
Case conversion may be inaccurate. Consider using '#align list.map_filter List.map_filterₓ'. -/
theorem map_filter (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := by
  rw [← filter_map_eq_map, filter_filter_map, filter_map_filter] <;> rfl
#align list.map_filter List.map_filter

/- warning: list.filter_filter -> List.filter_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (q : α -> Prop) [_inst_2 : DecidablePred.{succ u1} α q] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) (List.filterₓ.{u1} α q (fun (a : α) => _inst_2 a) l)) (List.filterₓ.{u1} α (fun (a : α) => And (p a) (q a)) (fun (a : α) => And.decidable (p a) (q a) (_inst_1 a) (_inst_2 a)) l)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : α -> Bool) (q : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α p (List.filter.{u1} α _inst_1 q)) (List.filter.{u1} α (fun (a : α) => Decidable.decide (And (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (_inst_1 a) Bool.true)) (instDecidableAnd (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (_inst_1 a) Bool.true) (instDecidableEqBool (p a) Bool.true) (instDecidableEqBool (_inst_1 a) Bool.true))) q)
Case conversion may be inaccurate. Consider using '#align list.filter_filter List.filter_filterₓ'. -/
@[simp]
theorem filter_filter (q) [DecidablePred q] :
    ∀ l, filter p (filter q l) = filter (fun a => p a ∧ q a) l
  | [] => rfl
  | a :: l => by
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, Filter, if_true, if_false, true_and_iff, false_and_iff, filter_filter l,
        eq_self_iff_true]
#align list.filter_filter List.filter_filter

/- warning: list.filter_true -> List.filter_true is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {h : DecidablePred.{succ u1} α (fun (a : α) => True)} (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α (fun (_x : α) => True) h l) l
but is expected to have type
  forall {α : Type.{u1}} (h : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α (fun (x._@.Mathlib.Data.List.Basic._hyg.46259 : α) => Bool.true) h) h
Case conversion may be inaccurate. Consider using '#align list.filter_true List.filter_trueₓ'. -/
@[simp]
theorem filter_true {h : DecidablePred fun a : α => True} (l : List α) :
    @filter α (fun _ => True) h l = l := by convert filter_eq_self.2 fun _ _ => trivial
#align list.filter_true List.filter_true

/- warning: list.filter_false -> List.filter_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {h : DecidablePred.{succ u1} α (fun (a : α) => False)} (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α (fun (_x : α) => False) h l) (List.nil.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (h : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α (fun (x._@.Mathlib.Data.List.Basic._hyg.46309 : α) => Bool.false) h) (List.nil.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.filter_false List.filter_falseₓ'. -/
@[simp]
theorem filter_false {h : DecidablePred fun a : α => False} (l : List α) :
    @filter α (fun _ => False) h l = [] := by convert filter_eq_nil.2 fun _ _ => id
#align list.filter_false List.filter_false

/- warning: list.span_eq_take_drop -> List.span_eq_take_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (Prod.{u1, u1} (List.{u1} α) (List.{u1} α)) (List.spanₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (Prod.mk.{u1, u1} (List.{u1} α) (List.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l) (List.dropWhileₓ.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{succ u1} (Prod.{u1, u1} (List.{u1} α) (List.{u1} α)) (List.span.{u1} α p _inst_1) (Prod.mk.{u1, u1} (List.{u1} α) (List.{u1} α) (List.takeWhile.{u1} α p _inst_1) (List.dropWhile.{u1} α p _inst_1))
Case conversion may be inaccurate. Consider using '#align list.span_eq_take_drop List.span_eq_take_dropₓ'. -/
@[simp]
theorem span_eq_take_drop : ∀ l : List α, span p l = (takeWhile p l, dropWhile p l)
  | [] => rfl
  | a :: l =>
    if pa : p a then by simp only [span, if_pos pa, span_eq_take_drop l, take_while, drop_while]
    else by simp only [span, take_while, drop_while, if_neg pa]
#align list.span_eq_take_drop List.span_eq_take_drop

/- warning: list.take_while_append_drop -> List.takeWhile_append_drop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l) (List.dropWhileₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) l
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{succ u1} (List.{u1} α) (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) (List.takeWhile.{u1} α p _inst_1) (List.dropWhile.{u1} α p _inst_1)) _inst_1
Case conversion may be inaccurate. Consider using '#align list.take_while_append_drop List.takeWhile_append_dropₓ'. -/
@[simp]
theorem takeWhile_append_drop : ∀ l : List α, takeWhile p l ++ dropWhile p l = l
  | [] => rfl
  | a :: l =>
    if pa : p a then by
      rw [take_while, drop_while, if_pos pa, if_pos pa, cons_append, take_while_append_drop l]
    else by rw [take_while, drop_while, if_neg pa, if_neg pa, nil_append]
#align list.take_while_append_drop List.takeWhile_append_drop

/- warning: list.drop_while_nth_le_zero_not -> List.dropWhile_nthLe_zero_not is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α) (hl : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.length.{u1} α (List.dropWhileₓ.{u1} α p (fun (a : α) => _inst_1 a) l))), Not (p (List.nthLe.{u1} α (List.dropWhileₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) hl))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α) (l : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.length.{u1} α (List.dropWhile.{u1} α p _inst_1))), Not (Eq.{1} Bool (p (List.nthLe.{u1} α (List.dropWhile.{u1} α p _inst_1) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) l)) Bool.true)
Case conversion may be inaccurate. Consider using '#align list.drop_while_nth_le_zero_not List.dropWhile_nthLe_zero_notₓ'. -/
theorem dropWhile_nthLe_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).nthLe 0 hl) :=
  by
  induction' l with hd tl IH
  · cases hl
  · simp only [drop_while]
    split_ifs with hp
    · exact IH _
    · simpa using hp
#align list.drop_while_nth_le_zero_not List.dropWhile_nthLe_zero_not

variable {p} {l : List α}

/- warning: list.drop_while_eq_nil_iff -> List.dropWhile_eq_nil_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.dropWhileₓ.{u1} α p (fun (a : α) => _inst_1 a) l) (List.nil.{u1} α)) (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (p x))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.dropWhile.{u1} α p _inst_1) (List.nil.{u1} α)) (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x _inst_1) -> (Eq.{1} Bool (p x) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.drop_while_eq_nil_iff List.dropWhile_eq_nil_iffₓ'. -/
@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x :=
  by
  induction' l with x xs IH
  · simp [drop_while]
  · by_cases hp : p x <;> simp [hp, drop_while, IH]
#align list.drop_while_eq_nil_iff List.dropWhile_eq_nil_iff

/- warning: list.take_while_eq_self_iff -> List.takeWhile_eq_self_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l) l) (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (p x))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p _inst_1) _inst_1) (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x _inst_1) -> (Eq.{1} Bool (p x) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.take_while_eq_self_iff List.takeWhile_eq_self_iffₓ'. -/
@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x :=
  by
  induction' l with x xs IH
  · simp [take_while]
  · by_cases hp : p x <;> simp [hp, take_while, IH]
#align list.take_while_eq_self_iff List.takeWhile_eq_self_iff

/- warning: list.take_while_eq_nil_iff -> List.takeWhile_eq_nil_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l) (List.nil.{u1} α)) (forall (hl : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.length.{u1} α l)), Not (p (List.nthLe.{u1} α l (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) hl)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Iff (Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p _inst_1) (List.nil.{u1} α)) (forall (hl : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.length.{u1} α _inst_1)), Not (Eq.{1} Bool (p (List.nthLe.{u1} α _inst_1 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) hl)) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.take_while_eq_nil_iff List.takeWhile_eq_nil_iffₓ'. -/
@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) :=
  by
  induction' l with x xs IH
  · simp
  · by_cases hp : p x <;> simp [hp, take_while, IH]
#align list.take_while_eq_nil_iff List.takeWhile_eq_nil_iff

/- warning: list.mem_take_while_imp -> List.mem_takeWhile_imp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l)) -> (p x)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α} {l : α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l (List.takeWhile.{u1} α p _inst_1)) -> (Eq.{1} Bool (p l) Bool.true)
Case conversion may be inaccurate. Consider using '#align list.mem_take_while_imp List.mem_takeWhile_impₓ'. -/
theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x :=
  by
  induction' l with hd tl IH
  · simpa [take_while] using hx
  · simp only [take_while] at hx
    split_ifs  at hx
    · rw [mem_cons_iff] at hx
      rcases hx with (rfl | hx)
      · exact h
      · exact IH hx
    · simpa using hx
#align list.mem_take_while_imp List.mem_takeWhile_imp

/- warning: list.take_while_take_while -> List.takeWhile_takeWhile is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : DecidablePred.{succ u1} α q] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_2 a) (List.takeWhile.{u1} α q (fun (a : α) => _inst_3 a) l)) (List.takeWhile.{u1} α (fun (a : α) => And (p a) (q a)) (fun (a : α) => And.decidable (p a) (q a) (_inst_2 a) (_inst_3 a)) l)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (q : α -> Bool) (_inst_2 : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (List.takeWhile.{u1} α q _inst_2)) (List.takeWhile.{u1} α (fun (a : α) => Decidable.decide (And (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (q a) Bool.true)) (instDecidableAnd (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (q a) Bool.true) (instDecidableEqBool (p a) Bool.true) (instDecidableEqBool (q a) Bool.true))) _inst_2)
Case conversion may be inaccurate. Consider using '#align list.take_while_take_while List.takeWhile_takeWhileₓ'. -/
theorem takeWhile_takeWhile (p q : α → Prop) [DecidablePred p] [DecidablePred q] (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l :=
  by
  induction' l with hd tl IH
  · simp [take_while]
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [take_while, hp, hq, IH]
#align list.take_while_take_while List.takeWhile_takeWhile

/- warning: list.take_while_idem -> List.takeWhile_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l)) (List.takeWhile.{u1} α p (fun (a : α) => _inst_1 a) l)
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Bool} {_inst_1 : List.{u1} α}, Eq.{succ u1} (List.{u1} α) (List.takeWhile.{u1} α p (List.takeWhile.{u1} α p _inst_1)) (List.takeWhile.{u1} α p _inst_1)
Case conversion may be inaccurate. Consider using '#align list.take_while_idem List.takeWhile_idemₓ'. -/
theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [take_while_take_while, and_self_iff]
#align list.take_while_idem List.takeWhile_idem

end Filter

/-! ### erasep -/


section Erasep

variable {p : α → Prop} [DecidablePred p]

@[simp]
theorem eraseP_nil : [].erasep p = [] :=
  rfl
#align list.erasep_nil List.eraseP_nilₓ

theorem eraseP_cons (a : α) (l : List α) : (a :: l).erasep p = if p a then l else a :: l.erasep p :=
  rfl
#align list.erasep_cons List.eraseP_consₓ

@[simp]
theorem eraseP_cons_of_pos {a : α} {l : List α} (h : p a) : (a :: l).erasep p = l := by
  simp [erasep_cons, h]
#align list.erasep_cons_of_pos List.eraseP_cons_of_posₓ

@[simp]
theorem eraseP_cons_of_neg {a : α} {l : List α} (h : ¬p a) : (a :: l).erasep p = a :: l.erasep p :=
  by simp [erasep_cons, h]
#align list.erasep_cons_of_neg List.eraseP_cons_of_negₓ

theorem eraseP_of_forall_not {l : List α} (h : ∀ a ∈ l, ¬p a) : l.erasep p = l := by
  induction' l with _ _ ih <;> [rfl, simp [h _ (Or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]]
#align list.erasep_of_forall_not List.eraseP_of_forall_notₓ

theorem exists_of_eraseP {l : List α} {a} (al : a ∈ l) (pa : p a) :
    ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
  by
  induction' l with b l IH; · cases al
  by_cases pb : p b
  · exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩
  · rcases al with (rfl | al)
    · exact pb.elim pa
    rcases IH al with ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩
    exact ⟨c, b :: l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩, h₂, by rw [h₃] <;> rfl, by simp [pb, h₄]⟩
#align list.exists_of_erasep List.exists_of_erasePₓ

theorem exists_or_eq_self_of_eraseP (p : α → Prop) [DecidablePred p] (l : List α) :
    l.erasep p = l ∨
      ∃ a l₁ l₂, (∀ b ∈ l₁, ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
  by
  by_cases h : ∃ a ∈ l, p a
  · rcases h with ⟨a, ha, pa⟩
    exact Or.inr (exists_of_erasep ha pa)
  · simp at h
    exact Or.inl (erasep_of_forall_not h)
#align list.exists_or_eq_self_of_erasep List.exists_or_eq_self_of_erasePₓ

@[simp]
theorem length_eraseP_of_mem {l : List α} {a} (al : a ∈ l) (pa : p a) :
    length (l.erasep p) = pred (length l) := by
  rcases exists_of_erasep al pa with ⟨_, l₁, l₂, _, _, e₁, e₂⟩ <;> rw [e₂] <;>
      simp [-add_comm, e₁] <;>
    rfl
#align list.length_erasep_of_mem List.length_eraseP_of_memₓ

@[simp]
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.erasep p).length + 1 = l.length :=
  by
  let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_eraseP al pa
  rw [h₂, h₁, length_append, length_append]
  rfl
#align list.length_erasep_add_one List.length_eraseP_add_oneₓ

theorem eraseP_append_left {a : α} (pa : p a) :
    ∀ {l₁ : List α} (l₂), a ∈ l₁ → (l₁ ++ l₂).erasep p = l₁.erasep p ++ l₂
  | x :: xs, l₂, h => by
    by_cases h' : p x <;> simp [h']
    rw [erasep_append_left l₂ (mem_of_ne_of_mem (mt _ h') h)]
    rintro rfl; exact pa
#align list.erasep_append_left List.eraseP_append_leftₓ

theorem eraseP_append_right :
    ∀ {l₁ : List α} (l₂), (∀ b ∈ l₁, ¬p b) → (l₁ ++ l₂).erasep p = l₁ ++ l₂.erasep p
  | [], l₂, h => rfl
  | x :: xs, l₂, h => by
    simp [(forall_mem_cons.1 h).1, erasep_append_right _ (forall_mem_cons.1 h).2]
#align list.erasep_append_right List.eraseP_append_rightₓ

theorem eraseP_sublist (l : List α) : l.erasep p <+ l := by
  rcases exists_or_eq_self_of_erasep p l with (h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩) <;> [rw [h],
    · rw [h₄, h₃]
      simp]
#align list.erasep_sublist List.eraseP_sublistₓ

theorem eraseP_subset (l : List α) : l.erasep p ⊆ l :=
  (eraseP_sublist l).Subset
#align list.erasep_subset List.eraseP_subsetₓ

theorem Sublist.eraseP {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
  by
  induction s
  case slnil => rfl
  case cons l₁ l₂ a s IH =>
    by_cases h : p a <;> simp [h]
    exacts[IH.trans (erasep_sublist _), IH.cons _ _ _]
  case cons2 l₁ l₂ a s IH =>
    by_cases h : p a <;> simp [h]
    exacts[s, IH.cons2 _ _ _]
#align list.sublist.erasep List.Sublist.erasePₓ

theorem mem_of_mem_eraseP {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
  @eraseP_subset _ _ _ _ _
#align list.mem_of_mem_erasep List.mem_of_mem_erasePₓ

@[simp]
theorem mem_eraseP_of_neg {a : α} {l : List α} (pa : ¬p a) : a ∈ l.erasep p ↔ a ∈ l :=
  ⟨mem_of_mem_eraseP, fun al =>
    by
    rcases exists_or_eq_self_of_erasep p l with (h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩)
    · rwa [h]
    · rw [h₄]
      rw [h₃] at al
      have : a ≠ c := by
        rintro rfl
        exact pa.elim h₂
      simpa [this] using al⟩
#align list.mem_erasep_of_neg List.mem_eraseP_of_negₓ

theorem eraseP_map (f : β → α) : ∀ l : List β, (map f l).erasep p = map f (l.erasep (p ∘ f))
  | [] => rfl
  | b :: l => by by_cases p (f b) <;> simp [h, erasep_map l]
#align list.erasep_map List.eraseP_mapₓ

@[simp]
theorem extractP_eq_find?_eraseP : ∀ l : List α, extractp p l = (find? p l, eraseP p l)
  | [] => rfl
  | a :: l => by by_cases pa : p a <;> simp [extractp, pa, extractp_eq_find_erasep l]
#align list.extractp_eq_find_erasep List.extractP_eq_find?_erasePₓ

end Erasep

/-! ### erase -/


section Erase

variable [DecidableEq α]

#print List.erase_nil /-
@[simp]
theorem erase_nil (a : α) : [].erase a = [] :=
  rfl
#align list.erase_nil List.erase_nil
-/

theorem erase_cons (a b : α) (l : List α) :
    (b :: l).erase a = if b = a then l else b :: l.erase a :=
  rfl
#align list.erase_cons List.erase_consₓ

@[simp]
theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l := by
  simp only [erase_cons, if_pos rfl]
#align list.erase_cons_head List.erase_cons_headₓ

@[simp]
theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) : (b :: l).erase a = b :: l.erase a := by
  simp only [erase_cons, if_neg h] <;> constructor <;> rfl
#align list.erase_cons_tail List.erase_cons_tailₓ

theorem erase_eq_eraseP (a : α) (l : List α) : l.erase a = l.erasep (Eq a) :=
  by
  induction' l with b l
  · rfl
  by_cases a = b <;> [simp [h], simp [h, Ne.symm h, *]]
#align list.erase_eq_erasep List.erase_eq_erasePₓ

@[simp]
theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l := by
  rw [erase_eq_erasep, erasep_of_forall_not] <;> rintro b h' rfl <;> exact h h'
#align list.erase_of_not_mem List.erase_of_not_memₓ

theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ := by
  rcases exists_of_erasep h rfl with ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩ <;> rw [erase_eq_erasep] <;>
    exact ⟨l₁, l₂, fun h => h₁ _ h rfl, h₂, h₃⟩
#align list.exists_erase_eq List.exists_erase_eqₓ

@[simp]
theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = pred (length l) := by
  rw [erase_eq_erasep] <;> exact length_erasep_of_mem h rfl
#align list.length_erase_of_mem List.length_erase_of_memₓ

@[simp]
theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) : (l.erase a).length + 1 = l.length :=
  by rw [erase_eq_erasep, length_erasep_add_one h rfl]
#align list.length_erase_add_one List.length_erase_add_oneₓ

theorem erase_append_left {a : α} {l₁ : List α} (l₂) (h : a ∈ l₁) :
    (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ := by
  simp [erase_eq_erasep] <;> exact erasep_append_left (by rfl) l₂ h
#align list.erase_append_left List.erase_append_leftₓ

theorem erase_append_right {a : α} {l₁ : List α} (l₂) (h : a ∉ l₁) :
    (l₁ ++ l₂).erase a = l₁ ++ l₂.erase a := by
  rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right] <;> rintro b h' rfl <;> exact h h'
#align list.erase_append_right List.erase_append_rightₓ

theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l := by
  rw [erase_eq_erasep] <;> apply erasep_sublist
#align list.erase_sublist List.erase_sublistₓ

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l :=
  (erase_sublist a l).Subset
#align list.erase_subset List.erase_subsetₓ

theorem Sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a := by
  simp [erase_eq_erasep] <;> exact sublist.erasep h
#align list.sublist.erase List.Sublist.eraseₓ

theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
  @erase_subset _ _ _ _ _
#align list.mem_of_mem_erase List.mem_of_mem_eraseₓ

@[simp]
theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l := by
  rw [erase_eq_erasep] <;> exact mem_erasep_of_neg ab.symm
#align list.mem_erase_of_ne List.mem_erase_of_neₓ

theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a :=
  if ab : a = b then by rw [ab]
  else
    if ha : a ∈ l then
      if hb : b ∈ l then
        match l, l.erase a, exists_erase_eq ha, hb with
        | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩, hb =>
          if h₁ : b ∈ l₁ then by
            rw [erase_append_left _ h₁, erase_append_left _ h₁,
              erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
          else by
            rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
              erase_cons_tail _ ab, erase_cons_head]
      else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
    else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]
#align list.erase_comm List.erase_commₓ

/- warning: list.map_erase -> List.map_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {a : α} (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l a)) (List.eraseₓ.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (List.map.{u1, u2} α β f l) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {a : α} (l : List.{u1} α), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l a)) (List.erase.{u2} β (instBEq.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) (List.map.{u1, u2} α β f l) (f a)))
Case conversion may be inaccurate. Consider using '#align list.map_erase List.map_eraseₓ'. -/
theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) :=
  by
  have this : Eq a = Eq (f a) ∘ f := by ext b; simp [finj.eq_iff]
  simp [erase_eq_erasep, erase_eq_erasep, erasep_map, this]
#align list.map_erase List.map_erase

/- warning: list.map_foldl_erase -> List.map_foldl_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.foldl.{u1, u1} (List.{u1} α) α (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂)) (List.foldl.{u2, u1} (List.{u2} β) α (fun (l : List.{u2} β) (a : α) => List.eraseₓ.{u2} β (fun (a : β) (b : β) => _inst_2 a b) l (f a)) (List.map.{u1, u2} α β f l₁) l₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.foldl.{u1, u1} (List.{u1} α) α (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) l₁ l₂)) (List.foldl.{u2, u1} (List.{u2} β) α (fun (l : List.{u2} β) (a : α) => List.erase.{u2} β (instBEq.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) l (f a)) (List.map.{u1, u2} α β f l₁) l₂))
Case conversion may be inaccurate. Consider using '#align list.map_foldl_erase List.map_foldl_eraseₓ'. -/
theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl, simp only [foldl_cons, map_erase finj, *]]
#align list.map_foldl_erase List.map_foldl_erase

end Erase

/-! ### diff -/


section Diff

variable [DecidableEq α]

#print List.diff_nil /-
@[simp]
theorem diff_nil (l : List α) : l.diff [] = l :=
  rfl
#align list.diff_nil List.diff_nil
-/

/- warning: list.diff_cons -> List.diff_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ (List.cons.{u1} α a l₂)) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ a) l₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ (List.cons.{u1} α a l₂)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ a) l₂)
Case conversion may be inaccurate. Consider using '#align list.diff_cons List.diff_consₓ'. -/
@[simp]
theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ :=
  if h : a ∈ l₁ then by simp only [List.diff, if_pos h]
  else by simp only [List.diff, if_neg h, erase_of_not_mem h]
#align list.diff_cons List.diff_cons

/- warning: list.diff_cons_right -> List.diff_cons_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ (List.cons.{u1} α a l₂)) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ (List.cons.{u1} α a l₂)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) a)
Case conversion may be inaccurate. Consider using '#align list.diff_cons_right List.diff_cons_rightₓ'. -/
theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.diff l₂).erase a :=
  by
  induction' l₂ with b l₂ ih generalizing l₁ a
  · simp_rw [diff_cons, diff_nil]
  · rw [diff_cons, diff_cons, erase_comm, ← diff_cons, ih, ← diff_cons]
#align list.diff_cons_right List.diff_cons_right

/- warning: list.diff_erase -> List.diff_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) a) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ a) l₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) a) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ a) l₂)
Case conversion may be inaccurate. Consider using '#align list.diff_erase List.diff_eraseₓ'. -/
theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ := by
  rw [← diff_cons_right, diff_cons]
#align list.diff_erase List.diff_erase

/- warning: list.nil_diff -> List.nil_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.nil.{u1} α) l) (List.nil.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.nil.{u1} α) l) (List.nil.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.nil_diff List.nil_diffₓ'. -/
@[simp]
theorem nil_diff (l : List α) : [].diff l = [] := by
  induction l <;> [rfl, simp only [*, diff_cons, erase_of_not_mem (not_mem_nil _)]]
#align list.nil_diff List.nil_diff

/- warning: list.cons_diff -> List.cons_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α a l₁) l₂) (ite.{succ u1} (List.{u1} α) (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂) (List.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l₂) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₂ a)) (List.cons.{u1} α a (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.cons.{u1} α a l₁) l₂) (ite.{succ u1} (List.{u1} α) (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l₂) (List.instDecidableMemListInstMembershipList.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l₂) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₂ a)) (List.cons.{u1} α a (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂)))
Case conversion may be inaccurate. Consider using '#align list.cons_diff List.cons_diffₓ'. -/
theorem cons_diff (a : α) (l₁ l₂ : List α) :
    (a :: l₁).diff l₂ = if a ∈ l₂ then l₁.diff (l₂.erase a) else a :: l₁.diff l₂ :=
  by
  induction' l₂ with b l₂ ih; · rfl
  rcases eq_or_ne a b with (rfl | hne)
  · simp
  · simp only [mem_cons_iff, *, false_or_iff, diff_cons_right]
    split_ifs with h₂ <;> simp [diff_erase, List.erase, hne, hne.symm]
#align list.cons_diff List.cons_diff

/- warning: list.cons_diff_of_mem -> List.cons_diff_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₂ : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂) -> (forall (l₁ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α a l₁) l₂) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₂ a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₂ : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l₂) -> (forall (l₁ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.cons.{u1} α a l₁) l₂) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₂ a)))
Case conversion may be inaccurate. Consider using '#align list.cons_diff_of_mem List.cons_diff_of_memₓ'. -/
theorem cons_diff_of_mem {a : α} {l₂ : List α} (h : a ∈ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = l₁.diff (l₂.erase a) := by rw [cons_diff, if_pos h]
#align list.cons_diff_of_mem List.cons_diff_of_mem

/- warning: list.cons_diff_of_not_mem -> List.cons_diff_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₂ : List.{u1} α}, (Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂)) -> (forall (l₁ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.cons.{u1} α a l₁) l₂) (List.cons.{u1} α a (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₂ : List.{u1} α}, (Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l₂)) -> (forall (l₁ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.cons.{u1} α a l₁) l₂) (List.cons.{u1} α a (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂)))
Case conversion may be inaccurate. Consider using '#align list.cons_diff_of_not_mem List.cons_diff_of_not_memₓ'. -/
theorem cons_diff_of_not_mem {a : α} {l₂ : List α} (h : a ∉ l₂) (l₁ : List α) :
    (a :: l₁).diff l₂ = a :: l₁.diff l₂ := by rw [cons_diff, if_neg h]
#align list.cons_diff_of_not_mem List.cons_diff_of_not_mem

/- warning: list.diff_eq_foldl -> List.diff_eq_foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) (List.foldl.{u1, u1} (List.{u1} α) α (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) (List.foldl.{u1, u1} (List.{u1} α) α (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align list.diff_eq_foldl List.diff_eq_foldlₓ'. -/
theorem diff_eq_foldl : ∀ l₁ l₂ : List α, l₁.diff l₂ = foldl List.erase l₁ l₂
  | l₁, [] => rfl
  | l₁, a :: l₂ => (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)
#align list.diff_eq_foldl List.diff_eq_foldl

/- warning: list.diff_append -> List.diff_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (l₃ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₂ l₃)) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) l₃)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α) (l₃ : List.{u1} α), Eq.{succ u1} (List.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₂ l₃)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) l₃)
Case conversion may be inaccurate. Consider using '#align list.diff_append List.diff_appendₓ'. -/
@[simp]
theorem diff_append (l₁ l₂ l₃ : List α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ := by
  simp only [diff_eq_foldl, foldl_append]
#align list.diff_append List.diff_append

/- warning: list.map_diff -> List.map_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂)) (List.diffₓ.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (List.map.{u1, u2} α β f l₁) (List.map.{u1, u2} α β f l₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall {l₁ : List.{u1} α} {l₂ : List.{u1} α}, Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β f (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂)) (List.diff.{u2} β (instBEq.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) (List.map.{u1, u2} α β f l₁) (List.map.{u1, u2} α β f l₂)))
Case conversion may be inaccurate. Consider using '#align list.map_diff List.map_diffₓ'. -/
@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]
#align list.map_diff List.map_diff

/- warning: list.diff_sublist -> List.diff_sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), List.Sublist.{u1} α (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) l₁
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), List.Sublist.{u1} α (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) l₁
Case conversion may be inaccurate. Consider using '#align list.diff_sublist List.diff_sublistₓ'. -/
theorem diff_sublist : ∀ l₁ l₂ : List α, l₁.diff l₂ <+ l₁
  | l₁, [] => Sublist.refl _
  | l₁, a :: l₂ =>
    calc
      l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := diff_cons _ _ _
      _ <+ l₁.erase a := diff_sublist _ _
      _ <+ l₁ := List.erase_sublist _ _
      
#align list.diff_sublist List.diff_sublist

/- warning: list.diff_subset -> List.diff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), HasSubset.Subset.{u1} (List.{u1} α) (List.hasSubset.{u1} α) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂) l₁
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), HasSubset.Subset.{u1} (List.{u1} α) (List.instHasSubsetList.{u1} α) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂) l₁
Case conversion may be inaccurate. Consider using '#align list.diff_subset List.diff_subsetₓ'. -/
theorem diff_subset (l₁ l₂ : List α) : l₁.diff l₂ ⊆ l₁ :=
  (diff_sublist _ _).Subset
#align list.diff_subset List.diff_subset

/- warning: list.mem_diff_of_mem -> List.mem_diff_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₁) -> (Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l₂)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l₁) -> (Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l₂)) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₂))
Case conversion may be inaccurate. Consider using '#align list.mem_diff_of_mem List.mem_diff_of_memₓ'. -/
theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
  | l₁, [], h₁, h₂ => h₁
  | l₁, b :: l₂, h₁, h₂ => by
    rw [diff_cons] <;>
      exact
        mem_diff_of_mem ((mem_erase_of_ne (ne_of_not_mem_cons h₂)).2 h₁)
          (not_mem_of_not_mem_cons h₂)
#align list.mem_diff_of_mem List.mem_diff_of_mem

/- warning: list.sublist.diff_right -> List.Sublist.diff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {l₁ : List.{u1} α} {l₂ : List.{u1} α} {l₃ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Sublist.{u1} α (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ l₃) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₂ l₃))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {l₁ : List.{u1} α} {l₂ : List.{u1} α} {l₃ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Sublist.{u1} α (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ l₃) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₂ l₃))
Case conversion may be inaccurate. Consider using '#align list.sublist.diff_right List.Sublist.diff_rightₓ'. -/
theorem Sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
  | l₁, l₂, [], h => h
  | l₁, l₂, a :: l₃, h => by simp only [diff_cons, (h.erase _).diff_right]
#align list.sublist.diff_right List.Sublist.diff_right

/- warning: list.erase_diff_erase_sublist_of_sublist -> List.erase_diff_erase_sublist_of_sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Sublist.{u1} α (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₂ a) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₁ a)) (List.diffₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l₂ l₁))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l₁ : List.{u1} α} {l₂ : List.{u1} α}, (List.Sublist.{u1} α l₁ l₂) -> (List.Sublist.{u1} α (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₂ a) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₁ a)) (List.diff.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) l₂ l₁))
Case conversion may be inaccurate. Consider using '#align list.erase_diff_erase_sublist_of_sublist List.erase_diff_erase_sublist_of_sublistₓ'. -/
theorem erase_diff_erase_sublist_of_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, h => erase_sublist _ _
  | b :: l₁, l₂, h =>
    if heq : b = a then by simp only [HEq, erase_cons_head, diff_cons]
    else by
      simpa only [erase_cons_head, erase_cons_tail _ HEq, diff_cons, erase_comm a b l₂] using
        erase_diff_erase_sublist_of_sublist (h.erase b)
#align list.erase_diff_erase_sublist_of_sublist List.erase_diff_erase_sublist_of_sublist

end Diff

/-! ### enum -/


#print List.length_enumFrom /-
theorem length_enumFrom : ∀ (n) (l : List α), length (enumFrom n l) = length l
  | n, [] => rfl
  | n, a :: l => congr_arg Nat.succ (length_enum_from _ _)
#align list.length_enum_from List.length_enumFrom
-/

#print List.length_enum /-
theorem length_enum : ∀ l : List α, length (enum l) = length l :=
  length_enumFrom _
#align list.length_enum List.length_enum
-/

/- warning: list.enum_from_nth -> List.enumFrom_get? is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : Nat) (l : List.{u1} α) (m : Nat), Eq.{succ u1} (Option.{u1} (Prod.{0, u1} Nat α)) (List.get?.{u1} (Prod.{0, u1} Nat α) (List.enumFrom.{u1} α n l) m) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α (Prod.{0, u1} Nat α) (fun (a : α) => Prod.mk.{0, u1} Nat α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m) a) (List.get?.{u1} α l m))
but is expected to have type
  forall {α : Type.{u1}} (n : Nat) (l : List.{u1} α) (m : Nat), Eq.{succ u1} (Option.{u1} (Prod.{0, u1} Nat α)) (List.get?.{u1} (Prod.{0, u1} Nat α) (List.enumFrom.{u1} α n l) m) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α (Prod.{0, u1} Nat α) (fun (a : α) => Prod.mk.{0, u1} Nat α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m) a) (List.get?.{u1} α l m))
Case conversion may be inaccurate. Consider using '#align list.enum_from_nth List.enumFrom_get?ₓ'. -/
@[simp]
theorem enumFrom_get? :
    ∀ (n) (l : List α) (m), get? (enumFrom n l) m = (fun a => (n + m, a)) <$> get? l m
  | n, [], m => rfl
  | n, a :: l, 0 => rfl
  | n, a :: l, m + 1 => (enum_from_nth (n + 1) l m).trans <| by rw [add_right_comm] <;> rfl
#align list.enum_from_nth List.enumFrom_get?

/- warning: list.enum_nth -> List.enum_get? is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α) (n : Nat), Eq.{succ u1} (Option.{u1} (Prod.{0, u1} Nat α)) (List.get?.{u1} (Prod.{0, u1} Nat α) (List.enum.{u1} α l) n) (Functor.map.{u1, u1} Option.{u1} (Traversable.toFunctor.{u1} Option.{u1} Option.traversable.{u1}) α (Prod.{0, u1} Nat α) (fun (a : α) => Prod.mk.{0, u1} Nat α n a) (List.get?.{u1} α l n))
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α) (n : Nat), Eq.{succ u1} (Option.{u1} (Prod.{0, u1} Nat α)) (List.get?.{u1} (Prod.{0, u1} Nat α) (List.enum.{u1} α l) n) (Functor.map.{u1, u1} Option.{u1} instFunctorOption.{u1} α (Prod.{0, u1} Nat α) (fun (a : α) => Prod.mk.{0, u1} Nat α n a) (List.get?.{u1} α l n))
Case conversion may be inaccurate. Consider using '#align list.enum_nth List.enum_get?ₓ'. -/
@[simp]
theorem enum_get? : ∀ (l : List α) (n), get? (enum l) n = (fun a => (n, a)) <$> get? l n := by
  simp only [enum, enum_from_nth, zero_add] <;> intros <;> rfl
#align list.enum_nth List.enum_get?

#print List.enumFrom_map_snd /-
@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | n, [] => rfl
  | n, a :: l => congr_arg (cons _) (enum_from_map_snd _ _)
#align list.enum_from_map_snd List.enumFrom_map_snd
-/

#print List.enum_map_snd /-
@[simp]
theorem enum_map_snd : ∀ l : List α, map Prod.snd (enum l) = l :=
  enumFrom_map_snd _
#align list.enum_map_snd List.enum_map_snd
-/

#print List.mem_enumFrom /-
theorem mem_enumFrom {x : α} {i : ℕ} :
    ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enumFrom j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
  | j, [] => by simp [enum_from]
  | j, y :: ys =>
    by
    suffices
      i = j ∧ x = y ∨ (i, x) ∈ enumFrom (j + 1) ys →
        j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys)
      by simpa [enum_from, mem_enum_from ys]
    rintro (h | h)
    · refine' ⟨le_of_eq h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      apply Nat.lt_add_of_pos_right <;> simp
    · obtain ⟨hji, hijlen, hmem⟩ := mem_enum_from _ h
      refine' ⟨_, _, _⟩
      · exact le_trans (Nat.le_succ _) hji
      · convert hijlen using 1
        ac_rfl
      · simp [hmem]
#align list.mem_enum_from List.mem_enumFrom
-/

#print List.enum_nil /-
@[simp]
theorem enum_nil : enum ([] : List α) = [] :=
  rfl
#align list.enum_nil List.enum_nil
-/

#print List.enumFrom_nil /-
@[simp]
theorem enumFrom_nil (n : ℕ) : enumFrom n ([] : List α) = [] :=
  rfl
#align list.enum_from_nil List.enumFrom_nil
-/

#print List.enumFrom_cons /-
@[simp]
theorem enumFrom_cons (x : α) (xs : List α) (n : ℕ) :
    enumFrom n (x :: xs) = (n, x) :: enumFrom (n + 1) xs :=
  rfl
#align list.enum_from_cons List.enumFrom_cons
-/

#print List.enum_cons /-
@[simp]
theorem enum_cons (x : α) (xs : List α) : enum (x :: xs) = (0, x) :: enumFrom 1 xs :=
  rfl
#align list.enum_cons List.enum_cons
-/

#print List.enumFrom_singleton /-
@[simp]
theorem enumFrom_singleton (x : α) (n : ℕ) : enumFrom n [x] = [(n, x)] :=
  rfl
#align list.enum_from_singleton List.enumFrom_singleton
-/

#print List.enum_singleton /-
@[simp]
theorem enum_singleton (x : α) : enum [x] = [(0, x)] :=
  rfl
#align list.enum_singleton List.enum_singleton
-/

#print List.enumFrom_append /-
theorem enumFrom_append (xs ys : List α) (n : ℕ) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys :=
  by
  induction' xs with x xs IH generalizing ys n
  · simp
  ·
    rw [cons_append, enum_from_cons, IH, ← cons_append, ← enum_from_cons, length, add_right_comm,
      add_assoc]
#align list.enum_from_append List.enumFrom_append
-/

#print List.enum_append /-
theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enum_from_append]
#align list.enum_append List.enum_append
-/

#print List.map_fst_add_enumFrom_eq_enumFrom /-
theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : ℕ) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l :=
  by
  induction' l with hd tl IH generalizing n k
  · simp [enum_from]
  · simp only [enum_from, map, zero_add, Prod.map_mk, id.def, eq_self_iff_true, true_and_iff]
    simp [IH, add_comm n k, add_assoc, add_left_comm]
#align list.map_fst_add_enum_from_eq_enum_from List.map_fst_add_enumFrom_eq_enumFrom
-/

#print List.map_fst_add_enum_eq_enumFrom /-
theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : ℕ) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _
#align list.map_fst_add_enum_eq_enum_from List.map_fst_add_enum_eq_enumFrom
-/

#print List.nthLe_enumFrom /-
theorem nthLe_enumFrom (l : List α) (n i : ℕ) (hi' : i < (l.enumFrom n).length)
    (hi : i < l.length := (by simpa [length_enum_from] using hi')) :
    (l.enumFrom n).nthLe i hi' = (n + i, l.nthLe i hi) :=
  by
  rw [← Option.some_inj, ← nth_le_nth]
  simp [enum_from_nth, nth_le_nth hi]
#align list.nth_le_enum_from List.nthLe_enumFrom
-/

#print List.nthLe_enum /-
theorem nthLe_enum (l : List α) (i : ℕ) (hi' : i < l.enum.length)
    (hi : i < l.length := (by simpa [length_enum] using hi')) :
    l.enum.nthLe i hi' = (i, l.nthLe i hi) :=
  by
  convert nth_le_enum_from _ _ _ hi'
  exact (zero_add _).symm
#align list.nth_le_enum List.nthLe_enum
-/

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

#print List.choose_spec /-
theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align list.choose_spec List.choose_spec
-/

#print List.choose_mem /-
theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align list.choose_mem List.choose_mem
-/

#print List.choose_property /-
theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align list.choose_property List.choose_property
-/

end Choose

/-! ### map₂_left' -/


section Map₂Left'

#print List.map₂Left'_nil_right /-
-- The definitional equalities for `map₂_left'` can already be used by the
-- simplifie because `map₂_left'` is marked `@[simp]`.
@[simp]
theorem map₂Left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl
#align list.map₂_left'_nil_right List.map₂Left'_nil_right
-/

end Map₂Left'

/-! ### map₂_right' -/


section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

#print List.map₂Right'_nil_left /-
@[simp]
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl
#align list.map₂_right'_nil_left List.map₂Right'_nil_left
-/

#print List.map₂Right'_nil_right /-
@[simp]
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl
#align list.map₂_right'_nil_right List.map₂Right'_nil_right
-/

#print List.map₂Right'_nil_cons /-
@[simp]
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl
#align list.map₂_right'_nil_cons List.map₂Right'_nil_cons
-/

#print List.map₂Right'_cons_cons /-
@[simp]
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let rec := map₂Right' f as bs
      (f (some a) b :: rec.fst, rec.snd) :=
  rfl
#align list.map₂_right'_cons_cons List.map₂Right'_cons_cons
-/

end Map₂Right'

/-! ### zip_left' -/


section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

#print List.zipLeft'_nil_right /-
@[simp]
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl
#align list.zip_left'_nil_right List.zipLeft'_nil_right
-/

#print List.zipLeft'_nil_left /-
@[simp]
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl
#align list.zip_left'_nil_left List.zipLeft'_nil_left
-/

#print List.zipLeft'_cons_nil /-
@[simp]
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl
#align list.zip_left'_cons_nil List.zipLeft'_cons_nil
-/

#print List.zipLeft'_cons_cons /-
@[simp]
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let rec := zipLeft' as bs
      ((a, some b) :: rec.fst, rec.snd) :=
  rfl
#align list.zip_left'_cons_cons List.zipLeft'_cons_cons
-/

end ZipLeft'

/-! ### zip_right' -/


section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

#print List.zipRight'_nil_left /-
@[simp]
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl
#align list.zip_right'_nil_left List.zipRight'_nil_left
-/

#print List.zipRight'_nil_right /-
@[simp]
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl
#align list.zip_right'_nil_right List.zipRight'_nil_right
-/

#print List.zipRight'_nil_cons /-
@[simp]
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl
#align list.zip_right'_nil_cons List.zipRight'_nil_cons
-/

#print List.zipRight'_cons_cons /-
@[simp]
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let rec := zipRight' as bs
      ((some a, b) :: rec.fst, rec.snd) :=
  rfl
#align list.zip_right'_cons_cons List.zipRight'_cons_cons
-/

end ZipRight'

/-! ### map₂_left -/


section Map₂Left

variable (f : α → Option β → γ) (as : List α)

#print List.map₂Left_nil_right /-
-- The definitional equalities for `map₂_left` can already be used by the
-- simplifier because `map₂_left` is marked `@[simp]`.
@[simp]
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl
#align list.map₂_left_nil_right List.map₂Left_nil_right
-/

#print List.map₂Left_eq_map₂Left' /-
theorem map₂Left_eq_map₂Left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], bs => by simp!
  | a :: as, [] => by simp!
  | a :: as, b :: bs => by simp! [*]
#align list.map₂_left_eq_map₂_left' List.map₂Left_eq_map₂Left'
-/

#print List.map₂Left_eq_zipWith /-
theorem map₂Left_eq_zipWith :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], h => by simp!
  | [], b :: bs, h => by simp!
  | a :: as, [], h => by
    simp at h
    contradiction
  | a :: as, b :: bs, h => by
    simp at h
    simp! [*]
#align list.map₂_left_eq_map₂ List.map₂Left_eq_zipWith
-/

end Map₂Left

/-! ### map₂_right -/


section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

#print List.map₂Right_nil_left /-
@[simp]
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl
#align list.map₂_right_nil_left List.map₂Right_nil_left
-/

#print List.map₂Right_nil_right /-
@[simp]
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl
#align list.map₂_right_nil_right List.map₂Right_nil_right
-/

#print List.map₂Right_nil_cons /-
@[simp]
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl
#align list.map₂_right_nil_cons List.map₂Right_nil_cons
-/

#print List.map₂Right_cons_cons /-
@[simp]
theorem map₂Right_cons_cons : map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl
#align list.map₂_right_cons_cons List.map₂Right_cons_cons
-/

#print List.map₂Right_eq_map₂Right' /-
theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂_right, map₂_right', map₂_left_eq_map₂_left']
#align list.map₂_right_eq_map₂_right' List.map₂Right_eq_map₂Right'
-/

#print List.map₂Right_eq_zipWith /-
theorem map₂Right_eq_zipWith (h : length bs ≤ length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs :=
  by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂_right, map₂_left_eq_map₂, map₂_flip, *]
#align list.map₂_right_eq_map₂ List.map₂Right_eq_zipWith
-/

end Map₂Right

/-! ### zip_left -/


section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

#print List.zipLeft_nil_right /-
@[simp]
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl
#align list.zip_left_nil_right List.zipLeft_nil_right
-/

#print List.zipLeft_nil_left /-
@[simp]
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl
#align list.zip_left_nil_left List.zipLeft_nil_left
-/

#print List.zipLeft_cons_nil /-
@[simp]
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl
#align list.zip_left_cons_nil List.zipLeft_cons_nil
-/

#print List.zipLeft_cons_cons /-
@[simp]
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl
#align list.zip_left_cons_cons List.zipLeft_cons_cons
-/

#print List.zipLeft_eq_zipLeft' /-
theorem zipLeft_eq_zipLeft' : zipLeft as bs = (zipLeft' as bs).fst := by
  simp only [zip_left, zip_left', map₂_left_eq_map₂_left']
#align list.zip_left_eq_zip_left' List.zipLeft_eq_zipLeft'
-/

end ZipLeft

/-! ### zip_right -/


section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

#print List.zipRight_nil_left /-
@[simp]
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl
#align list.zip_right_nil_left List.zipRight_nil_left
-/

#print List.zipRight_nil_right /-
@[simp]
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl
#align list.zip_right_nil_right List.zipRight_nil_right
-/

#print List.zipRight_nil_cons /-
@[simp]
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl
#align list.zip_right_nil_cons List.zipRight_nil_cons
-/

#print List.zipRight_cons_cons /-
@[simp]
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl
#align list.zip_right_cons_cons List.zipRight_cons_cons
-/

#print List.zipRight_eq_zipRight' /-
theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  simp only [zip_right, zip_right', map₂_right_eq_map₂_right']
#align list.zip_right_eq_zip_right' List.zipRight_eq_zipRight'
-/

end ZipRight

/-! ### to_chunks -/


section ToChunks

/- warning: list.to_chunks_nil clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_nil -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (n : Nat), Eq.{succ u} (List.{u} (List.{u} α)) (List.toChunks.{u} α n (List.nil.{u} α)) (List.nil.{u} (List.{u} α))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_nil [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (n) : @toChunks α n [] = [] := by cases n <;> rfl
#align list.to_chunks_nil [anonymous]

/- warning: list.to_chunks_aux_eq clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_aux_eq -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (n : Nat) (xs : List.{u} α) (i : Nat), Eq.{succ u} (Prod.{u, u} (List.{u} α) (List.{u} (List.{u} α))) (List.toChunksAux.{u} α n xs i) (Prod.mk.{u, u} (List.{u} α) (List.{u} (List.{u} α)) (List.take.{u} α i xs) (List.toChunks.{u} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (List.drop.{u} α i xs)))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_aux_eq [anonymous]ₓ'. -/
theorem [anonymous] (n) : ∀ xs i, @toChunksAux α n xs i = (xs.take i, (xs.drop i).toChunks (n + 1))
  | [], i => by cases i <;> rfl
  | x :: xs, 0 => by rw [to_chunks_aux, drop, to_chunks] <;> cases to_chunks_aux n xs n <;> rfl
  | x :: xs, i + 1 => by rw [to_chunks_aux, to_chunks_aux_eq] <;> rfl
#align list.to_chunks_aux_eq [anonymous]

/- warning: list.to_chunks_eq_cons' clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_eq_cons' -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (n : Nat) {xs : List.{u} α}, (Ne.{succ u} (List.{u} α) xs (List.nil.{u} α)) -> (Eq.{succ u} (List.{u} (List.{u} α)) (List.toChunks.{u} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) xs) (List.cons.{u} (List.{u} α) (List.take.{u} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) xs) (List.toChunks.{u} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (List.drop.{u} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) xs))))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_eq_cons' [anonymous]ₓ'. -/
theorem [anonymous] (n) :
    ∀ {xs : List α} (h : xs ≠ []),
      xs.toChunks (n + 1) = xs.take (n + 1) :: (xs.drop (n + 1)).toChunks (n + 1)
  | [], e => (e rfl).elim
  | x :: xs, _ => by rw [to_chunks, to_chunks_aux_eq] <;> rfl
#align list.to_chunks_eq_cons' [anonymous]

/- warning: list.to_chunks_eq_cons clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_eq_cons -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {n : Nat} {xs : List.{u} α}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{succ u} (List.{u} α) xs (List.nil.{u} α)) -> (Eq.{succ u} (List.{u} (List.{u} α)) (List.toChunks.{u} α n xs) (List.cons.{u} (List.{u} α) (List.take.{u} α n xs) (List.toChunks.{u} α n (List.drop.{u} α n xs))))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_eq_cons [anonymous]ₓ'. -/
theorem [anonymous] :
    ∀ {n} {xs : List α} (n0 : n ≠ 0) (x0 : xs ≠ []),
      xs.toChunks n = xs.take n :: (xs.drop n).toChunks n
  | 0, _, e => (e rfl).elim
  | n + 1, xs, _ => [anonymous] _
#align list.to_chunks_eq_cons [anonymous]

/- warning: list.to_chunks_aux_join clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_aux_join -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {n : Nat} {xs : List.{u} α} {i : Nat} {l : List.{u} α} {L : List.{u} (List.{u} α)}, (Eq.{succ u} (Prod.{u, u} (List.{u} α) (List.{u} (List.{u} α))) (List.toChunksAux.{u} α n xs i) (Prod.mk.{u, u} (List.{u} α) (List.{u} (List.{u} α)) l L)) -> (Eq.{succ u} (List.{u} α) (Append.append.{u} (List.{u} α) (List.hasAppend.{u} α) l (List.join.{u} α L)) xs)
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_aux_join [anonymous]ₓ'. -/
theorem [anonymous] {n} : ∀ {xs i l L}, @toChunksAux α n xs i = (l, L) → l ++ L.join = xs
  | [], _, _, _, rfl => rfl
  | x :: xs, i, l, L, e => by
    cases i <;> [cases' e' : to_chunks_aux n xs n with l L,
        cases' e' : to_chunks_aux n xs i with l L] <;>
      · rw [to_chunks_aux, e', to_chunks_aux] at e
        cases e
        exact (congr_arg (cons x) (to_chunks_aux_join e') : _)
#align list.to_chunks_aux_join [anonymous]

/- warning: list.to_chunks_join clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_join -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (n : Nat) (xs : List.{u} α), Eq.{succ u} (List.{u} α) (List.join.{u} α (List.toChunks.{u} α n xs)) xs
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_join [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] : ∀ n xs, (@toChunks α n xs).join = xs
  | n, [] => by cases n <;> rfl
  | 0, x :: xs => by simp only [to_chunks, join] <;> rw [append_nil]
  | n + 1, x :: xs => by
    rw [to_chunks]
    cases' e : to_chunks_aux n xs n with l L
    exact (congr_arg (cons x) (to_chunks_aux_join e) : _)
#align list.to_chunks_join [anonymous]

/- warning: list.to_chunks_length_le clashes with [anonymous] -> [anonymous]
warning: list.to_chunks_length_le -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} (n : Nat) (xs : List.{u} α), (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (forall (l : List.{u} α), (Membership.Mem.{u, u} (List.{u} α) (List.{u} (List.{u} α)) (List.hasMem.{u} (List.{u} α)) l (List.toChunks.{u} α n xs)) -> (LE.le.{0} Nat Nat.hasLe (List.length.{u} α l) n))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.to_chunks_length_le [anonymous]ₓ'. -/
theorem [anonymous] : ∀ n xs, n ≠ 0 → ∀ l : List α, l ∈ @toChunks α n xs → l.length ≤ n
  | 0, _, e, _ => (e rfl).elim
  | n + 1, xs, _, l => by
    refine' (measure_wf length).induction xs _; intro xs IH h
    by_cases x0 : xs = [];
    · subst xs
      cases h
    rw [to_chunks_eq_cons' _ x0] at h; rcases h with (rfl | h)
    · apply length_take_le
    · refine' IH _ _ h
      simp only [Measure, InvImage, length_drop]
      exact tsub_lt_self (length_pos_iff_ne_nil.2 x0) (succ_pos _)
#align list.to_chunks_length_le [anonymous]

end ToChunks

/-! ### all₂ -/


section All₂

variable {p q : α → Prop} {l : List α}

#print List.all₂_cons /-
@[simp]
theorem all₂_cons (p : α → Prop) (x : α) : ∀ l : List α, All₂ p (x :: l) ↔ p x ∧ All₂ p l
  | [] => (and_true_iff _).symm
  | x :: l => Iff.rfl
#align list.all₂_cons List.all₂_cons
-/

#print List.all₂_iff_forall /-
theorem all₂_iff_forall : ∀ {l : List α}, All₂ p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [ball_cons, all₂_cons, all₂_iff_forall]
#align list.all₂_iff_forall List.all₂_iff_forall
-/

#print List.All₂.imp /-
theorem All₂.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, All₂ p l → All₂ q l
  | [] => id
  | x :: l => by simpa using And.imp (h x) all₂.imp
#align list.all₂.imp List.All₂.imp
-/

#print List.all₂_map_iff /-
@[simp]
theorem all₂_map_iff {p : β → Prop} (f : α → β) : All₂ p (l.map f) ↔ All₂ (p ∘ f) l := by
  induction l <;> simp [*]
#align list.all₂_map_iff List.all₂_map_iff
-/

instance (p : α → Prop) [DecidablePred p] : DecidablePred (All₂ p) := fun l =>
  decidable_of_iff' _ all₂_iff_forall

end All₂

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/


attribute [to_additive] List.prod

-- `list.sum`
attribute [to_additive] alternating_prod

/-! ### Miscellaneous lemmas -/


#print List.getLast_reverse /-
-- `list.alternating_sum`
theorem getLast_reverse {l : List α} (hl : l.reverse ≠ [])
    (hl' : 0 < l.length :=
      (by
        contrapose! hl
        simpa [length_eq_zero] using hl)) :
    l.reverse.last hl = l.nthLe 0 hl' :=
  by
  rw [last_eq_nth_le, nth_le_reverse']
  · simp
  · simpa using hl'
#align list.last_reverse List.getLast_reverse
-/

#print List.ilast'_mem /-
theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
  | a, [] => Or.inl rfl
  | a, b :: l => Or.inr (ilast'_mem b l)
#align list.ilast'_mem List.ilast'_mem
-/

#print List.nthLe_attach /-
@[simp]
theorem nthLe_attach (L : List α) (i) (H : i < L.attach.length) :
    (L.attach.nthLe i H).1 = L.nthLe i (length_attach L ▸ H) :=
  calc
    (L.attach.nthLe i H).1 = (L.attach.map Subtype.val).nthLe i (by simpa using H) := by
      rw [nth_le_map']
    _ = L.nthLe i _ := by congr <;> apply attach_map_val
    
#align list.nth_le_attach List.nthLe_attach
-/

#print List.mem_map_swap /-
@[simp]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs :=
  by
  induction' xs with x xs
  · simp only [not_mem_nil, map_nil]
  · cases' x with a b
    simp only [mem_cons_iff, Prod.mk.inj_iff, map, Prod.swap_prod_mk, Prod.exists, xs_ih, and_comm']
#align list.mem_map_swap List.mem_map_swap
-/

#print List.dropSlice_eq /-
theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) :=
  by
  induction n generalizing xs
  · simp [slice]
  · cases xs <;> simp [slice, *, Nat.succ_add]
#align list.slice_eq List.dropSlice_eq
-/

/- warning: list.sizeof_slice_lt -> List.sizeOf_dropSlice_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] (i : Nat) (j : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) j) -> (forall (xs : List.{u1} α), (LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α xs)) -> (LT.lt.{0} Nat Nat.hasLt (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List.hasSizeof.{u1} α _inst_1) (List.dropSlice.{u1} α i j xs)) (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List.hasSizeof.{u1} α _inst_1) xs)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SizeOf.{succ u1} α] (i : Nat) (j : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) j) -> (forall (xs : List.{u1} α), (LT.lt.{0} Nat instLTNat i (List.length.{u1} α xs)) -> (LT.lt.{0} Nat instLTNat (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List._sizeOf_inst.{u1} α _inst_1) (List.dropSlice.{u1} α i j xs)) (SizeOf.sizeOf.{succ u1} (List.{u1} α) (List._sizeOf_inst.{u1} α _inst_1) xs)))
Case conversion may be inaccurate. Consider using '#align list.sizeof_slice_lt List.sizeOf_dropSlice_ltₓ'. -/
theorem sizeOf_dropSlice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.dropSlice i j xs) < SizeOf.sizeOf xs :=
  by
  induction xs generalizing i j
  case nil i j h => cases hi
  case
    cons x xs xs_ih i j h =>
    cases i <;> simp only [-slice_eq, List.dropSlice]
    · cases j
      cases h
      dsimp only [drop]
      unfold_wf
      apply @lt_of_le_of_lt _ _ _ xs.sizeof
      · clear * -
        induction xs generalizing j <;> unfold_wf
        case nil j => rfl
        case cons xs_hd xs_tl xs_ih j =>
          cases j <;> unfold_wf; rfl
          trans; apply xs_ih
          simp
      unfold_wf
    · unfold_wf
      apply xs_ih _ _ h
      apply lt_of_succ_lt_succ hi
#align list.sizeof_slice_lt List.sizeOf_dropSlice_lt

/-! ### nthd and inth -/


section Nthd

variable (l : List α) (x : α) (xs : List α) (d : α) (n : ℕ)

@[simp]
theorem getD_nil : getD [] n d = d :=
  rfl
#align list.nthd_nil List.getD_nilₓ

@[simp]
theorem getD_cons_zero : getD (x :: xs) 0 d = x :=
  rfl
#align list.nthd_cons_zero List.getD_cons_zeroₓ

@[simp]
theorem getD_cons_succ : getD (x :: xs) (n + 1) d = getD xs n d :=
  rfl
#align list.nthd_cons_succ List.getD_cons_succₓ

theorem getD_eq_nthLe {n : ℕ} (hn : n < l.length) : l.nthd n d = l.nthLe n hn :=
  by
  induction' l with hd tl IH generalizing n
  · exact absurd hn (not_lt_of_ge (Nat.zero_le _))
  · cases n
    · exact nthd_cons_zero _ _ _
    · exact IH _
#align list.nthd_eq_nth_le List.getD_eq_nthLeₓ

theorem getD_eq_default {n : ℕ} (hn : l.length ≤ n) : l.nthd n d = d :=
  by
  induction' l with hd tl IH generalizing n
  · exact nthd_nil _ _
  · cases n
    · refine' absurd (Nat.zero_lt_succ _) (not_lt_of_ge hn)
    · exact IH (Nat.le_of_succ_le_succ hn)
#align list.nthd_eq_default List.getD_eq_defaultₓ

/-- An empty list can always be decidably checked for the presence of an element.
Not an instance because it would clash with `decidable_eq α`. -/
def decidableGetDNilNe {α} (a : α) : DecidablePred fun i : ℕ => getD ([] : List α) i a ≠ a :=
  fun i => is_false fun H => H (getD_nil _ _)
#align list.decidable_nthd_nil_ne List.decidableGetDNilNeₓ

@[simp]
theorem getD_singleton_default_eq (n : ℕ) : [d].nthd n d = d := by cases n <;> simp
#align list.nthd_singleton_default_eq List.getD_singleton_default_eqₓ

@[simp]
theorem getD_replicate_default_eq (r n : ℕ) : (replicate r d).nthd n d = d :=
  by
  induction' r with r IH generalizing n
  · simp
  · cases n <;> simp [IH]
#align list.nthd_replicate_default_eq List.getD_replicate_default_eqₓ

theorem getD_append (l l' : List α) (d : α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').nthd n d = l.nthd n d := by
  rw [nthd_eq_nth_le _ _ h', nth_le_append h' h, nthd_eq_nth_le]
#align list.nthd_append List.getD_appendₓ

theorem getD_append_right (l l' : List α) (d : α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').nthd n d = l'.nthd (n - l.length) d :=
  by
  cases' lt_or_le _ _ with h' h'
  · rw [nthd_eq_nth_le _ _ h', nth_le_append_right h h', nthd_eq_nth_le]
  · rw [nthd_eq_default _ _ h', nthd_eq_default]
    rwa [le_tsub_iff_left h, ← length_append]
#align list.nthd_append_right List.getD_append_rightₓ

theorem getD_eq_getD_get? (n : ℕ) : l.nthd n d = (l.nth n).getOrElse d :=
  by
  cases' lt_or_le _ _ with h h
  · rw [nthd_eq_nth_le _ _ h, nth_le_nth h, Option.getD_some]
  · rw [nthd_eq_default _ _ h, nth_eq_none_iff.mpr h, Option.getD_none]
#align list.nthd_eq_get_or_else_nth List.getD_eq_getD_get?ₓ

end Nthd

section Inth

variable [Inhabited α] (l : List α) (x : α) (xs : List α) (n : ℕ)

#print List.getI_nil /-
@[simp]
theorem getI_nil : getI ([] : List α) n = default :=
  rfl
#align list.inth_nil List.getI_nil
-/

#print List.getI_cons_zero /-
@[simp]
theorem getI_cons_zero : getI (x :: xs) 0 = x :=
  rfl
#align list.inth_cons_zero List.getI_cons_zero
-/

#print List.getI_cons_succ /-
@[simp]
theorem getI_cons_succ : getI (x :: xs) (n + 1) = getI xs n :=
  rfl
#align list.inth_cons_succ List.getI_cons_succ
-/

#print List.getI_eq_nthLe /-
theorem getI_eq_nthLe {n : ℕ} (hn : n < l.length) : l.inth n = l.nthLe n hn :=
  getD_eq_nthLe _ _ _
#align list.inth_eq_nth_le List.getI_eq_nthLe
-/

#print List.getI_eq_default /-
theorem getI_eq_default {n : ℕ} (hn : l.length ≤ n) : l.inth n = default :=
  getD_eq_default _ _ hn
#align list.inth_eq_default List.getI_eq_default
-/

theorem getD_default_eq_getI : l.nthd n default = l.inth n :=
  rfl
#align list.nthd_default_eq_inth List.getD_default_eq_getIₓ

#print List.getI_append /-
theorem getI_append (l l' : List α) (n : ℕ) (h : n < l.length)
    (h' : n < (l ++ l').length := h.trans_le ((length_append l l').symm ▸ le_self_add)) :
    (l ++ l').inth n = l.inth n :=
  getD_append _ _ _ _ h h'
#align list.inth_append List.getI_append
-/

#print List.getI_append_right /-
theorem getI_append_right (l l' : List α) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').inth n = l'.inth (n - l.length) :=
  getD_append_right _ _ _ _ h
#align list.inth_append_right List.getI_append_right
-/

#print List.getI_eq_iget_get? /-
theorem getI_eq_iget_get? (n : ℕ) : l.inth n = (l.nth n).iget := by
  rw [← nthd_default_eq_inth, nthd_eq_get_or_else_nth, Option.getD_default_eq_iget]
#align list.inth_eq_iget_nth List.getI_eq_iget_get?
-/

#print List.getI_zero_eq_headI /-
theorem getI_zero_eq_headI : l.inth 0 = l.head := by cases l <;> rfl
#align list.inth_zero_eq_head List.getI_zero_eq_headI
-/

end Inth

end List

