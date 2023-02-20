/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather

! This file was ported from Lean 3 source module data.list.sigma
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Range
import Mathbin.Data.List.Perm

/-!
# Utilities for lists of sigmas

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes several ways of interacting with `list (sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `list (sigma β)` behaves like a key-value store.

## Main Definitions

- `list.keys` extracts the list of keys.
- `list.nodupkeys` determines if the store has duplicate keys.
- `list.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `list.kreplace` replaces the first value with a given key by a given value.
- `list.kerase` removes a value.
- `list.kinsert` inserts a value.
- `list.kunion` computes the union of two stores.
- `list.kextract` returns a value with a given key and the rest of the values.
-/


universe u v

namespace List

variable {α : Type u} {β : α → Type v} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/


#print List.keys /-
/-- List of keys from a list of key-value pairs -/
def keys : List (Sigma β) → List α :=
  map Sigma.fst
#align list.keys List.keys
-/

#print List.keys_nil /-
@[simp]
theorem keys_nil : @keys α β [] = [] :=
  rfl
#align list.keys_nil List.keys_nil
-/

#print List.keys_cons /-
@[simp]
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl
#align list.keys_cons List.keys_cons
-/

#print List.mem_keys_of_mem /-
theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s ∈ l → s.1 ∈ l.keys :=
  mem_map_of_mem Sigma.fst
#align list.mem_keys_of_mem List.mem_keys_of_mem
-/

#print List.exists_of_mem_keys /-
theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ b : β a, Sigma.mk a b ∈ l :=
  let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_map' h
  Eq.recOn e (Exists.intro b' m)
#align list.exists_of_mem_keys List.exists_of_mem_keys
-/

#print List.mem_keys /-
theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨b, h⟩ => mem_keys_of_mem h⟩
#align list.mem_keys List.mem_keys
-/

#print List.not_mem_keys /-
theorem not_mem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l :=
  (not_congr mem_keys).trans not_exists
#align list.not_mem_keys List.not_mem_keys
-/

#print List.not_eq_key /-
theorem not_eq_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 :=
  Iff.intro (fun h₁ s h₂ e => absurd (mem_keys_of_mem h₂) (by rwa [e] at h₁)) fun f h₁ =>
    let ⟨b, h₂⟩ := exists_of_mem_keys h₁
    f _ h₂ rfl
#align list.not_eq_key List.not_eq_key
-/

/-! ### `nodupkeys` -/


#print List.NodupKeys /-
/-- Determines whether the store uses a key several times. -/
def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup
#align list.nodupkeys List.NodupKeys
-/

#print List.nodupKeys_iff_pairwise /-
theorem nodupKeys_iff_pairwise {l} : NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map' _
#align list.nodupkeys_iff_pairwise List.nodupKeys_iff_pairwise
-/

#print List.NodupKeys.pairwise_ne /-
theorem NodupKeys.pairwise_ne {l} (h : NodupKeys l) :
    Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupKeys_iff_pairwise.1 h
#align list.nodupkeys.pairwise_ne List.NodupKeys.pairwise_ne
-/

#print List.nodupKeys_nil /-
@[simp]
theorem nodupKeys_nil : @NodupKeys α β [] :=
  Pairwise.nil
#align list.nodupkeys_nil List.nodupKeys_nil
-/

#print List.nodupKeys_cons /-
@[simp]
theorem nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
    NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l := by simp [keys, nodupkeys]
#align list.nodupkeys_cons List.nodupKeys_cons
-/

theorem not_mem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    s.1 ∉ l.keys :=
  (nodupKeys_cons.1 h).1
#align list.not_mem_keys_of_nodupkeys_cons List.not_mem_keys_of_nodupKeys_cons

theorem nodupKeys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    NodupKeys l :=
  (nodupKeys_cons.1 h).2
#align list.nodupkeys_of_nodupkeys_cons List.nodupKeys_of_nodupKeys_cons

#print List.NodupKeys.eq_of_fst_eq /-
theorem NodupKeys.eq_of_fst_eq {l : List (Sigma β)} (nd : NodupKeys l) {s s' : Sigma β} (h : s ∈ l)
    (h' : s' ∈ l) : s.1 = s'.1 → s = s' :=
  @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') _
    (fun s s' H h => (H h.symm).symm) (fun x h _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun s s' h h' => (h h').elim) _ h _ h'
#align list.nodupkeys.eq_of_fst_eq List.NodupKeys.eq_of_fst_eq
-/

#print List.NodupKeys.eq_of_mk_mem /-
theorem NodupKeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) (h' : Sigma.mk a b' ∈ l) : b = b' := by
  cases nd.eq_of_fst_eq h h' rfl <;> rfl
#align list.nodupkeys.eq_of_mk_mem List.NodupKeys.eq_of_mk_mem
-/

#print List.nodupKeys_singleton /-
theorem nodupKeys_singleton (s : Sigma β) : NodupKeys [s] :=
  nodup_singleton _
#align list.nodupkeys_singleton List.nodupKeys_singleton
-/

#print List.NodupKeys.sublist /-
theorem NodupKeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : NodupKeys l₂ → NodupKeys l₁ :=
  Nodup.sublist <| h.map _
#align list.nodupkeys.sublist List.NodupKeys.sublist
-/

#print List.NodupKeys.nodup /-
protected theorem NodupKeys.nodup {l : List (Sigma β)} : NodupKeys l → Nodup l :=
  Nodup.of_map _
#align list.nodupkeys.nodup List.NodupKeys.nodup
-/

#print List.perm_nodupKeys /-
theorem perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : NodupKeys l₁ ↔ NodupKeys l₂ :=
  (h.map _).nodup_iff
#align list.perm_nodupkeys List.perm_nodupKeys
-/

#print List.nodupKeys_join /-
theorem nodupKeys_join {L : List (List (Sigma β))} :
    NodupKeys (join L) ↔ (∀ l ∈ L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys) :=
  by
  rw [nodupkeys_iff_pairwise, pairwise_join, pairwise_map]
  refine' and_congr (ball_congr fun l h => by simp [nodupkeys_iff_pairwise]) _
  apply iff_of_eq; congr with (l₁ l₂)
  simp [keys, disjoint_iff_ne]
#align list.nodupkeys_join List.nodupKeys_join
-/

#print List.nodup_enum_map_fst /-
theorem nodup_enum_map_fst (l : List α) : (l.enum.map Prod.fst).Nodup := by simp [List.nodup_range]
#align list.nodup_enum_map_fst List.nodup_enum_map_fst
-/

#print List.mem_ext /-
theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
    (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ :=
  by
  induction' l₀ with x xs generalizing l₁ <;> cases' l₁ with y ys
  · constructor
  iterate 2 
    first |specialize h x|specialize h y; simp at h
    cases h
  simp at nd₀ nd₁
  classical
    obtain rfl | h' := eq_or_ne x y
    · constructor
      refine' l₀_ih nd₀.2 nd₁.2 fun a => _
      specialize h a
      simp at h
      obtain rfl | h' := eq_or_ne a x
      · exact iff_of_false nd₀.1 nd₁.1
      · simpa [h'] using h
    · trans x :: y :: ys.erase x
      · constructor
        refine' l₀_ih nd₀.2 ((nd₁.2.eraseₓ _).cons fun h => nd₁.1 <| mem_of_mem_erase h) fun a => _
        · specialize h a
          simp at h
          obtain rfl | h' := eq_or_ne a x
          · exact iff_of_false nd₀.1 fun h => h.elim h' nd₁.2.not_mem_erase
          · rw [or_iff_right h'] at h
            rw [h, mem_cons_iff]
            exact or_congr_right (mem_erase_of_ne h').symm
      trans y :: x :: ys.erase x
      · constructor
      · constructor
        symm
        apply perm_cons_erase
        specialize h x
        simp [h'] at h
        exact h
#align list.mem_ext List.mem_ext
-/

variable [DecidableEq α]

/-! ### `lookup` -/


#print List.dlookup /-
/-- `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else lookup l
#align list.lookup List.dlookup
-/

#print List.dlookup_nil /-
@[simp]
theorem dlookup_nil (a : α) : dlookup a [] = @none (β a) :=
  rfl
#align list.lookup_nil List.dlookup_nil
-/

#print List.dlookup_cons_eq /-
@[simp]
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl
#align list.lookup_cons_eq List.dlookup_cons_eq
-/

#print List.dlookup_cons_ne /-
@[simp]
theorem dlookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → dlookup a (s :: l) = dlookup a l
  | ⟨a', b⟩, h => dif_neg h.symm
#align list.lookup_cons_ne List.dlookup_cons_ne
-/

#print List.dlookup_isSome /-
theorem dlookup_isSome {a : α} : ∀ {l : List (Sigma β)}, (dlookup a l).isSome ↔ a ∈ l.keys
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, lookup_is_some]
#align list.lookup_is_some List.dlookup_isSome
-/

#print List.dlookup_eq_none /-
theorem dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.keys := by
  simp [← lookup_is_some, Option.isNone_iff_eq_none]
#align list.lookup_eq_none List.dlookup_eq_none
-/

#print List.of_mem_dlookup /-
theorem of_mem_dlookup {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ dlookup a l → Sigma.mk a b ∈ l
  | ⟨a', b'⟩ :: l, H => by
    by_cases h : a = a'
    · subst a'
      simp at H
      simp [H]
    · simp [h] at H
      exact Or.inr (of_mem_lookup H)
#align list.of_mem_lookup List.of_mem_dlookup
-/

#print List.mem_dlookup /-
theorem mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sigma.mk a b ∈ l) :
    b ∈ dlookup a l :=
  by
  cases' option.is_some_iff_exists.mp (lookup_is_some.mpr (mem_keys_of_mem h)) with b' h'
  cases nd.eq_of_mk_mem h (of_mem_lookup h')
  exact h'
#align list.mem_lookup List.mem_dlookup
-/

#print List.map_dlookup_eq_find /-
theorem map_dlookup_eq_find (a : α) :
    ∀ l : List (Sigma β), (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l
  | [] => rfl
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, map_lookup_eq_find]
#align list.map_lookup_eq_find List.map_dlookup_eq_find
-/

#print List.mem_dlookup_iff /-
theorem mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) :
    b ∈ dlookup a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_dlookup, mem_dlookup nd⟩
#align list.mem_lookup_iff List.mem_dlookup_iff
-/

#print List.perm_dlookup /-
theorem perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (p : l₁ ~ l₂) : dlookup a l₁ = dlookup a l₂ := by
  ext b <;> simp [mem_lookup_iff, nd₁, nd₂] <;> exact p.mem_iff
#align list.perm_lookup List.perm_dlookup
-/

#print List.lookup_ext /-
theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
    (h : ∀ x y, y ∈ l₀.dlookup x ↔ y ∈ l₁.dlookup x) : l₀ ~ l₁ :=
  mem_ext nd₀.Nodup nd₁.Nodup fun ⟨a, b⟩ => by
    rw [← mem_lookup_iff, ← mem_lookup_iff, h] <;> assumption
#align list.lookup_ext List.lookup_ext
-/

/-! ### `lookup_all` -/


#print List.lookupAll /-
/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookupAll (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOn h b :: lookup_all l else lookup_all l
#align list.lookup_all List.lookupAll
-/

#print List.lookupAll_nil /-
@[simp]
theorem lookupAll_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl
#align list.lookup_all_nil List.lookupAll_nil
-/

#print List.lookupAll_cons_eq /-
@[simp]
theorem lookupAll_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl
#align list.lookup_all_cons_eq List.lookupAll_cons_eq
-/

#print List.lookupAll_cons_ne /-
@[simp]
theorem lookupAll_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l
  | ⟨a', b⟩, h => dif_neg h.symm
#align list.lookup_all_cons_ne List.lookupAll_cons_ne
-/

#print List.lookupAll_eq_nil /-
theorem lookupAll_eq_nil {a : α} :
    ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, lookup_all_eq_nil]
#align list.lookup_all_eq_nil List.lookupAll_eq_nil
-/

#print List.head?_lookupAll /-
theorem head?_lookupAll (a : α) : ∀ l : List (Sigma β), head? (lookupAll a l) = dlookup a l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a' <;>
      [·
        subst h
        simp, simp [*]]
#align list.head_lookup_all List.head?_lookupAll
-/

#print List.mem_lookupAll /-
theorem mem_lookupAll {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a' <;>
      [·
        subst h
        simp [*], simp [*]]
#align list.mem_lookup_all List.mem_lookupAll
-/

#print List.lookupAll_sublist /-
theorem lookupAll_sublist (a : α) : ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp
      exact (lookup_all_sublist l).cons₂ _ _ _
    · simp [h]
      exact (lookup_all_sublist l).cons _ _ _
#align list.lookup_all_sublist List.lookupAll_sublist
-/

#print List.lookupAll_length_le_one /-
theorem lookupAll_length_le_one (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    length (lookupAll a l) ≤ 1 := by
  have := nodup.sublist ((lookup_all_sublist a l).map _) h <;> rw [map_map] at this <;>
    rwa [← nodup_replicate, ← map_const _ a]
#align list.lookup_all_length_le_one List.lookupAll_length_le_one
-/

#print List.lookupAll_eq_dlookup /-
theorem lookupAll_eq_dlookup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    lookupAll a l = (dlookup a l).toList :=
  by
  rw [← head_lookup_all]
  have := lookup_all_length_le_one a h; revert this
  rcases lookup_all a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro <;> try rfl
  exact absurd this (by decide)
#align list.lookup_all_eq_lookup List.lookupAll_eq_dlookup
-/

#print List.lookupAll_nodup /-
theorem lookupAll_nodup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : (lookupAll a l).Nodup := by
  rw [lookup_all_eq_lookup a h] <;> apply Option.toList_nodup
#align list.lookup_all_nodup List.lookupAll_nodup
-/

#print List.perm_lookupAll /-
theorem perm_lookupAll (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (p : l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂ := by
  simp [lookup_all_eq_lookup, nd₁, nd₂, perm_lookup a nd₁ nd₂ p]
#align list.perm_lookup_all List.perm_lookupAll
-/

/-! ### `kreplace` -/


#print List.kreplace /-
/-- Replaces the first value with key `a` by `b`. -/
def kreplace (a : α) (b : β a) : List (Sigma β) → List (Sigma β) :=
  lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none
#align list.kreplace List.kreplace
-/

#print List.kreplace_of_forall_not /-
theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)}
    (H : ∀ b : β a, Sigma.mk a b ∉ l) : kreplace a b l = l :=
  lookmap_of_forall_not _ <| by
    rintro ⟨a', b'⟩ h; dsimp; split_ifs
    · subst a'
      exact H _ h; · rfl
#align list.kreplace_of_forall_not List.kreplace_of_forall_not
-/

#print List.kreplace_self /-
theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) : kreplace a b l = l :=
  by
  refine' (lookmap_congr _).trans (lookmap_id' (Option.guard fun s => a = s.1) _ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      exact ⟨rfl, hEq_of_eq <| nd.eq_of_mk_mem h h'⟩
    · rfl
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    dsimp [Option.guard]
    split_ifs
    · exact id
    · rintro ⟨⟩
#align list.kreplace_self List.kreplace_self
-/

#print List.keys_kreplace /-
theorem keys_kreplace (a : α) (b : β a) : ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys :=
  lookmap_map_eq _ _ <| by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩ <;> dsimp <;> split_ifs <;> simp (config := { contextual := true }) [h]
#align list.keys_kreplace List.keys_kreplace
-/

#print List.kreplace_nodupKeys /-
theorem kreplace_nodupKeys (a : α) (b : β a) {l : List (Sigma β)} :
    (kreplace a b l).NodupKeys ↔ l.NodupKeys := by simp [nodupkeys, keys_kreplace]
#align list.kreplace_nodupkeys List.kreplace_nodupKeys
-/

#print List.Perm.kreplace /-
theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ <| by
    refine' nd.pairwise_ne.imp _
    intro x y h z h₁ w h₂
    split_ifs  at h₁ h₂ <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim
#align list.perm.kreplace List.Perm.kreplace
-/

/-! ### `kerase` -/


#print List.kerase /-
/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  eraseP fun s => a = s.1
#align list.kerase List.kerase
-/

#print List.kerase_nil /-
@[simp]
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl
#align list.kerase_nil List.kerase_nil
-/

#print List.kerase_cons_eq /-
@[simp]
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) :
    kerase a (s :: l) = l := by simp [kerase, h]
#align list.kerase_cons_eq List.kerase_cons_eq
-/

#print List.kerase_cons_ne /-
@[simp]
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a ≠ s.1) :
    kerase a (s :: l) = s :: kerase a l := by simp [kerase, h]
#align list.kerase_cons_ne List.kerase_cons_ne
-/

#print List.kerase_of_not_mem_keys /-
@[simp]
theorem kerase_of_not_mem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction' l with _ _ ih <;> [rfl,
    · simp [not_or] at h
      simp [h.1, ih h.2]]
#align list.kerase_of_not_mem_keys List.kerase_of_not_mem_keys
-/

#print List.kerase_sublist /-
theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  eraseP_sublist _
#align list.kerase_sublist List.kerase_sublist
-/

#print List.kerase_keys_subset /-
theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).Subset
#align list.kerase_keys_subset List.kerase_keys_subset
-/

#print List.mem_keys_of_mem_keys_kerase /-
theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} :
    a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _
#align list.mem_keys_of_mem_keys_kerase List.mem_keys_of_mem_keys_kerase
-/

#print List.exists_of_kerase /-
theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a)(l₁ l₂ : List (Sigma β)),
      a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ :=
  by
  induction l
  case nil => cases h
  case cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd <;> rfl, by simp⟩
    · simp at h
      cases h
      case inl h => exact absurd h e
      case inr h =>
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
        exact
          ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by rw [h₂] <;> rfl, by
            simp [e, h₃]⟩
#align list.exists_of_kerase List.exists_of_kerase
-/

#print List.mem_keys_kerase_of_ne /-
@[simp]
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ ≠ a₂) :
    a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
  Iff.intro mem_keys_of_mem_keys_kerase fun p =>
    if q : a₂ ∈ l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]
#align list.mem_keys_kerase_of_ne List.mem_keys_kerase_of_ne
-/

/- warning: list.keys_kerase -> List.keys_kerase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{max u1 u2} (Sigma.{u1, u2} α β)}, Eq.{succ u1} (List.{u1} α) (List.keys.{u1, u2} α β (List.kerase.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a l)) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (List.keys.{u1, u2} α β l) a)
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{max u2 u1} (Sigma.{u1, u2} α β)}, Eq.{succ u1} (List.{u1} α) (List.keys.{u1, u2} α β (List.kerase.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a l)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (List.keys.{u1, u2} α β l) a)
Case conversion may be inaccurate. Consider using '#align list.keys_kerase List.keys_keraseₓ'. -/
theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.eraseₓ a := by
  rw [keys, kerase, ← erasep_map Sigma.fst l, erase_eq_erasep]
#align list.keys_kerase List.keys_kerase

#print List.kerase_kerase /-
theorem kerase_kerase {a a'} {l : List (Sigma β)} :
    (kerase a' l).kerase a = (kerase a l).kerase a' :=
  by
  by_cases a = a'
  · subst a'
  induction' l with x xs; · rfl
  · by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_cons_ne, *]
#align list.kerase_kerase List.kerase_kerase
-/

#print List.NodupKeys.kerase /-
theorem NodupKeys.kerase (a : α) : NodupKeys l → (kerase a l).NodupKeys :=
  NodupKeys.sublist <| kerase_sublist _ _
#align list.nodupkeys.kerase List.NodupKeys.kerase
-/

#print List.Perm.kerase /-
theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
  Perm.erasep _ <| (nodupKeys_iff_pairwise.1 nd).imp <| by rintro x y h rfl <;> exact h
#align list.perm.kerase List.Perm.kerase
-/

#print List.not_mem_keys_kerase /-
@[simp]
theorem not_mem_keys_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) : a ∉ (kerase a l).keys :=
  by
  induction l
  case nil => simp
  case cons hd tl ih =>
    simp at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]
#align list.not_mem_keys_kerase List.not_mem_keys_kerase
-/

#print List.dlookup_kerase /-
@[simp]
theorem dlookup_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    dlookup a (kerase a l) = none :=
  dlookup_eq_none.mpr (not_mem_keys_kerase a nd)
#align list.lookup_kerase List.dlookup_kerase
-/

#print List.dlookup_kerase_ne /-
@[simp]
theorem dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kerase a' l) = dlookup a l :=
  by
  induction l
  case nil => rfl
  case cons hd tl ih =>
    cases' hd with ah bh
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · substs h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]
#align list.lookup_kerase_ne List.dlookup_kerase_ne
-/

#print List.kerase_append_left /-
theorem kerase_append_left {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by cases h
  | s :: l₁, l₂, h₁ =>
    if h₂ : a = s.1 then by simp [h₂]
    else by simp at h₁ <;> cases h₁ <;> [exact absurd h₁ h₂, simp [h₂, kerase_append_left h₁]]
#align list.kerase_append_left List.kerase_append_left
-/

#print List.kerase_append_right /-
theorem kerase_append_right {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, h => rfl
  | _ :: l₁, l₂, h => by simp [not_or] at h <;> simp [h.1, kerase_append_right h.2]
#align list.kerase_append_right List.kerase_append_right
-/

#print List.kerase_comm /-
theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) :
    kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [kerase_append_left h',
              kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]
#align list.kerase_comm List.kerase_comm
-/

/- warning: list.sizeof_kerase -> List.sizeOf_kerase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : SizeOf.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α β)] (x : α) (xs : List.{max u1 u2} (Sigma.{u1, u2} α β)), LE.le.{0} Nat Nat.hasLe (SizeOf.sizeOf.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α β)) (List.hasSizeof.{max u1 u2} (Sigma.{u1, u2} α β) _inst_3) (List.kerase.{u1, u2} α β (fun (a : α) (b : α) => _inst_2 a b) x xs)) (SizeOf.sizeOf.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α β)) (List.hasSizeof.{max u1 u2} (Sigma.{u1, u2} α β) _inst_3) xs)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : SizeOf.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α β)] (x : α) (xs : List.{max u1 u2} (Sigma.{u2, u1} α β)), LE.le.{0} Nat instLENat (SizeOf.sizeOf.{max (succ u1) (succ u2)} (List.{max u1 u2} (Sigma.{u2, u1} α β)) (List._sizeOf_inst.{max u1 u2} (Sigma.{u2, u1} α β) _inst_3) (List.kerase.{u2, u1} α β (fun (a : α) (b : α) => _inst_2 a b) x xs)) (SizeOf.sizeOf.{max (succ u1) (succ u2)} (List.{max u1 u2} (Sigma.{u2, u1} α β)) (List._sizeOf_inst.{max u1 u2} (Sigma.{u2, u1} α β) _inst_3) xs)
Case conversion may be inaccurate. Consider using '#align list.sizeof_kerase List.sizeOf_keraseₓ'. -/
theorem sizeOf_kerase {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (x : α)
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.kerase x xs) ≤ SizeOf.sizeOf xs :=
  by
  unfold_wf
  induction' xs with y ys
  · simp
  · by_cases x = y.1 <;> simp [*, List.sizeof]
#align list.sizeof_kerase List.sizeOf_kerase

/-! ### `kinsert` -/


#print List.kinsert /-
/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l
#align list.kinsert List.kinsert
-/

#print List.kinsert_def /-
@[simp]
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl
#align list.kinsert_def List.kinsert_def
-/

#print List.mem_keys_kinsert /-
theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} :
    a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys := by by_cases h : a = a' <;> simp [h]
#align list.mem_keys_kinsert List.mem_keys_kinsert
-/

#print List.kinsert_nodupKeys /-
theorem kinsert_nodupKeys (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    (kinsert a b l).NodupKeys :=
  nodupKeys_cons.mpr ⟨not_mem_keys_kerase a nd, nd.kerase a⟩
#align list.kinsert_nodupkeys List.kinsert_nodupKeys
-/

#print List.Perm.kinsert /-
theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _
#align list.perm.kinsert List.Perm.kinsert
-/

#print List.dlookup_kinsert /-
theorem dlookup_kinsert {a} {b : β a} (l : List (Sigma β)) : dlookup a (kinsert a b l) = some b :=
  by simp only [kinsert, lookup_cons_eq]
#align list.lookup_kinsert List.dlookup_kinsert
-/

#print List.dlookup_kinsert_ne /-
theorem dlookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kinsert a' b' l) = dlookup a l := by simp [h]
#align list.lookup_kinsert_ne List.dlookup_kinsert_ne
-/

/-! ### `kextract` -/


#print List.kextract /-
/-- Finds the first entry with a given key `a` and returns its value (as an `option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOn h s.2), l)
    else
      let (b', l') := kextract l
      (b', s :: l')
#align list.kextract List.kextract
-/

#print List.kextract_eq_dlookup_kerase /-
@[simp]
theorem kextract_eq_dlookup_kerase (a : α) :
    ∀ l : List (Sigma β), kextract a l = (dlookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp [kextract]; dsimp; split_ifs
    · subst a'
      simp [kerase]
    · simp [kextract, Ne.symm h, kextract_eq_lookup_kerase l, kerase]
#align list.kextract_eq_lookup_kerase List.kextract_eq_dlookup_kerase
-/

/-! ### `dedupkeys` -/


#print List.dedupKeys /-
/-- Remove entries with duplicate keys from `l : list (sigma β)`. -/
def dedupKeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []
#align list.dedupkeys List.dedupKeys
-/

#print List.dedupKeys_cons /-
theorem dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) :
    dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l) :=
  rfl
#align list.dedupkeys_cons List.dedupKeys_cons
-/

#print List.nodupKeys_dedupKeys /-
theorem nodupKeys_dedupKeys (l : List (Sigma β)) : NodupKeys (dedupKeys l) :=
  by
  dsimp [dedupkeys]
  generalize hl : nil = l'
  have : nodupkeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction' l with x xs
  · apply this
  · cases x
    simp [dedupkeys]
    constructor
    · simp [keys_kerase]
      apply l_ih.not_mem_erase
    · exact l_ih.kerase _
#align list.nodupkeys_dedupkeys List.nodupKeys_dedupKeys
-/

#print List.dlookup_dedupKeys /-
theorem dlookup_dedupKeys (a : α) (l : List (Sigma β)) : dlookup a (dedupKeys l) = dlookup a l :=
  by
  induction l; rfl
  cases' l_hd with a' b
  by_cases a = a'
  · subst a'
    rw [dedupkeys_cons, lookup_kinsert, lookup_cons_eq]
  · rw [dedupkeys_cons, lookup_kinsert_ne h, l_ih, lookup_cons_ne]
    exact h
#align list.lookup_dedupkeys List.dlookup_dedupKeys
-/

/- warning: list.sizeof_dedupkeys -> List.sizeOf_dedupKeys is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : SizeOf.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α β)] (xs : List.{max u1 u2} (Sigma.{u1, u2} α β)), LE.le.{0} Nat Nat.hasLe (SizeOf.sizeOf.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α β)) (List.hasSizeof.{max u1 u2} (Sigma.{u1, u2} α β) _inst_3) (List.dedupKeys.{u1, u2} α β (fun (a : α) (b : α) => _inst_2 a b) xs)) (SizeOf.sizeOf.{succ (max u1 u2)} (List.{max u1 u2} (Sigma.{u1, u2} α β)) (List.hasSizeof.{max u1 u2} (Sigma.{u1, u2} α β) _inst_3) xs)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : SizeOf.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α β)] (xs : List.{max u1 u2} (Sigma.{u2, u1} α β)), LE.le.{0} Nat instLENat (SizeOf.sizeOf.{max (succ u1) (succ u2)} (List.{max u1 u2} (Sigma.{u2, u1} α β)) (List._sizeOf_inst.{max u1 u2} (Sigma.{u2, u1} α β) _inst_3) (List.dedupKeys.{u2, u1} α β (fun (a : α) (b : α) => _inst_2 a b) xs)) (SizeOf.sizeOf.{max (succ u1) (succ u2)} (List.{max u1 u2} (Sigma.{u2, u1} α β)) (List._sizeOf_inst.{max u1 u2} (Sigma.{u2, u1} α β) _inst_3) xs)
Case conversion may be inaccurate. Consider using '#align list.sizeof_dedupkeys List.sizeOf_dedupKeysₓ'. -/
theorem sizeOf_dedupKeys {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)]
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.dedupKeys xs) ≤ SizeOf.sizeOf xs :=
  by
  unfold_wf
  induction' xs with x xs
  · simp [List.dedupKeys]
  · simp only [dedupkeys_cons, List.sizeof, kinsert_def, add_le_add_iff_left, Sigma.eta]
    trans
    apply sizeof_kerase
    assumption
#align list.sizeof_dedupkeys List.sizeOf_dedupKeys

/-! ### `kunion` -/


#print List.kunion /-
/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)
#align list.kunion List.kunion
-/

#print List.nil_kunion /-
@[simp]
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl
#align list.nil_kunion List.nil_kunion
-/

#print List.kunion_nil /-
@[simp]
theorem kunion_nil : ∀ {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by rw [kunion, kerase_nil, kunion_nil]
#align list.kunion_nil List.kunion_nil
-/

#print List.kunion_cons /-
@[simp]
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} :
    kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl
#align list.kunion_cons List.kunion_cons
-/

#print List.mem_keys_kunion /-
@[simp]
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} :
    a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h], simp [h, ih]]
#align list.mem_keys_kunion List.mem_keys_kunion
-/

#print List.kunion_kerase /-
@[simp]
theorem kunion_kerase {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by by_cases h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]
#align list.kunion_kerase List.kunion_kerase
-/

#print List.NodupKeys.kunion /-
theorem NodupKeys.kunion (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) : (kunion l₁ l₂).NodupKeys :=
  by
  induction l₁ generalizing l₂
  case nil => simp only [nil_kunion, nd₂]
  case cons s l₁ ih =>
    simp at nd₁
    simp [not_or, nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]
#align list.nodupkeys.kunion List.NodupKeys.kunion
-/

#print List.Perm.kunion_right /-
theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) : kunion l₁ l ~ kunion l₂ l :=
  by
  induction p generalizing l
  case nil => rfl
  case cons hd tl₁ tl₂ p ih => simp [ih (kerase hd.1 l), perm.cons]
  case swap s₁ s₂ l => simp [kerase_comm, perm.swap]
  case trans l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ => exact perm.trans (ih₁₂ l) (ih₂₃ l)
#align list.perm.kunion_right List.Perm.kunion_right
-/

#print List.Perm.kunion_left /-
theorem Perm.kunion_left :
    ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.NodupKeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, l₁, l₂, nd₁, p => by simp [((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s]
#align list.perm.kunion_left List.Perm.kunion_left
-/

#print List.Perm.kunion /-
theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
    (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)
#align list.perm.kunion List.Perm.kunion
-/

#print List.dlookup_kunion_left /-
@[simp]
theorem dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₁ :=
  by
  induction' l₁ with s _ ih generalizing l₂ <;> simp at h <;> cases h <;> cases' s with a'
  · subst h
    simp
  · rw [kunion_cons]
    by_cases h' : a = a'
    · subst h'
      simp
    · simp [h', ih h]
#align list.lookup_kunion_left List.dlookup_kunion_left
-/

#print List.dlookup_kunion_right /-
@[simp]
theorem dlookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₂ :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]
#align list.lookup_kunion_right List.dlookup_kunion_right
-/

#print List.mem_dlookup_kunion /-
@[simp]
theorem mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ dlookup a (kunion l₁ l₂) ↔ b ∈ dlookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ dlookup a l₂ :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons s _ ih =>
    cases' s with a'
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · let h₂ := @ih (kerase a' l₂)
      simp [h₁] at h₂
      simp [h₁, h₂]
#align list.mem_lookup_kunion List.mem_dlookup_kunion
-/

#print List.mem_dlookup_kunion_middle /-
theorem mem_dlookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
    (h₁ : b ∈ dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
    b ∈ dlookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_dlookup_kunion.mpr <| Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩
#align list.mem_lookup_kunion_middle List.mem_dlookup_kunion_middle
-/

end List

