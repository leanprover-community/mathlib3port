/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

! This file was ported from Lean 3 source module data.list.alist
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Sigma

/-!
# Association Lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `sigma`: The elements of the list are of type `sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `alist` structure. This file defines this structure and
provides ways to access, modify, and combine `alist`s.

* `alist.keys` returns a list of keys of the alist.
* `alist.has_mem` returns membership in the set of keys.
* `alist.erase` removes a certain key.
* `alist.insert` adds a key-value mapping to the list.
* `alist.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/


universe u v w

open List

variable {α : Type u} {β : α → Type v}

#print AList /-
/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure AList (β : α → Type v) : Type max u v where
  entries : List (Sigma β)
  Nodupkeys : entries.Nodupkeys
#align alist AList
-/

#print List.toAList /-
/-- Given `l : list (sigma β)`, create a term of type `alist β` by removing
entries with duplicate keys. -/
def List.toAList [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : AList β
    where
  entries := _
  Nodupkeys := nodupKeys_dedupKeys l
#align list.to_alist List.toAList
-/

namespace AList

#print AList.ext /-
@[ext]
theorem ext : ∀ {s t : AList β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩, H => by congr
#align alist.ext AList.ext
-/

#print AList.ext_iff /-
theorem ext_iff {s t : AList β} : s = t ↔ s.entries = t.entries :=
  ⟨congr_arg _, ext⟩
#align alist.ext_iff AList.ext_iff
-/

instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (AList β) := fun xs ys => by
  rw [ext_iff] <;> infer_instance

/-! ### keys -/


#print AList.keys /-
/-- The list of keys of an association list. -/
def keys (s : AList β) : List α :=
  s.entries.keys
#align alist.keys AList.keys
-/

#print AList.keys_nodup /-
theorem keys_nodup (s : AList β) : s.keys.Nodup :=
  s.Nodupkeys
#align alist.keys_nodup AList.keys_nodup
-/

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : Membership α (AList β) :=
  ⟨fun a s => a ∈ s.keys⟩

#print AList.mem_keys /-
theorem mem_keys {a : α} {s : AList β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl
#align alist.mem_keys AList.mem_keys
-/

#print AList.mem_of_perm /-
theorem mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff
#align alist.mem_of_perm AList.mem_of_perm
-/

/-! ### empty -/


/-- The empty association list. -/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], nodupKeys_nil⟩⟩

instance : Inhabited (AList β) :=
  ⟨∅⟩

#print AList.not_mem_empty /-
@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : AList β) :=
  not_mem_nil a
#align alist.not_mem_empty AList.not_mem_empty
-/

#print AList.empty_entries /-
@[simp]
theorem empty_entries : (∅ : AList β).entries = [] :=
  rfl
#align alist.empty_entries AList.empty_entries
-/

#print AList.keys_empty /-
@[simp]
theorem keys_empty : (∅ : AList β).keys = [] :=
  rfl
#align alist.keys_empty AList.keys_empty
-/

/-! ### singleton -/


#print AList.singleton /-
/-- The singleton association list. -/
def singleton (a : α) (b : β a) : AList β :=
  ⟨[⟨a, b⟩], nodupKeys_singleton _⟩
#align alist.singleton AList.singleton
-/

#print AList.singleton_entries /-
@[simp]
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl
#align alist.singleton_entries AList.singleton_entries
-/

#print AList.keys_singleton /-
@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl
#align alist.keys_singleton AList.keys_singleton
-/

/-! ### lookup -/


section

variable [DecidableEq α]

#print AList.lookup /-
/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.lookup a
#align alist.lookup AList.lookup
-/

#print AList.lookup_empty /-
@[simp]
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl
#align alist.lookup_empty AList.lookup_empty
-/

#print AList.lookup_isSome /-
theorem lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a ∈ s :=
  lookup_is_some
#align alist.lookup_is_some AList.lookup_isSome
-/

#print AList.lookup_eq_none /-
theorem lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s :=
  lookup_eq_none
#align alist.lookup_eq_none AList.lookup_eq_none
-/

#print AList.mem_lookup_iff /-
theorem mem_lookup_iff {a : α} {b : β a} {s : AList β} :
    b ∈ lookup a s ↔ Sigma.mk a b ∈ s.entries :=
  mem_dlookup_iff s.Nodupkeys
#align alist.mem_lookup_iff AList.mem_lookup_iff
-/

#print AList.perm_lookup /-
theorem perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.Nodupkeys s₂.Nodupkeys p
#align alist.perm_lookup AList.perm_lookup
-/

instance (a : α) (s : AList β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome

/-! ### replace -/


#print AList.replace /-
/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.Nodupkeys⟩
#align alist.replace AList.replace
-/

#print AList.keys_replace /-
@[simp]
theorem keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _
#align alist.keys_replace AList.keys_replace
-/

#print AList.mem_replace /-
@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : AList β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]
#align alist.mem_replace AList.mem_replace
-/

#print AList.perm_replace /-
theorem perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.Nodupkeys
#align alist.perm_replace AList.perm_replace
-/

end

#print AList.foldl /-
/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d
#align alist.foldl AList.foldl
-/

/-! ### erase -/


section

variable [DecidableEq α]

#print AList.erase /-
/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : AList β) : AList β :=
  ⟨s.entries.kerase a, s.Nodupkeys.kerase a⟩
#align alist.erase AList.erase
-/

/- warning: alist.keys_erase -> AList.keys_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : AList.{u1, u2} α β), Eq.{succ u1} (List.{u1} α) (AList.keys.{u1, u2} α β (AList.erase.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a s)) (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (AList.keys.{u1, u2} α β s) a)
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : AList.{u1, u2} α β), Eq.{succ u1} (List.{u1} α) (AList.keys.{u1, u2} α β (AList.erase.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a s)) (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (AList.keys.{u1, u2} α β s) a)
Case conversion may be inaccurate. Consider using '#align alist.keys_erase AList.keys_eraseₓ'. -/
@[simp]
theorem keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase
#align alist.keys_erase AList.keys_erase

#print AList.mem_erase /-
@[simp]
theorem mem_erase {a a' : α} {s : AList β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]
#align alist.mem_erase AList.mem_erase
-/

#print AList.perm_erase /-
theorem perm_erase {a : α} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.Nodupkeys
#align alist.perm_erase AList.perm_erase
-/

#print AList.lookup_erase /-
@[simp]
theorem lookup_erase (a) (s : AList β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.Nodupkeys
#align alist.lookup_erase AList.lookup_erase
-/

#print AList.lookup_erase_ne /-
@[simp]
theorem lookup_erase_ne {a a'} {s : AList β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h
#align alist.lookup_erase_ne AList.lookup_erase_ne
-/

#print AList.erase_erase /-
theorem erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase
#align alist.erase_erase AList.erase_erase
-/

/-! ### insert -/


#print AList.insert /-
/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.Nodupkeys⟩
#align alist.insert AList.insert
-/

#print AList.insert_entries /-
@[simp]
theorem insert_entries {a} {b : β a} {s : AList β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl
#align alist.insert_entries AList.insert_entries
-/

#print AList.insert_entries_of_neg /-
theorem insert_entries_of_neg {a} {b : β a} {s : AList β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [insert_entries, kerase_of_not_mem_keys h]
#align alist.insert_entries_of_neg AList.insert_entries_of_neg
-/

-- Todo: rename to `insert_of_not_mem`.
theorem insert_of_neg {a} {b : β a} {s : AList β} (h : a ∉ s) :
    insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩ :=
  ext <| insert_entries_of_neg h
#align alist.insert_of_neg AList.insert_of_neg

#print AList.insert_empty /-
@[simp]
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl
#align alist.insert_empty AList.insert_empty
-/

#print AList.mem_insert /-
@[simp]
theorem mem_insert {a a'} {b' : β a'} (s : AList β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert
#align alist.mem_insert AList.mem_insert
-/

/- warning: alist.keys_insert -> AList.keys_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {b : β a} (s : AList.{u1, u2} α β), Eq.{succ u1} (List.{u1} α) (AList.keys.{u1, u2} α (fun {a : α} => β a) (AList.insert.{u1, u2} α (fun {a : α} => β a) (fun (a : α) (b : α) => _inst_1 a b) a b s)) (List.cons.{u1} α a (List.eraseₓ.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (AList.keys.{u1, u2} α β s) a))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {b : β a} (s : AList.{u1, u2} α β), Eq.{succ u1} (List.{u1} α) (AList.keys.{u1, u2} α β (AList.insert.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a b s)) (List.cons.{u1} α a (List.erase.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (AList.keys.{u1, u2} α β s) a))
Case conversion may be inaccurate. Consider using '#align alist.keys_insert AList.keys_insertₓ'. -/
@[simp]
theorem keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]
#align alist.keys_insert AList.keys_insert

#print AList.perm_insert /-
theorem perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [insert_entries] <;> exact p.kinsert s₁.nodupkeys
#align alist.perm_insert AList.perm_insert
-/

#print AList.lookup_insert /-
@[simp]
theorem lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, lookup_kinsert]
#align alist.lookup_insert AList.lookup_insert
-/

#print AList.lookup_insert_ne /-
@[simp]
theorem lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a ≠ a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h
#align alist.lookup_insert_ne AList.lookup_insert_ne
-/

#print AList.lookup_to_alist /-
@[simp]
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAlist = s.lookup a := by
  rw [List.toAList, lookup, lookup_dedupkeys]
#align alist.lookup_to_alist AList.lookup_to_alist
-/

#print AList.insert_insert /-
@[simp]
theorem insert_insert {a} {b b' : β a} (s : AList β) : (s.insert a b).insert a b' = s.insert a b' :=
  by
  ext : 1 <;> simp only [AList.insert_entries, List.kerase_cons_eq] <;> constructorm*_ ∧ _ <;> rfl
#align alist.insert_insert AList.insert_insert
-/

#print AList.insert_insert_of_ne /-
theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [insert_entries] <;> rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply perm.swap, exact h, exact h.symm]
#align alist.insert_insert_of_ne AList.insert_insert_of_ne
-/

#print AList.insert_singleton_eq /-
@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [AList.insert_entries, List.kerase_cons_eq, and_self_iff, AList.singleton_entries,
      hEq_iff_eq, eq_self_iff_true]
#align alist.insert_singleton_eq AList.insert_singleton_eq
-/

#print AList.entries_toAList /-
@[simp]
theorem entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupKeys xs :=
  rfl
#align alist.entries_to_alist AList.entries_toAList
-/

#print AList.toAList_cons /-
theorem toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAList (⟨a, b⟩ :: xs) = insert a b xs.toAlist :=
  rfl
#align alist.to_alist_cons AList.toAList_cons
-/

theorem mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).Nodupkeys) :
    (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h⟩ := by
  simpa [insert] using (kerase_of_not_mem_keys <| not_mem_keys_of_nodupkeys_cons h).symm
#align alist.mk_cons_eq_insert AList.mk_cons_eq_insert

/- warning: alist.insert_rec -> AList.insertRec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {C : (AList.{u1, u2} α β) -> Sort.{u3}}, (C (EmptyCollection.emptyCollection.{max u1 u2} (AList.{u1, u2} α β) (AList.hasEmptyc.{u1, u2} α β))) -> (forall (a : α) (b : β a) (l : AList.{u1, u2} α β), (Not (Membership.Mem.{u1, max u1 u2} α (AList.{u1, u2} α β) (AList.hasMem.{u1, u2} α β) a l)) -> (C l) -> (C (AList.insert.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) a b l))) -> (forall (l : AList.{u1, u2} α β), C l)
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u3}} [_inst_1 : DecidableEq.{succ u2} α] {C : (AList.{u2, u3} α β) -> Sort.{u1}}, (C (EmptyCollection.emptyCollection.{max u2 u3} (AList.{u2, u3} α β) (AList.hasEmptyc.{u2, u3} α β))) -> (forall (a : α) (b : β a) (l : AList.{u2, u3} α β), (Not (Membership.Mem.{u2, max u2 u3} α (AList.{u2, u3} α β) (AList.hasMem.{u2, u3} α β) a l)) -> (C l) -> (C (AList.insert.{u2, u3} α β (fun (a : α) (b : α) => _inst_1 a b) a b l))) -> (forall (l : AList.{u2, u3} α β), C l)
Case conversion may be inaccurate. Consider using '#align alist.insert_rec AList.insertRecₓ'. -/
/-- Recursion on an `alist`, using `insert`. Use as `induction l using alist.insert_rec`. -/
@[elab_as_elim]
def insertRec {C : AList β → Sort _} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β) (h : a ∉ l), C l → C (l.insert a b)) :
    ∀ l : AList β, C l
  | ⟨[], _⟩ => H0
  | ⟨c :: l, h⟩ => by
    rw [mk_cons_eq_insert]
    refine' IH _ _ _ _ (insert_rec _)
    exact not_mem_keys_of_nodupkeys_cons h
#align alist.insert_rec AList.insertRec

-- Test that the `induction` tactic works on `insert_rec`.
example (l : AList β) : True := by induction l using AList.insertRec <;> trivial

@[simp]
theorem insertRec_empty {C : AList β → Sort _} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β) (h : a ∉ l), C l → C (l.insert a b)) :
    @insertRec α β _ C H0 IH ∅ = H0 :=
  by
  change @insert_rec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insert_rec]
#align alist.insert_rec_empty AList.insertRec_empty

theorem insertRec_insert {C : AList β → Sort _} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β) (h : a ∉ l), C l → C (l.insert a b)) {c : Sigma β}
    {l : AList β} (h : c.1 ∉ l) :
    @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l h (@insertRec α β _ C H0 IH l) :=
  by
  cases' l with l hl
  suffices
    HEq (@insert_rec α β _ C H0 IH ⟨c :: l, nodupkeys_cons.2 ⟨h, hl⟩⟩)
      (IH c.1 c.2 ⟨l, hl⟩ h (@insert_rec α β _ C H0 IH ⟨l, hl⟩))
    by
    cases c
    apply eq_of_hEq
    convert this <;> rw [insert_of_neg h]
  rw [insert_rec]
  apply cast_hEq
#align alist.insert_rec_insert AList.insertRec_insert

theorem recursion_insert_mk {C : AList β → Sort _} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β) (h : a ∉ l), C l → C (l.insert a b)) {a : α} (b : β a)
    {l : AList β} (h : a ∉ l) :
    @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (@insertRec α β _ C H0 IH l) :=
  @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h
#align alist.recursion_insert_mk AList.recursion_insert_mk

/-! ### extract -/


#print AList.extract /-
/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : AList β) : Option (β a) × AList β :=
  have : (kextract a s.entries).2.Nodupkeys := by
    rw [kextract_eq_lookup_kerase] <;> exact s.nodupkeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)
#align alist.extract AList.extract
-/

#print AList.extract_eq_lookup_erase /-
@[simp]
theorem extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s, erase a s) := by
  simp [extract] <;> constructor <;> rfl
#align alist.extract_eq_lookup_erase AList.extract_eq_lookup_erase
-/

/-! ### union -/


#print AList.union /-
/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : AList β) : AList β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.Nodupkeys.kunion s₂.Nodupkeys⟩
#align alist.union AList.union
-/

instance : Union (AList β) :=
  ⟨union⟩

#print AList.union_entries /-
@[simp]
theorem union_entries {s₁ s₂ : AList β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl
#align alist.union_entries AList.union_entries
-/

#print AList.empty_union /-
@[simp]
theorem empty_union {s : AList β} : (∅ : AList β) ∪ s = s :=
  ext rfl
#align alist.empty_union AList.empty_union
-/

#print AList.union_empty /-
@[simp]
theorem union_empty {s : AList β} : s ∪ (∅ : AList β) = s :=
  ext <| by simp
#align alist.union_empty AList.union_empty
-/

#print AList.mem_union /-
@[simp]
theorem mem_union {a} {s₁ s₂ : AList β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion
#align alist.mem_union AList.mem_union
-/

#print AList.perm_union /-
theorem perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [p₁₂.kunion s₃.nodupkeys p₃₄]
#align alist.perm_union AList.perm_union
-/

#print AList.union_erase /-
theorem union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm
#align alist.union_erase AList.union_erase
-/

#print AList.lookup_union_left /-
@[simp]
theorem lookup_union_left {a} {s₁ s₂ : AList β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  lookup_kunion_left
#align alist.lookup_union_left AList.lookup_union_left
-/

#print AList.lookup_union_right /-
@[simp]
theorem lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  lookup_kunion_right
#align alist.lookup_union_right AList.lookup_union_right
-/

#print AList.mem_lookup_union /-
@[simp]
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_lookup_kunion
#align alist.mem_lookup_union AList.mem_lookup_union
-/

#print AList.mem_lookup_union_middle /-
theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_lookup_kunion_middle
#align alist.mem_lookup_union_middle AList.mem_lookup_union_middle
-/

#print AList.insert_union /-
theorem insert_union {a} {b : β a} {s₁ s₂ : AList β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  by ext <;> simp
#align alist.insert_union AList.insert_union
-/

#print AList.union_assoc /-
theorem union_assoc {s₁ s₂ s₃ : AList β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [Decidable.not_or_iff_and_not, or_assoc', and_or_left, and_assoc'])
#align alist.union_assoc AList.union_assoc
-/

end

/-! ### disjoint -/


#print AList.Disjoint /-
/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  ∀ k ∈ s₁.keys, ¬k ∈ s₂.keys
#align alist.disjoint AList.Disjoint
-/

variable [DecidableEq α]

#print AList.union_comm_of_disjoint /-
theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros ; simp
      constructor <;> intro h'
      cases h'
      · right
        refine' ⟨_, h'⟩
        apply h
        rw [keys, ← List.dlookup_isSome, h']
        exact rfl
      · left
        rw [h'.2]
      cases h'
      · right
        refine' ⟨_, h'⟩
        intro h''
        apply h _ h''
        rw [keys, ← List.dlookup_isSome, h']
        exact rfl
      · left
        rw [h'.2])
#align alist.union_comm_of_disjoint AList.union_comm_of_disjoint
-/

end AList

