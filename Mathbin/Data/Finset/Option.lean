/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
import Mathbin.Data.Finset.Card
import Mathbin.Order.Hom.Basic

/-!
# Finite sets in `option α`

In this file we define

* `option.to_finset`: construct an empty or singleton `finset α` from an `option α`;
* `finset.insert_none`: given `s : finset α`, lift it to a finset on `option α` using `option.some`
  and then insert `option.none`;
* `finset.erase_none`: given `s : finset (option α)`, returns `t : finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/


variable {α β : Type _}

open Function

namespace Option

/-- Construct an empty or singleton finset from an `option` -/
def toFinset (o : Option α) : Finsetₓ α :=
  o.elim ∅ singleton

@[simp]
theorem to_finset_none : none.toFinset = (∅ : Finsetₓ α) :=
  rfl

@[simp]
theorem to_finset_some {a : α} : (some a).toFinset = {a} :=
  rfl

@[simp]
theorem mem_to_finset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by cases o <;> simp [eq_comm]

theorem card_to_finset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl

end Option

namespace Finsetₓ

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insertNone : Finsetₓ α ↪o Finsetₓ (Option α) :=
  (OrderEmbedding.ofMapLeIff fun s => cons none (s.map Embedding.some) <| by simp) fun s t =>
    cons_subset_cons.trans map_subset_map

/-⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, s.nodup.map $ λ a b, option.some.inj⟩⟩-/
@[simp]
theorem mem_insert_none {s : Finsetₓ α} : ∀ {o : Option α}, o ∈ s.insertNone ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp <;> rfl

theorem some_mem_insert_none {s : Finsetₓ α} {a : α} : some a ∈ s.insertNone ↔ a ∈ s := by simp

@[simp]
theorem card_insert_none (s : Finsetₓ α) : s.insertNone.card = s.card + 1 := by simp [insert_none]

/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def eraseNone : Finsetₓ (Option α) →o Finsetₓ α :=
  (Finsetₓ.mapEmbedding (Equivₓ.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp ⟨Finsetₓ.subtype _, subtype_mono⟩

@[simp]
theorem mem_erase_none {s : Finsetₓ (Option α)} {x : α} : x ∈ s.eraseNone ↔ some x ∈ s := by simp [erase_none]

theorem erase_none_eq_bUnion [DecidableEq α] (s : Finsetₓ (Option α)) : s.eraseNone = s.bUnion Option.toFinset := by
  ext
  simp

@[simp]
theorem erase_none_map_some (s : Finsetₓ α) : (s.map Embedding.some).eraseNone = s := by
  ext
  simp

@[simp]
theorem erase_none_image_some [DecidableEq (Option α)] (s : Finsetₓ α) : (s.Image some).eraseNone = s := by
  simpa only [map_eq_image] using erase_none_map_some s

@[simp]
theorem coe_erase_none (s : Finsetₓ (Option α)) : (s.eraseNone : Set α) = some ⁻¹' s :=
  Set.ext fun x => mem_erase_none

@[simp]
theorem erase_none_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finsetₓ (Option α)) :
    (s ∪ t).eraseNone = s.eraseNone ∪ t.eraseNone := by
  ext
  simp

@[simp]
theorem erase_none_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finsetₓ (Option α)) :
    (s ∩ t).eraseNone = s.eraseNone ∩ t.eraseNone := by
  ext
  simp

@[simp]
theorem erase_none_empty : (∅ : Finsetₓ (Option α)).eraseNone = ∅ := by
  ext
  simp

@[simp]
theorem erase_none_none : ({none} : Finsetₓ (Option α)).eraseNone = ∅ := by
  ext
  simp

@[simp]
theorem image_some_erase_none [DecidableEq (Option α)] (s : Finsetₓ (Option α)) :
    s.eraseNone.Image some = s.erase none := by ext (_ | x) <;> simp

@[simp]
theorem map_some_erase_none [DecidableEq (Option α)] (s : Finsetₓ (Option α)) :
    s.eraseNone.map Embedding.some = s.erase none := by rw [map_eq_image, embedding.some_apply, image_some_erase_none]

@[simp]
theorem insert_none_erase_none [DecidableEq (Option α)] (s : Finsetₓ (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp

@[simp]
theorem erase_none_insert_none (s : Finsetₓ α) : eraseNone (insertNone s) = s := by
  ext
  simp

end Finsetₓ

