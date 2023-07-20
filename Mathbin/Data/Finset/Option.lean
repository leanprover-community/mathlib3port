/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
import Mathbin.Data.Finset.Card

#align_import data.finset.option from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Finite sets in `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Option.toFinset /-
/-- Construct an empty or singleton finset from an `option` -/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
#align option.to_finset Option.toFinset
-/

#print Option.toFinset_none /-
@[simp]
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl
#align option.to_finset_none Option.toFinset_none
-/

#print Option.toFinset_some /-
@[simp]
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl
#align option.to_finset_some Option.toFinset_some
-/

#print Option.mem_toFinset /-
@[simp]
theorem mem_toFinset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
#align option.mem_to_finset Option.mem_toFinset
-/

#print Option.card_toFinset /-
theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl
#align option.card_to_finset Option.card_toFinset
-/

end Option

namespace Finset

#print Finset.insertNone /-
/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insertNone : Finset α ↪o Finset (Option α) :=
  OrderEmbedding.ofMapLEIff (fun s => cons none (s.map Embedding.some) <| by simp) fun s t =>
    cons_subset_cons.trans map_subset_map
#align finset.insert_none Finset.insertNone
-/

#print Finset.mem_insertNone /-
/-⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, s.nodup.map $ λ a b, option.some.inj⟩⟩-/
@[simp]
theorem mem_insertNone {s : Finset α} : ∀ {o : Option α}, o ∈ s.insertNone ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp <;> rfl
#align finset.mem_insert_none Finset.mem_insertNone
-/

#print Finset.some_mem_insertNone /-
theorem some_mem_insertNone {s : Finset α} {a : α} : some a ∈ s.insertNone ↔ a ∈ s := by simp
#align finset.some_mem_insert_none Finset.some_mem_insertNone
-/

#print Finset.card_insertNone /-
@[simp]
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insert_none]
#align finset.card_insert_none Finset.card_insertNone
-/

#print Finset.eraseNone /-
/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩
#align finset.erase_none Finset.eraseNone
-/

#print Finset.mem_eraseNone /-
@[simp]
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x ∈ s.eraseNone ↔ some x ∈ s := by
  simp [erase_none]
#align finset.mem_erase_none Finset.mem_eraseNone
-/

#print Finset.eraseNone_eq_biUnion /-
theorem eraseNone_eq_biUnion [DecidableEq α] (s : Finset (Option α)) :
    s.eraseNone = s.biUnion Option.toFinset := by ext; simp
#align finset.erase_none_eq_bUnion Finset.eraseNone_eq_biUnion
-/

#print Finset.eraseNone_map_some /-
@[simp]
theorem eraseNone_map_some (s : Finset α) : (s.map Embedding.some).eraseNone = s := by ext; simp
#align finset.erase_none_map_some Finset.eraseNone_map_some
-/

#print Finset.eraseNone_image_some /-
@[simp]
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    (s.image some).eraseNone = s := by simpa only [map_eq_image] using erase_none_map_some s
#align finset.erase_none_image_some Finset.eraseNone_image_some
-/

#print Finset.coe_eraseNone /-
@[simp]
theorem coe_eraseNone (s : Finset (Option α)) : (s.eraseNone : Set α) = some ⁻¹' s :=
  Set.ext fun x => mem_eraseNone
#align finset.coe_erase_none Finset.coe_eraseNone
-/

#print Finset.eraseNone_union /-
@[simp]
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∪ t).eraseNone = s.eraseNone ∪ t.eraseNone := by ext; simp
#align finset.erase_none_union Finset.eraseNone_union
-/

#print Finset.eraseNone_inter /-
@[simp]
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∩ t).eraseNone = s.eraseNone ∩ t.eraseNone := by ext; simp
#align finset.erase_none_inter Finset.eraseNone_inter
-/

#print Finset.eraseNone_empty /-
@[simp]
theorem eraseNone_empty : (∅ : Finset (Option α)).eraseNone = ∅ := by ext; simp
#align finset.erase_none_empty Finset.eraseNone_empty
-/

#print Finset.eraseNone_none /-
@[simp]
theorem eraseNone_none : ({none} : Finset (Option α)).eraseNone = ∅ := by ext; simp
#align finset.erase_none_none Finset.eraseNone_none
-/

#print Finset.image_some_eraseNone /-
@[simp]
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.image some = s.eraseₓ none := by ext (_ | x) <;> simp
#align finset.image_some_erase_none Finset.image_some_eraseNone
-/

#print Finset.map_some_eraseNone /-
@[simp]
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.map Embedding.some = s.eraseₓ none := by
  rw [map_eq_image, embedding.some_apply, image_some_erase_none]
#align finset.map_some_erase_none Finset.map_some_eraseNone
-/

#print Finset.insertNone_eraseNone /-
@[simp]
theorem insertNone_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp
#align finset.insert_none_erase_none Finset.insertNone_eraseNone
-/

#print Finset.eraseNone_insertNone /-
@[simp]
theorem eraseNone_insertNone (s : Finset α) : eraseNone (insertNone s) = s := by ext; simp
#align finset.erase_none_insert_none Finset.eraseNone_insertNone
-/

end Finset

