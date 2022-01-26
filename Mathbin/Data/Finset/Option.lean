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
def to_finset (o : Option α) : Finset α :=
  o.elim ∅ singleton

@[simp]
theorem to_finset_none : none.toFinset = (∅ : Finset α) :=
  rfl

@[simp]
theorem to_finset_some {a : α} : (some a).toFinset = {a} :=
  rfl

@[simp]
theorem mem_to_finset {a : α} {o : Option α} : a ∈ o.to_finset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]

theorem card_to_finset (o : Option α) : o.to_finset.card = o.elim 0 1 := by
  cases o <;> rfl

end Option

namespace Finset

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insert_none : Finset α ↪o Finset (Option α) :=
  (OrderEmbedding.ofMapLeIff fun s =>
      cons none (s.map embedding.some) <| by
        simp )
    fun s t => cons_subset_cons.trans map_subset_map

@[simp]
theorem mem_insert_none {s : Finset α} : ∀ {o : Option α}, o ∈ s.insert_none ↔ ∀, ∀ a ∈ o, ∀, a ∈ s
  | none =>
    iff_of_true (Multiset.mem_cons_self _ _) fun a h => by
      cases h
  | some a =>
    Multiset.mem_cons.trans <| by
      simp <;> rfl

theorem some_mem_insert_none {s : Finset α} {a : α} : some a ∈ s.insert_none ↔ a ∈ s := by
  simp

@[simp]
theorem card_insert_none (s : Finset α) : s.insert_none.card = s.card + 1 := by
  simp [insert_none]

/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def erase_none : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equivₓ.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp ⟨Finset.subtype _, subtype_mono⟩

@[simp]
theorem mem_erase_none {s : Finset (Option α)} {x : α} : x ∈ s.erase_none ↔ some x ∈ s := by
  simp [erase_none]

theorem erase_none_eq_bUnion [DecidableEq α] (s : Finset (Option α)) : s.erase_none = s.bUnion Option.toFinset := by
  ext
  simp

@[simp]
theorem erase_none_map_some (s : Finset α) : (s.map embedding.some).eraseNone = s := by
  ext
  simp

@[simp]
theorem erase_none_image_some [DecidableEq (Option α)] (s : Finset α) : (s.image some).eraseNone = s := by
  simpa only [map_eq_image] using erase_none_map_some s

@[simp]
theorem coe_erase_none (s : Finset (Option α)) : (s.erase_none : Set α) = some ⁻¹' s :=
  Set.ext fun x => mem_erase_none

@[simp]
theorem erase_none_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∪ t).eraseNone = s.erase_none ∪ t.erase_none := by
  ext
  simp

@[simp]
theorem erase_none_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∩ t).eraseNone = s.erase_none ∩ t.erase_none := by
  ext
  simp

@[simp]
theorem erase_none_empty : (∅ : Finset (Option α)).eraseNone = ∅ := by
  ext
  simp

@[simp]
theorem erase_none_none : ({none} : Finset (Option α)).eraseNone = ∅ := by
  ext
  simp

@[simp]
theorem image_some_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.erase_none.image some = s.erase none := by
  ext (_ | x) <;> simp

@[simp]
theorem map_some_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.erase_none.map embedding.some = s.erase none := by
  rw [map_eq_image, embedding.some_apply, image_some_erase_none]

@[simp]
theorem insert_none_erase_none [DecidableEq (Option α)] (s : Finset (Option α)) :
    insert_none (erase_none s) = insert none s := by
  ext (_ | x) <;> simp

@[simp]
theorem erase_none_insert_none (s : Finset α) : erase_none (insert_none s) = s := by
  ext
  simp

end Finset

