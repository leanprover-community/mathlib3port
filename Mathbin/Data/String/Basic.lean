/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.List.Lex
import Data.Char

#align_import data.string.basic from "leanprover-community/mathlib"@"75be6b616681ab6ca66d798ead117e75cd64f125"

/-!
# Strings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Supplementary theorems about the `string` type.
-/


namespace String

/- ./././Mathport/Syntax/Translate/Command.lean:299:8: warning: using_well_founded used, estimated equivalent -/
#print String.ltb /-
/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb : Iterator → Iterator → Bool
  | s₁, s₂ => by
    cases s₂.has_next; · exact ff
    cases h₁ : s₁.has_next; · exact tt
    exact
      if s₁.curr = s₂.curr then
        have : s₁.next.2.length < s₁.2.length :=
          match s₁, h₁ with
          | ⟨_, a :: l⟩, h => Nat.lt_succ_self _
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
termination_by x => WellFounded.wrap (measure_wf fun s => s.1.2.length) x
#align string.ltb String.ltb
-/

#print String.LT' /-
instance LT' : LT String :=
  ⟨fun s₁ s₂ => ltb s₁.mkIterator s₂.mkIterator⟩
#align string.has_lt' String.LT'
-/

#print String.decidableLT /-
instance decidableLT : @DecidableRel String (· < ·) := by infer_instance
#align string.decidable_lt String.decidableLT
-/

#print String.lt_iff_toList_lt /-
-- short-circuit type class inference
@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | ⟨i₁⟩, ⟨i₂⟩ =>
    by
    suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ ↔ s₁ < s₂ from this
    intros
    induction' s₁ with a s₁ IH generalizing p₁ p₂ s₂ <;> cases' s₂ with b s₂ <;> rw [ltb] <;>
      simp [iterator.has_next]
    · rfl
    · exact iff_of_true rfl List.Lex.nil
    · exact iff_of_false Bool.false_ne_true (not_lt_of_lt List.Lex.nil)
    · dsimp [iterator.has_next, iterator.curr, iterator.next]
      split_ifs
      · subst b; exact IH.trans list.lex.cons_iff.symm
      · simp; refine' ⟨List.Lex.rel, fun e => _⟩
        cases e; · cases h rfl; assumption
#align string.lt_iff_to_list_lt String.lt_iff_toList_lt
-/

#print String.LE /-
instance LE : LE String :=
  ⟨fun s₁ s₂ => ¬s₂ < s₁⟩
#align string.has_le String.LE
-/

#print String.decidableLE /-
instance decidableLE : @DecidableRel String (· ≤ ·) := by infer_instance
#align string.decidable_le String.decidableLE
-/

#print String.le_iff_toList_le /-
-- short-circuit type class inference
@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt
#align string.le_iff_to_list_le String.le_iff_toList_le
-/

#print String.toList_inj /-
theorem toList_inj : ∀ {s₁ s₂}, toList s₁ = toList s₂ ↔ s₁ = s₂
  | ⟨s₁⟩, ⟨s₂⟩ => ⟨congr_arg _, congr_arg _⟩
#align string.to_list_inj String.toList_inj
-/

#print String.nil_asString_eq_empty /-
theorem nil_asString_eq_empty : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.nil_asString_eq_empty
-/

#print String.toList_empty /-
@[simp]
theorem toList_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.toList_empty
-/

#print String.asString_inv_toList /-
theorem asString_inv_toList (s : String) : s.toList.asString = s := by cases s; rfl
#align string.as_string_inv_to_list String.asString_inv_toList
-/

#print String.data_singleton /-
@[simp]
theorem data_singleton (c : Char) : (String.singleton c).toList = [c] :=
  rfl
#align string.to_list_singleton String.data_singleton
-/

#print String.toList_nonempty /-
theorem toList_nonempty : ∀ {s : String}, s ≠ String.empty → s.toList = s.headI :: (s.drop 1).toList
  | ⟨s⟩, h => by cases s <;> [cases h rfl; rfl]
#align string.to_list_nonempty String.toList_nonempty
-/

#print String.head_empty /-
@[simp]
theorem head_empty : "".headI = default :=
  rfl
#align string.head_empty String.head_empty
-/

#print String.drop_empty /-
@[simp]
theorem drop_empty {n : ℕ} : "".drop n = "" :=
  by
  induction' n with n hn
  · rfl
  · rcases hs : "" with ⟨_ | ⟨hd, tl⟩⟩
    · rw [hs] at hn 
      conv_rhs => rw [← hn]
      simp only [popn, mk_iterator, iterator.nextn, iterator.next]
    · simpa only [← to_list_inj] using hs
#align string.popn_empty String.drop_empty
-/

instance : LinearOrder String where
  lt := (· < ·)
  le := (· ≤ ·)
  decidableLt := by infer_instance
  decidableLe := String.decidableLE
  DecidableEq := by infer_instance
  le_refl a := le_iff_toList_le.2 le_rfl
  le_trans a b c := by simp only [le_iff_to_list_le]; exact fun h₁ h₂ => h₁.trans h₂
  le_total a b := by simp only [le_iff_to_list_le]; exact le_total _ _
  le_antisymm a b := by simp only [le_iff_to_list_le, ← to_list_inj]; apply le_antisymm
  lt_iff_le_not_le a b := by simp only [le_iff_to_list_le, lt_iff_to_list_lt, lt_iff_le_not_le]

end String

open String

#print List.toList_inv_asString /-
theorem List.toList_inv_asString (l : List Char) : l.asString.toList = l := by
  cases hl : l.as_string; exact StringImp.mk.inj hl.symm
#align list.to_list_inv_as_string List.toList_inv_asString
-/

#print List.length_asString /-
@[simp]
theorem List.length_asString (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_asString
-/

#print List.asString_inj /-
@[simp]
theorem List.asString_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h => by rw [← List.toList_inv_asString l, ← List.toList_inv_asString l', to_list_inj, h],
    fun h => h ▸ rfl⟩
#align list.as_string_inj List.asString_inj
-/

#print String.length_data /-
@[simp]
theorem String.length_data (s : String) : s.toList.length = s.length := by
  rw [← String.asString_inv_toList s, List.toList_inv_asString, List.length_asString]
#align string.length_to_list String.length_data
-/

#print List.asString_eq /-
theorem List.asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← as_string_inv_to_list s, List.asString_inj, as_string_inv_to_list s]
#align list.as_string_eq List.asString_eq
-/

