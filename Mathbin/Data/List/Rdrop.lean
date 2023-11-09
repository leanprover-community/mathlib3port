/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Data.List.Basic
import Data.List.Infix

#align_import data.list.rdrop from "leanprover-community/mathlib"@"be24ec5de6701447e5df5ca75400ffee19d65659"

/-!

# Dropping or taking from lists on the right

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Taking or removing element from the tail end of a list

## Main defintions

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `drop_while p`: remove all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element
- `take_while p`: take all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`list.reverse`, followed by another `list.reverse`, so they are not the most performant.
The other two rely on `list.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/


variable {α : Type _} (p : α → Prop) [DecidablePred p] (l : List α) (n : ℕ)

namespace List

#print List.dropRight /-
/-- Drop `n` elements from the tail end of a list. -/
def dropRight : List α :=
  l.take (l.length - n)
#align list.rdrop List.dropRight
-/

#print List.dropRight_nil /-
@[simp]
theorem dropRight_nil : dropRight ([] : List α) n = [] := by simp [rdrop]
#align list.rdrop_nil List.dropRight_nil
-/

#print List.dropRight_zero /-
@[simp]
theorem dropRight_zero : dropRight l 0 = l := by simp [rdrop]
#align list.rdrop_zero List.dropRight_zero
-/

#print List.dropRight_eq_reverse_drop_reverse /-
theorem dropRight_eq_reverse_drop_reverse : l.dropRight n = reverse (l.reverse.drop n) :=
  by
  rw [rdrop]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp [take_append]
    · simp [take_append_eq_append_take, IH]
#align list.rdrop_eq_reverse_drop_reverse List.dropRight_eq_reverse_drop_reverse
-/

#print List.dropRight_concat_succ /-
@[simp]
theorem dropRight_concat_succ (x : α) : dropRight (l ++ [x]) (n + 1) = dropRight l n := by
  simp [rdrop_eq_reverse_drop_reverse]
#align list.rdrop_concat_succ List.dropRight_concat_succ
-/

#print List.takeRight /-
/-- Take `n` elements from the tail end of a list. -/
def takeRight : List α :=
  l.drop (l.length - n)
#align list.rtake List.takeRight
-/

#print List.takeRight_nil /-
@[simp]
theorem takeRight_nil : takeRight ([] : List α) n = [] := by simp [rtake]
#align list.rtake_nil List.takeRight_nil
-/

#print List.takeRight_zero /-
@[simp]
theorem takeRight_zero : takeRight l 0 = [] := by simp [rtake]
#align list.rtake_zero List.takeRight_zero
-/

#print List.takeRight_eq_reverse_take_reverse /-
theorem takeRight_eq_reverse_take_reverse : l.takeRight n = reverse (l.reverse.take n) :=
  by
  rw [rtake]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp
    · simp [drop_append_eq_append_drop, IH]
#align list.rtake_eq_reverse_take_reverse List.takeRight_eq_reverse_take_reverse
-/

#print List.takeRight_concat_succ /-
@[simp]
theorem takeRight_concat_succ (x : α) : takeRight (l ++ [x]) (n + 1) = takeRight l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]
#align list.rtake_concat_succ List.takeRight_concat_succ
-/

#print List.dropRightWhile /-
/-- Drop elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def dropRightWhile : List α :=
  reverse (l.reverse.dropWhileₓ p)
#align list.rdrop_while List.dropRightWhile
-/

#print List.dropRightWhile_nil /-
@[simp]
theorem dropRightWhile_nil : dropRightWhile p ([] : List α) = [] := by
  simp [rdrop_while, drop_while]
#align list.rdrop_while_nil List.dropRightWhile_nil
-/

#print List.dropRightWhile_concat /-
theorem dropRightWhile_concat (x : α) :
    dropRightWhile p (l ++ [x]) = if p x then dropRightWhile p l else l ++ [x] :=
  by
  simp only [rdrop_while, drop_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rdrop_while_concat List.dropRightWhile_concat
-/

#print List.dropRightWhile_concat_pos /-
@[simp]
theorem dropRightWhile_concat_pos (x : α) (h : p x) :
    dropRightWhile p (l ++ [x]) = dropRightWhile p l := by rw [rdrop_while_concat, if_pos h]
#align list.rdrop_while_concat_pos List.dropRightWhile_concat_pos
-/

#print List.dropRightWhile_concat_neg /-
@[simp]
theorem dropRightWhile_concat_neg (x : α) (h : ¬p x) : dropRightWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdrop_while_concat, if_neg h]
#align list.rdrop_while_concat_neg List.dropRightWhile_concat_neg
-/

#print List.dropRightWhile_singleton /-
theorem dropRightWhile_singleton (x : α) : dropRightWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdrop_while_concat, rdrop_while_nil]
#align list.rdrop_while_singleton List.dropRightWhile_singleton
-/

#print List.dropRightWhile_last_not /-
theorem dropRightWhile_last_not (hl : l.dropRightWhile p ≠ []) :
    ¬p ((dropRightWhile p l).getLast hl) :=
  by
  simp_rw [rdrop_while]
  rw [last_reverse]
  exact drop_while_nth_le_zero_not _ _ _
#align list.rdrop_while_last_not List.dropRightWhile_last_not
-/

#print List.dropRightWhile_prefix /-
theorem dropRightWhile_prefix : l.dropRightWhile p <+: l :=
  by
  rw [← reverse_suffix, rdrop_while, reverse_reverse]
  exact drop_while_suffix _
#align list.rdrop_while_prefix List.dropRightWhile_prefix
-/

variable {p} {l}

#print List.dropRightWhile_eq_nil_iff /-
@[simp]
theorem dropRightWhile_eq_nil_iff : dropRightWhile p l = [] ↔ ∀ x ∈ l, p x := by simp [rdrop_while]
#align list.rdrop_while_eq_nil_iff List.dropRightWhile_eq_nil_iff
-/

#print List.dropWhile_eq_self_iff /-
-- it is in this file because it requires `list.infix`
@[simp]
theorem dropWhile_eq_self_iff : dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) :=
  by
  induction' l with hd tl IH
  · simp
  · rw [drop_while]
    split_ifs
    · simp only [h, length, nth_le, Nat.succ_pos', not_true, forall_true_left, iff_false_iff]
      intro H
      refine' (cons_ne_self hd tl) (sublist.antisymm _ (sublist_cons _ _))
      rw [← H]
      exact (drop_while_suffix _).Sublist
    · simp [h]
#align list.drop_while_eq_self_iff List.dropWhile_eq_self_iff
-/

#print List.dropRightWhile_eq_self_iff /-
@[simp]
theorem dropRightWhile_eq_self_iff : dropRightWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) :=
  by
  simp only [rdrop_while, reverse_eq_iff, length_reverse, Ne.def, drop_while_eq_self_iff,
    last_eq_nth_le, ← length_eq_zero, pos_iff_ne_zero]
  refine' forall_congr' _
  intro h
  rw [nth_le_reverse']
  · simp
  · rw [← Ne.def, ← pos_iff_ne_zero] at h 
    simp [tsub_lt_iff_right (Nat.succ_le_of_lt h)]
#align list.rdrop_while_eq_self_iff List.dropRightWhile_eq_self_iff
-/

variable (p) (l)

#print List.dropWhile_idempotent /-
theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l :=
  dropWhile_eq_self_iff.mpr (dropWhile_nthLe_zero_not _ _)
#align list.drop_while_idempotent List.dropWhile_idempotent
-/

#print List.dropRightWhile_idempotent /-
theorem dropRightWhile_idempotent : dropRightWhile p (dropRightWhile p l) = dropRightWhile p l :=
  dropRightWhile_eq_self_iff.mpr (dropRightWhile_last_not _ _)
#align list.rdrop_while_idempotent List.dropRightWhile_idempotent
-/

#print List.takeRightWhile /-
/-- Take elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def takeRightWhile : List α :=
  reverse (l.reverse.takeWhile p)
#align list.rtake_while List.takeRightWhile
-/

#print List.takeRightWhile_nil /-
@[simp]
theorem takeRightWhile_nil : takeRightWhile p ([] : List α) = [] := by
  simp [rtake_while, take_while]
#align list.rtake_while_nil List.takeRightWhile_nil
-/

#print List.takeRightWhile_concat /-
theorem takeRightWhile_concat (x : α) :
    takeRightWhile p (l ++ [x]) = if p x then takeRightWhile p l ++ [x] else [] :=
  by
  simp only [rtake_while, take_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rtake_while_concat List.takeRightWhile_concat
-/

#print List.takeRightWhile_concat_pos /-
@[simp]
theorem takeRightWhile_concat_pos (x : α) (h : p x) :
    takeRightWhile p (l ++ [x]) = takeRightWhile p l ++ [x] := by rw [rtake_while_concat, if_pos h]
#align list.rtake_while_concat_pos List.takeRightWhile_concat_pos
-/

#print List.takeRightWhile_concat_neg /-
@[simp]
theorem takeRightWhile_concat_neg (x : α) (h : ¬p x) : takeRightWhile p (l ++ [x]) = [] := by
  rw [rtake_while_concat, if_neg h]
#align list.rtake_while_concat_neg List.takeRightWhile_concat_neg
-/

#print List.takeRightWhile_suffix /-
theorem takeRightWhile_suffix : l.takeRightWhile p <:+ l :=
  by
  rw [← reverse_prefix, rtake_while, reverse_reverse]
  exact take_while_prefix _
#align list.rtake_while_suffix List.takeRightWhile_suffix
-/

variable {p} {l}

#print List.takeRightWhile_eq_self_iff /-
@[simp]
theorem takeRightWhile_eq_self_iff : takeRightWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [rtake_while, reverse_eq_iff]
#align list.rtake_while_eq_self_iff List.takeRightWhile_eq_self_iff
-/

#print List.takeRightWhile_eq_nil_iff /-
@[simp]
theorem takeRightWhile_eq_nil_iff : takeRightWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction l using List.reverseRecOn <;> simp [rtake_while]
#align list.rtake_while_eq_nil_iff List.takeRightWhile_eq_nil_iff
-/

#print List.mem_takeRightWhile_imp /-
theorem mem_takeRightWhile_imp {x : α} (hx : x ∈ takeRightWhile p l) : p x :=
  by
  suffices x ∈ take_while p l.reverse by exact mem_take_while_imp this
  rwa [← mem_reverse, ← rtake_while]
#align list.mem_rtake_while_imp List.mem_takeRightWhile_imp
-/

variable (p) (l)

#print List.takeRightWhile_idempotent /-
theorem takeRightWhile_idempotent : takeRightWhile p (takeRightWhile p l) = takeRightWhile p l :=
  takeRightWhile_eq_self_iff.mpr fun _ => mem_takeRightWhile_imp
#align list.rtake_while_idempotent List.takeRightWhile_idempotent
-/

end List

