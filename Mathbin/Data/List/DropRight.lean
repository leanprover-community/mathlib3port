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

#print List.rdrop /-
/-- Drop `n` elements from the tail end of a list. -/
def rdrop : List α :=
  l.take (l.length - n)
#align list.rdrop List.rdrop
-/

#print List.rdrop_nil /-
@[simp]
theorem rdrop_nil : rdrop ([] : List α) n = [] := by simp [rdrop]
#align list.rdrop_nil List.rdrop_nil
-/

#print List.rdrop_zero /-
@[simp]
theorem rdrop_zero : rdrop l 0 = l := by simp [rdrop]
#align list.rdrop_zero List.rdrop_zero
-/

#print List.rdrop_eq_reverse_drop_reverse /-
theorem rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) :=
  by
  rw [rdrop]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp [take_append]
    · simp [take_append_eq_append_take, IH]
#align list.rdrop_eq_reverse_drop_reverse List.rdrop_eq_reverse_drop_reverse
-/

#print List.rdrop_concat_succ /-
@[simp]
theorem rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n := by
  simp [rdrop_eq_reverse_drop_reverse]
#align list.rdrop_concat_succ List.rdrop_concat_succ
-/

#print List.rtake /-
/-- Take `n` elements from the tail end of a list. -/
def rtake : List α :=
  l.drop (l.length - n)
#align list.rtake List.rtake
-/

#print List.rtake_nil /-
@[simp]
theorem rtake_nil : rtake ([] : List α) n = [] := by simp [rtake]
#align list.rtake_nil List.rtake_nil
-/

#print List.rtake_zero /-
@[simp]
theorem rtake_zero : rtake l 0 = [] := by simp [rtake]
#align list.rtake_zero List.rtake_zero
-/

#print List.rtake_eq_reverse_take_reverse /-
theorem rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) :=
  by
  rw [rtake]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp
    · simp [drop_append_eq_append_drop, IH]
#align list.rtake_eq_reverse_take_reverse List.rtake_eq_reverse_take_reverse
-/

#print List.rtake_concat_succ /-
@[simp]
theorem rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]
#align list.rtake_concat_succ List.rtake_concat_succ
-/

#print List.rdropWhile /-
/-- Drop elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rdropWhile : List α :=
  reverse (l.reverse.dropWhileₓ p)
#align list.rdrop_while List.rdropWhile
-/

#print List.rdropWhile_nil /-
@[simp]
theorem rdropWhile_nil : rdropWhile p ([] : List α) = [] := by simp [rdrop_while, drop_while]
#align list.rdrop_while_nil List.rdropWhile_nil
-/

#print List.rdropWhile_concat /-
theorem rdropWhile_concat (x : α) :
    rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x] :=
  by
  simp only [rdrop_while, drop_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rdrop_while_concat List.rdropWhile_concat
-/

#print List.rdropWhile_concat_pos /-
@[simp]
theorem rdropWhile_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropWhile p l := by
  rw [rdrop_while_concat, if_pos h]
#align list.rdrop_while_concat_pos List.rdropWhile_concat_pos
-/

#print List.rdropWhile_concat_neg /-
@[simp]
theorem rdropWhile_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdrop_while_concat, if_neg h]
#align list.rdrop_while_concat_neg List.rdropWhile_concat_neg
-/

#print List.rdropWhile_singleton /-
theorem rdropWhile_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdrop_while_concat, rdrop_while_nil]
#align list.rdrop_while_singleton List.rdropWhile_singleton
-/

#print List.rdropWhile_last_not /-
theorem rdropWhile_last_not (hl : l.rdropWhile p ≠ []) : ¬p ((rdropWhile p l).getLast hl) :=
  by
  simp_rw [rdrop_while]
  rw [last_reverse]
  exact drop_while_nth_le_zero_not _ _ _
#align list.rdrop_while_last_not List.rdropWhile_last_not
-/

#print List.rdropWhile_prefix /-
theorem rdropWhile_prefix : l.rdropWhile p <+: l :=
  by
  rw [← reverse_suffix, rdrop_while, reverse_reverse]
  exact drop_while_suffix _
#align list.rdrop_while_prefix List.rdropWhile_prefix
-/

variable {p} {l}

#print List.rdropWhile_eq_nil_iff /-
@[simp]
theorem rdropWhile_eq_nil_iff : rdropWhile p l = [] ↔ ∀ x ∈ l, p x := by simp [rdrop_while]
#align list.rdrop_while_eq_nil_iff List.rdropWhile_eq_nil_iff
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

#print List.rdropWhile_eq_self_iff /-
@[simp]
theorem rdropWhile_eq_self_iff : rdropWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) :=
  by
  simp only [rdrop_while, reverse_eq_iff, length_reverse, Ne.def, drop_while_eq_self_iff,
    last_eq_nth_le, ← length_eq_zero, pos_iff_ne_zero]
  refine' forall_congr' _
  intro h
  rw [nth_le_reverse']
  · simp
  · rw [← Ne.def, ← pos_iff_ne_zero] at h
    simp [tsub_lt_iff_right (Nat.succ_le_of_lt h)]
#align list.rdrop_while_eq_self_iff List.rdropWhile_eq_self_iff
-/

variable (p) (l)

#print List.dropWhile_idempotent /-
theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l :=
  dropWhile_eq_self_iff.mpr (dropWhile_nthLe_zero_not _ _)
#align list.drop_while_idempotent List.dropWhile_idempotent
-/

#print List.rdropWhile_idempotent /-
theorem rdropWhile_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l :=
  rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)
#align list.rdrop_while_idempotent List.rdropWhile_idempotent
-/

#print List.rtakeWhile /-
/-- Take elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rtakeWhile : List α :=
  reverse (l.reverse.takeWhile p)
#align list.rtake_while List.rtakeWhile
-/

#print List.rtakeWhile_nil /-
@[simp]
theorem rtakeWhile_nil : rtakeWhile p ([] : List α) = [] := by simp [rtake_while, take_while]
#align list.rtake_while_nil List.rtakeWhile_nil
-/

#print List.rtakeWhile_concat /-
theorem rtakeWhile_concat (x : α) :
    rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else [] :=
  by
  simp only [rtake_while, take_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rtake_while_concat List.rtakeWhile_concat
-/

#print List.rtakeWhile_concat_pos /-
@[simp]
theorem rtakeWhile_concat_pos (x : α) (h : p x) : rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x] :=
  by rw [rtake_while_concat, if_pos h]
#align list.rtake_while_concat_pos List.rtakeWhile_concat_pos
-/

#print List.rtakeWhile_concat_neg /-
@[simp]
theorem rtakeWhile_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = [] := by
  rw [rtake_while_concat, if_neg h]
#align list.rtake_while_concat_neg List.rtakeWhile_concat_neg
-/

#print List.rtakeWhile_suffix /-
theorem rtakeWhile_suffix : l.rtakeWhile p <:+ l :=
  by
  rw [← reverse_prefix, rtake_while, reverse_reverse]
  exact take_while_prefix _
#align list.rtake_while_suffix List.rtakeWhile_suffix
-/

variable {p} {l}

#print List.rtakeWhile_eq_self_iff /-
@[simp]
theorem rtakeWhile_eq_self_iff : rtakeWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [rtake_while, reverse_eq_iff]
#align list.rtake_while_eq_self_iff List.rtakeWhile_eq_self_iff
-/

#print List.rtakeWhile_eq_nil_iff /-
@[simp]
theorem rtakeWhile_eq_nil_iff : rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction l using List.reverseRecOn <;> simp [rtake_while]
#align list.rtake_while_eq_nil_iff List.rtakeWhile_eq_nil_iff
-/

#print List.mem_rtakeWhile_imp /-
theorem mem_rtakeWhile_imp {x : α} (hx : x ∈ rtakeWhile p l) : p x :=
  by
  suffices x ∈ take_while p l.reverse by exact mem_take_while_imp this
  rwa [← mem_reverse, ← rtake_while]
#align list.mem_rtake_while_imp List.mem_rtakeWhile_imp
-/

variable (p) (l)

#print List.rtakeWhile_idempotent /-
theorem rtakeWhile_idempotent : rtakeWhile p (rtakeWhile p l) = rtakeWhile p l :=
  rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp
#align list.rtake_while_idempotent List.rtakeWhile_idempotent
-/

end List

