/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak

! This file was ported from Lean 3 source module data.list.join
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic

/-!
# Join of a list of lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of `list.join`, which concatenates a list of lists. It is defined
in [`data.list.defs`](./defs).
-/


variable {α β : Type _}

namespace List

attribute [simp] join

#print List.join_singleton /-
@[simp]
theorem join_singleton (l : List α) : [l].join = l := by rw [join, join, append_nil]
#align list.join_singleton List.join_singleton
-/

#print List.join_eq_nil /-
@[simp]
theorem join_eq_nil : ∀ {L : List (List α)}, join L = [] ↔ ∀ l ∈ L, l = []
  | [] => iff_of_true rfl (forall_mem_nil _)
  | l :: L => by simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]
#align list.join_eq_nil List.join_eq_nil
-/

#print List.join_append /-
@[simp]
theorem join_append (L₁ L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ := by
  induction L₁ <;> [rfl, simp only [*, join, cons_append, append_assoc]]
#align list.join_append List.join_append
-/

#print List.join_concat /-
theorem join_concat (L : List (List α)) (l : List α) : join (L.concat l) = join L ++ l := by simp
#align list.join_concat List.join_concat
-/

/- warning: list.join_filter_empty_eq_ff -> List.join_filter_isEmpty_eq_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidablePred.{succ u1} (List.{u1} α) (fun (l : List.{u1} α) => Eq.{1} Bool (List.isEmpty.{u1} α l) Bool.false)] {L : List.{u1} (List.{u1} α)}, Eq.{succ u1} (List.{u1} α) (List.join.{u1} α (List.filterₓ.{u1} (List.{u1} α) (fun (l : List.{u1} α) => Eq.{1} Bool (List.isEmpty.{u1} α l) Bool.false) (fun (a : List.{u1} α) => _inst_1 a) L)) (List.join.{u1} α L)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidablePred.{succ u1} (List.{u1} α) (fun (l : List.{u1} α) => Eq.{1} Bool (List.isEmpty.{u1} α l) Bool.false)] {L : List.{u1} (List.{u1} α)}, Eq.{succ u1} (List.{u1} α) (List.join.{u1} α (List.filter.{u1} (List.{u1} α) (fun (a : List.{u1} α) => Decidable.decide (Eq.{1} Bool (List.isEmpty.{u1} α a) Bool.false) (_inst_1 a)) L)) (List.join.{u1} α L)
Case conversion may be inaccurate. Consider using '#align list.join_filter_empty_eq_ff List.join_filter_isEmpty_eq_falseₓ'. -/
@[simp]
theorem join_filter_isEmpty_eq_false [DecidablePred fun l : List α => l.Empty = ff] :
    ∀ {L : List (List α)}, join (L.filter fun l => l.Empty = ff) = L.join
  | [] => rfl
  | [] :: L => by simp [@join_filter_empty_eq_ff L]
  | (a :: l) :: L => by simp [@join_filter_empty_eq_ff L]
#align list.join_filter_empty_eq_ff List.join_filter_isEmpty_eq_false

/- warning: list.join_filter_ne_nil -> List.join_filter_ne_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidablePred.{succ u1} (List.{u1} α) (fun (l : List.{u1} α) => Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α))] {L : List.{u1} (List.{u1} α)}, Eq.{succ u1} (List.{u1} α) (List.join.{u1} α (List.filterₓ.{u1} (List.{u1} α) (fun (l : List.{u1} α) => Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) (fun (a : List.{u1} α) => _inst_1 a) L)) (List.join.{u1} α L)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidablePred.{succ u1} (List.{u1} α) (fun (l : List.{u1} α) => Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α))] {L : List.{u1} (List.{u1} α)}, Eq.{succ u1} (List.{u1} α) (List.join.{u1} α (List.filter.{u1} (List.{u1} α) (fun (a : List.{u1} α) => Decidable.decide (Ne.{succ u1} (List.{u1} α) a (List.nil.{u1} α)) (_inst_1 a)) L)) (List.join.{u1} α L)
Case conversion may be inaccurate. Consider using '#align list.join_filter_ne_nil List.join_filter_ne_nilₓ'. -/
@[simp]
theorem join_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    join (L.filter fun l => l ≠ []) = L.join := by
  simp [join_filter_empty_eq_ff, ← empty_iff_eq_nil]
#align list.join_filter_ne_nil List.join_filter_ne_nil

#print List.join_join /-
theorem join_join (l : List (List (List α))) : l.join.join = (l.map join).join :=
  by
  induction l
  simp
  simp [l_ih]
#align list.join_join List.join_join
-/

#print List.length_join /-
@[simp]
theorem length_join (L : List (List α)) : length (join L) = sum (map length L) := by
  induction L <;> [rfl, simp only [*, join, map, sum_cons, length_append]]
#align list.length_join List.length_join
-/

/- warning: list.length_bind -> List.length_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : α -> (List.{u2} β)), Eq.{1} Nat (List.length.{u2} β (List.bind.{u1, u2} α β l f)) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{u1, 0} α Nat (Function.comp.{succ u1, succ u2, 1} α (List.{u2} β) Nat (List.length.{u2} β) f) l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : α -> (List.{u1} β)), Eq.{1} Nat (List.length.{u1} β (List.bind.{u2, u1} α β l f)) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{u2, 0} α Nat (Function.comp.{succ u2, succ u1, 1} α (List.{u1} β) Nat (List.length.{u1} β) f) l))
Case conversion may be inaccurate. Consider using '#align list.length_bind List.length_bindₓ'. -/
@[simp]
theorem length_bind (l : List α) (f : α → List β) :
    length (List.bind l f) = sum (map (length ∘ f) l) := by rw [List.bind, length_join, map_map]
#align list.length_bind List.length_bind

/- warning: list.bind_eq_nil -> List.bind_eq_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : List.{u1} α} {f : α -> (List.{u2} β)}, Iff (Eq.{succ u2} (List.{u2} β) (List.bind.{u1, u2} α β l f) (List.nil.{u2} β)) (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (Eq.{succ u2} (List.{u2} β) (f x) (List.nil.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : List.{u2} α} {f : α -> (List.{u1} β)}, Iff (Eq.{succ u1} (List.{u1} β) (List.bind.{u2, u1} α β l f) (List.nil.{u1} β)) (forall (x : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) x l) -> (Eq.{succ u1} (List.{u1} β) (f x) (List.nil.{u1} β)))
Case conversion may be inaccurate. Consider using '#align list.bind_eq_nil List.bind_eq_nilₓ'. -/
@[simp]
theorem bind_eq_nil {l : List α} {f : α → List β} : List.bind l f = [] ↔ ∀ x ∈ l, f x = [] :=
  join_eq_nil.trans <| by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
#align list.bind_eq_nil List.bind_eq_nil

#print List.take_sum_join /-
/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
theorem take_sum_join (L : List (List α)) (i : ℕ) :
    L.join.take ((L.map length).take i).Sum = (L.take i).join :=
  by
  induction L generalizing i; · simp
  cases i; · simp
  simp [take_append, L_ih]
#align list.take_sum_join List.take_sum_join
-/

#print List.drop_sum_join /-
/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
theorem drop_sum_join (L : List (List α)) (i : ℕ) :
    L.join.drop ((L.map length).take i).Sum = (L.drop i).join :=
  by
  induction L generalizing i; · simp
  cases i; · simp
  simp [drop_append, L_ih]
#align list.drop_sum_join List.drop_sum_join
-/

#print List.drop_take_succ_eq_cons_nthLe /-
/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_nthLe (L : List α) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).drop i = [nthLe L i hi] :=
  by
  induction L generalizing i
  · simp only [length] at hi
    exact (Nat.not_succ_le_zero i hi).elim
  cases i
  · simp
  have : i < L_tl.length := by
    simp at hi
    exact Nat.lt_of_succ_lt_succ hi
  simp [L_ih this]
  rfl
#align list.drop_take_succ_eq_cons_nth_le List.drop_take_succ_eq_cons_nthLe
-/

#print List.drop_take_succ_join_eq_nthLe /-
/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
theorem drop_take_succ_join_eq_nthLe (L : List (List α)) {i : ℕ} (hi : i < L.length) :
    (L.join.take ((L.map length).take (i + 1)).Sum).drop ((L.map length).take i).Sum =
      nthLe L i hi :=
  by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take]
  simp [take_sum_join, this, drop_sum_join, drop_take_succ_eq_cons_nth_le _ hi]
#align list.drop_take_succ_join_eq_nth_le List.drop_take_succ_join_eq_nthLe
-/

#print List.sum_take_map_length_lt1 /-
/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt1 (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) :
    ((L.map length).take i).Sum + j < ((L.map length).take (i + 1)).Sum := by
  simp [hi, sum_take_succ, hj]
#align list.sum_take_map_length_lt1 List.sum_take_map_length_lt1
-/

#print List.sum_take_map_length_lt2 /-
/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt2 (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) : ((L.map length).take i).Sum + j < L.join.length :=
  by
  convert lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi)
  have : L.length = (L.map length).length := by simp
  simp [this, -length_map]
#align list.sum_take_map_length_lt2 List.sum_take_map_length_lt2
-/

#print List.nthLe_join /-
/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
theorem nthLe_join (L : List (List α)) {i j : ℕ} (hi : i < L.length)
    (hj : j < (nthLe L i hi).length) :
    nthLe L.join (((L.map length).take i).Sum + j) (sum_take_map_length_lt2 L hi hj) =
      nthLe (nthLe L i hi) j hj :=
  by
  rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj),
    nth_le_drop, nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]
#align list.nth_le_join List.nthLe_join
-/

#print List.eq_iff_join_eq /-
/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : List (List α)) :
    L = L' ↔ L.join = L'.join ∧ map length L = map length L' :=
  by
  refine' ⟨fun H => by simp [H], _⟩
  rintro ⟨join_eq, length_eq⟩
  apply ext_le
  · have : length (map length L) = length (map length L') := by rw [length_eq]
    simpa using this
  · intro n h₁ h₂
    rw [← drop_take_succ_join_eq_nth_le, ← drop_take_succ_join_eq_nth_le, join_eq, length_eq]
#align list.eq_iff_join_eq List.eq_iff_join_eq
-/

#print List.join_drop_length_sub_one /-
theorem join_drop_length_sub_one {L : List (List α)} (h : L ≠ []) :
    (L.drop (L.length - 1)).join = L.last h :=
  by
  induction L using List.reverseRecOn
  · cases h rfl
  · simp
#align list.join_drop_length_sub_one List.join_drop_length_sub_one
-/

#print List.append_join_map_append /-
/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
theorem append_join_map_append (L : List (List α)) (x : List α) :
    x ++ (List.map (fun l => l ++ x) L).join = (List.map (fun l => x ++ l) L).join ++ x :=
  by
  induction L
  · rw [map_nil, join, append_nil, map_nil, join, nil_append]
  · rw [map_cons, join, map_cons, join, append_assoc, L_ih, append_assoc, append_assoc]
#align list.append_join_map_append List.append_join_map_append
-/

#print List.reverse_join /-
/-- Reversing a join is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_join (L : List (List α)) :
    L.join.reverse = (List.map List.reverse L).reverse.join :=
  by
  induction L
  · rfl
  · rw [join, reverse_append, L_ih, map_cons, reverse_cons', join_concat]
#align list.reverse_join List.reverse_join
-/

#print List.join_reverse /-
/-- Joining a reverse is the same as reversing all parts and reversing the joined result. -/
theorem join_reverse (L : List (List α)) :
    L.reverse.join = (List.map List.reverse L).join.reverse := by
  simpa [reverse_reverse] using congr_arg List.reverse (reverse_join L.reverse)
#align list.join_reverse List.join_reverse
-/

end List

