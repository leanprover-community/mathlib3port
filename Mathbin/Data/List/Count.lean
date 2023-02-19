/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.count
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic

/-!
# Counting in lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties of `list.countp` and `list.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in [`data.list.defs`](./defs).
-/


open Nat

variable {α β : Type _} {l l₁ l₂ : List α}

namespace List

section Countp

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q]

/- warning: list.countp_nil -> List.countp_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.nil.{u1} α)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool), Eq.{1} Nat (List.countp.{u1} α p (List.nil.{u1} α)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align list.countp_nil List.countp_nilₓ'. -/
@[simp]
theorem countp_nil : countp p [] = 0 :=
  rfl
#align list.countp_nil List.countp_nil

/- warning: list.countp_cons_of_pos -> List.countp_cons_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {a : α} (l : List.{u1} α), (p a) -> (Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a l)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) {_inst_1 : α} (a : List.{u1} α), (Eq.{1} Bool (p _inst_1) Bool.true) -> (Eq.{1} Nat (List.countp.{u1} α p (List.cons.{u1} α _inst_1 a)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.countp.{u1} α p a) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.countp_cons_of_pos List.countp_cons_of_posₓ'. -/
@[simp]
theorem countp_cons_of_pos {a : α} (l) (pa : p a) : countp p (a :: l) = countp p l + 1 :=
  if_pos pa
#align list.countp_cons_of_pos List.countp_cons_of_pos

/- warning: list.countp_cons_of_neg -> List.countp_cons_of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {a : α} (l : List.{u1} α), (Not (p a)) -> (Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a l)) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) {_inst_1 : α} (a : List.{u1} α), (Not (Eq.{1} Bool (p _inst_1) Bool.true)) -> (Eq.{1} Nat (List.countp.{u1} α p (List.cons.{u1} α _inst_1 a)) (List.countp.{u1} α p a))
Case conversion may be inaccurate. Consider using '#align list.countp_cons_of_neg List.countp_cons_of_negₓ'. -/
@[simp]
theorem countp_cons_of_neg {a : α} (l) (pa : ¬p a) : countp p (a :: l) = countp p l :=
  if_neg pa
#align list.countp_cons_of_neg List.countp_cons_of_neg

/- warning: list.countp_cons -> List.countp_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (a : α) (l : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.cons.{u1} α a l)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (ite.{1} Nat (p a) (_inst_1 a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : α) (a : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (List.cons.{u1} α _inst_1 a)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.countp.{u1} α p a) (ite.{1} Nat (Eq.{1} Bool (p _inst_1) Bool.true) (instDecidableEqBool (p _inst_1) Bool.true) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align list.countp_cons List.countp_consₓ'. -/
theorem countp_cons (a : α) (l) : countp p (a :: l) = countp p l + ite (p a) 1 0 := by
  by_cases h : p a <;> simp [h]
#align list.countp_cons List.countp_cons

/- warning: list.length_eq_countp_add_countp -> List.length_eq_countp_add_countp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{1} Nat (List.length.{u1} α l) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.countp.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{1} Nat (List.length.{u1} α _inst_1) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.countp.{u1} α p _inst_1) (List.countp.{u1} α (fun (a : α) => Decidable.decide (Not (Eq.{1} Bool (p a) Bool.true)) (instDecidableNot (Eq.{1} Bool (p a) Bool.true) (instDecidableEqBool (p a) Bool.true))) _inst_1))
Case conversion may be inaccurate. Consider using '#align list.length_eq_countp_add_countp List.length_eq_countp_add_countpₓ'. -/
theorem length_eq_countp_add_countp (l) : length l = countp p l + countp (fun a => ¬p a) l := by
  induction' l with x h ih <;> [rfl, by_cases p x] <;>
      [simp only [countp_cons_of_pos _ _ h,
        countp_cons_of_neg (fun a => ¬p a) _ (Decidable.not_not.2 h), ih, length],
      simp only [countp_cons_of_pos (fun a => ¬p a) _ h, countp_cons_of_neg _ _ h, ih, length]] <;>
    ac_rfl
#align list.length_eq_countp_add_countp List.length_eq_countp_add_countp

/- warning: list.countp_eq_length_filter -> List.countp_eq_length_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.length.{u1} α (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p _inst_1) (List.length.{u1} α (List.filter.{u1} α p _inst_1))
Case conversion may be inaccurate. Consider using '#align list.countp_eq_length_filter List.countp_eq_length_filterₓ'. -/
theorem countp_eq_length_filter (l) : countp p l = length (filter p l) := by
  induction' l with x l ih <;> [rfl, by_cases p x] <;>
      [simp only [filter_cons_of_pos _ h, countp, ih, if_pos h],
      simp only [countp_cons_of_neg _ _ h, ih, filter_cons_of_neg _ h]] <;>
    rfl
#align list.countp_eq_length_filter List.countp_eq_length_filter

/- warning: list.countp_le_length -> List.countp_le_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], LE.le.{0} Nat Nat.hasLe (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.length.{u1} α l)
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} (p : α -> Bool), LE.le.{0} Nat instLENat (List.countp.{u1} α p l) (List.length.{u1} α l)
Case conversion may be inaccurate. Consider using '#align list.countp_le_length List.countp_le_lengthₓ'. -/
theorem countp_le_length : countp p l ≤ l.length := by
  simpa only [countp_eq_length_filter] using length_filter_le _ _
#align list.countp_le_length List.countp_le_length

/- warning: list.countp_append -> List.countp_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l₁) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l₂))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α) (l₁ : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) _inst_1 l₁)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.countp.{u1} α p _inst_1) (List.countp.{u1} α p l₁))
Case conversion may be inaccurate. Consider using '#align list.countp_append List.countp_appendₓ'. -/
@[simp]
theorem countp_append (l₁ l₂) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ := by
  simp only [countp_eq_length_filter, filter_append, length_append]
#align list.countp_append List.countp_append

/- warning: list.countp_join -> List.countp_join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} (List.{u1} α)), Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.join.{u1} α l)) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{u1, 0} (List.{u1} α) Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a)) l))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} (List.{u1} α)), Eq.{1} Nat (List.countp.{u1} α p (List.join.{u1} α _inst_1)) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{u1, 0} (List.{u1} α) Nat (List.countp.{u1} α p) _inst_1))
Case conversion may be inaccurate. Consider using '#align list.countp_join List.countp_joinₓ'. -/
theorem countp_join : ∀ l : List (List α), countp p l.join = (l.map (countp p)).Sum
  | [] => rfl
  | a :: l => by rw [join, countp_append, map_cons, sum_cons, countp_join]
#align list.countp_join List.countp_join

/- warning: list.countp_pos -> List.countp_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) => p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : List.{u1} α} (_inst_1 : α -> Bool), Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (List.countp.{u1} α _inst_1 p)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a p) (Eq.{1} Bool (_inst_1 a) Bool.true)))
Case conversion may be inaccurate. Consider using '#align list.countp_pos List.countp_posₓ'. -/
theorem countp_pos {l} : 0 < countp p l ↔ ∃ a ∈ l, p a := by
  simp only [countp_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]
#align list.countp_pos List.countp_pos

/- warning: list.countp_eq_zero -> List.countp_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Not (p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : List.{u1} α} (_inst_1 : α -> Bool), Iff (Eq.{1} Nat (List.countp.{u1} α _inst_1 p) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (forall (a : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a p) -> (Not (Eq.{1} Bool (_inst_1 a) Bool.true)))
Case conversion may be inaccurate. Consider using '#align list.countp_eq_zero List.countp_eq_zeroₓ'. -/
@[simp]
theorem countp_eq_zero {l} : countp p l = 0 ↔ ∀ a ∈ l, ¬p a :=
  by
  rw [← not_iff_not, ← Ne.def, ← pos_iff_ne_zero, countp_pos]
  simp
#align list.countp_eq_zero List.countp_eq_zero

/- warning: list.countp_eq_length -> List.countp_eq_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] {l : List.{u1} α}, Iff (Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.length.{u1} α l)) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (p a))
but is expected to have type
  forall {α : Type.{u1}} {p : List.{u1} α} (_inst_1 : α -> Bool), Iff (Eq.{1} Nat (List.countp.{u1} α _inst_1 p) (List.length.{u1} α p)) (forall (a : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a p) -> (Eq.{1} Bool (_inst_1 a) Bool.true))
Case conversion may be inaccurate. Consider using '#align list.countp_eq_length List.countp_eq_lengthₓ'. -/
@[simp]
theorem countp_eq_length {l} : countp p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countp_eq_length_filter, filter_length_eq_length]
#align list.countp_eq_length List.countp_eq_length

/- warning: list.length_filter_lt_length_iff_exists -> List.length_filter_lt_length_iff_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (l : List.{u1} α), Iff (LT.lt.{0} Nat Nat.hasLt (List.length.{u1} α (List.filterₓ.{u1} α p (fun (a : α) => _inst_1 a) l)) (List.length.{u1} α l)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) (fun (H : Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) => Not (p x))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (_inst_1 : List.{u1} α), Iff (LT.lt.{0} Nat instLTNat (List.length.{u1} α (List.filter.{u1} α p _inst_1)) (List.length.{u1} α _inst_1)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x _inst_1) (Not (Eq.{1} Bool (p x) Bool.true))))
Case conversion may be inaccurate. Consider using '#align list.length_filter_lt_length_iff_exists List.length_filter_lt_length_iff_existsₓ'. -/
theorem length_filter_lt_length_iff_exists (l) : length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x :=
  by
  rw [length_eq_countp_add_countp p l, ← countp_pos, countp_eq_length_filter, lt_add_iff_pos_right]
#align list.length_filter_lt_length_iff_exists List.length_filter_lt_length_iff_exists

/- warning: list.sublist.countp_le -> List.Sublist.countp_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l₁ : List.{u1} α} {l₂ : List.{u1} α} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.Sublist.{u1} α l₁ l₂) -> (LE.le.{0} Nat Nat.hasLe (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l₁) (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l₂))
but is expected to have type
  forall {α : Type.{u1}} (l₁ : α -> Bool) {l₂ : List.{u1} α} {p : List.{u1} α}, (List.Sublist.{u1} α l₂ p) -> (LE.le.{0} Nat instLENat (List.countp.{u1} α l₁ l₂) (List.countp.{u1} α l₁ p))
Case conversion may be inaccurate. Consider using '#align list.sublist.countp_le List.Sublist.countp_leₓ'. -/
theorem Sublist.countp_le (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ := by
  simpa only [countp_eq_length_filter] using length_le_of_sublist (s.filter p)
#align list.sublist.countp_le List.Sublist.countp_le

/- warning: list.countp_filter -> List.countp_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q] (l : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) (List.filterₓ.{u1} α q (fun (a : α) => _inst_2 a) l)) (List.countp.{u1} α (fun (a : α) => And (p a) (q a)) (fun (a : α) => And.decidable (p a) (q a) (_inst_1 a) (_inst_2 a)) l)
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Bool) (q : α -> Bool) (_inst_1 : List.{u1} α), Eq.{1} Nat (List.countp.{u1} α p (List.filter.{u1} α q _inst_1)) (List.countp.{u1} α (fun (a : α) => Decidable.decide (And (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (q a) Bool.true)) (instDecidableAnd (Eq.{1} Bool (p a) Bool.true) (Eq.{1} Bool (q a) Bool.true) (instDecidableEqBool (p a) Bool.true) (instDecidableEqBool (q a) Bool.true))) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.countp_filter List.countp_filterₓ'. -/
@[simp]
theorem countp_filter (l : List α) : countp p (filter q l) = countp (fun a => p a ∧ q a) l := by
  simp only [countp_eq_length_filter, filter_filter]
#align list.countp_filter List.countp_filter

#print List.countp_true /-
@[simp]
theorem countp_true : (l.countp fun _ => True) = l.length := by simp
#align list.countp_true List.countp_true
-/

#print List.countp_false /-
@[simp]
theorem countp_false : (l.countp fun _ => False) = 0 := by simp
#align list.countp_false List.countp_false
-/

/- warning: list.countp_map -> List.countp_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : β -> Prop) [_inst_3 : DecidablePred.{succ u2} β p] (f : α -> β) (l : List.{u1} α), Eq.{1} Nat (List.countp.{u2} β p (fun (a : β) => _inst_3 a) (List.map.{u1, u2} α β f l)) (List.countp.{u1} α (Function.comp.{succ u1, succ u2, 1} α β Prop p f) (fun (a : α) => _inst_3 (f a)) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : β -> Bool) (_inst_3 : α -> β) (f : List.{u1} α), Eq.{1} Nat (List.countp.{u2} β p (List.map.{u1, u2} α β _inst_3 f)) (List.countp.{u1} α (Function.comp.{succ u1, succ u2, 1} α β Bool p _inst_3) f)
Case conversion may be inaccurate. Consider using '#align list.countp_map List.countp_mapₓ'. -/
@[simp]
theorem countp_map (p : β → Prop) [DecidablePred p] (f : α → β) :
    ∀ l, countp p (map f l) = countp (p ∘ f) l
  | [] => rfl
  | a :: l => by rw [map_cons, countp_cons, countp_cons, countp_map]
#align list.countp_map List.countp_map

variable {p q}

/- warning: list.countp_mono_left -> List.countp_mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q], (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (p x) -> (q x)) -> (LE.le.{0} Nat Nat.hasLe (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.countp.{u1} α q (fun (a : α) => _inst_2 a) l))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Bool} {q : α -> Bool}, (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (Eq.{1} Bool (p x) Bool.true) -> (Eq.{1} Bool (q x) Bool.true)) -> (LE.le.{0} Nat instLENat (List.countp.{u1} α p l) (List.countp.{u1} α q l))
Case conversion may be inaccurate. Consider using '#align list.countp_mono_left List.countp_mono_leftₓ'. -/
theorem countp_mono_left (h : ∀ x ∈ l, p x → q x) : countp p l ≤ countp q l :=
  by
  induction' l with a l ihl; · rfl
  rw [forall_mem_cons] at h; cases' h with ha hl
  rw [countp_cons, countp_cons]
  refine' add_le_add (ihl hl) _
  split_ifs <;> try simp only [le_rfl, zero_le]
  exact absurd (ha ‹_›) ‹_›
#align list.countp_mono_left List.countp_mono_left

/- warning: list.countp_congr -> List.countp_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q], (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (Iff (p x) (q x))) -> (Eq.{1} Nat (List.countp.{u1} α p (fun (a : α) => _inst_1 a) l) (List.countp.{u1} α q (fun (a : α) => _inst_2 a) l))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {p : α -> Bool} {q : α -> Bool}, (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (Iff (Eq.{1} Bool (p x) Bool.true) (Eq.{1} Bool (q x) Bool.true))) -> (Eq.{1} Nat (List.countp.{u1} α p l) (List.countp.{u1} α q l))
Case conversion may be inaccurate. Consider using '#align list.countp_congr List.countp_congrₓ'. -/
theorem countp_congr (h : ∀ x ∈ l, p x ↔ q x) : countp p l = countp q l :=
  le_antisymm (countp_mono_left fun x hx => (h x hx).1) (countp_mono_left fun x hx => (h x hx).2)
#align list.countp_congr List.countp_congr

end Countp

/-! ### count -/


section Count

variable [DecidableEq α]

#print List.count_nil /-
@[simp]
theorem count_nil (a : α) : count a [] = 0 :=
  rfl
#align list.count_nil List.count_nil
-/

#print List.count_cons /-
theorem count_cons (a b : α) (l : List α) :
    count a (b :: l) = if a = b then succ (count a l) else count a l :=
  rfl
#align list.count_cons List.count_cons
-/

#print List.count_cons' /-
theorem count_cons' (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by rw [count_cons]; split_ifs <;> rfl
#align list.count_cons' List.count_cons'
-/

#print List.count_cons_self /-
@[simp]
theorem count_cons_self (a : α) (l : List α) : count a (a :: l) = count a l + 1 :=
  if_pos rfl
#align list.count_cons_self List.count_cons_self
-/

#print List.count_cons_of_ne /-
@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (l : List α) : count a (b :: l) = count a l :=
  if_neg h
#align list.count_cons_of_ne List.count_cons_of_ne
-/

#print List.count_tail /-
theorem count_tail :
    ∀ (l : List α) (a : α) (h : 0 < l.length),
      l.tail.count a = l.count a - ite (a = List.nthLe l 0 h) 1 0
  | _ :: _, a, h => by
    rw [count_cons]
    split_ifs <;> simp
#align list.count_tail List.count_tail
-/

#print List.count_le_length /-
theorem count_le_length (a : α) (l : List α) : count a l ≤ l.length :=
  countp_le_length _
#align list.count_le_length List.count_le_length
-/

/- warning: list.sublist.count_le -> List.Sublist.count_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l₁ : List.{u1} α} {l₂ : List.{u1} α} [_inst_1 : DecidableEq.{succ u1} α], (List.Sublist.{u1} α l₁ l₂) -> (forall (a : α), LE.le.{0} Nat Nat.hasLe (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l₁) (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l₂))
but is expected to have type
  forall {α : Type.{u1}} [l₁ : DecidableEq.{succ u1} α] {l₂ : List.{u1} α} {_inst_1 : List.{u1} α}, (List.Sublist.{u1} α l₂ _inst_1) -> (forall (a : α), LE.le.{0} Nat instLENat (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => l₁ a b)) a l₂) (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => l₁ a b)) a _inst_1))
Case conversion may be inaccurate. Consider using '#align list.sublist.count_le List.Sublist.count_leₓ'. -/
theorem Sublist.count_le (h : l₁ <+ l₂) (a : α) : count a l₁ ≤ count a l₂ :=
  h.countp_le _
#align list.sublist.count_le List.Sublist.count_le

#print List.count_le_count_cons /-
theorem count_le_count_cons (a b : α) (l : List α) : count a l ≤ count a (b :: l) :=
  (sublist_cons _ _).count_le _
#align list.count_le_count_cons List.count_le_count_cons
-/

#print List.count_singleton /-
theorem count_singleton (a : α) : count a [a] = 1 :=
  if_pos rfl
#align list.count_singleton List.count_singleton
-/

#print List.count_singleton' /-
theorem count_singleton' (a b : α) : count a [b] = ite (a = b) 1 0 :=
  rfl
#align list.count_singleton' List.count_singleton'
-/

#print List.count_append /-
@[simp]
theorem count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countp_append _
#align list.count_append List.count_append
-/

#print List.count_join /-
theorem count_join (l : List (List α)) (a : α) : l.join.count a = (l.map (count a)).Sum :=
  countp_join _ _
#align list.count_join List.count_join
-/

#print List.count_concat /-
theorem count_concat (a : α) (l : List α) : count a (concat l a) = succ (count a l) := by
  simp [-add_comm]
#align list.count_concat List.count_concat
-/

#print List.count_pos /-
@[simp]
theorem count_pos {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := by
  simp only [count, countp_pos, exists_prop, exists_eq_right']
#align list.count_pos List.count_pos
-/

#print List.one_le_count_iff_mem /-
@[simp]
theorem one_le_count_iff_mem {a : α} {l : List α} : 1 ≤ count a l ↔ a ∈ l :=
  count_pos
#align list.one_le_count_iff_mem List.one_le_count_iff_mem
-/

#print List.count_eq_zero_of_not_mem /-
@[simp]
theorem count_eq_zero_of_not_mem {a : α} {l : List α} (h : a ∉ l) : count a l = 0 :=
  Decidable.by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')
#align list.count_eq_zero_of_not_mem List.count_eq_zero_of_not_mem
-/

#print List.not_mem_of_count_eq_zero /-
theorem not_mem_of_count_eq_zero {a : α} {l : List α} (h : count a l = 0) : a ∉ l := fun h' =>
  (count_pos.2 h').ne' h
#align list.not_mem_of_count_eq_zero List.not_mem_of_count_eq_zero
-/

/- warning: list.count_eq_zero -> List.count_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{u1} α}, Iff (Eq.{1} Nat (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Not (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l))
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [a : DecidableEq.{succ u1} α] {l : α}, Iff (Eq.{1} Nat (List.count.{u1} α (instBEq.{u1} α (fun (a_1 : α) (b : α) => a a_1 b)) l _inst_1) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Not (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) l _inst_1))
Case conversion may be inaccurate. Consider using '#align list.count_eq_zero List.count_eq_zeroₓ'. -/
@[simp]
theorem count_eq_zero {a : α} {l} : count a l = 0 ↔ a ∉ l :=
  ⟨not_mem_of_count_eq_zero, count_eq_zero_of_not_mem⟩
#align list.count_eq_zero List.count_eq_zero

/- warning: list.count_eq_length -> List.count_eq_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{u1} α}, Iff (Eq.{1} Nat (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) (List.length.{u1} α l)) (forall (b : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) b l) -> (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [a : DecidableEq.{succ u1} α] {l : α}, Iff (Eq.{1} Nat (List.count.{u1} α (instBEq.{u1} α (fun (a_1 : α) (b : α) => a a_1 b)) l _inst_1) (List.length.{u1} α _inst_1)) (forall (b : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) b _inst_1) -> (Eq.{succ u1} α l b))
Case conversion may be inaccurate. Consider using '#align list.count_eq_length List.count_eq_lengthₓ'. -/
@[simp]
theorem count_eq_length {a : α} {l} : count a l = l.length ↔ ∀ b ∈ l, a = b :=
  countp_eq_length _
#align list.count_eq_length List.count_eq_length

#print List.count_replicate_self /-
@[simp]
theorem count_replicate_self (a : α) (n : ℕ) : count a (replicate n a) = n := by
  rw [count, countp_eq_length_filter, filter_eq_self.2, length_replicate] <;>
    exact fun b m => (eq_of_mem_replicate m).symm
#align list.count_replicate_self List.count_replicate_self
-/

#print List.count_replicate /-
theorem count_replicate (a b : α) (n : ℕ) : count a (replicate n b) = if a = b then n else 0 :=
  by
  split_ifs with h
  exacts[h ▸ count_replicate_self _ _, count_eq_zero_of_not_mem <| mt eq_of_mem_replicate h]
#align list.count_replicate List.count_replicate
-/

/- warning: list.filter_eq -> List.filter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α (Eq.{succ u1} α a) (fun (a_1 : α) => _inst_1 a a_1) l) (List.replicate.{u1} α (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α (fun (a_1 : α) => Decidable.decide (Eq.{succ u1} α a a_1) (_inst_1 a a_1)) l) (List.replicate.{u1} α (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l) a)
Case conversion may be inaccurate. Consider using '#align list.filter_eq List.filter_eqₓ'. -/
theorem filter_eq (l : List α) (a : α) : l.filterₓ (Eq a) = replicate (count a l) a := by
  simp [eq_replicate, count, countp_eq_length_filter, @eq_comm _ _ a]
#align list.filter_eq List.filter_eq

/- warning: list.filter_eq' -> List.filter_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.filterₓ.{u1} α (fun (x : α) => Eq.{succ u1} α x a) (fun (a_1 : α) => _inst_1 a_1 a) l) (List.replicate.{u1} α (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (l : List.{u1} α) (a : α), Eq.{succ u1} (List.{u1} α) (List.filter.{u1} α (fun (a_1 : α) => Decidable.decide (Eq.{succ u1} α a_1 a) (_inst_1 a_1 a)) l) (List.replicate.{u1} α (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a l) a)
Case conversion may be inaccurate. Consider using '#align list.filter_eq' List.filter_eq'ₓ'. -/
theorem filter_eq' (l : List α) (a : α) : (l.filterₓ fun x => x = a) = replicate (count a l) a := by
  simp only [filter_eq, @eq_comm _ _ a]
#align list.filter_eq' List.filter_eq'

/- warning: list.le_count_iff_replicate_sublist -> List.le_count_iff_replicate_sublist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{u1} α} {n : Nat}, Iff (LE.le.{0} Nat Nat.hasLe n (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l)) (List.Sublist.{u1} α (List.replicate.{u1} α n a) l)
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [a : DecidableEq.{succ u1} α] {l : Nat} {n : α}, Iff (LE.le.{0} Nat instLENat l (List.count.{u1} α (instBEq.{u1} α (fun (a_1 : α) (b : α) => a a_1 b)) n _inst_1)) (List.Sublist.{u1} α (List.replicate.{u1} α l n) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.le_count_iff_replicate_sublist List.le_count_iff_replicate_sublistₓ'. -/
theorem le_count_iff_replicate_sublist {a : α} {l : List α} {n : ℕ} :
    n ≤ count a l ↔ replicate n a <+ l :=
  ⟨fun h => ((replicate_sublist_replicate a).2 h).trans <| filter_eq l a ▸ filter_sublist _,
    fun h => by simpa only [count_replicate_self] using h.count_le a⟩
#align list.le_count_iff_replicate_sublist List.le_count_iff_replicate_sublist

/- warning: list.replicate_count_eq_of_count_eq_length -> List.replicate_count_eq_of_count_eq_length is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {l : List.{u1} α}, (Eq.{1} Nat (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) (List.length.{u1} α l)) -> (Eq.{succ u1} (List.{u1} α) (List.replicate.{u1} α (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l) a) l)
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [a : DecidableEq.{succ u1} α] {l : α}, (Eq.{1} Nat (List.count.{u1} α (instBEq.{u1} α (fun (a_1 : α) (b : α) => a a_1 b)) l _inst_1) (List.length.{u1} α _inst_1)) -> (Eq.{succ u1} (List.{u1} α) (List.replicate.{u1} α (List.count.{u1} α (instBEq.{u1} α (fun (a_1 : α) (b : α) => a a_1 b)) l _inst_1) l) _inst_1)
Case conversion may be inaccurate. Consider using '#align list.replicate_count_eq_of_count_eq_length List.replicate_count_eq_of_count_eq_lengthₓ'. -/
theorem replicate_count_eq_of_count_eq_length {a : α} {l : List α} (h : count a l = length l) :
    replicate (count a l) a = l :=
  (le_count_iff_replicate_sublist.mp le_rfl).eq_of_length <|
    (length_replicate (count a l) a).trans h
#align list.replicate_count_eq_of_count_eq_length List.replicate_count_eq_of_count_eq_length

/- warning: list.count_filter -> List.count_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] {a : α} {l : List.{u1} α}, (p a) -> (Eq.{1} Nat (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (List.filterₓ.{u1} α p (fun (a : α) => _inst_2 a) l)) (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l))
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [p : DecidableEq.{succ u1} α] {_inst_2 : α -> Bool} {a : α}, (Eq.{1} Bool (_inst_2 a) Bool.true) -> (Eq.{1} Nat (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => p a b)) a (List.filter.{u1} α _inst_2 _inst_1)) (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => p a b)) a _inst_1))
Case conversion may be inaccurate. Consider using '#align list.count_filter List.count_filterₓ'. -/
@[simp]
theorem count_filter {p} [DecidablePred p] {a} {l : List α} (h : p a) :
    count a (filter p l) = count a l := by
  simp only [count, countp_filter,
    show (fun b => a = b ∧ p b) = Eq a by
      ext b
      constructor <;> cc]
#align list.count_filter List.count_filter

/- warning: list.count_bind -> List.count_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} β] (l : List.{u1} α) (f : α -> (List.{u2} β)) (x : β), Eq.{1} Nat (List.count.{u2} β (fun (a : β) (b : β) => _inst_2 a b) x (List.bind.{u1, u2} α β l f)) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{u1, 0} α Nat (Function.comp.{succ u1, succ u2, 1} α (List.{u2} β) Nat (List.count.{u2} β (fun (a : β) (b : β) => _inst_2 a b) x) f) l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} β] (l : List.{u2} α) (f : α -> (List.{u1} β)) (x : β), Eq.{1} Nat (List.count.{u1} β (instBEq.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) x (List.bind.{u2, u1} α β l f)) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{u2, 0} α Nat (Function.comp.{succ u2, succ u1, 1} α (List.{u1} β) Nat (List.count.{u1} β (instBEq.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) x) f) l))
Case conversion may be inaccurate. Consider using '#align list.count_bind List.count_bindₓ'. -/
theorem count_bind {α β} [DecidableEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = sum (map (count x ∘ f) l) := by rw [List.bind, count_join, map_map]
#align list.count_bind List.count_bind

/- warning: list.count_map_of_injective -> List.count_map_of_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : DecidableEq.{succ u2} β] (l : List.{u1} α) (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (x : α), Eq.{1} Nat (List.count.{u2} β (fun (a : β) (b : β) => _inst_3 a b) (f x) (List.map.{u1, u2} α β f l)) (List.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) x l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : DecidableEq.{succ u1} β] (l : List.{u2} α) (f : α -> β), (Function.Injective.{succ u2, succ u1} α β f) -> (forall (x : α), Eq.{1} Nat (List.count.{u1} β (instBEq.{u1} β (fun (a : β) (b : β) => _inst_3 a b)) (f x) (List.map.{u2, u1} α β f l)) (List.count.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) x l))
Case conversion may be inaccurate. Consider using '#align list.count_map_of_injective List.count_map_of_injectiveₓ'. -/
@[simp]
theorem count_map_of_injective {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countp_map, (· ∘ ·), hf.eq_iff]
#align list.count_map_of_injective List.count_map_of_injective

/- warning: list.count_le_count_map -> List.count_le_count_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (l : List.{u1} α) (f : α -> β) (x : α), LE.le.{0} Nat Nat.hasLe (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x l) (List.count.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (f x) (List.map.{u1, u2} α β f l))
but is expected to have type
  forall {α : Type.{u1}} [β : DecidableEq.{succ u1} α] {_inst_1 : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} _inst_1] (l : List.{u1} α) (f : α -> _inst_1) (x : α), LE.le.{0} Nat instLENat (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => β a b)) x l) (List.count.{u2} _inst_1 (instBEq.{u2} _inst_1 (fun (a : _inst_1) (b : _inst_1) => _inst_2 a b)) (f x) (List.map.{u1, u2} α _inst_1 f l))
Case conversion may be inaccurate. Consider using '#align list.count_le_count_map List.count_le_count_mapₓ'. -/
theorem count_le_count_map [DecidableEq β] (l : List α) (f : α → β) (x : α) :
    count x l ≤ count (f x) (map f l) :=
  by
  rw [count, count, countp_map]
  exact countp_mono_left fun y hyl => congr_arg f
#align list.count_le_count_map List.count_le_count_map

#print List.count_erase /-
theorem count_erase (a b : α) : ∀ l : List α, count a (l.eraseₓ b) = count a l - ite (a = b) 1 0
  | [] => by simp
  | c :: l => by
    rw [erase_cons]
    by_cases hc : c = b
    · rw [if_pos hc, hc, count_cons', Nat.add_sub_cancel]
    · rw [if_neg hc, count_cons', count_cons', count_erase]
      by_cases ha : a = b
      · rw [← ha, eq_comm] at hc
        rw [if_pos ha, if_neg hc, add_zero, add_zero]
      · rw [if_neg ha, tsub_zero, tsub_zero]
#align list.count_erase List.count_erase
-/

#print List.count_erase_self /-
@[simp]
theorem count_erase_self (a : α) (l : List α) : count a (List.erase l a) = count a l - 1 := by
  rw [count_erase, if_pos rfl]
#align list.count_erase_self List.count_erase_self
-/

#print List.count_erase_of_ne /-
@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (l : List α) : count a (l.eraseₓ b) = count a l :=
  by rw [count_erase, if_neg ab, tsub_zero]
#align list.count_erase_of_ne List.count_erase_of_ne
-/

/- warning: list.prod_map_eq_pow_single -> List.prod_map_eq_pow_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Monoid.{u2} β] {l : List.{u1} α} (a : α) (f : α -> β), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a' l) -> (Eq.{succ u2} β (f a') (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))))))) -> (Eq.{succ u2} β (List.prod.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (List.map.{u1, u2} α β f l)) (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β _inst_2)) (f a) (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l)))
but is expected to have type
  forall {α : Type.{u1}} {β : List.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] {_inst_2 : Type.{u2}} [l : Monoid.{u2} _inst_2] (a : α) (f : α -> _inst_2), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a' β) -> (Eq.{succ u2} _inst_2 (f a') (OfNat.ofNat.{u2} _inst_2 1 (One.toOfNat1.{u2} _inst_2 (Monoid.toOne.{u2} _inst_2 l))))) -> (Eq.{succ u2} _inst_2 (List.prod.{u2} _inst_2 (MulOneClass.toMul.{u2} _inst_2 (Monoid.toMulOneClass.{u2} _inst_2 l)) (Monoid.toOne.{u2} _inst_2 l) (List.map.{u1, u2} α _inst_2 f β)) (HPow.hPow.{u2, 0, u2} _inst_2 Nat _inst_2 (instHPow.{u2, 0} _inst_2 Nat (Monoid.Pow.{u2} _inst_2 l)) (f a) (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a β)))
Case conversion may be inaccurate. Consider using '#align list.prod_map_eq_pow_single List.prod_map_eq_pow_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a' «expr ≠ » a) -/
@[to_additive]
theorem prod_map_eq_pow_single [Monoid β] {l : List α} (a : α) (f : α → β)
    (hf : ∀ (a') (_ : a' ≠ a), a' ∈ l → f a' = 1) : (l.map f).Prod = f a ^ l.count a :=
  by
  induction' l with a' as h generalizing a
  · rw [map_nil, prod_nil, count_nil, pow_zero]
  · specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    split_ifs with ha'
    · rw [ha', pow_succ]
    · rw [hf a' (Ne.symm ha') (List.mem_cons_self a' as), one_mul]
#align list.prod_map_eq_pow_single List.prod_map_eq_pow_single
#align list.sum_map_eq_nsmul_single List.sum_map_eq_nsmul_single

/- warning: list.prod_eq_pow_single -> List.prod_eq_pow_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Monoid.{u1} α] {l : List.{u1} α} (a : α), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a' l) -> (Eq.{succ u1} α a' (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_2))))))) -> (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_2)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_2)) l) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_2)) a (List.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a l)))
but is expected to have type
  forall {α : Type.{u1}} {_inst_1 : List.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] [l : Monoid.{u1} α] (a : α), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a' _inst_1) -> (Eq.{succ u1} α a' (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α l))))) -> (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α l)) (Monoid.toOne.{u1} α l) _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α l)) a (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a _inst_1)))
Case conversion may be inaccurate. Consider using '#align list.prod_eq_pow_single List.prod_eq_pow_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a' «expr ≠ » a) -/
@[to_additive]
theorem prod_eq_pow_single [Monoid α] {l : List α} (a : α)
    (h : ∀ (a') (_ : a' ≠ a), a' ∈ l → a' = 1) : l.Prod = a ^ l.count a :=
  trans (by rw [map_id'']) (prod_map_eq_pow_single a id h)
#align list.prod_eq_pow_single List.prod_eq_pow_single
#align list.sum_eq_nsmul_single List.sum_eq_nsmul_single

end Count

end List

