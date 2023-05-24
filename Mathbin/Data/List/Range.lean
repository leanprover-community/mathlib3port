/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison

! This file was ported from Lean 3 source module data.list.range
! leanprover-community/mathlib commit be24ec5de6701447e5df5ca75400ffee19d65659
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Chain
import Mathbin.Data.List.Zip

/-!
# Ranges of naturals as lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows basic results about `list.iota`, `list.range`, `list.range'` (all defined in
`data.list.defs`) and defines `list.fin_range`.
`fin_range n` is the list of elements of `fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `list.Ico` instead.
-/


universe u

open Nat

namespace List

variable {α : Type u}

/- warning: list.length_range' -> List.length_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), Eq.{1} Nat (List.length.{0} Nat (List.range' s n)) n
but is expected to have type
  forall (s : Nat) (n : Nat), Eq.{1} Nat (List.length.{0} Nat (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) n
Case conversion may be inaccurate. Consider using '#align list.length_range' List.length_range'ₓ'. -/
@[simp]
theorem length_range' : ∀ s n : ℕ, length (range' s n) = n
  | s, 0 => rfl
  | s, n + 1 => congr_arg succ (length_range' _ _)
#align list.length_range' List.length_range'

/- warning: list.range'_eq_nil -> List.range'_eq_nil is a dubious translation:
lean 3 declaration is
  forall {s : Nat} {n : Nat}, Iff (Eq.{1} (List.{0} Nat) (List.range' s n) (List.nil.{0} Nat)) (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {s : Nat} {n : Nat}, Iff (Eq.{1} (List.{0} Nat) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.nil.{0} Nat)) (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align list.range'_eq_nil List.range'_eq_nilₓ'. -/
@[simp]
theorem range'_eq_nil {s n : ℕ} : range' s n = [] ↔ n = 0 := by rw [← length_eq_zero, length_range']
#align list.range'_eq_nil List.range'_eq_nil

/- warning: list.mem_range' -> List.mem_range' is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {s : Nat} {n : Nat}, Iff (Membership.Mem.{0, 0} Nat (List.{0} Nat) (List.hasMem.{0} Nat) m (List.range' s n)) (And (LE.le.{0} Nat Nat.hasLe s m) (LT.lt.{0} Nat Nat.hasLt m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s n)))
but is expected to have type
  forall {m : Nat} {s : Nat} {n : Nat}, Iff (Membership.mem.{0, 0} Nat (List.{0} Nat) (List.instMembershipList.{0} Nat) m (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (And (LE.le.{0} Nat instLENat s m) (LT.lt.{0} Nat instLTNat m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s n)))
Case conversion may be inaccurate. Consider using '#align list.mem_range' List.mem_range'ₓ'. -/
@[simp]
theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | s, 0 => (false_iff_iff _).2 fun ⟨H1, H2⟩ => not_le_of_lt H2 H1
  | s, succ n =>
    have : m = s → m < s + n + 1 := fun e => e ▸ lt_succ_of_le (Nat.le_add_right _ _)
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      simpa only [eq_comm] using (@Decidable.le_iff_eq_or_lt _ _ _ s m).symm
    (mem_cons _ _ _).trans <| by
      simp only [mem_range', or_and_left, or_iff_right_of_imp this, l, add_right_comm] <;> rfl
#align list.mem_range' List.mem_range'

/- warning: list.map_add_range' -> List.map_add_range' is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.map.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a) (List.range' s n)) (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a s) n)
but is expected to have type
  forall (a : Nat) (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.map.{0, 0} Nat Nat ((fun (x._@.Mathlib.Data.List.Range._hyg.391 : Nat) (x._@.Mathlib.Data.List.Range._hyg.393 : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) x._@.Mathlib.Data.List.Range._hyg.391 x._@.Mathlib.Data.List.Range._hyg.393) a) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a s) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.map_add_range' List.map_add_range'ₓ'. -/
theorem map_add_range' (a) : ∀ s n : ℕ, map ((· + ·) a) (range' s n) = range' (a + s) n
  | s, 0 => rfl
  | s, n + 1 => congr_arg (cons _) (map_add_range' (s + 1) n)
#align list.map_add_range' List.map_add_range'

/- warning: list.map_sub_range' -> List.map_sub_range' is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (s : Nat) (n : Nat), (LE.le.{0} Nat Nat.hasLe a s) -> (Eq.{1} (List.{0} Nat) (List.map.{0, 0} Nat Nat (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) x a) (List.range' s n)) (List.range' (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) s a) n))
but is expected to have type
  forall (a : Nat) (s : Nat) (n : Nat), (LE.le.{0} Nat instLENat a s) -> (Eq.{1} (List.{0} Nat) (List.map.{0, 0} Nat Nat (fun (x : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) x a) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (List.range' (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) s a) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.map_sub_range' List.map_sub_range'ₓ'. -/
theorem map_sub_range' (a) :
    ∀ (s n : ℕ) (h : a ≤ s), map (fun x => x - a) (range' s n) = range' (s - a) n
  | s, 0, _ => rfl
  | s, n + 1, h =>
    by
    convert congr_arg (cons (s - a)) (map_sub_range' (s + 1) n (Nat.le_succ_of_le h))
    rw [Nat.succ_sub h]
    rfl
#align list.map_sub_range' List.map_sub_range'

/- warning: list.chain_succ_range' -> List.chain_succ_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), List.Chain.{0} Nat (fun (a : Nat) (b : Nat) => Eq.{1} Nat b (Nat.succ a)) s (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) n)
but is expected to have type
  forall (s : Nat) (n : Nat), List.Chain.{0} Nat (fun (a : Nat) (b : Nat) => Eq.{1} Nat b (Nat.succ a)) s (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.chain_succ_range' List.chain_succ_range'ₓ'. -/
theorem chain_succ_range' : ∀ s n : ℕ, Chain (fun a b => b = succ a) s (range' (s + 1) n)
  | s, 0 => Chain.nil
  | s, n + 1 => (chain_succ_range' (s + 1) n).cons rfl
#align list.chain_succ_range' List.chain_succ_range'

/- warning: list.chain_lt_range' -> List.chain_lt_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), List.Chain.{0} Nat (LT.lt.{0} Nat Nat.hasLt) s (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) n)
but is expected to have type
  forall (s : Nat) (n : Nat), List.Chain.{0} Nat (fun (x._@.Mathlib.Data.List.Range._hyg.791 : Nat) (x._@.Mathlib.Data.List.Range._hyg.793 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Data.List.Range._hyg.791 x._@.Mathlib.Data.List.Range._hyg.793) s (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.chain_lt_range' List.chain_lt_range'ₓ'. -/
theorem chain_lt_range' (s n : ℕ) : Chain (· < ·) s (range' (s + 1) n) :=
  (chain_succ_range' s n).imp fun a b e => e.symm ▸ lt_succ_self _
#align list.chain_lt_range' List.chain_lt_range'

/- warning: list.pairwise_lt_range' -> List.pairwise_lt_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), List.Pairwise.{0} Nat (LT.lt.{0} Nat Nat.hasLt) (List.range' s n)
but is expected to have type
  forall (s : Nat) (n : Nat), List.Pairwise.{0} Nat (fun (x._@.Mathlib.Data.List.Range._hyg.852 : Nat) (x._@.Mathlib.Data.List.Range._hyg.854 : Nat) => LT.lt.{0} Nat instLTNat x._@.Mathlib.Data.List.Range._hyg.852 x._@.Mathlib.Data.List.Range._hyg.854) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.pairwise_lt_range' List.pairwise_lt_range'ₓ'. -/
theorem pairwise_lt_range' : ∀ s n : ℕ, Pairwise (· < ·) (range' s n)
  | s, 0 => Pairwise.nil
  | s, n + 1 => chain_iff_pairwise.1 (chain_lt_range' s n)
#align list.pairwise_lt_range' List.pairwise_lt_range'

/- warning: list.nodup_range' -> List.nodup_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), List.Nodup.{0} Nat (List.range' s n)
but is expected to have type
  forall (s : Nat) (n : Nat), List.Nodup.{0} Nat (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.nodup_range' List.nodup_range'ₓ'. -/
theorem nodup_range' (s n : ℕ) : Nodup (range' s n) :=
  (pairwise_lt_range' s n).imp fun a b => ne_of_lt
#align list.nodup_range' List.nodup_range'

/- warning: list.range'_append -> List.range'_append is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (m : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (Append.append.{0} (List.{0} Nat) (List.hasAppend.{0} Nat) (List.range' s m) (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s m) n)) (List.range' s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m))
but is expected to have type
  forall (s : Nat) (m : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat) (instHAppend.{0} (List.{0} Nat) (List.instAppendList.{0} Nat)) (List.range' s m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.range' (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s m) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (List.range' s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.range'_append List.range'_appendₓ'. -/
@[simp]
theorem range'_append : ∀ s m n : ℕ, range' s m ++ range' (s + m) n = range' s (n + m)
  | s, 0, n => rfl
  | s, m + 1, n =>
    show s :: (range' (s + 1) m ++ range' (s + m + 1) n) = s :: range' (s + 1) (n + m) by
      rw [add_right_comm, range'_append]
#align list.range'_append List.range'_append

/- warning: list.range'_sublist_right -> List.range'_sublist_right is a dubious translation:
lean 3 declaration is
  forall {s : Nat} {m : Nat} {n : Nat}, Iff (List.Sublist.{0} Nat (List.range' s m) (List.range' s n)) (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall {s : Nat} {m : Nat} {n : Nat}, Iff (List.Sublist.{0} Nat (List.range' s m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (LE.le.{0} Nat instLENat m n)
Case conversion may be inaccurate. Consider using '#align list.range'_sublist_right List.range'_sublist_rightₓ'. -/
theorem range'_sublist_right {s m n : ℕ} : range' s m <+ range' s n ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_range'] using h.length_le, fun h => by
    rw [← tsub_add_cancel_of_le h, ← range'_append] <;> apply sublist_append_left⟩
#align list.range'_sublist_right List.range'_sublist_right

/- warning: list.range'_subset_right -> List.range'_subset_right is a dubious translation:
lean 3 declaration is
  forall {s : Nat} {m : Nat} {n : Nat}, Iff (HasSubset.Subset.{0} (List.{0} Nat) (List.hasSubset.{0} Nat) (List.range' s m) (List.range' s n)) (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall {s : Nat} {m : Nat} {n : Nat}, Iff (HasSubset.Subset.{0} (List.{0} Nat) (List.instHasSubsetList.{0} Nat) (List.range' s m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (LE.le.{0} Nat instLENat m n)
Case conversion may be inaccurate. Consider using '#align list.range'_subset_right List.range'_subset_rightₓ'. -/
theorem range'_subset_right {s m n : ℕ} : range' s m ⊆ range' s n ↔ m ≤ n :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      lt_irrefl (s + n) <|
        (mem_range'.1 <| h <| mem_range'.2 ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hn s⟩).2,
    fun h => (range'_sublist_right.2 h).Subset⟩
#align list.range'_subset_right List.range'_subset_right

/- warning: list.nth_range' -> List.get?_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) {m : Nat} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt m n) -> (Eq.{1} (Option.{0} Nat) (List.get?.{0} Nat (List.range' s n) m) (Option.some.{0} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s m)))
but is expected to have type
  forall (s : Nat) {m : Nat} {n : Nat}, (LT.lt.{0} Nat instLTNat m n) -> (Eq.{1} (Option.{0} Nat) (List.get?.{0} Nat (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) m) (Option.some.{0} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s m)))
Case conversion may be inaccurate. Consider using '#align list.nth_range' List.get?_range'ₓ'. -/
theorem get?_range' : ∀ (s) {m n : ℕ}, m < n → get? (range' s n) m = some (s + m)
  | s, 0, n + 1, _ => rfl
  | s, m + 1, n + 1, h =>
    (nth_range' (s + 1) (lt_of_add_lt_add_right h)).trans <| by rw [add_right_comm] <;> rfl
#align list.nth_range' List.get?_range'

/- warning: list.nth_le_range' -> List.nthLe_range' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat} (i : Nat) (H : LT.lt.{0} Nat Nat.hasLt i (List.length.{0} Nat (List.range' n m))), Eq.{1} Nat (List.nthLe.{0} Nat (List.range' n m) i H) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n i)
but is expected to have type
  forall {n : Nat} {m : Nat} (i : Nat) (H : LT.lt.{0} Nat instLTNat i (List.length.{0} Nat (List.range' n m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))), Eq.{1} Nat (List.nthLe.{0} Nat (List.range' n m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i H) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n i)
Case conversion may be inaccurate. Consider using '#align list.nth_le_range' List.nthLe_range'ₓ'. -/
@[simp]
theorem nthLe_range' {n m} (i) (H : i < (range' n m).length) : nthLe (range' n m) i H = n + i :=
  Option.some.inj <| by rw [← nth_le_nth _, nth_range' _ (by simpa using H)]
#align list.nth_le_range' List.nthLe_range'

/- warning: list.range'_concat -> List.range'_concat is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range' s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Append.append.{0} (List.{0} Nat) (List.hasAppend.{0} Nat) (List.range' s n) (List.cons.{0} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s n) (List.nil.{0} Nat)))
but is expected to have type
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range' s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat) (instHAppend.{0} (List.{0} Nat) (List.instAppendList.{0} Nat)) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.cons.{0} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s n) (List.nil.{0} Nat)))
Case conversion may be inaccurate. Consider using '#align list.range'_concat List.range'_concatₓ'. -/
theorem range'_concat (s n : ℕ) : range' s (n + 1) = range' s n ++ [s + n] := by
  rw [add_comm n 1] <;> exact (range'_append s n 1).symm
#align list.range'_concat List.range'_concat

/- warning: list.range_core_range' -> List.range_loop_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range.loop s (List.range' s n)) (List.range' (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n s))
but is expected to have type
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range.loop s (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (List.range' (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n s) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.range_core_range' List.range_loop_range'ₓ'. -/
theorem range_loop_range' : ∀ s n : ℕ, List.range.loop s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by
    rw [show n + (s + 1) = n + 1 + s from add_right_comm n s 1] <;>
      exact range_core_range' s (n + 1)
#align list.range_core_range' List.range_loop_range'

/- warning: list.range_eq_range' -> List.range_eq_range' is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (List.{0} Nat) (List.range n) (List.range' (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} (List.{0} Nat) (List.range n) (List.range' (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.range_eq_range' List.range_eq_range'ₓ'. -/
theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [zero_add]
#align list.range_eq_range' List.range_eq_range'

#print List.range_succ_eq_map /-
theorem range_succ_eq_map (n : ℕ) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', add_comm, ← map_add_range'] <;> congr <;>
    exact funext one_add
#align list.range_succ_eq_map List.range_succ_eq_map
-/

/- warning: list.range'_eq_map_range -> List.range'_eq_map_range is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range' s n) (List.map.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s) (List.range n))
but is expected to have type
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (List.map.{0, 0} Nat Nat (fun (x._@.Mathlib.Data.List.Range._hyg.1967 : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s x._@.Mathlib.Data.List.Range._hyg.1967) (List.range n))
Case conversion may be inaccurate. Consider using '#align list.range'_eq_map_range List.range'_eq_map_rangeₓ'. -/
theorem range'_eq_map_range (s n : ℕ) : range' s n = map ((· + ·) s) (range n) := by
  rw [range_eq_range', map_add_range'] <;> rfl
#align list.range'_eq_map_range List.range'_eq_map_range

#print List.length_range /-
@[simp]
theorem length_range (n : ℕ) : length (range n) = n := by simp only [range_eq_range', length_range']
#align list.length_range List.length_range
-/

#print List.range_eq_nil /-
@[simp]
theorem range_eq_nil {n : ℕ} : range n = [] ↔ n = 0 := by rw [← length_eq_zero, length_range]
#align list.range_eq_nil List.range_eq_nil
-/

#print List.pairwise_lt_range /-
theorem pairwise_lt_range (n : ℕ) : Pairwise (· < ·) (range n) := by
  simp only [range_eq_range', pairwise_lt_range']
#align list.pairwise_lt_range List.pairwise_lt_range
-/

#print List.pairwise_le_range /-
theorem pairwise_le_range (n : ℕ) : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp (@le_of_lt ℕ _) (pairwise_lt_range _)
#align list.pairwise_le_range List.pairwise_le_range
-/

#print List.nodup_range /-
theorem nodup_range (n : ℕ) : Nodup (range n) := by simp only [range_eq_range', nodup_range']
#align list.nodup_range List.nodup_range
-/

#print List.range_sublist /-
theorem range_sublist {m n : ℕ} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]
#align list.range_sublist List.range_sublist
-/

#print List.range_subset /-
theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right]
#align list.range_subset List.range_subset
-/

#print List.mem_range /-
@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range', Nat.zero_le, true_and_iff, zero_add]
#align list.mem_range List.mem_range
-/

#print List.not_mem_range_self /-
@[simp]
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  mt mem_range.1 <| lt_irrefl _
#align list.not_mem_range_self List.not_mem_range_self
-/

#print List.self_mem_range_succ /-
@[simp]
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := by
  simp only [succ_pos', lt_add_iff_pos_right, mem_range]
#align list.self_mem_range_succ List.self_mem_range_succ
-/

#print List.get?_range /-
theorem get?_range {m n : ℕ} (h : m < n) : get? (range n) m = some m := by
  simp only [range_eq_range', nth_range' _ h, zero_add]
#align list.nth_range List.get?_range
-/

#print List.range_succ /-
theorem range_succ (n : ℕ) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_concat, zero_add]
#align list.range_succ List.range_succ
-/

#print List.range_zero /-
@[simp]
theorem range_zero : range 0 = [] :=
  rfl
#align list.range_zero List.range_zero
-/

#print List.chain'_range_succ /-
theorem chain'_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain' r (range n.succ) ↔ ∀ m < n, r m m.succ :=
  by
  rw [range_succ]
  induction' n with n hn
  · simp
  · rw [range_succ]
    simp only [append_assoc, singleton_append, chain'_append_cons_cons, chain'_singleton,
      and_true_iff]
    rw [hn, forall_lt_succ]
#align list.chain'_range_succ List.chain'_range_succ
-/

#print List.chain_range_succ /-
theorem chain_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    Chain r a (range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ :=
  by
  rw [range_succ_eq_map, chain_cons, and_congr_right_iff, ← chain'_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl
#align list.chain_range_succ List.chain_range_succ
-/

#print List.range_add /-
theorem range_add (a : ℕ) : ∀ b, range (a + b) = range a ++ (range b).map fun x => a + x
  | 0 => by rw [add_zero, range_zero, map_nil, append_nil]
  | b + 1 => by
    rw [Nat.add_succ, range_succ, range_add b, range_succ, map_append, map_singleton, append_assoc]
#align list.range_add List.range_add
-/

/- warning: list.iota_eq_reverse_range' -> List.iota_eq_reverse_range' is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (List.{0} Nat) (List.iota n) (List.reverse.{0} Nat (List.range' (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) n))
but is expected to have type
  forall (n : Nat), Eq.{1} (List.{0} Nat) (List.iota n) (List.reverse.{0} Nat (List.range' (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align list.iota_eq_reverse_range' List.iota_eq_reverse_range'ₓ'. -/
theorem iota_eq_reverse_range' : ∀ n : ℕ, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by
    simp only [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, add_comm] <;> rfl
#align list.iota_eq_reverse_range' List.iota_eq_reverse_range'

#print List.length_iota /-
@[simp]
theorem length_iota (n : ℕ) : length (iota n) = n := by
  simp only [iota_eq_reverse_range', length_reverse, length_range']
#align list.length_iota List.length_iota
-/

#print List.pairwise_gt_iota /-
theorem pairwise_gt_iota (n : ℕ) : Pairwise (· > ·) (iota n) := by
  simp only [iota_eq_reverse_range', pairwise_reverse, pairwise_lt_range']
#align list.pairwise_gt_iota List.pairwise_gt_iota
-/

#print List.nodup_iota /-
theorem nodup_iota (n : ℕ) : Nodup (iota n) :=
  (pairwise_gt_iota n).imp fun a b => ne_of_gt
#align list.nodup_iota List.nodup_iota
-/

#print List.mem_iota /-
theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp only [iota_eq_reverse_range', mem_reverse, mem_range', add_comm, lt_succ_iff]
#align list.mem_iota List.mem_iota
-/

/- warning: list.reverse_range' -> List.reverse_range' is a dubious translation:
lean 3 declaration is
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.reverse.{0} Nat (List.range' s n)) (List.map.{0, 0} Nat Nat (fun (i : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) s n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i) (List.range n))
but is expected to have type
  forall (s : Nat) (n : Nat), Eq.{1} (List.{0} Nat) (List.reverse.{0} Nat (List.range' s n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (List.map.{0, 0} Nat Nat (fun (i : Nat) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) s n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i) (List.range n))
Case conversion may be inaccurate. Consider using '#align list.reverse_range' List.reverse_range'ₓ'. -/
theorem reverse_range' : ∀ s n : ℕ, reverse (range' s n) = map (fun i => s + n - 1 - i) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_concat, reverse_append, range_succ_eq_map] <;>
      simpa only [show s + (n + 1) - 1 = s + n from rfl, (· ∘ ·), fun a i =>
        show a - 1 - i = a - succ i from pred_sub _ _, reverse_singleton, map_cons, tsub_zero,
        cons_append, nil_append, eq_self_iff_true, true_and_iff, map_map] using reverse_range' s n
#align list.reverse_range' List.reverse_range'

#print List.finRange /-
/-- All elements of `fin n`, from `0` to `n-1`. The corresponding finset is `finset.univ`. -/
def finRange (n : ℕ) : List (Fin n) :=
  (range n).pmap Fin.mk fun _ => List.mem_range.1
#align list.fin_range List.finRange
-/

#print List.finRange_zero /-
@[simp]
theorem finRange_zero : finRange 0 = [] :=
  rfl
#align list.fin_range_zero List.finRange_zero
-/

#print List.mem_finRange /-
@[simp]
theorem mem_finRange {n : ℕ} (a : Fin n) : a ∈ finRange n :=
  mem_pmap.2
    ⟨a.1, mem_range.2 a.2, by
      cases a
      rfl⟩
#align list.mem_fin_range List.mem_finRange
-/

#print List.nodup_finRange /-
theorem nodup_finRange (n : ℕ) : (finRange n).Nodup :=
  Pairwise.pmap (nodup_range n) _ fun _ _ _ _ => @Fin.ne_of_vne _ ⟨_, _⟩ ⟨_, _⟩
#align list.nodup_fin_range List.nodup_finRange
-/

#print List.length_finRange /-
@[simp]
theorem length_finRange (n : ℕ) : (finRange n).length = n := by
  rw [fin_range, length_pmap, length_range]
#align list.length_fin_range List.length_finRange
-/

#print List.finRange_eq_nil /-
@[simp]
theorem finRange_eq_nil {n : ℕ} : finRange n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_fin_range]
#align list.fin_range_eq_nil List.finRange_eq_nil
-/

/- warning: list.prod_range_succ -> List.prod_range_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.map.{0, u1} Nat α f (List.range (Nat.succ n)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.map.{0, u1} Nat α f (List.range n))) (f n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.map.{0, u1} Nat α f (List.range (Nat.succ n)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.map.{0, u1} Nat α f (List.range n))) (f n))
Case conversion may be inaccurate. Consider using '#align list.prod_range_succ List.prod_range_succₓ'. -/
@[to_additive]
theorem prod_range_succ {α : Type u} [Monoid α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).Prod = ((range n).map f).Prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_one]
#align list.prod_range_succ List.prod_range_succ
#align list.sum_range_succ List.sum_range_succ

/- warning: list.prod_range_succ' -> List.prod_range_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.map.{0, u1} Nat α f (List.range (Nat.succ n)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (List.map.{0, u1} Nat α (fun (i : Nat) => f (Nat.succ i)) (List.range n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (f : Nat -> α) (n : Nat), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.map.{0, u1} Nat α f (List.range (Nat.succ n)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (List.map.{0, u1} Nat α (fun (i : Nat) => f (Nat.succ i)) (List.range n))))
Case conversion may be inaccurate. Consider using '#align list.prod_range_succ' List.prod_range_succ'ₓ'. -/
/-- A variant of `prod_range_succ` which pulls off the first
  term in the product rather than the last.-/
@[to_additive
      "A variant of `sum_range_succ` which pulls off the first term in the sum\n  rather than the last."]
theorem prod_range_succ' {α : Type u} [Monoid α] (f : ℕ → α) (n : ℕ) :
    ((range n.succ).map f).Prod = f 0 * ((range n).map fun i => f (succ i)).Prod :=
  Nat.recOn n (show 1 * f 0 = f 0 * 1 by rw [one_mul, mul_one]) fun _ hd => by
    rw [List.prod_range_succ, hd, mul_assoc, ← List.prod_range_succ]
#align list.prod_range_succ' List.prod_range_succ'
#align list.sum_range_succ' List.sum_range_succ'

/- warning: list.enum_from_map_fst -> List.enum_from_map_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (n : Nat) (l : List.{u1} α), Eq.{1} (List.{0} Nat) (List.map.{u1, 0} (Prod.{0, u1} Nat α) Nat (Prod.fst.{0, u1} Nat α) (List.enumFrom.{u1} α n l)) (List.range' n (List.length.{u1} α l))
but is expected to have type
  forall {α : Type.{u1}} (n : Nat) (l : List.{u1} α), Eq.{1} (List.{0} Nat) (List.map.{u1, 0} (Prod.{0, u1} Nat α) Nat (Prod.fst.{0, u1} Nat α) (List.enumFrom.{u1} α n l)) (List.range' n (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align list.enum_from_map_fst List.enum_from_map_fstₓ'. -/
@[simp]
theorem enum_from_map_fst : ∀ (n) (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | n, [] => rfl
  | n, a :: l => congr_arg (cons _) (enum_from_map_fst _ _)
#align list.enum_from_map_fst List.enum_from_map_fst

#print List.enum_map_fst /-
@[simp]
theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enum_from_map_fst, range_eq_range']
#align list.enum_map_fst List.enum_map_fst
-/

#print List.enum_eq_zip_range /-
theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)
#align list.enum_eq_zip_range List.enum_eq_zip_range
-/

#print List.unzip_enum_eq_prod /-
@[simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]
#align list.unzip_enum_eq_prod List.unzip_enum_eq_prod
-/

/- warning: list.enum_from_eq_zip_range' -> List.enum_from_eq_zip_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α) {n : Nat}, Eq.{succ u1} (List.{u1} (Prod.{0, u1} Nat α)) (List.enumFrom.{u1} α n l) (List.zip.{0, u1} Nat α (List.range' n (List.length.{u1} α l)) l)
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α) {n : Nat}, Eq.{succ u1} (List.{u1} (Prod.{0, u1} Nat α)) (List.enumFrom.{u1} α n l) (List.zip.{0, u1} Nat α (List.range' n (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) l)
Case conversion may be inaccurate. Consider using '#align list.enum_from_eq_zip_range' List.enum_from_eq_zip_range'ₓ'. -/
theorem enum_from_eq_zip_range' (l : List α) {n : ℕ} : l.enumFrom n = (range' n l.length).zip l :=
  zip_of_prod (enum_from_map_fst _ _) (enumFrom_map_snd _ _)
#align list.enum_from_eq_zip_range' List.enum_from_eq_zip_range'

/- warning: list.unzip_enum_from_eq_prod -> List.unzip_enum_from_eq_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α) {n : Nat}, Eq.{succ u1} (Prod.{0, u1} (List.{0} Nat) (List.{u1} α)) (List.unzip.{0, u1} Nat α (List.enumFrom.{u1} α n l)) (Prod.mk.{0, u1} (List.{0} Nat) (List.{u1} α) (List.range' n (List.length.{u1} α l)) l)
but is expected to have type
  forall {α : Type.{u1}} (l : List.{u1} α) {n : Nat}, Eq.{succ u1} (Prod.{0, u1} (List.{0} Nat) (List.{u1} α)) (List.unzip.{0, u1} Nat α (List.enumFrom.{u1} α n l)) (Prod.mk.{0, u1} (List.{0} Nat) (List.{u1} α) (List.range' n (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) l)
Case conversion may be inaccurate. Consider using '#align list.unzip_enum_from_eq_prod List.unzip_enum_from_eq_prodₓ'. -/
@[simp]
theorem unzip_enum_from_eq_prod (l : List α) {n : ℕ} :
    (l.enumFrom n).unzip = (range' n l.length, l) := by
  simp only [enum_from_eq_zip_range', unzip_zip, length_range']
#align list.unzip_enum_from_eq_prod List.unzip_enum_from_eq_prod

#print List.nthLe_range /-
@[simp]
theorem nthLe_range {n} (i) (H : i < (range n).length) : nthLe (range n) i H = i :=
  Option.some.inj <| by rw [← nth_le_nth _, nth_range (by simpa using H)]
#align list.nth_le_range List.nthLe_range
-/

#print List.nthLe_finRange /-
@[simp]
theorem nthLe_finRange {n : ℕ} {i : ℕ} (h) : (finRange n).nthLe i h = ⟨i, length_finRange n ▸ h⟩ :=
  by simp only [fin_range, nth_le_range, nth_le_pmap]
#align list.nth_le_fin_range List.nthLe_finRange
-/

end List

