/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.list.intervals
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Lattice
import Mathbin.Data.List.Range

/-!
# Intervals in ℕ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines intervals of naturals. `list.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `set.Ico a b` is `[finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `data.int.range` (and maybe `list.range'`?).
-/


open Nat

namespace List

#print List.Ico /-
/-- `Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `data/set/intervals.lean` for `set.Ico`, modelling intervals in general preorders, and
`multiset.Ico` and `finset.Ico` for `n ≤ x < m` as a multiset or as a finset.
 -/
def Ico (n m : ℕ) : List ℕ :=
  range' n (m - n)
#align list.Ico List.Ico
-/

namespace Ico

#print List.Ico.zero_bot /-
theorem zero_bot (n : ℕ) : Ico 0 n = range n := by rw [Ico, tsub_zero, range_eq_range']
#align list.Ico.zero_bot List.Ico.zero_bot
-/

#print List.Ico.length /-
@[simp]
theorem length (n m : ℕ) : length (Ico n m) = m - n := by dsimp [Ico]; simp only [length_range']
#align list.Ico.length List.Ico.length
-/

#print List.Ico.pairwise_lt /-
theorem pairwise_lt (n m : ℕ) : Pairwise (· < ·) (Ico n m) := by dsimp [Ico];
  simp only [pairwise_lt_range']
#align list.Ico.pairwise_lt List.Ico.pairwise_lt
-/

#print List.Ico.nodup /-
theorem nodup (n m : ℕ) : Nodup (Ico n m) := by dsimp [Ico]; simp only [nodup_range']
#align list.Ico.nodup List.Ico.nodup
-/

#print List.Ico.mem /-
@[simp]
theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
  by
  suffices n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m by simp [Ico, this]
  cases' le_total n m with hnm hmn
  · rw [add_tsub_cancel_of_le hnm]
  · rw [tsub_eq_zero_iff_le.mpr hmn, add_zero]
    exact
      and_congr_right fun hnl =>
        Iff.intro (fun hln => (not_le_of_gt hln hnl).elim) fun hlm => lt_of_lt_of_le hlm hmn
#align list.Ico.mem List.Ico.mem
-/

#print List.Ico.eq_nil_of_le /-
theorem eq_nil_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = [] := by
  simp [Ico, tsub_eq_zero_iff_le.mpr h]
#align list.Ico.eq_nil_of_le List.Ico.eq_nil_of_le
-/

#print List.Ico.map_add /-
theorem map_add (n m k : ℕ) : (Ico n m).map ((· + ·) k) = Ico (n + k) (m + k) := by
  rw [Ico, Ico, map_add_range', add_tsub_add_eq_tsub_right, add_comm n k]
#align list.Ico.map_add List.Ico.map_add
-/

#print List.Ico.map_sub /-
theorem map_sub (n m k : ℕ) (h₁ : k ≤ n) : ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k) :=
  by rw [Ico, Ico, tsub_tsub_tsub_cancel_right h₁, map_sub_range' _ _ _ h₁]
#align list.Ico.map_sub List.Ico.map_sub
-/

#print List.Ico.self_empty /-
@[simp]
theorem self_empty {n : ℕ} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)
#align list.Ico.self_empty List.Ico.self_empty
-/

#print List.Ico.eq_empty_iff /-
@[simp]
theorem eq_empty_iff {n m : ℕ} : Ico n m = [] ↔ m ≤ n :=
  Iff.intro (fun h => tsub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le
#align list.Ico.eq_empty_iff List.Ico.eq_empty_iff
-/

#print List.Ico.append_consecutive /-
theorem append_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) : Ico n m ++ Ico m l = Ico n l :=
  by
  dsimp only [Ico]
  convert range'_append _ _ _
  · exact (add_tsub_cancel_of_le hnm).symm
  · rwa [← add_tsub_assoc_of_le hnm, tsub_add_cancel_of_le]
#align list.Ico.append_consecutive List.Ico.append_consecutive
-/

@[simp]
theorem inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = [] :=
  by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter, List.Ico.mem]
  intro h₁ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂
#align list.Ico.inter_consecutive List.Ico.inter_consecutive

@[simp]
theorem bagInter_consecutive (n m l : ℕ) : List.bagInter (Ico n m) (Ico m l) = [] :=
  (bagInter_nil_iff_inter_nil _ _).2 (inter_consecutive n m l)
#align list.Ico.bag_inter_consecutive List.Ico.bagInter_consecutive

#print List.Ico.succ_singleton /-
@[simp]
theorem succ_singleton {n : ℕ} : Ico n (n + 1) = [n] := by dsimp [Ico]; simp [add_tsub_cancel_left]
#align list.Ico.succ_singleton List.Ico.succ_singleton
-/

#print List.Ico.succ_top /-
theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = Ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]; exact Nat.le_succ _
#align list.Ico.succ_top List.Ico.succ_top
-/

#print List.Ico.eq_cons /-
theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succ n) h, succ_singleton]; rfl
#align list.Ico.eq_cons List.Ico.eq_cons
-/

#print List.Ico.pred_singleton /-
@[simp]
theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = [m - 1] := by dsimp [Ico];
  rw [tsub_tsub_cancel_of_le (succ_le_of_lt h)]; simp
#align list.Ico.pred_singleton List.Ico.pred_singleton
-/

#print List.Ico.chain'_succ /-
theorem chain'_succ (n m : ℕ) : Chain' (fun a b => b = succ a) (Ico n m) :=
  by
  by_cases n < m
  · rw [eq_cons h]; exact chain_succ_range' _ _
  · rw [eq_nil_of_le (le_of_not_gt h)]; trivial
#align list.Ico.chain'_succ List.Ico.chain'_succ
-/

#print List.Ico.not_mem_top /-
@[simp]
theorem not_mem_top {n m : ℕ} : m ∉ Ico n m := by simp
#align list.Ico.not_mem_top List.Ico.not_mem_top
-/

theorem filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) :
    ((Ico n m).filterₓ fun x => x < l) = Ico n m :=
  filter_eq_self.2 fun k hk => lt_of_lt_of_le (mem.1 hk).2 hml
#align list.Ico.filter_lt_of_top_le List.Ico.filter_lt_of_top_le

theorem filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((Ico n m).filterₓ fun x => x < l) = [] :=
  filter_eq_nil.2 fun k hk => not_lt_of_le <| le_trans hln <| (mem.1 hk).1
#align list.Ico.filter_lt_of_le_bot List.Ico.filter_lt_of_le_bot

theorem filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : ((Ico n m).filterₓ fun x => x < l) = Ico n l :=
  by
  cases' le_total n l with hnl hln
  ·
    rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]
#align list.Ico.filter_lt_of_ge List.Ico.filter_lt_of_ge

@[simp]
theorem filter_lt (n m l : ℕ) : ((Ico n m).filterₓ fun x => x < l) = Ico n (min m l) :=
  by
  cases' le_total m l with hml hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]
#align list.Ico.filter_lt List.Ico.filter_lt

theorem filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) :
    ((Ico n m).filterₓ fun x => l ≤ x) = Ico n m :=
  filter_eq_self.2 fun k hk => le_trans hln (mem.1 hk).1
#align list.Ico.filter_le_of_le_bot List.Ico.filter_le_of_le_bot

theorem filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((Ico n m).filterₓ fun x => l ≤ x) = [] :=
  filter_eq_nil.2 fun k hk => not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)
#align list.Ico.filter_le_of_top_le List.Ico.filter_le_of_top_le

theorem filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : ((Ico n m).filterₓ fun x => l ≤ x) = Ico l m :=
  by
  cases' le_total l m with hlm hml
  ·
    rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]
#align list.Ico.filter_le_of_le List.Ico.filter_le_of_le

@[simp]
theorem filter_le (n m l : ℕ) : ((Ico n m).filterₓ fun x => l ≤ x) = Ico (max n l) m :=
  by
  cases' le_total n l with hnl hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]
#align list.Ico.filter_le List.Ico.filter_le

theorem filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) :
    ((Ico n m).filterₓ fun x => x < n + 1) = [n] :=
  by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]
#align list.Ico.filter_lt_of_succ_bot List.Ico.filter_lt_of_succ_bot

@[simp]
theorem filter_le_of_bot {n m : ℕ} (hnm : n < m) : ((Ico n m).filterₓ fun x => x ≤ n) = [n] :=
  by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr' fun _ _ => lt_succ_iff.symm
#align list.Ico.filter_le_of_bot List.Ico.filter_le_of_bot

#print List.Ico.trichotomy /-
/-- For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b :=
  by
  by_cases h₁ : n < a
  · left; exact h₁
  · right
    by_cases h₂ : n ∈ Ico a b
    · right; exact h₂
    · left; simp only [Ico.mem, not_and, not_lt] at *; exact h₂ h₁
#align list.Ico.trichotomy List.Ico.trichotomy
-/

end Ico

end List

