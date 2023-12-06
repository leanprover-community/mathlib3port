/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import SetTheory.Cardinal.Basic
import Tactic.Ring

#align_import data.nat.count from "leanprover-community/mathlib"@"1ead22342e1a078bd44744ace999f85756555d35"

/-!
# Counting on ℕ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/


open Finset

namespace Nat

variable (p : ℕ → Prop)

section Count

variable [DecidablePred p]

#print Nat.count /-
/-- Count the number of naturals `k < n` satisfying `p k`. -/
def count (n : ℕ) : ℕ :=
  (List.range n).countP p
#align nat.count Nat.count
-/

#print Nat.count_zero /-
@[simp]
theorem count_zero : count p 0 = 0 := by rw [count, List.range_zero, List.countP]
#align nat.count_zero Nat.count_zero
-/

#print Nat.CountSet.fintype /-
/-- A fintype instance for the set relevant to `nat.count`. Locally an instance in locale `count` -/
def CountSet.fintype (n : ℕ) : Fintype { i // i < n ∧ p i } :=
  by
  apply Fintype.ofFinset ((Finset.range n).filterₓ p)
  intro x
  rw [mem_filter, mem_range]
  rfl
#align nat.count_set.fintype Nat.CountSet.fintype
-/

scoped[Count] attribute [instance] Nat.CountSet.fintype

#print Nat.count_eq_card_filter_range /-
theorem count_eq_card_filter_range (n : ℕ) : count p n = ((range n).filterₓ p).card := by
  rw [count, List.countP_eq_length_filter]; rfl
#align nat.count_eq_card_filter_range Nat.count_eq_card_filter_range
-/

#print Nat.count_eq_card_fintype /-
/-- `count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`. -/
theorem count_eq_card_fintype (n : ℕ) : count p n = Fintype.card { k : ℕ // k < n ∧ p k } := by
  rw [count_eq_card_filter_range, ← Fintype.card_ofFinset, ← count_set.fintype]; rfl
#align nat.count_eq_card_fintype Nat.count_eq_card_fintype
-/

#print Nat.count_succ /-
theorem count_succ (n : ℕ) : count p (n + 1) = count p n + if p n then 1 else 0 := by
  split_ifs <;> simp [count, List.range_succ, h]
#align nat.count_succ Nat.count_succ
-/

#print Nat.count_monotone /-
@[mono]
theorem count_monotone : Monotone (count p) :=
  monotone_nat_of_le_succ fun n => by by_cases h : p n <;> simp [count_succ, h]
#align nat.count_monotone Nat.count_monotone
-/

#print Nat.count_add /-
theorem count_add (a b : ℕ) : count p (a + b) = count p a + count (fun k => p (a + k)) b :=
  by
  have : Disjoint ((range a).filterₓ p) (((range b).map <| addLeftEmbedding a).filterₓ p) :=
    by
    apply disjoint_filter_filter
    rw [Finset.disjoint_left]
    simp_rw [mem_map, mem_range, addLeftEmbedding_apply]
    rintro x hx ⟨c, _, rfl⟩
    exact (self_le_add_right _ _).not_lt hx
  simp_rw [count_eq_card_filter_range, range_add, filter_union, card_disjoint_union this,
    filter_map, addLeftEmbedding, card_map]
  rfl
#align nat.count_add Nat.count_add
-/

#print Nat.count_add' /-
theorem count_add' (a b : ℕ) : count p (a + b) = count (fun k => p (k + b)) a + count p b := by
  rw [add_comm, count_add, add_comm]; simp_rw [add_comm b]
#align nat.count_add' Nat.count_add'
-/

#print Nat.count_one /-
theorem count_one : count p 1 = if p 0 then 1 else 0 := by simp [count_succ]
#align nat.count_one Nat.count_one
-/

#print Nat.count_succ' /-
theorem count_succ' (n : ℕ) :
    count p (n + 1) = count (fun k => p (k + 1)) n + if p 0 then 1 else 0 := by
  rw [count_add', count_one]
#align nat.count_succ' Nat.count_succ'
-/

variable {p}

#print Nat.count_lt_count_succ_iff /-
@[simp]
theorem count_lt_count_succ_iff {n : ℕ} : count p n < count p (n + 1) ↔ p n := by
  by_cases h : p n <;> simp [count_succ, h]
#align nat.count_lt_count_succ_iff Nat.count_lt_count_succ_iff
-/

#print Nat.count_succ_eq_succ_count_iff /-
theorem count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n := by
  by_cases h : p n <;> simp [h, count_succ]
#align nat.count_succ_eq_succ_count_iff Nat.count_succ_eq_succ_count_iff
-/

#print Nat.count_succ_eq_count_iff /-
theorem count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n := by
  by_cases h : p n <;> simp [h, count_succ]
#align nat.count_succ_eq_count_iff Nat.count_succ_eq_count_iff
-/

alias ⟨_, count_succ_eq_succ_count⟩ := count_succ_eq_succ_count_iff
#align nat.count_succ_eq_succ_count Nat.count_succ_eq_succ_count

alias ⟨_, count_succ_eq_count⟩ := count_succ_eq_count_iff
#align nat.count_succ_eq_count Nat.count_succ_eq_count

#print Nat.count_le_cardinal /-
theorem count_le_cardinal (n : ℕ) : (count p n : Cardinal) ≤ Cardinal.mk {k | p k} :=
  by
  rw [count_eq_card_fintype, ← Cardinal.mk_fintype]
  exact Cardinal.mk_subtype_mono fun x hx => hx.2
#align nat.count_le_cardinal Nat.count_le_cardinal
-/

#print Nat.lt_of_count_lt_count /-
theorem lt_of_count_lt_count {a b : ℕ} (h : count p a < count p b) : a < b :=
  (count_monotone p).reflect_lt h
#align nat.lt_of_count_lt_count Nat.lt_of_count_lt_count
-/

#print Nat.count_strict_mono /-
theorem count_strict_mono {m n : ℕ} (hm : p m) (hmn : m < n) : count p m < count p n :=
  (count_lt_count_succ_iff.2 hm).trans_le <| count_monotone _ (Nat.succ_le_iff.2 hmn)
#align nat.count_strict_mono Nat.count_strict_mono
-/

#print Nat.count_injective /-
theorem count_injective {m n : ℕ} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n :=
  by
  by_contra! h : m ≠ n
  wlog hmn : m < n
  · exact this hn hm HEq.symm h.symm (h.lt_or_lt.resolve_left hmn)
  · simpa [HEq] using count_strict_mono hm hmn
#align nat.count_injective Nat.count_injective
-/

#print Nat.count_le_card /-
theorem count_le_card (hp : (setOf p).Finite) (n : ℕ) : count p n ≤ hp.toFinset.card :=
  by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx => hp.mem_to_finset.2 (mem_filter.1 hx).2
#align nat.count_le_card Nat.count_le_card
-/

#print Nat.count_lt_card /-
theorem count_lt_card {n : ℕ} (hp : (setOf p).Finite) (hpn : p n) : count p n < hp.toFinset.card :=
  (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)
#align nat.count_lt_card Nat.count_lt_card
-/

variable {q : ℕ → Prop}

variable [DecidablePred q]

#print Nat.count_mono_left /-
theorem count_mono_left {n : ℕ} (hpq : ∀ k, p k → q k) : count p n ≤ count q n :=
  by
  simp only [count_eq_card_filter_range]
  exact card_le_of_subset ((range n).monotone_filter_right hpq)
#align nat.count_mono_left Nat.count_mono_left
-/

end Count

end Nat

