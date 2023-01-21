/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.range
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Basic
import Mathbin.Data.List.Range

/-! # `multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


open List Nat

namespace Multiset

#print Multiset.range /-
-- range
/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : Multiset ℕ :=
  range n
#align multiset.range Multiset.range
-/

#print Multiset.coe_range /-
theorem coe_range (n : ℕ) : ↑(List.range n) = range n :=
  rfl
#align multiset.coe_range Multiset.coe_range
-/

#print Multiset.range_zero /-
@[simp]
theorem range_zero : range 0 = 0 :=
  rfl
#align multiset.range_zero Multiset.range_zero
-/

#print Multiset.range_succ /-
@[simp]
theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n := by
  rw [range, range_succ, ← coe_add, add_comm] <;> rfl
#align multiset.range_succ Multiset.range_succ
-/

/- warning: multiset.card_range -> Multiset.card_range is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Nat (coeFn.{1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toCancelAddMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toCancelAddMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{0} Nat) -> Nat) (AddMonoidHom.hasCoeToFun.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toCancelAddMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.orderedCancelAddCommMonoid.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{0} Nat) (Multiset.range n)) n
but is expected to have type
  forall (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat) => Nat) (Multiset.range n)) (FunLike.coe.{1, 1, 1} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) (fun (_x : Multiset.{0} Nat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{0} Nat) => Nat) _x) (AddHomClass.toFunLike.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) Nat (AddZeroClass.toAdd.{0} (Multiset.{0} Nat) (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{0, 0, 0} (AddMonoidHom.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{0, 0} (Multiset.{0} Nat) Nat (AddMonoid.toAddZeroClass.{0} (Multiset.{0} Nat) (AddRightCancelMonoid.toAddMonoid.{0} (Multiset.{0} Nat) (AddCancelMonoid.toAddRightCancelMonoid.{0} (Multiset.{0} Nat) (AddCancelCommMonoid.toAddCancelMonoid.{0} (Multiset.{0} Nat) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} (Multiset.{0} Nat) (Multiset.instOrderedCancelAddCommMonoidMultiset.{0} Nat)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{0} Nat) (Multiset.range n)) n
Case conversion may be inaccurate. Consider using '#align multiset.card_range Multiset.card_rangeₓ'. -/
@[simp]
theorem card_range (n : ℕ) : card (range n) = n :=
  length_range _
#align multiset.card_range Multiset.card_range

#print Multiset.range_subset /-
theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  range_subset
#align multiset.range_subset Multiset.range_subset
-/

#print Multiset.mem_range /-
@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
  mem_range
#align multiset.mem_range Multiset.mem_range
-/

#print Multiset.not_mem_range_self /-
@[simp]
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  not_mem_range_self
#align multiset.not_mem_range_self Multiset.not_mem_range_self
-/

#print Multiset.self_mem_range_succ /-
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  List.self_mem_range_succ n
#align multiset.self_mem_range_succ Multiset.self_mem_range_succ
-/

#print Multiset.range_add /-
theorem range_add (a b : ℕ) : range (a + b) = range a + (range b).map fun x => a + x :=
  congr_arg coe (List.range_add _ _)
#align multiset.range_add Multiset.range_add
-/

#print Multiset.range_disjoint_map_add /-
theorem range_disjoint_map_add (a : ℕ) (m : Multiset ℕ) :
    (range a).Disjoint (m.map fun x => a + x) :=
  by
  intro x hxa hxb
  rw [range, mem_coe, List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (self_le_add_right _ _).not_lt hxa
#align multiset.range_disjoint_map_add Multiset.range_disjoint_map_add
-/

/- warning: multiset.range_add_eq_union -> Multiset.range_add_eq_union is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Eq.{1} (Multiset.{0} Nat) (Multiset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Union.union.{0} (Multiset.{0} Nat) (Multiset.hasUnion.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (Multiset.range a) (Multiset.map.{0, 0} Nat Nat (fun (x : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a x) (Multiset.range b)))
but is expected to have type
  forall (a : Nat) (b : Nat), Eq.{1} (Multiset.{0} Nat) (Multiset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (Union.union.{0} (Multiset.{0} Nat) (Multiset.instUnionMultiset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (Multiset.range a) (Multiset.map.{0, 0} Nat Nat (fun (x : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a x) (Multiset.range b)))
Case conversion may be inaccurate. Consider using '#align multiset.range_add_eq_union Multiset.range_add_eq_unionₓ'. -/
theorem range_add_eq_union (a b : ℕ) : range (a + b) = range a ∪ (range b).map fun x => a + x :=
  by
  rw [range_add, add_eq_union_iff_disjoint]
  apply range_disjoint_map_add
#align multiset.range_add_eq_union Multiset.range_add_eq_union

end Multiset

