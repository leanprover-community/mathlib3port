/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.fold
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Dedup
import Mathbin.Data.List.MinMax

/-!
# The fold operation for a commutative associative operation over a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

variable {α β : Type _}

/-! ### fold -/


section Fold

variable (op : α → α → α) [hc : IsCommutative α op] [ha : IsAssociative α op]

-- mathport name: op
local notation a " * " b => op a b

include hc ha

#print Multiset.fold /-
/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → Multiset α → α :=
  foldr op (left_comm _ hc.comm ha.and_assoc)
#align multiset.fold Multiset.fold
-/

#print Multiset.fold_eq_foldr /-
theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op (left_comm _ hc.comm ha.and_assoc) b s :=
  rfl
#align multiset.fold_eq_foldr Multiset.fold_eq_foldr
-/

#print Multiset.coe_fold_r /-
@[simp]
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl
#align multiset.coe_fold_r Multiset.coe_fold_r
-/

#print Multiset.coe_fold_l /-
theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op _ b l).trans <| by simp [hc.comm]
#align multiset.coe_fold_l Multiset.coe_fold_l
-/

#print Multiset.fold_eq_foldl /-
theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op (right_comm _ hc.comm ha.and_assoc) b s :=
  Quot.inductionOn s fun l => coe_fold_l _ _ _
#align multiset.fold_eq_foldl Multiset.fold_eq_foldl
-/

#print Multiset.fold_zero /-
@[simp]
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl
#align multiset.fold_zero Multiset.fold_zero
-/

#print Multiset.fold_cons_left /-
@[simp]
theorem fold_cons_left : ∀ (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b :=
  foldr_cons _ _
#align multiset.fold_cons_left Multiset.fold_cons_left
-/

#print Multiset.fold_cons_right /-
theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b * a := by
  simp [hc.comm]
#align multiset.fold_cons_right Multiset.fold_cons_right
-/

#print Multiset.fold_cons'_right /-
theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) := by
  rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]
#align multiset.fold_cons'_right Multiset.fold_cons'_right
-/

#print Multiset.fold_cons'_left /-
theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) := by
  rw [fold_cons'_right, hc.comm]
#align multiset.fold_cons'_left Multiset.fold_cons'_left
-/

#print Multiset.fold_add /-
theorem fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) :
    (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
  Multiset.induction_on s₂ (by rw [add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (by simp (config := { contextual := true }) <;> cc)
#align multiset.fold_add Multiset.fold_add
-/

#print Multiset.fold_bind /-
theorem fold_bind {ι : Type _} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) = (s.map fun i => (t i).fold op (b i)).fold op b₀ :=
  by
  induction' s using Multiset.induction_on with a ha ih
  · rw [zero_bind, map_zero, map_zero, fold_zero]
  · rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]
#align multiset.fold_bind Multiset.fold_bind
-/

#print Multiset.fold_singleton /-
theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b :=
  foldr_singleton _ _ _ _
#align multiset.fold_singleton Multiset.fold_singleton
-/

#print Multiset.fold_distrib /-
theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : Multiset β) :
    (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }) <;> cc)
#align multiset.fold_distrib Multiset.fold_distrib
-/

#print Multiset.fold_hom /-
theorem fold_hom {op' : β → β → β} [IsCommutative β op'] [IsAssociative β op'] {m : α → β}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp (config := { contextual := true }) [hm])
#align multiset.fold_hom Multiset.fold_hom
-/

#print Multiset.fold_union_inter /-
theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
    ((s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂ := by
  rw [← fold_add op, union_add_inter, fold_add op]
#align multiset.fold_union_inter Multiset.fold_union_inter
-/

#print Multiset.fold_dedup_idem /-
@[simp]
theorem fold_dedup_idem [DecidableEq α] [hi : IsIdempotent α op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  Multiset.induction_on s (by simp) fun a s IH =>
    by
    by_cases a ∈ s <;> simp [IH, h]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent]
#align multiset.fold_dedup_idem Multiset.fold_dedup_idem
-/

end Fold

section Order

/- warning: multiset.max_le_of_forall_le -> Multiset.max_le_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedAddMonoid.{u1} α] (l : Multiset.{u1} α) (n : α), (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) x n)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) (Multiset.fold.{u1} α (LinearOrder.max.{u1} α (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{u1} α _inst_1)) (sup_isCommutative.{u1} α (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{u1} α _inst_1)) (sup_isAssociative.{u1} α (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{u1} α _inst_1)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toHasBot.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))) l) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedAddMonoid.{u1} α] (l : Multiset.{u1} α) (n : α), (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) x n)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))))) (Multiset.fold.{u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{u1} α _inst_1))) (instIsCommutativeMaxToMax.{u1} α (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{u1} α _inst_1)) (instIsAssociativeMaxToMax.{u1} α (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{u1} α _inst_1)) (Bot.bot.{u1} α (CanonicallyOrderedAddMonoid.toBot.{u1} α (CanonicallyLinearOrderedAddMonoid.toCanonicallyOrderedAddMonoid.{u1} α _inst_1))) l) n)
Case conversion may be inaccurate. Consider using '#align multiset.max_le_of_forall_le Multiset.max_le_of_forall_leₓ'. -/
theorem max_le_of_forall_le {α : Type _} [CanonicallyLinearOrderedAddMonoid α] (l : Multiset α)
    (n : α) (h : ∀ x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n :=
  by
  induction l using Quotient.inductionOn
  simpa using List.max_le_of_forall_le _ _ h
#align multiset.max_le_of_forall_le Multiset.max_le_of_forall_le

/- warning: multiset.max_nat_le_of_forall_le -> Multiset.max_nat_le_of_forall_le is a dubious translation:
lean 3 declaration is
  forall (l : Multiset.{0} Nat) (n : Nat), (forall (x : Nat), (Membership.Mem.{0, 0} Nat (Multiset.{0} Nat) (Multiset.hasMem.{0} Nat) x l) -> (LE.le.{0} Nat Nat.hasLe x n)) -> (LE.le.{0} Nat Nat.hasLe (Multiset.fold.{0} Nat (LinearOrder.max.{0} Nat Nat.linearOrder) (sup_isCommutative.{0} Nat (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid)) (sup_isAssociative.{0} Nat (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) l) n)
but is expected to have type
  forall (l : Multiset.{0} Nat) (n : Nat), (forall (x : Nat), (Membership.mem.{0, 0} Nat (Multiset.{0} Nat) (Multiset.instMembershipMultiset.{0} Nat) x l) -> (LE.le.{0} Nat instLENat x n)) -> (LE.le.{0} Nat instLENat (Multiset.fold.{0} Nat (Max.max.{0} Nat (LinearOrder.toMax.{0} Nat Nat.linearOrder)) (instIsCommutativeMaxToMax.{0} Nat Nat.linearOrder) (instIsAssociativeMaxToMax.{0} Nat Nat.linearOrder) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) l) n)
Case conversion may be inaccurate. Consider using '#align multiset.max_nat_le_of_forall_le Multiset.max_nat_le_of_forall_leₓ'. -/
theorem max_nat_le_of_forall_le (l : Multiset ℕ) (n : ℕ) (h : ∀ x ∈ l, x ≤ n) : l.fold max 0 ≤ n :=
  max_le_of_forall_le l n h
#align multiset.max_nat_le_of_forall_le Multiset.max_nat_le_of_forall_le

end Order

open Nat

/- warning: multiset.le_smul_dedup -> Multiset.le_smul_dedup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Exists.{1} Nat (fun (n : Nat) => LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Exists.{1} Nat (fun (n : Nat) => LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)))
Case conversion may be inaccurate. Consider using '#align multiset.le_smul_dedup Multiset.le_smul_dedupₓ'. -/
theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s :=
  ⟨(s.map fun a => count a s).fold max 0,
    le_iff_count.2 fun a => by
      rw [count_nsmul]; by_cases a ∈ s
      · refine' le_trans _ (Nat.mul_le_mul_left _ <| count_pos.2 <| mem_dedup.2 h)
        have : count a s ≤ fold max 0 (map (fun a => count a s) (a ::ₘ erase s a)) <;>
          [simp [le_max_left], simpa [cons_erase h] ]
      · simp [count_eq_zero.2 h, Nat.zero_le]⟩
#align multiset.le_smul_dedup Multiset.le_smul_dedup

end Multiset

