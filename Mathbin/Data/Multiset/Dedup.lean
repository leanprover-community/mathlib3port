/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.dedup
! leanprover-community/mathlib commit f2f413b9d4be3a02840d0663dace76e8fe3da053
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Nodup

/-!
# Erasing duplicates in a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

open List

variable {α β : Type _} [DecidableEq α]

/-! ### dedup -/


#print Multiset.dedup /-
/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun s t p => Quot.sound p.dedup
#align multiset.dedup Multiset.dedup
-/

#print Multiset.coe_dedup /-
@[simp]
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl
#align multiset.coe_dedup Multiset.coe_dedup
-/

#print Multiset.dedup_zero /-
@[simp]
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl
#align multiset.dedup_zero Multiset.dedup_zero
-/

#print Multiset.mem_dedup /-
@[simp]
theorem mem_dedup {a : α} {s : Multiset α} : a ∈ dedup s ↔ a ∈ s :=
  Quot.inductionOn s fun l => mem_dedup
#align multiset.mem_dedup Multiset.mem_dedup
-/

#print Multiset.dedup_cons_of_mem /-
@[simp]
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → dedup (a ::ₘ s) = dedup s :=
  Quot.inductionOn s fun l m => @congr_arg _ _ _ _ coe <| dedup_cons_of_mem m
#align multiset.dedup_cons_of_mem Multiset.dedup_cons_of_mem
-/

#print Multiset.dedup_cons_of_not_mem /-
@[simp]
theorem dedup_cons_of_not_mem {a : α} {s : Multiset α} : a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s :=
  Quot.inductionOn s fun l m => congr_arg coe <| dedup_cons_of_not_mem m
#align multiset.dedup_cons_of_not_mem Multiset.dedup_cons_of_not_mem
-/

/- warning: multiset.dedup_le -> Multiset.dedup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) s
Case conversion may be inaccurate. Consider using '#align multiset.dedup_le Multiset.dedup_leₓ'. -/
theorem dedup_le (s : Multiset α) : dedup s ≤ s :=
  Quot.inductionOn s fun l => (dedup_sublist _).Subperm
#align multiset.dedup_le Multiset.dedup_le

#print Multiset.dedup_subset /-
theorem dedup_subset (s : Multiset α) : dedup s ⊆ s :=
  subset_of_le <| dedup_le _
#align multiset.dedup_subset Multiset.dedup_subset
-/

#print Multiset.subset_dedup /-
theorem subset_dedup (s : Multiset α) : s ⊆ dedup s := fun a => mem_dedup.2
#align multiset.subset_dedup Multiset.subset_dedup
-/

#print Multiset.dedup_subset' /-
@[simp]
theorem dedup_subset' {s t : Multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩
#align multiset.dedup_subset' Multiset.dedup_subset'
-/

#print Multiset.subset_dedup' /-
@[simp]
theorem subset_dedup' {s t : Multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩
#align multiset.subset_dedup' Multiset.subset_dedup'
-/

#print Multiset.nodup_dedup /-
@[simp]
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.inductionOn s nodup_dedup
#align multiset.nodup_dedup Multiset.nodup_dedup
-/

#print Multiset.dedup_eq_self /-
theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, Quot.inductionOn s fun l h => congr_arg coe h.dedup⟩
#align multiset.dedup_eq_self Multiset.dedup_eq_self
-/

alias dedup_eq_self ↔ _ nodup.dedup
#align multiset.nodup.dedup Multiset.Nodup.dedup

#print Multiset.count_dedup /-
theorem count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a ∈ m then 1 else 0 :=
  Quot.inductionOn m fun l => count_dedup _ _
#align multiset.count_dedup Multiset.count_dedup
-/

#print Multiset.dedup_idempotent /-
@[simp]
theorem dedup_idempotent {m : Multiset α} : m.dedup.dedup = m.dedup :=
  Quot.inductionOn m fun l => @congr_arg _ _ _ _ coe dedup_idempotent
#align multiset.dedup_idempotent Multiset.dedup_idempotent
-/

#print Multiset.dedup_bind_dedup /-
@[simp]
theorem dedup_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
    (m.dedup.bind f).dedup = (m.bind f).dedup := by ext x;
  simp_rw [count_dedup, mem_bind, mem_dedup]
#align multiset.dedup_bind_dedup Multiset.dedup_bind_dedup
-/

#print Multiset.dedup_eq_zero /-
theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩
#align multiset.dedup_eq_zero Multiset.dedup_eq_zero
-/

#print Multiset.dedup_singleton /-
@[simp]
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup
#align multiset.dedup_singleton Multiset.dedup_singleton
-/

/- warning: multiset.le_dedup -> Multiset.le_dedup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) (Multiset.Nodup.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (And (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) (Multiset.Nodup.{u1} α s))
Case conversion may be inaccurate. Consider using '#align multiset.le_dedup Multiset.le_dedupₓ'. -/
theorem le_dedup {s t : Multiset α} : s ≤ dedup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩, fun ⟨l, d⟩ =>
    (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_dedup _)⟩
#align multiset.le_dedup Multiset.le_dedup

/- warning: multiset.le_dedup_self -> Multiset.le_dedup_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Multiset.Nodup.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Multiset.Nodup.{u1} α s)
Case conversion may be inaccurate. Consider using '#align multiset.le_dedup_self Multiset.le_dedup_selfₓ'. -/
theorem le_dedup_self {s : Multiset α} : s ≤ dedup s ↔ Nodup s := by
  rw [le_dedup, and_iff_right le_rfl]
#align multiset.le_dedup_self Multiset.le_dedup_self

#print Multiset.dedup_ext /-
theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by simp [nodup.ext]
#align multiset.dedup_ext Multiset.dedup_ext
-/

#print Multiset.dedup_map_dedup_eq /-
theorem dedup_map_dedup_eq [DecidableEq β] (f : α → β) (s : Multiset α) :
    dedup (map f (dedup s)) = dedup (map f s) := by simp [dedup_ext]
#align multiset.dedup_map_dedup_eq Multiset.dedup_map_dedup_eq
-/

/- warning: multiset.dedup_nsmul -> Multiset.dedup_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Multiset.{u1} α) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Multiset.{u1} α) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
Case conversion may be inaccurate. Consider using '#align multiset.dedup_nsmul Multiset.dedup_nsmulₓ'. -/
@[simp]
theorem dedup_nsmul {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : (n • s).dedup = s.dedup :=
  by
  ext a
  by_cases h : a ∈ s <;> simp [h, h0]
#align multiset.dedup_nsmul Multiset.dedup_nsmul

/- warning: multiset.nodup.le_dedup_iff_le -> Multiset.Nodup.le_dedup_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (Multiset.Nodup.{u1} α s) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (Multiset.Nodup.{u1} α s) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (Multiset.dedup.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t))
Case conversion may be inaccurate. Consider using '#align multiset.nodup.le_dedup_iff_le Multiset.Nodup.le_dedup_iff_leₓ'. -/
theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.dedup ↔ s ≤ t := by
  simp [le_dedup, hno]
#align multiset.nodup.le_dedup_iff_le Multiset.Nodup.le_dedup_iff_le

end Multiset

/- warning: multiset.nodup.le_nsmul_iff_le -> Multiset.Nodup.le_nsmul_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {n : Nat}, (Multiset.Nodup.{u1} α s) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toHasLe.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Multiset.{u1} α} {t : Multiset.{u1} α} {n : Nat}, (Multiset.Nodup.{u1} α s) -> (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n t)) (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t))
Case conversion may be inaccurate. Consider using '#align multiset.nodup.le_nsmul_iff_le Multiset.Nodup.le_nsmul_iff_leₓ'. -/
theorem Multiset.Nodup.le_nsmul_iff_le {α : Type _} {s t : Multiset α} {n : ℕ} (h : s.Nodup)
    (hn : n ≠ 0) : s ≤ n • t ↔ s ≤ t := by
  classical
    rw [← h.le_dedup_iff_le, Iff.comm, ← h.le_dedup_iff_le]
    simp [hn]
#align multiset.nodup.le_nsmul_iff_le Multiset.Nodup.le_nsmul_iff_le

