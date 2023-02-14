/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma

! This file was ported from Lean 3 source module data.vector.mem
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Vector.Basic

/-!
# Theorems about membership of elements in vectors

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems for membership in a `v.to_list` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `inhabited`,
  and make more general statements about `head` and `tail`.
-/


namespace Vector

variable {α β : Type _} {n : ℕ} (a a' : α)

#print Vector.get_mem /-
@[simp]
theorem get_mem (i : Fin n) (v : Vector α n) : v.get? i ∈ v.toList :=
  by
  rw [nth_eq_nth_le]
  exact List.nthLe_mem _ _ _
#align vector.nth_mem Vector.get_mem
-/

#print Vector.mem_iff_get /-
theorem mem_iff_get (v : Vector α n) : a ∈ v.toList ↔ ∃ i, v.get? i = a := by
  simp only [List.mem_iff_nthLe, Fin.exists_iff, Vector.get_eq_get] <;>
    exact
      ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [to_list_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
        ⟨i, by rwa [to_list_length], h⟩⟩
#align vector.mem_iff_nth Vector.mem_iff_get
-/

#print Vector.not_mem_nil /-
theorem not_mem_nil : a ∉ (Vector.nil : Vector α 0).toList :=
  id
#align vector.not_mem_nil Vector.not_mem_nil
-/

#print Vector.not_mem_zero /-
theorem not_mem_zero (v : Vector α 0) : a ∉ v.toList :=
  (Vector.eq_nil v).symm ▸ not_mem_nil a
#align vector.not_mem_zero Vector.not_mem_zero
-/

#print Vector.mem_cons_iff /-
theorem mem_cons_iff (v : Vector α n) : a' ∈ (a ::ᵥ v).toList ↔ a' = a ∨ a' ∈ v.toList := by
  rw [Vector.toList_cons, List.mem_cons]
#align vector.mem_cons_iff Vector.mem_cons_iff
-/

#print Vector.mem_succ_iff /-
theorem mem_succ_iff (v : Vector α (n + 1)) : a ∈ v.toList ↔ a = v.headI ∨ a ∈ v.tail.toList :=
  by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]
#align vector.mem_succ_iff Vector.mem_succ_iff
-/

#print Vector.mem_cons_self /-
theorem mem_cons_self (v : Vector α n) : a ∈ (a ::ᵥ v).toList :=
  (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩
#align vector.mem_cons_self Vector.mem_cons_self
-/

#print Vector.head_mem /-
@[simp]
theorem head_mem (v : Vector α (n + 1)) : v.headI ∈ v.toList :=
  (Vector.mem_iff_get v.headI v).2 ⟨0, Vector.get_zero v⟩
#align vector.head_mem Vector.head_mem
-/

#print Vector.mem_cons_of_mem /-
theorem mem_cons_of_mem (v : Vector α n) (ha' : a' ∈ v.toList) : a' ∈ (a ::ᵥ v).toList :=
  (Vector.mem_cons_iff a a' v).2 (Or.inr ha')
#align vector.mem_cons_of_mem Vector.mem_cons_of_mem
-/

#print Vector.mem_of_mem_tail /-
theorem mem_of_mem_tail (v : Vector α n) (ha : a ∈ v.tail.toList) : a ∈ v.toList :=
  by
  induction' n with n hn
  · exact False.elim (Vector.not_mem_zero a v.tail ha)
  · exact (mem_succ_iff a v).2 (Or.inr ha)
#align vector.mem_of_mem_tail Vector.mem_of_mem_tail
-/

/- warning: vector.mem_map_iff -> Vector.mem_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {n : Nat} (b : β) (v : Vector.{u1} α n) (f : α -> β), Iff (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β) b (Vector.toList.{u2} β n (Vector.map.{u1, u2} α β n f v))) (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Vector.toList.{u1} α n v)) (Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {n : Nat} (b : β) (v : Vector.{u2} α n) (f : α -> β), Iff (Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) b (Vector.toList.{u1} β n (Vector.map.{u2, u1} α β n f v))) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (Vector.toList.{u2} α n v)) (Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align vector.mem_map_iff Vector.mem_map_iffₓ'. -/
theorem mem_map_iff (b : β) (v : Vector α n) (f : α → β) :
    b ∈ (v.map f).toList ↔ ∃ a : α, a ∈ v.toList ∧ f a = b := by
  rw [Vector.toList_map, List.mem_map']
#align vector.mem_map_iff Vector.mem_map_iff

/- warning: vector.not_mem_map_zero -> Vector.not_mem_map_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (b : β) (v : Vector.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f : α -> β), Not (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β) b (Vector.toList.{u2} β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Vector.map.{u1, u2} α β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) f v)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (b : β) (v : Vector.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f : α -> β), Not (Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) b (Vector.toList.{u1} β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Vector.map.{u2, u1} α β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) f v)))
Case conversion may be inaccurate. Consider using '#align vector.not_mem_map_zero Vector.not_mem_map_zeroₓ'. -/
theorem not_mem_map_zero (b : β) (v : Vector α 0) (f : α → β) : b ∉ (v.map f).toList := by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil b
#align vector.not_mem_map_zero Vector.not_mem_map_zero

/- warning: vector.mem_map_succ_iff -> Vector.mem_map_succ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {n : Nat} (b : β) (v : Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f : α -> β), Iff (Membership.Mem.{u2, u2} β (List.{u2} β) (List.hasMem.{u2} β) b (Vector.toList.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Vector.map.{u1, u2} α β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) f v))) (Or (Eq.{succ u2} β (f (Vector.head.{u1} α n v)) b) (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a (Vector.toList.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Vector.tail.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) v))) (Eq.{succ u2} β (f a) b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {n : Nat} (b : β) (v : Vector.{u2} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f : α -> β), Iff (Membership.mem.{u1, u1} β (List.{u1} β) (List.instMembershipList.{u1} β) b (Vector.toList.{u1} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Vector.map.{u2, u1} α β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) f v))) (Or (Eq.{succ u1} β (f (Vector.head.{u2} α n v)) b) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a (Vector.toList.{u2} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Vector.tail.{u2} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) v))) (Eq.{succ u1} β (f a) b))))
Case conversion may be inaccurate. Consider using '#align vector.mem_map_succ_iff Vector.mem_map_succ_iffₓ'. -/
theorem mem_map_succ_iff (b : β) (v : Vector α (n + 1)) (f : α → β) :
    b ∈ (v.map f).toList ↔ f v.headI = b ∨ ∃ a : α, a ∈ v.tail.toList ∧ f a = b := by
  rw [mem_succ_iff, head_map, tail_map, mem_map_iff, @eq_comm _ b]
#align vector.mem_map_succ_iff Vector.mem_map_succ_iff

end Vector

