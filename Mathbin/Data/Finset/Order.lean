/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau

! This file was ported from Lean 3 source module data.finset.order
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Basic

/-!
# Finsets of ordered types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w

variable {α : Type u}

/- warning: directed.finset_le -> Directed.finset_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsTrans.{u1} α r] {ι : Type.{u2}} [hι : Nonempty.{succ u2} ι] {f : ι -> α}, (Directed.{u1, succ u2} α ι r f) -> (forall (s : Finset.{u2} ι), Exists.{succ u2} ι (fun (z : ι) => forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (r (f i) (f z))))
but is expected to have type
  forall {α : Type.{u2}} {r : α -> α -> Prop} [_inst_1 : IsTrans.{u2} α r] {ι : Type.{u1}} [hι : Nonempty.{succ u1} ι] {f : ι -> α}, (Directed.{u2, succ u1} α ι r f) -> (forall (s : Finset.{u1} ι), Exists.{succ u1} ι (fun (z : ι) => forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (r (f i) (f z))))
Case conversion may be inaccurate. Consider using '#align directed.finset_le Directed.finset_leₓ'. -/
theorem Directed.finset_le {r : α → α → Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι → α}
    (D : Directed r f) (s : Finset ι) : ∃ z, ∀ i ∈ s, r (f i) (f z) :=
  show ∃ z, ∀ i ∈ s.1, r (f i) (f z) from
    Multiset.induction_on s.1
      (let ⟨z⟩ := hι
      ⟨z, fun _ => False.elim⟩)
      fun i s ⟨j, H⟩ =>
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun a h =>
        Or.cases_on (Multiset.mem_cons.1 h) (fun h => h.symm ▸ h₁) fun h => trans (H _ h) h₂⟩
#align directed.finset_le Directed.finset_le

#print Finset.exists_le /-
theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] (s : Finset α) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finset_le _
#align finset.exists_le Finset.exists_le
-/

