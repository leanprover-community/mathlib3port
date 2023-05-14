/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.finset.pi
! leanprover-community/mathlib commit 4c586d291f189eecb9d00581aeb3dd998ac34442
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Image
import Mathbin.Data.Multiset.Pi

/-!
# The cartesian product of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Finset

open Multiset

/-! ### pi -/


section Pi

variable {α : Type _}

#print Finset.Pi.empty /-
/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
def Pi.empty (β : α → Sort _) (a : α) (h : a ∈ (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h
#align finset.pi.empty Finset.Pi.empty
-/

variable {β : α → Type _} {δ : α → Sort _} [DecidableEq α]

/- warning: finset.pi -> Finset.pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), (forall (a : α), Finset.{u2} (β a)) -> (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α), (forall (a : α), Finset.{u1} (β a)) -> (Finset.{max u1 u2} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (β a)))
Case conversion may be inaccurate. Consider using '#align finset.pi Finset.piₓ'. -/
/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.Nodup.pi fun a _ => (t a).Nodup⟩
#align finset.pi Finset.pi

/- warning: finset.pi_val -> Finset.pi_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : forall (a : α), Finset.{u2} (β a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a))) (Finset.val.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a)) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (Finset.val.{u1} α s) (fun (a : α) => Finset.val.{u2} (β a) (t a)))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : forall (a : α), Finset.{u2} (β a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a))) (Finset.val.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a)) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (Finset.val.{u1} α s) (fun (a : α) => Finset.val.{u2} (β a) (t a)))
Case conversion may be inaccurate. Consider using '#align finset.pi_val Finset.pi_valₓ'. -/
@[simp]
theorem pi_val (s : Finset α) (t : ∀ a, Finset (β a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl
#align finset.pi_val Finset.pi_val

/- warning: finset.mem_pi -> Finset.mem_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u2} (β a)} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a)) (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a))) (Finset.hasMem.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a))) f (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (forall (a : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s), Membership.Mem.{u2, u2} (β a) (Finset.{u2} (β a)) (Finset.hasMem.{u2} (β a)) (f a h) (t a))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u2} (β a)} {f : forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a)}, Iff (Membership.mem.{max u2 u1, max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a)) (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a))) (Finset.instMembershipFinset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a))) f (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (forall (a : α) (h : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s), Membership.mem.{u2, u2} (β a) (Finset.{u2} (β a)) (Finset.instMembershipFinset.{u2} (β a)) (f a h) (t a))
Case conversion may be inaccurate. Consider using '#align finset.mem_pi Finset.mem_piₓ'. -/
@[simp]
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (β a)} {f : ∀ a ∈ s, β a} :
    f ∈ s.pi t ↔ ∀ (a) (h : a ∈ s), f a h ∈ t a :=
  mem_pi _ _ _
#align finset.mem_pi Finset.mem_pi

/- warning: finset.pi.cons -> Finset.Pi.cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α), (δ a) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) -> (forall (a' : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a'))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α), (δ a) -> (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) -> (forall (a' : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a'))
Case conversion may be inaccurate. Consider using '#align finset.pi.cons Finset.Pi.consₓ'. -/
/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def Pi.cons (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)
#align finset.pi.cons Finset.Pi.cons

/- warning: finset.pi.cons_same -> Finset.Pi.cons_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α) (b : δ a) (f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)), Eq.{u2} (δ a) (Finset.Pi.cons.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b f a h) b
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α) (b : δ a) (f : forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a)) (h : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)), Eq.{u2} (δ a) (Finset.Pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b f a h) b
Case conversion may be inaccurate. Consider using '#align finset.pi.cons_same Finset.Pi.cons_sameₓ'. -/
@[simp]
theorem Pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (h : a ∈ insert a s) :
    Pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _
#align finset.pi.cons_same Finset.Pi.cons_same

/- warning: finset.pi.cons_ne -> Finset.Pi.cons_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)} {h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)} (ha : Ne.{succ u1} α a a'), Eq.{u2} (δ a') (Finset.Pi.cons.{u1, u2} α (fun {a : α} => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b f a' h) (f a' (Or.resolve_left (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' s) (Iff.mp (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Or (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' s)) (Finset.mem_insert.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a' a) h) (Ne.symm.{succ u1} α a a' ha)))
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a)} {h : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)} (ha : Ne.{succ u1} α a a'), Eq.{u2} (δ a') (Finset.Pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b f a' h) (f a' (Or.resolve_left (Eq.{succ u1} α a' a) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a' s) (Iff.mp (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Or (Eq.{succ u1} α a' a) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a' s)) (Finset.mem_insert.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a' a) h) (Ne.symm.{succ u1} α a a' ha)))
Case conversion may be inaccurate. Consider using '#align finset.pi.cons_ne Finset.Pi.cons_neₓ'. -/
theorem Pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : ∀ a, a ∈ s → δ a} {h : a' ∈ insert a s}
    (ha : a ≠ a') : Pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ _
#align finset.pi.cons_ne Finset.Pi.cons_ne

/- warning: finset.pi_cons_injective -> Finset.pi_cons_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {b : δ a} {s : Finset.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Function.Injective.{imax (succ u1) u2, imax (succ u1) u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (forall (a' : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a')) (Finset.Pi.cons.{u1, u2} α (fun {a : α} => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b))
but is expected to have type
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {b : δ a} {s : Finset.{u1} α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Function.Injective.{imax (succ u1) u2, imax (succ u1) u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a)) (forall (a' : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a')) (Finset.Pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b))
Case conversion may be inaccurate. Consider using '#align finset.pi_cons_injective Finset.pi_cons_injectiveₓ'. -/
theorem pi_cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun e₁ e₂ eq =>
  @Multiset.pi_cons_injective α _ δ a b s.1 hs _ _ <|
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using h) :=
          by rw [Eq]
        this
#align finset.pi_cons_injective Finset.pi_cons_injective

/- warning: finset.pi_empty -> Finset.pi_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {t : forall (a : α), Finset.{u2} (β a)}, Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (β a))) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) t) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (β a)) (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (β a))) (Finset.hasSingleton.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) -> (β a))) (Finset.Pi.empty.{u1, succ u2} α β))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {t : forall (a : α), Finset.{u2} (β a)}, Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (β a))) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) t) (Singleton.singleton.{max u2 u1, max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (β a)) (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (β a))) (Finset.instSingletonFinset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) -> (β a))) (Finset.Pi.empty.{u1, succ u2} α β))
Case conversion may be inaccurate. Consider using '#align finset.pi_empty Finset.pi_emptyₓ'. -/
@[simp]
theorem pi_empty {t : ∀ a : α, Finset (β a)} : pi (∅ : Finset α) t = singleton (Pi.empty β) :=
  rfl
#align finset.pi_empty Finset.pi_empty

/- warning: finset.pi_insert -> Finset.pi_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : forall (a : α), DecidableEq.{succ u2} (β a)] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u2} (β a)} {a : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1))) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) t) (Finset.biUnion.{u2, max u1 u2} (β a) (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (fun (a_1 : forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (b : forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) => Finset.decidableEqPiFinset.{u1, u2} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (fun (a : α) => β a) (fun (a : α) (a_1 : β a) (b : β a) => _inst_2 a a_1 b) a_1 b) (t a) (fun (b : β a) => Finset.image.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a)) (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (fun (a_1 : forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (b : forall (a_1 : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) => Finset.decidableEqPiFinset.{u1, u2} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (fun (a : α) => β a) (fun (a : α) (a_1 : β a) (b : β a) => _inst_2 a a_1 b) a_1 b) (Finset.Pi.cons.{u1, succ u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s a b) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t))))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : forall (a : α), DecidableEq.{succ u2} (β a)] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u2} (β a)} {a : α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1))) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) t) (Finset.biUnion.{u2, max u2 u1} (β a) (forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (fun (a_1 : forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (b : forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) => Finset.decidableEqPiFinset.{u1, u2} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (fun (a : α) => β a) (fun (a : α) => (fun (a : α) (a_1 : β a) (b : β a) => _inst_2 a a_1 b) a) a_1 b) (t a) (fun (b : β a) => Finset.image.{max u2 u1, max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a)) (forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (fun (a_1 : forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) (b : forall (a_1 : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (β a_1)) => Finset.decidableEqPiFinset.{u1, u2} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (fun (a : α) => β a) (fun (a : α) => (fun (a : α) (a_1 : β a) (b : β a) => _inst_2 a a_1 b) a) a_1 b) (Finset.Pi.cons.{succ u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) s a b) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t))))
Case conversion may be inaccurate. Consider using '#align finset.pi_insert Finset.pi_insertₓ'. -/
@[simp]
theorem pi_insert [∀ a, DecidableEq (β a)] {s : Finset α} {t : ∀ a : α, Finset (β a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).biUnion fun b => (pi s t).image (Pi.cons s a b) :=
  by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine'
    (fun s' (h : s' = a ::ₘ s.1) =>
        (_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
                dedup <|
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a' h' =>
                    Multiset.Pi.cons s.1 a b f a' (h ▸ h'))))
      _ (insert_val_of_not_mem ha)
  subst s'; rw [pi_cons]
  congr ; funext b
  refine' ((pi s t).Nodup.map _).dedup.symm
  exact Multiset.pi_cons_injective ha
#align finset.pi_insert Finset.pi_insert

/- warning: finset.pi_singletons -> Finset.pi_singletons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : Type.{u2}} (s : Finset.{u1} α) (f : α -> β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (Finset.pi.{u1, u2} α (fun (a : α) => β) (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (f a))) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β) (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (Finset.hasSingleton.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (fun (a : α) (_x : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : Type.{u2}} (s : Finset.{u1} α) (f : α -> β), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (Finset.pi.{u2, u1} α (fun (a : α) => β) (fun (a : α) (b : α) => _inst_1 a b) s (fun (a : α) => Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.instSingletonFinset.{u2} β) (f a))) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β) (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (Finset.instSingletonFinset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (fun (a : α) (_x : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) => f a))
Case conversion may be inaccurate. Consider using '#align finset.pi_singletons Finset.pi_singletonsₓ'. -/
theorem pi_singletons {β : Type _} (s : Finset α) (f : α → β) :
    (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a} :=
  by
  rw [eq_singleton_iff_unique_mem]
  constructor
  · simp
  intro a ha
  ext (i hi)
  rw [mem_pi] at ha
  simpa using ha i hi
#align finset.pi_singletons Finset.pi_singletons

/- warning: finset.pi_const_singleton -> Finset.pi_const_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : Type.{u2}} (s : Finset.{u1} α) (i : β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (Finset.pi.{u1, u2} α (fun (_x : α) => β) (fun (a : α) (b : α) => _inst_1 a b) s (fun (_x : α) => Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) i)) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β) (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (Finset.hasSingleton.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> β)) (fun (_x : α) (_x : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) _x s) => i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : Type.{u2}} (s : Finset.{u1} α) (i : β), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (Finset.pi.{u2, u1} α (fun (_x : α) => β) (fun (a : α) (b : α) => _inst_1 a b) s (fun (_x : α) => Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.instSingletonFinset.{u2} β) i)) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β) (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (Finset.instSingletonFinset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> β)) (fun (_x : α) (_x : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) _x s) => i))
Case conversion may be inaccurate. Consider using '#align finset.pi_const_singleton Finset.pi_const_singletonₓ'. -/
theorem pi_const_singleton {β : Type _} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i
#align finset.pi_const_singleton Finset.pi_const_singleton

/- warning: finset.pi_subset -> Finset.pi_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (β a)) (t₂ : forall (a : α), Finset.{u2} (β a)), (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u2} (Finset.{u2} (β a)) (Finset.hasSubset.{u2} (β a)) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a))) (Finset.hasSubset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (β a))) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (β a)) (t₂ : forall (a : α), Finset.{u2} (β a)), (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (HasSubset.Subset.{u2} (Finset.{u2} (β a)) (Finset.instHasSubsetFinset.{u2} (β a)) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a))) (Finset.instHasSubsetFinset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (β a))) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.pi_subset Finset.pi_subsetₓ'. -/
theorem pi_subset {s : Finset α} (t₁ t₂ : ∀ a, Finset (β a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
    s.pi t₁ ⊆ s.pi t₂ := fun g hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)
#align finset.pi_subset Finset.pi_subset

/- warning: finset.pi_disjoint_of_disjoint -> Finset.pi_disjoint_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.orderBot.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.partialOrder.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.orderBot.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u1 u2} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.partialOrder.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.pi_disjoint_of_disjoint Finset.pi_disjoint_of_disjointₓ'. -/
theorem pi_disjoint_of_disjoint {δ : α → Type _} {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (ha : a ∈ s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha) <|
      congr_fun (congr_fun eq₁₂ a) ha
#align finset.pi_disjoint_of_disjoint Finset.pi_disjoint_of_disjoint

end Pi

end Finset

