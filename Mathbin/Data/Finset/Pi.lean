/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.finset.pi
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
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

variable {δ : α → Type _} [DecidableEq α]

#print Finset.pi /-
/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi (s : Finset α) (t : ∀ a, Finset (δ a)) : Finset (∀ a ∈ s, δ a) :=
  ⟨s.1.pi fun a => (t a).1, s.Nodup.pi fun a _ => (t a).Nodup⟩
#align finset.pi Finset.pi
-/

/- warning: finset.pi_val -> Finset.pi_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : forall (a : α), Finset.{u2} (δ a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.val.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) (Finset.val.{u1} α s) (fun (a : α) => Finset.val.{u2} (δ a) (t a)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : forall (a : α), Finset.{u1} (δ a)), Eq.{max (succ u2) (succ u1)} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a))) (Finset.val.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) (Finset.val.{u2} α s) (fun (a : α) => Finset.val.{u1} (δ a) (t a)))
Case conversion may be inaccurate. Consider using '#align finset.pi_val Finset.pi_valₓ'. -/
@[simp]
theorem pi_val (s : Finset α) (t : ∀ a, Finset (δ a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl
#align finset.pi_val Finset.pi_val

/- warning: finset.mem_pi -> Finset.mem_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : forall (a : α), Finset.{u2} (δ a)} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.hasMem.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) f (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (forall (a : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s), Membership.Mem.{u2, u2} (δ a) (Finset.{u2} (δ a)) (Finset.hasMem.{u2} (δ a)) (f a h) (t a))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {t : forall (a : α), Finset.{u1} (δ a)} {f : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)}, Iff (Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a))) (Finset.instMembershipFinset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a))) f (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (forall (a : α) (h : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s), Membership.mem.{u1, u1} (δ a) (Finset.{u1} (δ a)) (Finset.instMembershipFinset.{u1} (δ a)) (f a h) (t a))
Case conversion may be inaccurate. Consider using '#align finset.mem_pi Finset.mem_piₓ'. -/
@[simp]
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (δ a)} {f : ∀ a ∈ s, δ a} :
    f ∈ s.pi t ↔ ∀ (a) (h : a ∈ s), f a h ∈ t a :=
  mem_pi _ _ _
#align finset.mem_pi Finset.mem_pi

#print Finset.pi.cons /-
/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def pi.cons (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)
#align finset.pi.cons Finset.pi.cons
-/

/- warning: finset.pi.cons_same -> Finset.pi.cons_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α) (b : δ a) (f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)), Eq.{succ u2} (δ a) (Finset.pi.cons.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b f a h) b
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : δ a) (f : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (h : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)), Eq.{succ u1} (δ a) (Finset.pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b f a h) b
Case conversion may be inaccurate. Consider using '#align finset.pi.cons_same Finset.pi.cons_sameₓ'. -/
@[simp]
theorem pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (h : a ∈ insert a s) :
    pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _
#align finset.pi.cons_same Finset.pi.cons_same

/- warning: finset.pi.cons_ne -> Finset.pi.cons_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)} {h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)} (ha : Ne.{succ u1} α a a'), Eq.{succ u2} (δ a') (Finset.pi.cons.{u1, u2} α (fun {a : α} => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b f a' h) (f a' (Or.resolve_left (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' s) (Iff.mp (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Or (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' s)) (Finset.mem_insert.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a' a) h) (Ne.symm.{succ u1} α a a' ha)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)} {h : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)} (ha : Ne.{succ u2} α a a'), Eq.{succ u1} (δ a') (Finset.pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b f a' h) (f a' (Or.resolve_left (Eq.{succ u2} α a' a) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' s) (Iff.mp (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Or (Eq.{succ u2} α a' a) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' s)) (Finset.mem_insert.{u2} α (fun (a : α) (b : α) => _inst_1 a b) s a' a) h) (Ne.symm.{succ u2} α a a' ha)))
Case conversion may be inaccurate. Consider using '#align finset.pi.cons_ne Finset.pi.cons_neₓ'. -/
theorem pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : ∀ a, a ∈ s → δ a} {h : a' ∈ insert a s}
    (ha : a ≠ a') : pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ _
#align finset.pi.cons_ne Finset.pi.cons_ne

/- warning: finset.pi_cons_injective -> Finset.pi_cons_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {a : α} {b : δ a} {s : Finset.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (forall (a' : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a' (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a')) (Finset.pi.cons.{u1, u2} α (fun {a : α} => δ a) (fun (a : α) (b : α) => _inst_1 a b) s a b))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {a : α} {b : δ a} {s : Finset.{u2} α}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (forall (a' : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a' (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) -> (δ a')) (Finset.pi.cons.{u2, u1} α δ (fun (a : α) (b : α) => _inst_1 a b) s a b))
Case conversion may be inaccurate. Consider using '#align finset.pi_cons_injective Finset.pi_cons_injectiveₓ'. -/
theorem pi_cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (pi.cons s a b) := fun e₁ e₂ eq =>
  @Multiset.pi_cons_injective α _ δ a b s.1 hs _ _ <|
    funext fun e =>
      funext fun h =>
        have :
          pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using h) =
            pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using h) :=
          by rw [Eq]
        this
#align finset.pi_cons_injective Finset.pi_cons_injective

#print Finset.pi_empty /-
@[simp]
theorem pi_empty {t : ∀ a : α, Finset (δ a)} : pi (∅ : Finset α) t = singleton (Pi.empty δ) :=
  rfl
#align finset.pi_empty Finset.pi_empty
-/

#print Finset.pi_insert /-
@[simp]
theorem pi_insert [∀ a, DecidableEq (δ a)] {s : Finset α} {t : ∀ a : α, Finset (δ a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).bunionᵢ fun b => (pi s t).image (pi.cons s a b) :=
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
  exact ((pi s t).Nodup.map <| Multiset.pi_cons_injective ha).dedup.symm
#align finset.pi_insert Finset.pi_insert
-/

#print Finset.pi_singletons /-
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
-/

#print Finset.pi_const_singleton /-
theorem pi_const_singleton {β : Type _} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i
#align finset.pi_const_singleton Finset.pi_const_singleton
-/

/- warning: finset.pi_subset -> Finset.pi_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)), (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u2} (Finset.{u2} (δ a)) (Finset.hasSubset.{u2} (δ a)) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.hasSubset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} (t₁ : forall (a : α), Finset.{u1} (δ a)) (t₂ : forall (a : α), Finset.{u1} (δ a)), (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} (δ a)) (Finset.instHasSubsetFinset.{u1} (δ a)) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{max u2 u1} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a))) (Finset.instHasSubsetFinset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a))) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.pi_subset Finset.pi_subsetₓ'. -/
theorem pi_subset {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
    s.pi t₁ ⊆ s.pi t₂ := fun g hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)
#align finset.pi_subset Finset.pi_subset

/- warning: finset.pi_disjoint_of_disjoint -> Finset.pi_disjoint_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.orderBot.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.partialOrder.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.orderBot.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a))) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} {s : Finset.{u1} α} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.partialOrder.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (δ a))) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₁) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.pi_disjoint_of_disjoint Finset.pi_disjoint_of_disjointₓ'. -/
theorem pi_disjoint_of_disjoint {δ : α → Type _} {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (ha : a ∈ s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha) <|
      congr_fun (congr_fun eq₁₂ a) ha
#align finset.pi_disjoint_of_disjoint Finset.pi_disjoint_of_disjoint

end Pi

end Finset

