/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.multiset.pi
! leanprover-community/mathlib commit 4c586d291f189eecb9d00581aeb3dd998ac34442
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Nodup

/-!
# The cartesian product of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

section Pi

variable {α : Type _}

open Function

/- warning: multiset.pi.empty -> Multiset.Pi.empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (δ : α -> Sort.{u2}) (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (δ a)
but is expected to have type
  forall {α : Type.{u1}} (δ : α -> Type.{u2}) (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (δ a)
Case conversion may be inaccurate. Consider using '#align multiset.pi.empty Multiset.Pi.emptyₓ'. -/
/-- Given `δ : α → Type*`, `pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def Pi.empty (δ : α → Sort _) : ∀ a ∈ (0 : Multiset α), δ a :=
  fun.
#align multiset.pi.empty Multiset.Pi.empty

variable [DecidableEq α] {β : α → Type _} {δ : α → Sort _}

/- warning: multiset.pi.cons -> Multiset.Pi.cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} (m : Multiset.{u1} α) (a : α), (δ a) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (δ a)) -> (forall (a' : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a m)) -> (δ a'))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} (m : Multiset.{u1} α) (a : α), (δ a) -> (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a m) -> (δ a)) -> (forall (a' : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a' (Multiset.cons.{u1} α a m)) -> (δ a'))
Case conversion may be inaccurate. Consider using '#align multiset.pi.cons Multiset.Pi.consₓ'. -/
/-- Given `δ : α → Type*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def Pi.cons (m : Multiset α) (a : α) (b : δ a) (f : ∀ a ∈ m, δ a) : ∀ a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' <| (mem_cons.1 ha').resolve_left h
#align multiset.pi.cons Multiset.Pi.cons

/- warning: multiset.pi.cons_same -> Multiset.Pi.cons_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} {m : Multiset.{u1} α} {a : α} {b : δ a} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (δ a)} (h : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (Multiset.cons.{u1} α a m)), Eq.{u2} (δ a) (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a : α} => δ a) m a b f a h) b
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} {m : Multiset.{u2} α} {a : α} {b : δ a} {f : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (δ a)} (h : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a (Multiset.cons.{u2} α a m)), Eq.{succ u1} (δ a) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ m a b f a h) b
Case conversion may be inaccurate. Consider using '#align multiset.pi.cons_same Multiset.Pi.cons_sameₓ'. -/
theorem Pi.cons_same {m : Multiset α} {a : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
    Pi.cons m a b f a h = b :=
  dif_pos rfl
#align multiset.pi.cons_same Multiset.Pi.cons_same

/- warning: multiset.pi.cons_ne -> Multiset.Pi.cons_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} {m : Multiset.{u1} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (δ a)} (h' : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a m)) (h : Ne.{succ u1} α a' a), Eq.{u2} (δ a') (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a : α} => δ a) m a b f a' h') (f a' (Or.resolve_left (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' m) (Iff.mp (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a m)) (Or (Eq.{succ u1} α a' a) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' m)) (Multiset.mem_cons.{u1} α a' a m) h') h))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} {m : Multiset.{u2} α} {a : α} {a' : α} {b : δ a} {f : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (δ a)} (h' : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' (Multiset.cons.{u2} α a m)) (h : Ne.{succ u2} α a' a), Eq.{succ u1} (δ a') (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ m a b f a' h') (f a' (Or.resolve_left (Eq.{succ u2} α a' a) (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' m) (Iff.mp (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' (Multiset.cons.{u2} α a m)) (Or (Eq.{succ u2} α a' a) (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' m)) (Multiset.mem_cons.{u2} α a' a m) h') h))
Case conversion may be inaccurate. Consider using '#align multiset.pi.cons_ne Multiset.Pi.cons_neₓ'. -/
theorem Pi.cons_ne {m : Multiset α} {a a' : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h' : a' ∈ a ::ₘ m)
    (h : a' ≠ a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h
#align multiset.pi.cons_ne Multiset.Pi.cons_ne

/- warning: multiset.pi.cons_swap -> Multiset.Pi.cons_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} {a : α} {a' : α} {b : δ a} {b' : δ a'} {m : Multiset.{u1} α} {f : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (δ a)}, (Ne.{succ u1} α a a') -> (HEq.{imax (succ u1) u2} (forall (a'_1 : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a'_1 (Multiset.cons.{u1} α a (Multiset.cons.{u1} α a' m))) -> (δ a'_1)) (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a : α} => δ a) (Multiset.cons.{u1} α a' m) a b (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) m a' b' f)) (forall (a'_1 : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a'_1 (Multiset.cons.{u1} α a' (Multiset.cons.{u1} α a m))) -> (δ a'_1)) (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a' : α} => δ a') (Multiset.cons.{u1} α a m) a' b' (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) m a b f)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} {a : α} {a' : α} {b : δ a} {b' : δ a'} {m : Multiset.{u2} α} {f : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (δ a)}, (Ne.{succ u2} α a a') -> (HEq.{max (succ u2) (succ u1)} (forall (a'_1 : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a'_1 (Multiset.cons.{u2} α a (Multiset.cons.{u2} α a' m))) -> (δ a'_1)) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ (Multiset.cons.{u2} α a' m) a b (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) m a' b' f)) (forall (a'_1 : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a'_1 (Multiset.cons.{u2} α a' (Multiset.cons.{u2} α a m))) -> (δ a'_1)) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ (Multiset.cons.{u2} α a m) a' b' (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => δ a) m a b f)))
Case conversion may be inaccurate. Consider using '#align multiset.pi.cons_swap Multiset.Pi.cons_swapₓ'. -/
theorem Pi.cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a ∈ m, δ a}
    (h : a ≠ a') :
    HEq (Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f)) (Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f)) :=
  by
  apply hfunext rfl
  rintro a'' _ rfl
  refine' hfunext (by rw [cons_swap]) fun ha₁ ha₂ _ => _
  rcases ne_or_eq a'' a with (h₁ | rfl)
  rcases eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, pi.cons_same, pi.cons_ne]
#align multiset.pi.cons_swap Multiset.Pi.cons_swap

#print Multiset.pi /-
/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst Eq
      · simp [map_bind, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b hb
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' hb'
        apply map_hcongr
        · rw [cons_swap a a']
        intro f hf
        exact pi.cons_swap Eq)
#align multiset.pi Multiset.pi
-/

/- warning: multiset.pi_zero -> Multiset.pi_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} (t : forall (a : α), Multiset.{u2} (β a)), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (β a))) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) t) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (β a)) (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (β a))) (Multiset.hasSingleton.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) -> (β a))) (Multiset.Pi.empty.{u1, succ u2} α β))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} (t : forall (a : α), Multiset.{u2} (β a)), Eq.{max (succ u1) (succ u2)} (Multiset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (β a))) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))) t) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (β a)) (Multiset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (β a))) (Multiset.instSingletonMultiset.{max u1 u2} (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) -> (β a))) (Multiset.Pi.empty.{u1, u2} α β))
Case conversion may be inaccurate. Consider using '#align multiset.pi_zero Multiset.pi_zeroₓ'. -/
@[simp]
theorem pi_zero (t : ∀ a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl
#align multiset.pi_zero Multiset.pi_zero

/- warning: multiset.pi_cons -> Multiset.pi_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} (m : Multiset.{u1} α) (t : forall (a : α), Multiset.{u2} (β a)) (a : α), Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a_1 (Multiset.cons.{u1} α a m)) -> (β a_1))) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (Multiset.cons.{u1} α a m) t) (Multiset.bind.{u2, max u1 u2} (β a) (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a_1 (Multiset.cons.{u1} α a m)) -> (β a_1)) (t a) (fun (b : β a) => Multiset.map.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)) (forall (a_1 : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a_1 (Multiset.cons.{u1} α a m)) -> (β a_1)) (Multiset.Pi.cons.{u1, succ u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m a b) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {β : α -> Type.{u1}} (m : Multiset.{u2} α) (t : forall (a : α), Multiset.{u1} (β a)) (a : α), Eq.{max (succ u2) (succ u1)} (Multiset.{max u2 u1} (forall (a_1 : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a_1 (Multiset.cons.{u2} α a m)) -> (β a_1))) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) (Multiset.cons.{u2} α a m) t) (Multiset.bind.{u1, max u2 u1} (β a) (forall (a_1 : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a_1 (Multiset.cons.{u2} α a m)) -> (β a_1)) (t a) (fun (b : β a) => Multiset.map.{max u2 u1, max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)) (forall (a_1 : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a_1 (Multiset.cons.{u2} α a m)) -> (β a_1)) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) β m a b) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)))
Case conversion may be inaccurate. Consider using '#align multiset.pi_cons Multiset.pi_consₓ'. -/
@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b :=
  recOn_cons a m
#align multiset.pi_cons Multiset.pi_cons

/- warning: multiset.pi_cons_injective -> Multiset.pi_cons_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} {a : α} {b : δ a} {s : Multiset.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s)) -> (Function.Injective.{imax (succ u1) u2, imax (succ u1) u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (δ a)) (forall (a' : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a s)) -> (δ a')) (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a : α} => δ a) s a b))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} {a : α} {b : δ a} {s : Multiset.{u2} α}, (Not (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s)) -> (Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (δ a)) (forall (a' : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' (Multiset.cons.{u2} α a s)) -> (δ a')) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ s a b))
Case conversion may be inaccurate. Consider using '#align multiset.pi_cons_injective Multiset.pi_cons_injectiveₓ'. -/
theorem pi_cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
      have ne : a ≠ a' := fun h => hs <| h.symm ▸ h'
      have : a' ∈ a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [pi.cons_ne this Ne.symm]
        _ = Pi.cons s a b f₂ a' this := by rw [Eq]
        _ = f₂ a' h' := by rw [pi.cons_ne this Ne.symm]
        
#align multiset.pi_cons_injective Multiset.pi_cons_injective

/- warning: multiset.card_pi -> Multiset.card_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} (m : Multiset.{u1} α) (t : forall (a : α), Multiset.{u2} (β a)), Eq.{1} Nat (coeFn.{succ (max u1 u2), succ (max u1 u2)} (AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{max u1 u2, 0} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) -> Nat) (AddMonoidHom.hasCoeToFun.{max u1 u2, 0} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u1 u2} (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (Multiset.orderedCancelAddCommMonoid.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)) (Multiset.prod.{0} Nat Nat.commMonoid (Multiset.map.{u1, 0} α Nat (fun (a : α) => coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} (β a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (β a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (β a)) (Multiset.orderedCancelAddCommMonoid.{u2} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} (β a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (β a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (β a)) (Multiset.orderedCancelAddCommMonoid.{u2} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} (β a)) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} (β a)) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} (β a)) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} (β a)) (Multiset.orderedCancelAddCommMonoid.{u2} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} (β a)) (t a)) m))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {β : α -> Type.{u1}} (m : Multiset.{u2} α) (t : forall (a : α), Multiset.{u1} (β a)), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) => Nat) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), 1} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (fun (_x : Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) => Nat) _x) (AddHomClass.toFunLike.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddZeroClass.toAdd.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{max u2 u1, max u2 u1, 0} (AddMonoidHom.{max u2 u1, 0} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{max u2 u1, 0} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) Nat (AddMonoid.toAddZeroClass.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddRightCancelMonoid.toAddMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelMonoid.toAddRightCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (AddCancelCommMonoid.toAddCancelMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{max u2 u1} (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instOrderedCancelAddCommMonoidMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)) (Multiset.prod.{0} Nat Nat.commMonoid (Multiset.map.{u2, 0} α Nat (fun (a : α) => FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} (β a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (β a)) (fun (_x : Multiset.{u1} (β a)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} (β a)) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (β a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (β a)) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} (β a)) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a)))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} (β a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} (β a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} (β a)) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} (β a)) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} (β a)) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} (β a)) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} (β a)) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} (β a))))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} (β a)) (t a)) m))
Case conversion may be inaccurate. Consider using '#align multiset.card_pi Multiset.card_piₓ'. -/
theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp (config := { contextual := true }) [mul_comm])
#align multiset.card_pi Multiset.card_pi

/- warning: multiset.nodup.pi -> Multiset.Nodup.pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} {s : Multiset.{u1} α} {t : forall (a : α), Multiset.{u2} (β a)}, (Multiset.Nodup.{u1} α s) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Multiset.Nodup.{u2} (β a) (t a))) -> (Multiset.Nodup.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (β a)) (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) s t))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {β : α -> Type.{u1}} {s : Multiset.{u2} α} {t : forall (a : α), Multiset.{u1} (β a)}, (Multiset.Nodup.{u2} α s) -> (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (Multiset.Nodup.{u1} (β a) (t a))) -> (Multiset.Nodup.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (β a)) (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) s t))
Case conversion may be inaccurate. Consider using '#align multiset.nodup.pi Multiset.Nodup.piₓ'. -/
protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp at hs <;> exact hs.1
      have hs : nodup s := by simp at hs <;> exact hs.2
      simp
      refine'
        ⟨fun b hb => (ih hs fun a' h' => ht a' <| mem_cons_of_mem h').map (pi_cons_injective has),
          _⟩
      refine' (ht a <| mem_cons_self _ _).Pairwise _
      exact fun b₁ hb₁ b₂ hb₂ neb =>
        disjoint_map_map.2 fun f hf g hg eq =>
          have : pi.cons s a b₁ f a (mem_cons_self _ _) = pi.cons s a b₂ g a (mem_cons_self _ _) :=
            by rw [Eq]
          neb <| show b₁ = b₂ by rwa [pi.cons_same, pi.cons_same] at this)
#align multiset.nodup.pi Multiset.Nodup.pi

/- warning: multiset.pi.cons_ext -> Multiset.pi.cons_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Sort.{u2}} {m : Multiset.{u1} α} {a : α} (f : forall (a' : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a m)) -> (δ a')), Eq.{imax (succ u1) u2} (forall (a' : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' (Multiset.cons.{u1} α a m)) -> (δ a')) (Multiset.Pi.cons.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun {a : α} => δ a) m a (f a (Multiset.mem_cons_self.{u1} α a m)) (fun (a' : α) (ha' : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' m) => f a' (Multiset.mem_cons_of_mem.{u1} α a' a m ha'))) f
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} {m : Multiset.{u2} α} {a : α} (f : forall (a' : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' (Multiset.cons.{u2} α a m)) -> (δ a')), Eq.{max (succ u2) (succ u1)} (forall (a' : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' (Multiset.cons.{u2} α a m)) -> (δ a')) (Multiset.Pi.cons.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) δ m a (f a (Multiset.mem_cons_self.{u2} α a m)) (fun (a' : α) (ha' : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a' m) => f a' (Multiset.mem_cons_of_mem.{u2} α a' a m ha'))) f
Case conversion may be inaccurate. Consider using '#align multiset.pi.cons_ext Multiset.pi.cons_extₓ'. -/
@[simp]
theorem pi.cons_ext {m : Multiset α} {a : α} (f : ∀ a' ∈ a ::ₘ m, δ a') :
    (Pi.cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f :=
  by
  ext (a' h')
  by_cases a' = a
  · subst h
    rw [pi.cons_same]
  · rw [pi.cons_ne _ h]
#align multiset.pi.cons_ext Multiset.pi.cons_ext

/- warning: multiset.mem_pi -> Multiset.mem_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : α -> Type.{u2}} (m : Multiset.{u1} α) (t : forall (a : α), Multiset.{u2} (β a)) (f : forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)), Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a)) (Multiset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) (Multiset.hasMem.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (β a))) f (Multiset.pi.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)) (forall (a : α) (h : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m), Membership.Mem.{u2, u2} (β a) (Multiset.{u2} (β a)) (Multiset.hasMem.{u2} (β a)) (f a h) (t a))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {β : α -> Type.{u1}} (m : Multiset.{u2} α) (t : forall (a : α), Multiset.{u1} (β a)) (f : forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)), Iff (Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a)) (Multiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) (Multiset.instMembershipMultiset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m) -> (β a))) f (Multiset.pi.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) => β a) m t)) (forall (a : α) (h : Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a m), Membership.mem.{u1, u1} (β a) (Multiset.{u1} (β a)) (Multiset.instMembershipMultiset.{u1} (β a)) (f a h) (t a))
Case conversion may be inaccurate. Consider using '#align multiset.mem_pi Multiset.mem_piₓ'. -/
theorem mem_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    ∀ f : ∀ a ∈ m, β a, f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a :=
  by
  intro f
  induction' m using Multiset.induction_on with a m ih
  · simpa using show f = pi.empty β by funext a ha <;> exact ha.elim
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases a' = a
    · subst h
      rwa [pi.cons_same]
    · rw [pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine' ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), _⟩
    rw [pi.cons_ext]
#align multiset.mem_pi Multiset.mem_pi

end Pi

end Multiset

