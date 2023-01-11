/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.nat.set
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
### Recursion on the natural numbers and `set.range`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Nat

section Set

open Set

/- warning: nat.zero_union_range_succ -> Nat.zero_union_range_succ is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Nat) (Union.union.{0} (Set.{0} Nat) (Set.hasUnion.{0} Nat) (Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (Set.hasSingleton.{0} Nat) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Set.range.{0, 1} Nat Nat Nat.succ)) (Set.univ.{0} Nat)
but is expected to have type
  Eq.{1} (Set.{0} Nat) (Union.union.{0} (Set.{0} Nat) (Set.instUnionSet_1.{0} Nat) (Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (Set.instSingletonSet.{0} Nat) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Set.range.{0, 1} Nat Nat Nat.succ)) (Set.univ.{0} Nat)
Case conversion may be inaccurate. Consider using '#align nat.zero_union_range_succ Nat.zero_union_range_succₓ'. -/
theorem zero_union_range_succ : {0} ∪ range succ = univ :=
  by
  ext n
  cases n <;> simp
#align nat.zero_union_range_succ Nat.zero_union_range_succ

#print Nat.range_succ /-
@[simp]
protected theorem range_succ : range succ = { i | 0 < i } := by
  ext (_ | i) <;> simp [succ_pos, succ_ne_zero]
#align nat.range_succ Nat.range_succ
-/

variable {α : Type _}

/- warning: nat.range_of_succ -> Nat.range_of_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Nat -> α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (Set.range.{u1, 1} α Nat (Function.comp.{1, 1, succ u1} Nat Nat α f Nat.succ))) (Set.range.{u1, 1} α Nat f)
but is expected to have type
  forall {α : Type.{u1}} (f : Nat -> α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet_1.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Set.range.{u1, 1} α Nat (Function.comp.{1, 1, succ u1} Nat Nat α f Nat.succ))) (Set.range.{u1, 1} α Nat f)
Case conversion may be inaccurate. Consider using '#align nat.range_of_succ Nat.range_of_succₓ'. -/
theorem range_of_succ (f : ℕ → α) : {f 0} ∪ range (f ∘ succ) = range f := by
  rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]
#align nat.range_of_succ Nat.range_of_succ

/- warning: nat.range_rec -> Nat.range_rec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (f : Nat -> α -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.rec.{succ u1} (fun (_x : Nat) => α) x f n)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.rec.{succ u1} (fun (_x : Nat) => α) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) x) (Function.comp.{1, 1, succ u1} Nat Nat (α -> α) f Nat.succ) n)))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (f : Nat -> α -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.rec.{succ u1} (fun (_x : Nat) => α) x f n)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet_1.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.rec.{succ u1} (fun (_x : Nat) => α) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) x) (Function.comp.{1, 1, succ u1} Nat Nat (α -> α) f Nat.succ) n)))
Case conversion may be inaccurate. Consider using '#align nat.range_rec Nat.range_recₓ'. -/
theorem range_rec {α : Type _} (x : α) (f : ℕ → α → α) :
    (Set.range fun n => Nat.rec x f n : Set α) =
      {x} ∪ Set.range fun n => Nat.rec (f 0 x) (f ∘ succ) n :=
  by
  convert (range_of_succ _).symm
  ext n
  induction' n with n ihn
  · rfl
  · dsimp at ihn⊢
    rw [ihn]
#align nat.range_rec Nat.range_rec

/- warning: nat.range_cases_on -> Nat.range_casesOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (f : Nat -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.casesOn.{succ u1} (fun (_x : Nat) => α) n x f)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) (Set.range.{u1, 1} α Nat f))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (f : Nat -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α Nat (fun (n : Nat) => Nat.casesOn.{succ u1} (fun (_x : Nat) => α) n x f)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet_1.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) (Set.range.{u1, 1} α Nat f))
Case conversion may be inaccurate. Consider using '#align nat.range_cases_on Nat.range_casesOnₓ'. -/
theorem range_casesOn {α : Type _} (x : α) (f : ℕ → α) :
    (Set.range fun n => Nat.casesOn n x f : Set α) = {x} ∪ Set.range f :=
  (range_of_succ _).symm
#align nat.range_cases_on Nat.range_casesOn

end Set

end Nat

