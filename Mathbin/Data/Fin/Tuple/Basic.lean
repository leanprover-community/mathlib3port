/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes

! This file was ported from Lean 3 source module data.fin.tuple.basic
! leanprover-community/mathlib commit ef997baa41b5c428be3fb50089a7139bf4ee886b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Pi.Lex
import Mathbin.Data.Set.Intervals.Basic

/-!
# Operation on tuples

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We interpret maps `Π i : fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `vector`s.

We define the following operations:

* `fin.tail` : the tail of an `n+1` tuple, i.e., its last `n` entries;
* `fin.cons` : adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple;
* `fin.init` : the beginning of an `n+1` tuple, i.e., its first `n` entries;
* `fin.snoc` : adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc`
  comes from `cons` (i.e., adding an element to the left of a tuple) read in reverse order.
* `fin.insert_nth` : insert an element to a tuple at a given position.
* `fin.find p` : returns the first index `n` where `p n` is satisfied, and `none` if it is never
  satisfied.
* `fin.append a b` : append two tuples.
* `fin.repeat n a` : repeat a tuple `n` times.

-/


universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example (α : Fin 0 → Sort u) : Unique (∀ i : Fin 0, α i) := by infer_instance

/- warning: fin.tuple0_le -> Fin.tuple0_le is a dubious translation:
lean 3 declaration is
  forall {α : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> Type.{u1}} [_inst_1 : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), Preorder.{u1} (α i)] (f : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), α i) (g : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), α i), LE.le.{u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), α i) (Pi.hasLe.{0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => α i) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Preorder.toHasLe.{u1} (α i) (_inst_1 i))) f g
but is expected to have type
  forall {α : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> Type.{u1}} [_inst_1 : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), Preorder.{u1} (α i)] (f : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), α i) (g : forall (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), α i), LE.le.{u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), α i) (Pi.hasLe.{0, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => α i) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Preorder.toLE.{u1} (α i) (_inst_1 i))) f g
Case conversion may be inaccurate. Consider using '#align fin.tuple0_le Fin.tuple0_leₓ'. -/
@[simp]
theorem tuple0_le {α : ∀ i : Fin 0, Type _} [∀ i, Preorder (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim
#align fin.tuple0_le Fin.tuple0_le

variable {α : Fin (n + 1) → Type u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

#print Fin.tail /-
/-- The tail of an `n+1` tuple, i.e., its last `n` entries. -/
def tail (q : ∀ i, α i) : ∀ i : Fin n, α i.succ := fun i => q i.succ
#align fin.tail Fin.tail
-/

#print Fin.tail_def /-
theorem tail_def {n : ℕ} {α : Fin (n + 1) → Type _} {q : ∀ i, α i} :
    (tail fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.succ :=
  rfl
#align fin.tail_def Fin.tail_def
-/

/- warning: fin.cons -> Fin.cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}}, (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) -> (forall (i : Fin n), α (Fin.succ n i)) -> (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}}, (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) -> (forall (i : Fin n), α (Fin.succ n i)) -> (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i)
Case conversion may be inaccurate. Consider using '#align fin.cons Fin.consₓ'. -/
/-- Adding an element at the beginning of an `n`-tuple, to get an `n+1`-tuple. -/
def cons (x : α 0) (p : ∀ i : Fin n, α i.succ) : ∀ i, α i := fun j => Fin.cases x p j
#align fin.cons Fin.cons

/- warning: fin.tail_cons -> Fin.tail_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p : forall (i : Fin n), α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (Fin.cons.{u1} n α x p)) p
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p : forall (i : Fin n), α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (Fin.cons.{u1} n α x p)) p
Case conversion may be inaccurate. Consider using '#align fin.tail_cons Fin.tail_consₓ'. -/
@[simp]
theorem tail_cons : tail (cons x p) = p := by simp [tail, cons]
#align fin.tail_cons Fin.tail_cons

/- warning: fin.cons_succ -> Fin.cons_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p : forall (i : Fin n), α (Fin.succ n i)) (i : Fin n), Eq.{succ u1} (α (Fin.succ n i)) (Fin.cons.{u1} n α x p (Fin.succ n i)) (p i)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p : forall (i : Fin n), α (Fin.succ n i)) (i : Fin n), Eq.{succ u1} (α (Fin.succ n i)) (Fin.cons.{u1} n α x p (Fin.succ n i)) (p i)
Case conversion may be inaccurate. Consider using '#align fin.cons_succ Fin.cons_succₓ'. -/
@[simp]
theorem cons_succ : cons x p i.succ = p i := by simp [cons]
#align fin.cons_succ Fin.cons_succ

/- warning: fin.cons_zero -> Fin.cons_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p : forall (i : Fin n), α (Fin.succ n i)), Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Fin.cons.{u1} n α x p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) x
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p : forall (i : Fin n), α (Fin.succ n i)), Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Fin.cons.{u1} n α x p (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) x
Case conversion may be inaccurate. Consider using '#align fin.cons_zero Fin.cons_zeroₓ'. -/
@[simp]
theorem cons_zero : cons x p 0 = x := by simp [cons]
#align fin.cons_zero Fin.cons_zero

/- warning: fin.cons_update -> Fin.cons_update is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p : forall (i : Fin n), α (Fin.succ n i)) (i : Fin n) (y : α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Fin.cons.{u1} n α x (Function.update.{1, succ u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) p i y)) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.cons.{u1} n (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α a) x p) (Fin.succ n i) y)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p : forall (i : Fin n), α (Fin.succ n i)) (i : Fin n) (y : α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Fin.cons.{u1} n α x (Function.update.{1, succ u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) p i y)) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (Fin.cons.{u1} n α x p) (Fin.succ n i) y)
Case conversion may be inaccurate. Consider using '#align fin.cons_update Fin.cons_updateₓ'. -/
/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y :=
  by
  ext j
  by_cases h : j = 0
  · rw [h]; simp [Ne.symm (succ_ne_zero i)]
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ]
    by_cases h' : j' = i
    · rw [h']; simp
    · have : j'.succ ≠ i.succ := by rwa [Ne.def, succ_inj]
      rw [update_noteq h', update_noteq this, cons_succ]
#align fin.cons_update Fin.cons_update

/- warning: fin.cons_injective2 -> Fin.cons_injective2 is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}}, Function.Injective2.{succ u1, succ u1, succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (forall (i : Fin n), α (Fin.succ n i)) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Fin.cons.{u1} n α)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}}, Function.Injective2.{succ u1, succ u1, succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (forall (i : Fin n), α (Fin.succ n i)) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Fin.cons.{u1} n α)
Case conversion may be inaccurate. Consider using '#align fin.cons_injective2 Fin.cons_injective2ₓ'. -/
/-- As a binary function, `fin.cons` is injective. -/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h =>
  ⟨congr_fun h 0, funext fun i => by simpa using congr_fun h (Fin.succ i)⟩
#align fin.cons_injective2 Fin.cons_injective2

/- warning: fin.cons_eq_cons -> Fin.cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)}, Iff (Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Fin.cons.{u1} n α x₀ x) (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) y₀ y)) (And (Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) x₀ y₀) (Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) x y))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)}, Iff (Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Fin.cons.{u1} n α x₀ x) (Fin.cons.{u1} n α y₀ y)) (And (Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) x₀ y₀) (Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) x y))
Case conversion may be inaccurate. Consider using '#align fin.cons_eq_cons Fin.cons_eq_consₓ'. -/
@[simp]
theorem cons_eq_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff
#align fin.cons_eq_cons Fin.cons_eq_cons

/- warning: fin.cons_left_injective -> Fin.cons_left_injective is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : forall (i : Fin n), α (Fin.succ n i)), Function.Injective.{succ u1, succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (fun (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) => Fin.cons.{u1} n α x₀ x)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : forall (i : Fin n), α (Fin.succ n i)), Function.Injective.{succ u1, succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (fun (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) => Fin.cons.{u1} n α x₀ x)
Case conversion may be inaccurate. Consider using '#align fin.cons_left_injective Fin.cons_left_injectiveₓ'. -/
theorem cons_left_injective (x : ∀ i : Fin n, α i.succ) : Function.Injective fun x₀ => cons x₀ x :=
  cons_injective2.left _
#align fin.cons_left_injective Fin.cons_left_injective

/- warning: fin.cons_right_injective -> Fin.cons_right_injective is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))), Function.Injective.{succ u1, succ u1} (forall (i : Fin n), α (Fin.succ n i)) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Fin.cons.{u1} n α x₀)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))), Function.Injective.{succ u1, succ u1} (forall (i : Fin n), α (Fin.succ n i)) (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Fin.cons.{u1} n α x₀)
Case conversion may be inaccurate. Consider using '#align fin.cons_right_injective Fin.cons_right_injectiveₓ'. -/
theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _
#align fin.cons_right_injective Fin.cons_right_injective

/- warning: fin.update_cons_zero -> Fin.update_cons_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (p : forall (i : Fin n), α (Fin.succ n i)) (z : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))), Eq.{succ u1} (forall (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α a) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α a) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.cons.{u1} n α x p) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) z) (Fin.cons.{u1} n (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α a) z p)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (p : forall (i : Fin n), α (Fin.succ n i)) (z : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))), Eq.{succ u1} (forall (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α a) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α a) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (Fin.cons.{u1} n α x p) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))) z) (Fin.cons.{u1} n α z p)
Case conversion may be inaccurate. Consider using '#align fin.update_cons_zero Fin.update_cons_zeroₓ'. -/
/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_cons_zero : update (cons x p) 0 z = cons z p :=
  by
  ext j
  by_cases h : j = 0
  · rw [h]; simp
  · simp only [h, update_noteq, Ne.def, not_false_iff]
    let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, cons_succ]
#align fin.update_cons_zero Fin.update_cons_zero

/- warning: fin.cons_self_tail -> Fin.cons_self_tail is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i), Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Fin.cons.{u1} n α (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Fin.tail.{u1} n α q)) q
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i), Eq.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Fin.cons.{u1} n α (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Fin.tail.{u1} n α q)) q
Case conversion may be inaccurate. Consider using '#align fin.cons_self_tail Fin.cons_self_tailₓ'. -/
/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem cons_self_tail : cons (q 0) (tail q) = q :=
  by
  ext j
  by_cases h : j = 0
  · rw [h]; simp
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, tail, cons_succ]
#align fin.cons_self_tail Fin.cons_self_tail

/- warning: fin.cons_cases -> Fin.consCases is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {P : (forall (i : Fin (Nat.succ n)), α i) -> Sort.{u2}}, (forall (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (x : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) -> (forall (x : forall (i : Fin (Nat.succ n)), α i), P x)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {P : (forall (i : Fin (Nat.succ n)), α i) -> Sort.{u2}}, (forall (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (x : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) -> (forall (x : forall (i : Fin (Nat.succ n)), α i), P x)
Case conversion may be inaccurate. Consider using '#align fin.cons_cases Fin.consCasesₓ'. -/
/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
def consCases {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x : ∀ i : Fin n.succ, α i) : P x :=
  cast (by rw [cons_self_tail]) <| h (x 0) (tail x)
#align fin.cons_cases Fin.consCases

/- warning: fin.cons_cases_cons -> Fin.consCases_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {P : (forall (i : Fin (Nat.succ n)), α i) -> Sort.{u2}} (h : forall (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (x : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (x : forall (i : Fin n), α (Fin.succ n i)), Eq.{u2} (P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (Fin.consCases.{u1, u2} n α P h (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (h x₀ x)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {P : (forall (i : Fin (Nat.succ n)), α i) -> Sort.{u2}} (h : forall (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (x : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (x : forall (i : Fin n), α (Fin.succ n i)), Eq.{u2} (P (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (Fin.consCases.{u1, u2} n α P h (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x)) (h x₀ x)
Case conversion may be inaccurate. Consider using '#align fin.cons_cases_cons Fin.consCases_consₓ'. -/
@[simp]
theorem consCases_cons {P : (∀ i : Fin n.succ, α i) → Sort v} (h : ∀ x₀ x, P (Fin.cons x₀ x))
    (x₀ : α 0) (x : ∀ i : Fin n, α i.succ) : @consCases _ _ _ h (cons x₀ x) = h x₀ x :=
  by
  rw [cons_cases, cast_eq]
  congr
  exact tail_cons _ _
#align fin.cons_cases_cons Fin.consCases_cons

/- warning: fin.cons_induction -> Fin.consInductionₓ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u2}} {P : forall {n : Nat}, ((Fin n) -> α) -> Sort.{u1}}, (P (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Fin.elim0ₓ.{succ u2} (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => α))) -> (forall {n : Nat} (x₀ : α) (x : (Fin n) -> α), (P n x) -> (P (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin.cons.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) x₀ x))) -> (forall {n : Nat} (x : (Fin n) -> α), P n x)
but is expected to have type
  forall {α : Type.{u1}} {P : forall {n : Nat}, ((Fin n) -> α) -> Sort.{u2}}, (P (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Fin.elim0ₓ.{succ u1} (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => α))) -> (forall {n : Nat} (x₀ : α) (x : (Fin n) -> α), (P n x) -> (P (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) x₀ x))) -> (forall {n : Nat} (x : (Fin n) -> α), P n x)
Case conversion may be inaccurate. Consider using '#align fin.cons_induction Fin.consInductionₓₓ'. -/
/-- Recurse on an tuple by splitting into `fin.elim0` and `fin.cons`. -/
@[elab_as_elim]
def consInduction {α : Type _} {P : ∀ {n : ℕ}, (Fin n → α) → Sort v} (h0 : P Fin.elim0)
    (h : ∀ {n} (x₀) (x : Fin n → α), P x → P (Fin.cons x₀ x)) : ∀ {n : ℕ} (x : Fin n → α), P x
  | 0, x => by convert h0
  | n + 1, x => consCases (fun x₀ x => h _ _ <| cons_induction _) x
#align fin.cons_induction Fin.consInductionₓ

#print Fin.cons_injective_of_injective /-
theorem cons_injective_of_injective {α} {x₀ : α} {x : Fin n → α} (hx₀ : x₀ ∉ Set.range x)
    (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.succ → α) :=
  by
  refine' Fin.cases _ _
  · refine' Fin.cases _ _
    · intro
      rfl
    · intro j h
      rw [cons_zero, cons_succ] at h
      exact hx₀.elim ⟨_, h.symm⟩
  · intro i
    refine' Fin.cases _ _
    · intro h
      rw [cons_zero, cons_succ] at h
      exact hx₀.elim ⟨_, h⟩
    · intro j h
      rw [cons_succ, cons_succ] at h
      exact congr_arg _ (hx h)
#align fin.cons_injective_of_injective Fin.cons_injective_of_injective
-/

#print Fin.cons_injective_iff /-
theorem cons_injective_iff {α} {x₀ : α} {x : Fin n → α} :
    Function.Injective (cons x₀ x : Fin n.succ → α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x :=
  by
  refine' ⟨fun h => ⟨_, _⟩, fun h => cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simpa [hi, succ_ne_zero] using h
  · simpa [Function.comp] using h.comp (Fin.succ_injective _)
#align fin.cons_injective_iff Fin.cons_injective_iff
-/

#print Fin.forall_fin_zero_pi /-
@[simp]
theorem forall_fin_zero_pi {α : Fin 0 → Sort _} {P : (∀ i, α i) → Prop} :
    (∀ x, P x) ↔ P finZeroElim :=
  ⟨fun h => h _, fun h x => Subsingleton.elim finZeroElim x ▸ h⟩
#align fin.forall_fin_zero_pi Fin.forall_fin_zero_pi
-/

#print Fin.exists_fin_zero_pi /-
@[simp]
theorem exists_fin_zero_pi {α : Fin 0 → Sort _} {P : (∀ i, α i) → Prop} :
    (∃ x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ => Subsingleton.elim x finZeroElim ▸ h, fun h => ⟨_, h⟩⟩
#align fin.exists_fin_zero_pi Fin.exists_fin_zero_pi
-/

/- warning: fin.forall_fin_succ_pi -> Fin.forall_fin_succ_pi is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {P : (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) -> Prop}, Iff (forall (x : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i), P x) (forall (a : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (v : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) a v))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {P : (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) -> Prop}, Iff (forall (x : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i), P x) (forall (a : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (v : forall (i : Fin n), α (Fin.succ n i)), P (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) a v))
Case conversion may be inaccurate. Consider using '#align fin.forall_fin_succ_pi Fin.forall_fin_succ_piₓ'. -/
theorem forall_fin_succ_pi {P : (∀ i, α i) → Prop} : (∀ x, P x) ↔ ∀ a v, P (Fin.cons a v) :=
  ⟨fun h a v => h (Fin.cons a v), consCases⟩
#align fin.forall_fin_succ_pi Fin.forall_fin_succ_pi

/- warning: fin.exists_fin_succ_pi -> Fin.exists_fin_succ_pi is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {P : (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) -> Prop}, Iff (Exists.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (fun (x : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) => P x)) (Exists.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (fun (a : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) => Exists.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (fun (v : forall (i : Fin n), α (Fin.succ n i)) => P (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) a v))))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {P : (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) -> Prop}, Iff (Exists.{succ u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (fun (x : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) => P x)) (Exists.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (fun (a : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) => Exists.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (fun (v : forall (i : Fin n), α (Fin.succ n i)) => P (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) a v))))
Case conversion may be inaccurate. Consider using '#align fin.exists_fin_succ_pi Fin.exists_fin_succ_piₓ'. -/
theorem exists_fin_succ_pi {P : (∀ i, α i) → Prop} : (∃ x, P x) ↔ ∃ a v, P (Fin.cons a v) :=
  ⟨fun ⟨x, h⟩ => ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨a, v, h⟩ => ⟨_, h⟩⟩
#align fin.exists_fin_succ_pi Fin.exists_fin_succ_pi

/- warning: fin.tail_update_zero -> Fin.tail_update_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (z : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) z)) (Fin.tail.{u1} n α q)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (z : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))) z)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) q)
Case conversion may be inaccurate. Consider using '#align fin.tail_update_zero Fin.tail_update_zeroₓ'. -/
/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
theorem tail_update_zero : tail (update q 0 z) = tail q := by ext j; simp [tail, Fin.succ_ne_zero]
#align fin.tail_update_zero Fin.tail_update_zero

/- warning: fin.tail_update_succ -> Fin.tail_update_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (i : Fin n) (y : α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) q (Fin.succ n i) y)) (Function.update.{1, succ u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (a : Fin n) (b : Fin n) => Fin.decidableEq n a b) (Fin.tail.{u1} n α q) i y)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (i : Fin n) (y : α (Fin.succ n i)), Eq.{succ u1} (forall (i : Fin n), α (Fin.succ n i)) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) q (Fin.succ n i) y)) (Function.update.{1, succ u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (a : Fin n) (b : Fin n) => instDecidableEqFin n a b) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) q) i y)
Case conversion may be inaccurate. Consider using '#align fin.tail_update_succ Fin.tail_update_succₓ'. -/
/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y :=
  by
  ext j
  by_cases h : j = i
  · rw [h]; simp [tail]
  · simp [tail, (Fin.succ_injective n).Ne h, h]
#align fin.tail_update_succ Fin.tail_update_succ

/- warning: fin.comp_cons -> Fin.comp_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (g : α -> β) (y : α) (q : (Fin n) -> α), Eq.{succ u2} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> β) (Function.comp.{1, succ u1, succ u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) α β g (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) y q)) (Fin.cons.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) (g y) (Function.comp.{1, succ u1, succ u2} (Fin n) α β g q))
but is expected to have type
  forall {n : Nat} {α : Type.{u2}} {β : Type.{u1}} (g : α -> β) (y : α) (q : (Fin n) -> α), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> β) (Function.comp.{1, succ u2, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) α β g (Fin.cons.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) y q)) (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) (g y) (Function.comp.{1, succ u2, succ u1} (Fin n) α β g q))
Case conversion may be inaccurate. Consider using '#align fin.comp_cons Fin.comp_consₓ'. -/
theorem comp_cons {α : Type _} {β : Type _} (g : α → β) (y : α) (q : Fin n → α) :
    g ∘ cons y q = cons (g y) (g ∘ q) := by
  ext j
  by_cases h : j = 0
  · rw [h]; rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this, cons_succ, comp_app, cons_succ]
#align fin.comp_cons Fin.comp_cons

/- warning: fin.comp_tail -> Fin.comp_tail is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (g : α -> β) (q : (Fin (Nat.succ n)) -> α), Eq.{succ u2} ((Fin n) -> β) (Function.comp.{1, succ u1, succ u2} (Fin n) α β g (Fin.tail.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => α) q)) (Fin.tail.{u2} n (fun (ᾰ : Fin (Nat.succ n)) => β) (Function.comp.{1, succ u1, succ u2} (Fin (Nat.succ n)) α β g q))
but is expected to have type
  forall {n : Nat} {α : Type.{u2}} {β : Type.{u1}} (g : α -> β) (q : (Fin (Nat.succ n)) -> α), Eq.{succ u1} ((Fin n) -> β) (Function.comp.{1, succ u2, succ u1} (Fin n) α β g (Fin.tail.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) q)) (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) (Function.comp.{1, succ u2, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) α β g q))
Case conversion may be inaccurate. Consider using '#align fin.comp_tail Fin.comp_tailₓ'. -/
theorem comp_tail {α : Type _} {β : Type _} (g : α → β) (q : Fin n.succ → α) :
    g ∘ tail q = tail (g ∘ q) := by ext j; simp [tail]
#align fin.comp_tail Fin.comp_tail

/- warning: fin.le_cons -> Fin.le_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Preorder.{u1} (α i)] {x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i} {p : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Preorder.toHasLe.{u1} (α i) (_inst_1 i))) q (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) x p)) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Preorder.toHasLe.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))))) (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) x) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toHasLe.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) q) p))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Preorder.{u1} (α i)] {x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i} {p : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => Preorder.toLE.{u1} (α i) (_inst_1 i))) q (Fin.cons.{u1} n α x p)) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Preorder.toLE.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))))) (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) x) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toLE.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) q) p))
Case conversion may be inaccurate. Consider using '#align fin.le_cons Fin.le_consₓ'. -/
theorem le_cons [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    q ≤ cons x p ↔ q 0 ≤ x ∧ tail q ≤ p :=
  forall_fin_succ.trans <| and_congr Iff.rfl <| forall_congr' fun j => by simp [tail]
#align fin.le_cons Fin.le_cons

/- warning: fin.cons_le -> Fin.cons_le is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Preorder.{u1} (α i)] {x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i} {p : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Preorder.toHasLe.{u1} (α i) (_inst_1 i))) (Fin.cons.{u1} n α x p) q) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Preorder.toHasLe.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))))) x (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))))) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toHasLe.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) p (Fin.tail.{u1} n α q)))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Preorder.{u1} (α i)] {x : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i} {p : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => Preorder.toLE.{u1} (α i) (_inst_1 i))) (Fin.cons.{u1} n α x p) q) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Preorder.toLE.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))))) x (q (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))))) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toLE.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) p (Fin.tail.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) q)))
Case conversion may be inaccurate. Consider using '#align fin.cons_le Fin.cons_leₓ'. -/
theorem cons_le [∀ i, Preorder (α i)] {x : α 0} {q : ∀ i, α i} {p : ∀ i : Fin n, α i.succ} :
    cons x p ≤ q ↔ x ≤ q 0 ∧ p ≤ tail q :=
  @le_cons _ (fun i => (α i)ᵒᵈ) _ x q p
#align fin.cons_le Fin.cons_le

/- warning: fin.cons_le_cons -> Fin.cons_le_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Preorder.{u1} (α i)] {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Preorder.toHasLe.{u1} (α i) (_inst_1 i))) (Fin.cons.{u1} n α x₀ x) (Fin.cons.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) y₀ y)) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Preorder.toHasLe.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))))) x₀ y₀) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toHasLe.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) x y))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_1 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Preorder.{u1} (α i)] {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)}, Iff (LE.le.{u1} (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (Pi.hasLe.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => Preorder.toLE.{u1} (α i) (_inst_1 i))) (Fin.cons.{u1} n α x₀ x) (Fin.cons.{u1} n α y₀ y)) (And (LE.le.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Preorder.toLE.{u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (_inst_1 (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))))) x₀ y₀) (LE.le.{u1} (forall (i : Fin n), α (Fin.succ n i)) (Pi.hasLe.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (i : Fin n) => Preorder.toLE.{u1} (α (Fin.succ n i)) (_inst_1 (Fin.succ n i)))) x y))
Case conversion may be inaccurate. Consider using '#align fin.cons_le_cons Fin.cons_le_consₓ'. -/
theorem cons_le_cons [∀ i, Preorder (α i)] {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ} :
    cons x₀ x ≤ cons y₀ y ↔ x₀ ≤ y₀ ∧ x ≤ y :=
  forall_fin_succ.trans <| and_congr_right' <| by simp only [cons_succ, Pi.le_def]
#align fin.cons_le_cons Fin.cons_le_cons

/- warning: fin.pi_lex_lt_cons_cons -> Fin.pi_lex_lt_cons_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)} (s : forall {i : Fin (Nat.succ n)}, (α i) -> (α i) -> Prop), Iff (Pi.Lex.{0, u1} (Fin (Nat.succ n)) (fun (i : Fin (Nat.succ n)) => α i) (LT.lt.{0} (Fin (Nat.succ n)) (Fin.hasLt (Nat.succ n))) s (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x) (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) y₀ y)) (Or (s (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) x₀ y₀) (And (Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) x₀ y₀) (Pi.Lex.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (LT.lt.{0} (Fin n) (Fin.hasLt n)) (fun (i : Fin n) => s (Fin.succ n i)) x y)))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} {x₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {y₀ : α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))} {x : forall (i : Fin n), α (Fin.succ n i)} {y : forall (i : Fin n), α (Fin.succ n i)} (s : forall {i : Fin (Nat.succ n)}, (α i) -> (α i) -> Prop), Iff (Pi.Lex.{0, u1} (Fin (Nat.succ n)) (fun (i : Fin (Nat.succ n)) => α i) (fun (x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3610 : Fin (Nat.succ n)) (x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3612 : Fin (Nat.succ n)) => LT.lt.{0} (Fin (Nat.succ n)) (instLTFin (Nat.succ n)) x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3610 x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3612) s (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) x₀ x) (Fin.cons.{u1} n (fun (i : Fin (Nat.succ n)) => α i) y₀ y)) (Or (s (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))) x₀ y₀) (And (Eq.{succ u1} (α (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) x₀ y₀) (Pi.Lex.{0, u1} (Fin n) (fun (i : Fin n) => α (Fin.succ n i)) (fun (x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3654 : Fin n) (x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3656 : Fin n) => LT.lt.{0} (Fin n) (instLTFin n) x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3654 x._@.Mathlib.Data.Fin.Tuple.Basic._hyg.3656) (fun (i : Fin n) => s (Fin.succ n i)) x y)))
Case conversion may be inaccurate. Consider using '#align fin.pi_lex_lt_cons_cons Fin.pi_lex_lt_cons_consₓ'. -/
theorem pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : ∀ i : Fin n, α i.succ}
    (s : ∀ {i : Fin n.succ}, α i → α i → Prop) :
    Pi.Lex (· < ·) (@s) (Fin.cons x₀ x) (Fin.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (fun i : Fin n => @s i.succ) x y :=
  by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp [and_assoc', exists_and_left]
#align fin.pi_lex_lt_cons_cons Fin.pi_lex_lt_cons_cons

/- warning: fin.range_fin_succ -> Fin.range_fin_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) f) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Set.range.{u1, 1} α (Fin n) (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) f)))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) f) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (f (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n)))) (Set.range.{u1, 1} α (Fin n) (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) f)))
Case conversion may be inaccurate. Consider using '#align fin.range_fin_succ Fin.range_fin_succₓ'. -/
theorem range_fin_succ {α} (f : Fin (n + 1) → α) :
    Set.range f = insert (f 0) (Set.range (Fin.tail f)) :=
  Set.ext fun y => exists_fin_succ.trans <| eq_comm.Or Iff.rfl
#align fin.range_fin_succ Fin.range_fin_succ

#print Fin.range_cons /-
@[simp]
theorem range_cons {α : Type _} {n : ℕ} (x : α) (b : Fin n → α) :
    Set.range (Fin.cons x b : Fin n.succ → α) = insert x (Set.range b) := by
  rw [range_fin_succ, cons_zero, tail_cons]
#align fin.range_cons Fin.range_cons
-/

section Append

#print Fin.append /-
/-- Append a tuple of length `m` to a tuple of length `n` to get a tuple of length `m + n`.
This is a non-dependent version of `fin.add_cases`. -/
def append {α : Type _} (a : Fin m → α) (b : Fin n → α) : Fin (m + n) → α :=
  @Fin.addCases _ _ (fun _ => α) a b
#align fin.append Fin.append
-/

/- warning: fin.append_left -> Fin.append_left is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {α : Type.{u1}} (u : (Fin m) -> α) (v : (Fin n) -> α) (i : Fin m), Eq.{succ u1} α (Fin.append.{u1} m n α u v (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe m) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin m) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.castAdd m n) i)) (u i)
but is expected to have type
  forall {m : Nat} {n : Nat} {α : Type.{u1}} (u : (Fin m) -> α) (v : (Fin n) -> α) (i : Fin m), Eq.{succ u1} α (Fin.append.{u1} m n α u v (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (fun (_x : Fin m) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin m) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin m) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castAdd m n) i)) (u i)
Case conversion may be inaccurate. Consider using '#align fin.append_left Fin.append_leftₓ'. -/
@[simp]
theorem append_left {α : Type _} (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i :=
  addCases_left _ _ _
#align fin.append_left Fin.append_left

/- warning: fin.append_right -> Fin.append_right is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {α : Type.{u1}} (u : (Fin m) -> α) (v : (Fin n) -> α) (i : Fin n), Eq.{succ u1} α (Fin.append.{u1} m n α u v (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.natAdd m n) i)) (v i)
but is expected to have type
  forall {m : Nat} {n : Nat} {α : Type.{u1}} (u : (Fin m) -> α) (v : (Fin n) -> α) (i : Fin n), Eq.{succ u1} α (Fin.append.{u1} m n α u v (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.natAdd m n) i)) (v i)
Case conversion may be inaccurate. Consider using '#align fin.append_right Fin.append_rightₓ'. -/
@[simp]
theorem append_right {α : Type _} (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    append u v (natAdd m i) = v i :=
  addCases_right _ _ _
#align fin.append_right Fin.append_right

/- warning: fin.append_right_nil -> Fin.append_right_nil is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.append_right_nil Fin.append_right_nilₓ'. -/
theorem append_right_nil {α : Type _} (u : Fin m → α) (v : Fin n → α) (hv : n = 0) :
    append u v = u ∘ Fin.cast (by rw [hv, add_zero]) :=
  by
  refine' funext (Fin.addCases (fun l => _) fun r => _)
  · rw [append_left, Function.comp_apply]
    refine' congr_arg u (Fin.ext _)
    simp
  · exact (Fin.cast hv r).elim0'
#align fin.append_right_nil Fin.append_right_nil

/- warning: fin.append_elim0' -> Fin.append_elim0' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.append_elim0' Fin.append_elim0'ₓ'. -/
@[simp]
theorem append_elim0' {α : Type _} (u : Fin m → α) :
    append u Fin.elim0' = u ∘ Fin.cast (add_zero _) :=
  append_right_nil _ _ rfl
#align fin.append_elim0' Fin.append_elim0'

/- warning: fin.append_left_nil -> Fin.append_left_nil is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.append_left_nil Fin.append_left_nilₓ'. -/
theorem append_left_nil {α : Type _} (u : Fin m → α) (v : Fin n → α) (hu : m = 0) :
    append u v = v ∘ Fin.cast (by rw [hu, zero_add]) :=
  by
  refine' funext (Fin.addCases (fun l => _) fun r => _)
  · exact (Fin.cast hu l).elim0'
  · rw [append_right, Function.comp_apply]
    refine' congr_arg v (Fin.ext _)
    simp [hu]
#align fin.append_left_nil Fin.append_left_nil

/- warning: fin.elim0'_append -> Fin.elim0'_append is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.elim0'_append Fin.elim0'_appendₓ'. -/
@[simp]
theorem elim0'_append {α : Type _} (v : Fin n → α) :
    append Fin.elim0' v = v ∘ Fin.cast (zero_add _) :=
  append_left_nil _ _ rfl
#align fin.elim0'_append Fin.elim0'_append

/- warning: fin.append_assoc -> Fin.append_assoc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.append_assoc Fin.append_assocₓ'. -/
theorem append_assoc {p : ℕ} {α : Type _} (a : Fin m → α) (b : Fin n → α) (c : Fin p → α) :
    append (append a b) c = append a (append b c) ∘ Fin.cast (add_assoc _ _ _) :=
  by
  ext i
  rw [Function.comp_apply]
  refine' Fin.addCases (fun l => _) (fun r => _) i
  · rw [append_left]
    refine' Fin.addCases (fun ll => _) (fun lr => _) l
    · rw [append_left]
      simp [cast_add_cast_add]
    · rw [append_right]
      simp [cast_add_nat_add]
  · rw [append_right]
    simp [← nat_add_nat_add]
#align fin.append_assoc Fin.append_assoc

/- warning: fin.append_left_eq_cons -> Fin.append_left_eq_cons is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.append_left_eq_cons Fin.append_left_eq_consₓ'. -/
/-- Appending a one-tuple to the left is the same as `fin.cons`. -/
theorem append_left_eq_cons {α : Type _} {n : ℕ} (x₀ : Fin 1 → α) (x : Fin n → α) :
    Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (add_comm _ _) :=
  by
  ext i
  refine' Fin.addCases _ _ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_left, Function.comp_apply, eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right, Function.comp_apply, Fin.cast_natAdd, eq_comm, Fin.addNat_one]
    exact Fin.cons_succ _ _ _
#align fin.append_left_eq_cons Fin.append_left_eq_cons

end Append

section Repeat

#print Fin.repeat /-
/-- Repeat `a` `m` times. For example `fin.repeat 2 ![0, 3, 7] = ![0, 3, 7, 0, 3, 7]`. -/
@[simp]
def repeat {α : Type _} (m : ℕ) (a : Fin n → α) : Fin (m * n) → α
  | i => a i.modNat
#align fin.repeat Fin.repeat
-/

#print Fin.repeat_zero /-
@[simp]
theorem repeat_zero {α : Type _} (a : Fin n → α) :
    repeat 0 a = Fin.elim0' ∘ cast (MulZeroClass.zero_mul _) :=
  funext fun x => (cast (MulZeroClass.zero_mul _) x).elim0'
#align fin.repeat_zero Fin.repeat_zero
-/

/- warning: fin.repeat_one -> Fin.repeat_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.repeat_one Fin.repeat_oneₓ'. -/
@[simp]
theorem repeat_one {α : Type _} (a : Fin n → α) : repeat 1 a = a ∘ cast (one_mul _) :=
  by
  generalize_proofs h
  apply funext
  rw [(Fin.cast h.symm).Surjective.forall]
  intro i
  simp [mod_nat, Nat.mod_eq_of_lt i.is_lt]
#align fin.repeat_one Fin.repeat_one

/- warning: fin.repeat_succ -> Fin.repeat_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.repeat_succ Fin.repeat_succₓ'. -/
theorem repeat_succ {α : Type _} (a : Fin n → α) (m : ℕ) :
    repeat m.succ a = append a (repeat m a) ∘ cast ((Nat.succ_mul _ _).trans (add_comm _ _)) :=
  by
  generalize_proofs h
  apply funext
  rw [(Fin.cast h.symm).Surjective.forall]
  refine' Fin.addCases (fun l => _) fun r => _
  · simp [mod_nat, Nat.mod_eq_of_lt l.is_lt]
  · simp [mod_nat]
#align fin.repeat_succ Fin.repeat_succ

/- warning: fin.repeat_add -> Fin.repeat_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.repeat_add Fin.repeat_addₓ'. -/
@[simp]
theorem repeat_add {α : Type _} (a : Fin n → α) (m₁ m₂ : ℕ) :
    repeat (m₁ + m₂) a = append (repeat m₁ a) (repeat m₂ a) ∘ cast (add_mul _ _ _) :=
  by
  generalize_proofs h
  apply funext
  rw [(Fin.cast h.symm).Surjective.forall]
  refine' Fin.addCases (fun l => _) fun r => _
  · simp [mod_nat, Nat.mod_eq_of_lt l.is_lt]
  · simp [mod_nat, Nat.add_mod]
#align fin.repeat_add Fin.repeat_add

end Repeat

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `fin (n+1)` is constructed
inductively from `fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/


variable {α : Fin (n + 1) → Type u} (x : α (last n)) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.cast_succ)
  (i : Fin n) (y : α i.cast_succ) (z : α (last n))

/- warning: fin.init -> Fin.init is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}}, (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) -> (forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}}, (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) -> (forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i))
Case conversion may be inaccurate. Consider using '#align fin.init Fin.initₓ'. -/
/-- The beginning of an `n+1` tuple, i.e., its first `n` entries -/
def init (q : ∀ i, α i) (i : Fin n) : α i.cast_succ :=
  q i.cast_succ
#align fin.init Fin.init

/- warning: fin.init_def -> Fin.init_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.init_def Fin.init_defₓ'. -/
theorem init_def {n : ℕ} {α : Fin (n + 1) → Type _} {q : ∀ i, α i} :
    (init fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.cast_succ :=
  rfl
#align fin.init_def Fin.init_def

/- warning: fin.snoc -> Fin.snoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}}, (forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)) -> (α (Fin.last n)) -> (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}}, (forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)) -> (α (Fin.last n)) -> (forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i)
Case conversion may be inaccurate. Consider using '#align fin.snoc Fin.snocₓ'. -/
/-- Adding an element at the end of an `n`-tuple, to get an `n+1`-tuple. The name `snoc` comes from
`cons` (i.e., adding an element to the left of a tuple) read in reverse order. -/
def snoc (p : ∀ i : Fin n, α i.cast_succ) (x : α (last n)) (i : Fin (n + 1)) : α i :=
  if h : i.val < n then cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else cast (by rw [eq_last_of_not_lt h]) x
#align fin.snoc Fin.snoc

/- warning: fin.init_snoc -> Fin.init_snoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)), Eq.{succ u1} (forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)) (Fin.init.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (Fin.snoc.{u1} n α p x)) p
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)), Eq.{succ u1} (forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)) (Fin.init.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (Fin.snoc.{u1} n α p x)) p
Case conversion may be inaccurate. Consider using '#align fin.init_snoc Fin.init_snocₓ'. -/
@[simp]
theorem init_snoc : init (snoc p x) = p := by
  ext i
  have h' := Fin.castLT_castSucc i i.is_lt
  simp [init, snoc, i.is_lt, h']
  convert cast_eq rfl (p i)
#align fin.init_snoc Fin.init_snoc

/- warning: fin.snoc_cast_succ -> Fin.snoc_castSucc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.snoc_cast_succ Fin.snoc_castSuccₓ'. -/
@[simp]
theorem snoc_castSucc : snoc p x i.cast_succ = p i :=
  by
  have : i.cast_succ.val < n := i.is_lt
  have h' := Fin.castLT_castSucc i i.is_lt
  simp [snoc, this, h']
  convert cast_eq rfl (p i)
#align fin.snoc_cast_succ Fin.snoc_castSucc

/- warning: fin.snoc_comp_cast_succ -> Fin.snoc_comp_castSucc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {a : α} {f : (Fin n) -> α}, Eq.{succ u1} ((Fin n) -> α) (Function.comp.{1, 1, succ u1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) α (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) f a) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n))) f
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} {a : α} {f : (Fin n) -> α}, Eq.{succ u1} ((Fin n) -> α) (Function.comp.{1, 1, succ u1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) α (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) f a) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n))) f
Case conversion may be inaccurate. Consider using '#align fin.snoc_comp_cast_succ Fin.snoc_comp_castSuccₓ'. -/
@[simp]
theorem snoc_comp_castSucc {n : ℕ} {α : Sort _} {a : α} {f : Fin n → α} :
    (snoc f a : Fin (n + 1) → α) ∘ castSucc = f :=
  funext fun i => by rw [Function.comp_apply, snoc_cast_succ]
#align fin.snoc_comp_cast_succ Fin.snoc_comp_castSucc

/- warning: fin.snoc_last -> Fin.snoc_last is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)), Eq.{succ u1} (α (Fin.last n)) (Fin.snoc.{u1} n α p x (Fin.last n)) x
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)), Eq.{succ u1} (α (Fin.last n)) (Fin.snoc.{u1} n α p x (Fin.last n)) x
Case conversion may be inaccurate. Consider using '#align fin.snoc_last Fin.snoc_lastₓ'. -/
@[simp]
theorem snoc_last : snoc p x (last n) = x := by simp [snoc]
#align fin.snoc_last Fin.snoc_last

/- warning: fin.snoc_comp_nat_add -> Fin.snoc_comp_nat_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.snoc_comp_nat_add Fin.snoc_comp_nat_addₓ'. -/
@[simp]
theorem snoc_comp_nat_add {n m : ℕ} {α : Sort _} (f : Fin (m + n) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ (natAdd m : Fin (n + 1) → Fin (m + n + 1)) = snoc (f ∘ natAdd m) a :=
  by
  ext i
  refine' Fin.lastCases _ (fun i => _) i
  · simp only [Function.comp_apply]
    rw [snoc_last, nat_add_last, snoc_last]
  · simp only [Function.comp_apply]
    rw [snoc_cast_succ, nat_add_cast_succ, snoc_cast_succ]
#align fin.snoc_comp_nat_add Fin.snoc_comp_nat_add

/- warning: fin.snoc_cast_add -> Fin.snoc_cast_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.snoc_cast_add Fin.snoc_cast_addₓ'. -/
@[simp]
theorem snoc_cast_add {α : Fin (n + m + 1) → Type _} (f : ∀ i : Fin (n + m), α (castSucc i))
    (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _
#align fin.snoc_cast_add Fin.snoc_cast_add

/- warning: fin.snoc_comp_cast_add -> Fin.snoc_comp_cast_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.snoc_comp_cast_add Fin.snoc_comp_cast_addₓ'. -/
@[simp]
theorem snoc_comp_cast_add {n m : ℕ} {α : Sort _} (f : Fin (n + m) → α) (a : α) :
    (snoc f a : Fin _ → α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (snoc_cast_add f a)
#align fin.snoc_comp_cast_add Fin.snoc_comp_cast_add

/- warning: fin.snoc_update -> Fin.snoc_update is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.snoc_update Fin.snoc_updateₓ'. -/
/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
theorem snoc_update : snoc (update p i y) x = update (snoc p x) i.cast_succ y :=
  by
  ext j
  by_cases h : j.val < n
  · simp only [snoc, h, dif_pos]
    by_cases h' : j = cast_succ i
    · have C1 : α i.cast_succ = α j := by rw [h']
      have E1 : update (snoc p x) i.cast_succ y j = _root_.cast C1 y :=
        by
        have : update (snoc p x) j (_root_.cast C1 y) j = _root_.cast C1 y := by simp
        convert this
        · exact h'.symm
        · exact heq_of_cast_eq (congr_arg α (Eq.symm h')) rfl
      have C2 : α i.cast_succ = α (cast_succ (cast_lt j h)) := by rw [cast_succ_cast_lt, h']
      have E2 : update p i y (cast_lt j h) = _root_.cast C2 y :=
        by
        have : update p (cast_lt j h) (_root_.cast C2 y) (cast_lt j h) = _root_.cast C2 y := by simp
        convert this
        · simp [h, h']
        · exact heq_of_cast_eq C2 rfl
      rw [E1, E2]
      exact eq_rec_compose _ _ _
    · have : ¬cast_lt j h = i := by intro E; apply h'; rw [← E, cast_succ_cast_lt]
      simp [h', this, snoc, h]
  · rw [eq_last_of_not_lt h]
    simp [Ne.symm (ne_of_lt (cast_succ_lt_last i))]
#align fin.snoc_update Fin.snoc_update

/- warning: fin.update_snoc_last -> Fin.update_snoc_last is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)) (z : α (Fin.last n)), Eq.{succ u1} (forall (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α a) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α a) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.snoc.{u1} n α p x) (Fin.last n) z) (Fin.snoc.{u1} n (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α a) p z)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (x : α (Fin.last n)) (p : forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)) (z : α (Fin.last n)), Eq.{succ u1} (forall (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α a) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α a) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (Fin.snoc.{u1} n α p x) (Fin.last n) z) (Fin.snoc.{u1} n α p z)
Case conversion may be inaccurate. Consider using '#align fin.update_snoc_last Fin.update_snoc_lastₓ'. -/
/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z :=
  by
  ext j
  by_cases h : j.val < n
  · have : j ≠ last n := ne_of_lt h
    simp [h, update_noteq, this, snoc]
  · rw [eq_last_of_not_lt h]
    simp
#align fin.update_snoc_last Fin.update_snoc_last

#print Fin.snoc_init_self /-
/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
theorem snoc_init_self : snoc (init q) (q (last n)) = q :=
  by
  ext j
  by_cases h : j.val < n
  · have : j ≠ last n := ne_of_lt h
    simp [h, update_noteq, this, snoc, init, cast_succ_cast_lt]
    have A : cast_succ (cast_lt j h) = j := cast_succ_cast_lt _ _
    rw [← cast_eq rfl (q j)]
    congr 1 <;> rw [A]
  · rw [eq_last_of_not_lt h]
    simp
#align fin.snoc_init_self Fin.snoc_init_self
-/

/- warning: fin.init_update_last -> Fin.init_update_last is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α i) (z : α (Fin.last n)), Eq.{succ u1} (forall (i : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)) (Fin.init.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) q (Fin.last n) z)) (Fin.init.{u1} n α q)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (q : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α i) (z : α (Fin.last n)), Eq.{succ u1} (forall (i : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) i)) (Fin.init.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (Function.update.{1, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) q (Fin.last n) z)) (Fin.init.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α i) q)
Case conversion may be inaccurate. Consider using '#align fin.init_update_last Fin.init_update_lastₓ'. -/
/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
theorem init_update_last : init (update q (last n) z) = init q := by ext j;
  simp [init, ne_of_lt, cast_succ_lt_last]
#align fin.init_update_last Fin.init_update_last

/- warning: fin.init_update_cast_succ -> Fin.init_update_castSucc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.init_update_cast_succ Fin.init_update_castSuccₓ'. -/
/-- Updating an element and taking the beginning commute. -/
@[simp]
theorem init_update_castSucc : init (update q i.cast_succ y) = update (init q) i y :=
  by
  ext j
  by_cases h : j = i
  · rw [h]; simp [init]
  · simp [init, h]
#align fin.init_update_cast_succ Fin.init_update_castSucc

#print Fin.tail_init_eq_init_tail /-
/-- `tail` and `init` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem tail_init_eq_init_tail {β : Type _} (q : Fin (n + 2) → β) : tail (init q) = init (tail q) :=
  by ext i; simp [tail, init, cast_succ_fin_succ]
#align fin.tail_init_eq_init_tail Fin.tail_init_eq_init_tail
-/

#print Fin.cons_snoc_eq_snoc_cons /-
/-- `cons` and `snoc` commute. We state this lemma in a non-dependent setting, as otherwise it
would involve a cast to convince Lean that the two types are equal, making it harder to use. -/
theorem cons_snoc_eq_snoc_cons {β : Type _} (a : β) (q : Fin n → β) (b : β) :
    @cons n.succ (fun i => β) a (snoc q b) = snoc (cons a q) b :=
  by
  ext i
  by_cases h : i = 0
  · rw [h]; rfl
  set j := pred i h with ji
  have : i = j.succ := by rw [ji, succ_pred]
  rw [this, cons_succ]
  by_cases h' : j.val < n
  · set k := cast_lt j h' with jk
    have : j = k.cast_succ := by rw [jk, cast_succ_cast_lt]
    rw [this, ← cast_succ_fin_succ]
    simp
  rw [eq_last_of_not_lt h', succ_last]
  simp
#align fin.cons_snoc_eq_snoc_cons Fin.cons_snoc_eq_snoc_cons
-/

/- warning: fin.comp_snoc -> Fin.comp_snoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (g : α -> β) (q : (Fin n) -> α) (y : α), Eq.{succ u2} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> β) (Function.comp.{1, succ u1, succ u2} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) α β g (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) q y)) (Fin.snoc.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) (Function.comp.{1, succ u1, succ u2} (Fin n) α β g q) (g y))
but is expected to have type
  forall {n : Nat} {α : Type.{u2}} {β : Type.{u1}} (g : α -> β) (q : (Fin n) -> α) (y : α), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> β) (Function.comp.{1, succ u2, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) α β g (Fin.snoc.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) q y)) (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) (Function.comp.{1, succ u2, succ u1} (Fin n) α β g q) (g y))
Case conversion may be inaccurate. Consider using '#align fin.comp_snoc Fin.comp_snocₓ'. -/
theorem comp_snoc {α : Type _} {β : Type _} (g : α → β) (q : Fin n → α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) := by
  ext j
  by_cases h : j.val < n
  · have : j ≠ last n := ne_of_lt h
    simp [h, this, snoc, cast_succ_cast_lt]
  · rw [eq_last_of_not_lt h]
    simp
#align fin.comp_snoc Fin.comp_snoc

/- warning: fin.append_right_eq_snoc -> Fin.append_right_eq_snoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (x : (Fin n) -> α) (x₀ : (Fin (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> α), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (Fin.append.{u1} n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) α x x₀) (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α) x (x₀ (OfNat.ofNat.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (OfNat.mk.{0} (Fin (One.one.{0} Nat Nat.hasOne)) 0 (Zero.zero.{0} (Fin (One.one.{0} Nat Nat.hasOne)) (Fin.hasZeroOfNeZero (One.one.{0} Nat Nat.hasOne) (NeZero.one.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)) Nat.nontrivial)))))))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (x : (Fin n) -> α) (x₀ : (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> α), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (Fin.append.{u1} n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) α x x₀) (Fin.snoc.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) x (x₀ (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align fin.append_right_eq_snoc Fin.append_right_eq_snocₓ'. -/
/-- Appending a one-tuple to the right is the same as `fin.snoc`. -/
theorem append_right_eq_snoc {α : Type _} {n : ℕ} (x : Fin n → α) (x₀ : Fin 1 → α) :
    Fin.append x x₀ = Fin.snoc x (x₀ 0) := by
  ext i
  refine' Fin.addCases _ _ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_cast_succ _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0, Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm
#align fin.append_right_eq_snoc Fin.append_right_eq_snoc

/- warning: fin.comp_init -> Fin.comp_init is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (g : α -> β) (q : (Fin (Nat.succ n)) -> α), Eq.{succ u2} ((Fin n) -> β) (Function.comp.{1, succ u1, succ u2} (Fin n) α β g (Fin.init.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => α) q)) (Fin.init.{u2} n (fun (ᾰ : Fin (Nat.succ n)) => β) (Function.comp.{1, succ u1, succ u2} (Fin (Nat.succ n)) α β g q))
but is expected to have type
  forall {n : Nat} {α : Type.{u2}} {β : Type.{u1}} (g : α -> β) (q : (Fin (Nat.succ n)) -> α), Eq.{succ u1} ((Fin n) -> β) (Function.comp.{1, succ u2, succ u1} (Fin n) α β g (Fin.init.{u2} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α) q)) (Fin.init.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) (Function.comp.{1, succ u2, succ u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) α β g q))
Case conversion may be inaccurate. Consider using '#align fin.comp_init Fin.comp_initₓ'. -/
theorem comp_init {α : Type _} {β : Type _} (g : α → β) (q : Fin n.succ → α) :
    g ∘ init q = init (g ∘ q) := by ext j; simp [init]
#align fin.comp_init Fin.comp_init

end TupleRight

section InsertNth

variable {α : Fin (n + 1) → Type u} {β : Type v}

/- warning: fin.succ_above_cases -> Fin.succAboveCases is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Sort.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), (α i) -> (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Sort.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), (α i) -> (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j)
Case conversion may be inaccurate. Consider using '#align fin.succ_above_cases Fin.succAboveCasesₓ'. -/
/-- Define a function on `fin (n + 1)` from a value on `i : fin (n + 1)` and values on each
`fin.succ_above i j`, `j : fin n`. This version is elaborated as eliminator and works for
propositions, see also `fin.insert_nth` for a version without an `@[elab_as_eliminator]`
attribute. -/
@[elab_as_elim]
def succAboveCases {α : Fin (n + 1) → Sort u} (i : Fin (n + 1)) (x : α i)
    (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) : α j :=
  if hj : j = i then Eq.ndrec x hj.symm
  else
    if hlt : j < i then Eq.recOn (succAbove_castLT hlt) (p _)
    else Eq.recOn (succAbove_pred <| (Ne.lt_or_lt hj).resolve_left hlt) (p _)
#align fin.succ_above_cases Fin.succAboveCases

/- warning: fin.forall_iff_succ_above -> Fin.forall_iff_succAbove is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Prop} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Iff (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), p j) (And (p i) (forall (j : Fin n), p (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)))
but is expected to have type
  forall {n : Nat} {p : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Prop} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Iff (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), p j) (And (p i) (forall (j : Fin n), p (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i) j)))
Case conversion may be inaccurate. Consider using '#align fin.forall_iff_succ_above Fin.forall_iff_succAboveₓ'. -/
theorem forall_iff_succAbove {p : Fin (n + 1) → Prop} (i : Fin (n + 1)) :
    (∀ j, p j) ↔ p i ∧ ∀ j, p (i.succAbove j) :=
  ⟨fun h => ⟨h _, fun j => h _⟩, fun h => succAboveCases i h.1 h.2⟩
#align fin.forall_iff_succ_above Fin.forall_iff_succAbove

/- warning: fin.insert_nth -> Fin.insertNth is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), (α i) -> (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j)
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), (α i) -> (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j)
Case conversion may be inaccurate. Consider using '#align fin.insert_nth Fin.insertNthₓ'. -/
/-- Insert an element into a tuple at a given position. For `i = 0` see `fin.cons`,
for `i = fin.last n` see `fin.snoc`. See also `fin.succ_above_cases` for a version elaborated
as an eliminator. -/
def insertNth (i : Fin (n + 1)) (x : α i) (p : ∀ j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) :
    α j :=
  succAboveCases i x p j
#align fin.insert_nth Fin.insertNth

/- warning: fin.insert_nth_apply_same -> Fin.insertNth_apply_same is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (x : α i) (p : forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)), Eq.{succ u1} (α i) (Fin.insertNth.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) i x p i) x
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x : α i) (p : forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i) j)), Eq.{succ u1} (α i) (Fin.insertNth.{u1} n α i x p i) x
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_apply_same Fin.insertNth_apply_sameₓ'. -/
@[simp]
theorem insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p i = x := by simp [insert_nth, succ_above_cases]
#align fin.insert_nth_apply_same Fin.insertNth_apply_same

/- warning: fin.insert_nth_apply_succ_above -> Fin.insertNth_apply_succAbove is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_apply_succ_above Fin.insertNth_apply_succAboveₓ'. -/
@[simp]
theorem insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j))
    (j : Fin n) : insertNth i x p (i.succAbove j) = p j :=
  by
  simp only [insert_nth, succ_above_cases, dif_neg (succ_above_ne _ _)]
  by_cases hlt : j.cast_succ < i
  · rw [dif_pos ((succ_above_lt_iff _ _).2 hlt)]
    apply eq_of_hEq ((eq_rec_hEq _ _).trans _)
    rw [cast_lt_succ_above hlt]
  · rw [dif_neg (mt (succ_above_lt_iff _ _).1 hlt)]
    apply eq_of_hEq ((eq_rec_hEq _ _).trans _)
    rw [pred_succ_above (le_of_not_lt hlt)]
#align fin.insert_nth_apply_succ_above Fin.insertNth_apply_succAbove

/- warning: fin.succ_above_cases_eq_insert_nth -> Fin.succAbove_cases_eq_insertNth is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} (forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), (α i) -> (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j)) Fin.succAboveCases.{succ u1} Fin.insertNth.{u1}
but is expected to have type
  Eq.{succ (succ u1)} (forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), (α i) -> (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i) j)) -> (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j)) Fin.succAboveCases.{succ u1} Fin.insertNth.{u1}
Case conversion may be inaccurate. Consider using '#align fin.succ_above_cases_eq_insert_nth Fin.succAbove_cases_eq_insertNthₓ'. -/
@[simp]
theorem succAbove_cases_eq_insertNth : @succAboveCases.{u + 1} = @insertNth.{u} :=
  rfl
#align fin.succ_above_cases_eq_insert_nth Fin.succAbove_cases_eq_insertNth

/- warning: fin.insert_nth_comp_succ_above -> Fin.insertNth_comp_succAbove is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {β : Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (x : β) (p : (Fin n) -> β), Eq.{succ u1} ((Fin n) -> β) (Function.comp.{1, 1, succ u1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) β (Fin.insertNth.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) i x p) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i))) p
but is expected to have type
  forall {n : Nat} {β : Type.{u1}} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x : β) (p : (Fin n) -> β), Eq.{succ u1} ((Fin n) -> β) (Function.comp.{1, 1, succ u1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) β (Fin.insertNth.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) i x p) (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n i))) p
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_comp_succ_above Fin.insertNth_comp_succAboveₓ'. -/
@[simp]
theorem insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n → β) :
    insertNth i x p ∘ i.succAbove = p :=
  funext <| insertNth_apply_succAbove i x p
#align fin.insert_nth_comp_succ_above Fin.insertNth_comp_succAbove

/- warning: fin.insert_nth_eq_iff -> Fin.insertNth_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_eq_iff Fin.insertNth_eq_iffₓ'. -/
theorem insertNth_eq_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p = q ↔ q i = x ∧ p = fun j => q (i.succAbove j) := by
  simp [funext_iff, forall_iff_succ_above i, eq_comm]
#align fin.insert_nth_eq_iff Fin.insertNth_eq_iff

/- warning: fin.eq_insert_nth_iff -> Fin.eq_insertNth_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.eq_insert_nth_iff Fin.eq_insertNth_iffₓ'. -/
theorem eq_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q = i.insertNth x p ↔ q i = x ∧ p = fun j => q (i.succAbove j) :=
  eq_comm.trans insertNth_eq_iff
#align fin.eq_insert_nth_iff Fin.eq_insertNth_iff

/- warning: fin.insert_nth_apply_below -> Fin.insertNth_apply_below is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_apply_below Fin.insertNth_apply_belowₓ'. -/
theorem insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = Eq.recOn (succAbove_castLT h) (p <| j.castLT _) := by
  rw [insert_nth, succ_above_cases, dif_neg h.ne, dif_pos h]
#align fin.insert_nth_apply_below Fin.insertNth_apply_below

/- warning: fin.insert_nth_apply_above -> Fin.insertNth_apply_above is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_apply_above Fin.insertNth_apply_aboveₓ'. -/
theorem insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i)
    (p : ∀ k, α (i.succAbove k)) :
    i.insertNth x p j = Eq.recOn (succAbove_pred h) (p <| j.pred _) := by
  rw [insert_nth, succ_above_cases, dif_neg h.ne', dif_neg h.not_lt]
#align fin.insert_nth_apply_above Fin.insertNth_apply_above

/- warning: fin.insert_nth_zero -> Fin.insertNth_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_zero Fin.insertNth_zeroₓ'. -/
theorem insertNth_zero (x : α 0) (p : ∀ j : Fin n, α (succAbove 0 j)) :
    insertNth 0 x p = cons x fun j => cast (congr_arg α (congr_fun succAbove_zero j)) (p j) :=
  by
  refine' insert_nth_eq_iff.2 ⟨by simp, _⟩
  ext j
  convert(cons_succ _ _ _).symm
#align fin.insert_nth_zero Fin.insertNth_zero

/- warning: fin.insert_nth_zero' -> Fin.insertNth_zero' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {β : Type.{u1}} (x : β) (p : (Fin n) -> β), Eq.{succ u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) j) (Fin.insertNth.{u1} n (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) x p) (Fin.cons.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => β) j) x p)
but is expected to have type
  forall {n : Nat} {β : Type.{u1}} (x : β) (p : (Fin n) -> β), Eq.{succ u1} ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> β) (Fin.insertNth.{u1} n (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ n))) x p) (Fin.cons.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => β) x p)
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_zero' Fin.insertNth_zero'ₓ'. -/
@[simp]
theorem insertNth_zero' (x : β) (p : Fin n → β) : @insertNth _ (fun _ => β) 0 x p = cons x p := by
  simp [insert_nth_zero]
#align fin.insert_nth_zero' Fin.insertNth_zero'

/- warning: fin.insert_nth_last -> Fin.insertNth_last is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_last Fin.insertNth_lastₓ'. -/
theorem insertNth_last (x : α (last n)) (p : ∀ j : Fin n, α ((last n).succAbove j)) :
    insertNth (last n) x p = snoc (fun j => cast (congr_arg α (succAbove_last_apply j)) (p j)) x :=
  by
  refine' insert_nth_eq_iff.2 ⟨by simp, _⟩
  ext j
  apply eq_of_hEq
  trans snoc (fun j => _root_.cast (congr_arg α (succ_above_last_apply j)) (p j)) x j.cast_succ
  · rw [snoc_cast_succ]; exact (cast_hEq _ _).symm
  · apply congr_arg_heq
    rw [succ_above_last]
#align fin.insert_nth_last Fin.insertNth_last

#print Fin.insertNth_last' /-
@[simp]
theorem insertNth_last' (x : β) (p : Fin n → β) :
    @insertNth _ (fun _ => β) (last n) x p = snoc p x := by simp [insert_nth_last]
#align fin.insert_nth_last' Fin.insertNth_last'
-/

/- warning: fin.insert_nth_zero_right -> Fin.insertNth_zero_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_zero_right Fin.insertNth_zero_rightₓ'. -/
@[simp]
theorem insertNth_zero_right [∀ j, Zero (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 0 = Pi.single i x :=
  insertNth_eq_iff.2 <| by simp [succ_above_ne, Pi.zero_def]
#align fin.insert_nth_zero_right Fin.insertNth_zero_right

/- warning: fin.insert_nth_binop -> Fin.insertNth_binop is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_binop Fin.insertNth_binopₓ'. -/
theorem insertNth_binop (op : ∀ j, α j → α j → α j) (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j => op _ (p j) (q j)) = fun j =>
      op j (i.insertNth x p j) (i.insertNth y q j) :=
  insertNth_eq_iff.2 <| by simp
#align fin.insert_nth_binop Fin.insertNth_binop

/- warning: fin.insert_nth_mul -> Fin.insertNth_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_mul Fin.insertNth_mulₓ'. -/
@[simp]
theorem insertNth_mul [∀ j, Mul (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insertNth_binop (fun _ => (· * ·)) i x y p q
#align fin.insert_nth_mul Fin.insertNth_mul

/- warning: fin.insert_nth_add -> Fin.insertNth_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_add Fin.insertNth_addₓ'. -/
@[simp]
theorem insertNth_add [∀ j, Add (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x + y) (p + q) = i.insertNth x p + i.insertNth y q :=
  insertNth_binop (fun _ => (· + ·)) i x y p q
#align fin.insert_nth_add Fin.insertNth_add

/- warning: fin.insert_nth_div -> Fin.insertNth_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_div Fin.insertNth_divₓ'. -/
@[simp]
theorem insertNth_div [∀ j, Div (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insertNth_binop (fun _ => (· / ·)) i x y p q
#align fin.insert_nth_div Fin.insertNth_div

/- warning: fin.insert_nth_sub -> Fin.insertNth_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_sub Fin.insertNth_subₓ'. -/
@[simp]
theorem insertNth_sub [∀ j, Sub (α j)] (i : Fin (n + 1)) (x y : α i)
    (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x - y) (p - q) = i.insertNth x p - i.insertNth y q :=
  insertNth_binop (fun _ => Sub.sub) i x y p q
#align fin.insert_nth_sub Fin.insertNth_sub

/- warning: fin.insert_nth_sub_same -> Fin.insertNth_sub_same is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_sub_same Fin.insertNth_sub_sameₓ'. -/
@[simp]
theorem insertNth_sub_same [∀ j, AddGroup (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p - i.insertNth y p = Pi.single i (x - y) := by
  simp_rw [← insert_nth_sub, ← insert_nth_zero_right, Pi.sub_def, sub_self, Pi.zero_def]
#align fin.insert_nth_sub_same Fin.insertNth_sub_same

variable [∀ i, Preorder (α i)]

/- warning: fin.insert_nth_le_iff -> Fin.insertNth_le_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_le_iff Fin.insertNth_le_iffₓ'. -/
theorem insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    i.insertNth x p ≤ q ↔ x ≤ q i ∧ p ≤ fun j => q (i.succAbove j) := by
  simp [Pi.le_def, forall_iff_succ_above i]
#align fin.insert_nth_le_iff Fin.insertNth_le_iff

/- warning: fin.le_insert_nth_iff -> Fin.le_insertNth_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.le_insert_nth_iff Fin.le_insertNth_iffₓ'. -/
theorem le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)} {q : ∀ j, α j} :
    q ≤ i.insertNth x p ↔ q i ≤ x ∧ (fun j => q (i.succAbove j)) ≤ p := by
  simp [Pi.le_def, forall_iff_succ_above i]
#align fin.le_insert_nth_iff Fin.le_insertNth_iff

open Set

/- warning: fin.insert_nth_mem_Icc -> Fin.insertNth_mem_Icc is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.insert_nth_mem_Icc Fin.insertNth_mem_Iccₓ'. -/
theorem insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : ∀ j, α (i.succAbove j)}
    {q₁ q₂ : ∀ j, α j} :
    i.insertNth x p ∈ Icc q₁ q₂ ↔
      x ∈ Icc (q₁ i) (q₂ i) ∧ p ∈ Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) :=
  by simp only [mem_Icc, insert_nth_le_iff, le_insert_nth_iff, and_assoc, and_left_comm]
#align fin.insert_nth_mem_Icc Fin.insertNth_mem_Icc

/- warning: fin.preimage_insert_nth_Icc_of_mem -> Fin.preimage_insertNth_Icc_of_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.preimage_insert_nth_Icc_of_mem Fin.preimage_insertNth_Icc_of_memₓ'. -/
theorem preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∈ Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) :=
  Set.ext fun p => by simp only [mem_preimage, insert_nth_mem_Icc, hx, true_and_iff]
#align fin.preimage_insert_nth_Icc_of_mem Fin.preimage_insertNth_Icc_of_mem

/- warning: fin.preimage_insert_nth_Icc_of_not_mem -> Fin.preimage_insertNth_Icc_of_not_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fin.preimage_insert_nth_Icc_of_not_mem Fin.preimage_insertNth_Icc_of_not_memₓ'. -/
theorem preimage_insertNth_Icc_of_not_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : ∀ j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p => by
    simp only [mem_preimage, insert_nth_mem_Icc, hx, false_and_iff, mem_empty_iff_false]
#align fin.preimage_insert_nth_Icc_of_not_mem Fin.preimage_insertNth_Icc_of_not_mem

end InsertNth

section Find

#print Fin.find /-
/-- `find p` returns the first index `n` where `p n` is satisfied, and `none` if it is never
satisfied. -/
def find : ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p], Option (Fin n)
  | 0, p, _ => none
  | n + 1, p, _ => by
    skip <;>
      exact
        Option.casesOn (@find n (fun i => p (i.castLT (Nat.lt_succ_of_lt i.2))) _)
          (if h : p (Fin.last n) then some (Fin.last n) else none) fun i =>
          some (i.castLT (Nat.lt_succ_of_lt i.2))
#align fin.find Fin.find
-/

#print Fin.find_spec /-
/-- If `find p = some i`, then `p i` holds -/
theorem find_spec :
    ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p] {i : Fin n} (hi : i ∈ Fin.find p), p i
  | 0, p, I, i, hi => Option.noConfusion hi
  | n + 1, p, I, i, hi => by
    dsimp [find] at hi
    skip
    cases' h : find fun i : Fin n => p (i.castLT (Nat.lt_succ_of_lt i.2)) with j
    · rw [h] at hi
      dsimp at hi
      split_ifs  at hi with hl hl
      · exact hi ▸ hl
      · exact hi.elim
    · rw [h] at hi
      rw [← Option.some_inj.1 hi]
      exact find_spec _ h
#align fin.find_spec Fin.find_spec
-/

#print Fin.isSome_find_iff /-
/-- `find p` does not return `none` if and only if `p i` holds at some index `i`. -/
theorem isSome_find_iff : ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p], (find p).isSome ↔ ∃ i, p i
  | 0, p, _ => iff_of_false (fun h => Bool.noConfusion h) fun ⟨i, _⟩ => finZeroElim i
  | n + 1, p, _ =>
    ⟨fun h => by
      rw [Option.isSome_iff_exists] at h
      cases' h with i hi
      exact ⟨i, find_spec _ hi⟩, fun ⟨⟨i, hin⟩, hi⟩ =>
      by
      skip
      dsimp [find]
      cases' h : find fun i : Fin n => p (i.castLT (Nat.lt_succ_of_lt i.2)) with j
      · split_ifs with hl hl
        · exact Option.isSome_some
        · have :=
            (@is_some_find_iff n (fun x => p (x.castLT (Nat.lt_succ_of_lt x.2))) _).2
              ⟨⟨i,
                  lt_of_le_of_ne (Nat.le_of_lt_succ hin) fun h => by
                    clear_aux_decl <;> cases h <;> exact hl hi⟩,
                hi⟩
          rw [h] at this
          exact this
      · simp⟩
#align fin.is_some_find_iff Fin.isSome_find_iff
-/

#print Fin.find_eq_none_iff /-
/-- `find p` returns `none` if and only if `p i` never holds. -/
theorem find_eq_none_iff {n : ℕ} {p : Fin n → Prop} [DecidablePred p] : find p = none ↔ ∀ i, ¬p i :=
  by rw [← not_exists, ← is_some_find_iff] <;> cases find p <;> simp
#align fin.find_eq_none_iff Fin.find_eq_none_iff
-/

#print Fin.find_min /-
/-- If `find p` returns `some i`, then `p j` does not hold for `j < i`, i.e., `i` is minimal among
the indices where `p` holds. -/
theorem find_min :
    ∀ {n : ℕ} {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (hi : i ∈ Fin.find p) {j : Fin n}
      (hj : j < i), ¬p j
  | 0, p, _, i, hi, j, hj, hpj => Option.noConfusion hi
  | n + 1, p, _, i, hi, ⟨j, hjn⟩, hj, hpj => by
    skip
    dsimp [find] at hi
    cases' h : find fun i : Fin n => p (i.castLT (Nat.lt_succ_of_lt i.2)) with k
    · rw [h] at hi
      split_ifs  at hi with hl hl
      · subst hi
        rw [find_eq_none_iff] at h
        exact h ⟨j, hj⟩ hpj
      · exact hi.elim
    · rw [h] at hi
      dsimp at hi
      obtain rfl := Option.some_inj.1 hi
      exact find_min h (show (⟨j, lt_trans hj k.2⟩ : Fin n) < k from hj) hpj
#align fin.find_min Fin.find_min
-/

#print Fin.find_min' /-
theorem find_min' {p : Fin n → Prop} [DecidablePred p] {i : Fin n} (h : i ∈ Fin.find p) {j : Fin n}
    (hj : p j) : i ≤ j :=
  le_of_not_gt fun hij => find_min h hij hj
#align fin.find_min' Fin.find_min'
-/

/- warning: fin.nat_find_mem_find -> Fin.nat_find_mem_find is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {p : (Fin n) -> Prop} [_inst_1 : DecidablePred.{1} (Fin n) p] (h : Exists.{1} Nat (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin)))), Membership.Mem.{0, 0} (Fin n) (Option.{0} (Fin n)) (Option.hasMem.{0} (Fin n)) (Fin.mk n (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin))) (fun (a : Nat) => existsPropDecidable (LT.lt.{0} Nat Nat.hasLt a n) (fun (hin : LT.lt.{0} Nat Nat.hasLt a n) => p (Fin.mk n a hin)) (Nat.decidableLt a n) (fun (h : LT.lt.{0} Nat Nat.hasLt a n) => _inst_1 (Fin.mk n a h))) h) (Exists.fst (LT.lt.{0} Nat Nat.hasLt (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin))) (fun (a : Nat) => existsPropDecidable (LT.lt.{0} Nat Nat.hasLt a n) (fun (hin : LT.lt.{0} Nat Nat.hasLt a n) => p (Fin.mk n a hin)) (Nat.decidableLt a n) (fun (h : LT.lt.{0} Nat Nat.hasLt a n) => _inst_1 (Fin.mk n a h))) h) n) (fun (hin : LT.lt.{0} Nat Nat.hasLt (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin))) (fun (a : Nat) => existsPropDecidable (LT.lt.{0} Nat Nat.hasLt a n) (fun (hin : LT.lt.{0} Nat Nat.hasLt a n) => p (Fin.mk n a hin)) (Nat.decidableLt a n) (fun (h : LT.lt.{0} Nat Nat.hasLt a n) => _inst_1 (Fin.mk n a h))) h) n) => p (Fin.mk n (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin))) (fun (a : Nat) => existsPropDecidable (LT.lt.{0} Nat Nat.hasLt a n) (fun (hin : LT.lt.{0} Nat Nat.hasLt a n) => p (Fin.mk n a hin)) (Nat.decidableLt a n) (fun (h : LT.lt.{0} Nat Nat.hasLt a n) => _inst_1 (Fin.mk n a h))) h) hin)) (Nat.find_spec (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat Nat.hasLt i n) (fun (hin : LT.lt.{0} Nat Nat.hasLt i n) => p (Fin.mk n i hin))) (fun (a : Nat) => existsPropDecidable (LT.lt.{0} Nat Nat.hasLt a n) (fun (hin : LT.lt.{0} Nat Nat.hasLt a n) => p (Fin.mk n a hin)) (Nat.decidableLt a n) (fun (h : LT.lt.{0} Nat Nat.hasLt a n) => _inst_1 (Fin.mk n a h))) h))) (Fin.find n p (fun (a : Fin n) => _inst_1 a))
but is expected to have type
  forall {n : Nat} {p : (Fin n) -> Prop} [_inst_1 : DecidablePred.{1} (Fin n) p] (h : Exists.{1} Nat (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin)))), Membership.mem.{0, 0} (Fin n) (Option.{0} (Fin n)) (Option.instMembershipOption.{0} (Fin n)) (Fin.mk n (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin))) (fun (a : Nat) => exists_prop_decidable (LT.lt.{0} Nat instLTNat a n) (fun (hin : LT.lt.{0} Nat instLTNat a n) => p (Fin.mk n a hin)) (Nat.decLt a n) (fun (h : LT.lt.{0} Nat instLTNat a n) => _inst_1 (Fin.mk n a h))) h) (Exists.fst (LT.lt.{0} Nat instLTNat (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin))) (fun (a : Nat) => exists_prop_decidable (LT.lt.{0} Nat instLTNat a n) (fun (hin : LT.lt.{0} Nat instLTNat a n) => p (Fin.mk n a hin)) (Nat.decLt a n) (fun (h : LT.lt.{0} Nat instLTNat a n) => _inst_1 (Fin.mk n a h))) h) n) (fun (hin : LT.lt.{0} Nat instLTNat (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin))) (fun (a : Nat) => exists_prop_decidable (LT.lt.{0} Nat instLTNat a n) (fun (hin : LT.lt.{0} Nat instLTNat a n) => p (Fin.mk n a hin)) (Nat.decLt a n) (fun (h : LT.lt.{0} Nat instLTNat a n) => _inst_1 (Fin.mk n a h))) h) n) => p (Fin.mk n (Nat.find (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin))) (fun (a : Nat) => exists_prop_decidable (LT.lt.{0} Nat instLTNat a n) (fun (hin : LT.lt.{0} Nat instLTNat a n) => p (Fin.mk n a hin)) (Nat.decLt a n) (fun (h : LT.lt.{0} Nat instLTNat a n) => _inst_1 (Fin.mk n a h))) h) hin)) (Nat.find_spec (fun (i : Nat) => Exists.{0} (LT.lt.{0} Nat instLTNat i n) (fun (hin : LT.lt.{0} Nat instLTNat i n) => p (Fin.mk n i hin))) (fun (a : Nat) => exists_prop_decidable (LT.lt.{0} Nat instLTNat a n) (fun (hin : LT.lt.{0} Nat instLTNat a n) => p (Fin.mk n a hin)) (Nat.decLt a n) (fun (h : LT.lt.{0} Nat instLTNat a n) => _inst_1 (Fin.mk n a h))) h))) (Fin.find n p (fun (a : Fin n) => _inst_1 a))
Case conversion may be inaccurate. Consider using '#align fin.nat_find_mem_find Fin.nat_find_mem_findₓ'. -/
theorem nat_find_mem_find {p : Fin n → Prop} [DecidablePred p]
    (h : ∃ i, ∃ hin : i < n, p ⟨i, hin⟩) : (⟨Nat.find h, (Nat.find_spec h).fst⟩ : Fin n) ∈ find p :=
  by
  let ⟨i, hin, hi⟩ := h
  cases' hf : find p with f
  · rw [find_eq_none_iff] at hf
    exact (hf ⟨i, hin⟩ hi).elim
  · refine' Option.some_inj.2 (le_antisymm _ _)
    · exact find_min' hf (Nat.find_spec h).snd
    · exact Nat.find_min' _ ⟨f.2, by convert find_spec p hf <;> exact Fin.eta _ _⟩
#align fin.nat_find_mem_find Fin.nat_find_mem_find

#print Fin.mem_find_iff /-
theorem mem_find_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    i ∈ Fin.find p ↔ p i ∧ ∀ j, p j → i ≤ j :=
  ⟨fun hi => ⟨find_spec _ hi, fun _ => find_min' hi⟩,
    by
    rintro ⟨hpi, hj⟩
    cases hfp : Fin.find p
    · rw [find_eq_none_iff] at hfp
      exact (hfp _ hpi).elim
    · exact Option.some_inj.2 (le_antisymm (find_min' hfp hpi) (hj _ (find_spec _ hfp)))⟩
#align fin.mem_find_iff Fin.mem_find_iff
-/

#print Fin.find_eq_some_iff /-
theorem find_eq_some_iff {p : Fin n → Prop} [DecidablePred p] {i : Fin n} :
    Fin.find p = some i ↔ p i ∧ ∀ j, p j → i ≤ j :=
  mem_find_iff
#align fin.find_eq_some_iff Fin.find_eq_some_iff
-/

#print Fin.mem_find_of_unique /-
theorem mem_find_of_unique {p : Fin n → Prop} [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    {i : Fin n} (hi : p i) : i ∈ Fin.find p :=
  mem_find_iff.2 ⟨hi, fun j hj => le_of_eq <| h i j hi hj⟩
#align fin.mem_find_of_unique Fin.mem_find_of_unique
-/

end Find

section ContractNth

variable {α : Type _}

#print Fin.contractNth /-
/-- Sends `(g₀, ..., gₙ)` to `(g₀, ..., op gⱼ gⱼ₊₁, ..., gₙ)`. -/
def contractNth (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n) : α :=
  if (k : ℕ) < j then g k.cast_succ
  else if (k : ℕ) = j then op (g k.cast_succ) (g k.succ) else g k.succ
#align fin.contract_nth Fin.contractNth
-/

/- warning: fin.contract_nth_apply_of_lt -> Fin.contractNth_apply_of_lt is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (k : Fin n), (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) k) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (HasLiftT.mk.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (CoeTCₓ.coe.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (coeBase.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (Fin.coeToNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) j)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (g (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) k)))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (k : Fin n), (LT.lt.{0} Nat instLTNat (Fin.val n k) (Fin.val (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (g (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) k)))
Case conversion may be inaccurate. Consider using '#align fin.contract_nth_apply_of_lt Fin.contractNth_apply_of_ltₓ'. -/
theorem contractNth_apply_of_lt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) < j) : contractNth j op g k = g k.cast_succ :=
  if_pos h
#align fin.contract_nth_apply_of_lt Fin.contractNth_apply_of_lt

/- warning: fin.contract_nth_apply_of_eq -> Fin.contractNth_apply_of_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (k : Fin n), (Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) k) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (HasLiftT.mk.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (CoeTCₓ.coe.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (coeBase.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (Fin.coeToNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) j)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (op (g (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) k)) (g (Fin.succ n k))))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (k : Fin n), (Eq.{1} Nat (Fin.val n k) (Fin.val (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (op (g (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.castSucc n) k)) (g (Fin.succ n k))))
Case conversion may be inaccurate. Consider using '#align fin.contract_nth_apply_of_eq Fin.contractNth_apply_of_eqₓ'. -/
theorem contractNth_apply_of_eq (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (k : ℕ) = j) : contractNth j op g k = op (g k.cast_succ) (g k.succ) :=
  by
  have : ¬(k : ℕ) < j := not_lt.2 (le_of_eq h.symm)
  rw [contract_nth, if_neg this, if_pos h]
#align fin.contract_nth_apply_of_eq Fin.contractNth_apply_of_eq

#print Fin.contractNth_apply_of_gt /-
theorem contractNth_apply_of_gt (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (h : (j : ℕ) < k) : contractNth j op g k = g k.succ := by
  rw [contract_nth, if_neg (not_lt_of_gt h), if_neg (Ne.symm <| ne_of_lt h)]
#align fin.contract_nth_apply_of_gt Fin.contractNth_apply_of_gt
-/

/- warning: fin.contract_nth_apply_of_ne -> Fin.contractNth_apply_of_ne is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (k : Fin n), (Ne.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (HasLiftT.mk.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (CoeTCₓ.coe.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (coeBase.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (Fin.coeToNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) j) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) k)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (g (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n j) k)))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (op : α -> α -> α) (g : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (k : Fin n), (Ne.{1} Nat (Fin.val (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j) (Fin.val n k)) -> (Eq.{succ u1} α (Fin.contractNth.{u1} n α j op g k) (g (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (RelHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (Fin.succAbove n j) k)))
Case conversion may be inaccurate. Consider using '#align fin.contract_nth_apply_of_ne Fin.contractNth_apply_of_neₓ'. -/
theorem contractNth_apply_of_ne (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n)
    (hjk : (j : ℕ) ≠ k) : contractNth j op g k = g (j.succAbove k) :=
  by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [j.succ_above_below, contract_nth_apply_of_lt]
    · rwa [Fin.lt_iff_val_lt_val]
  · exact False.elim (hjk h.symm)
  · rwa [j.succ_above_above, contract_nth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)
#align fin.contract_nth_apply_of_ne Fin.contractNth_apply_of_ne

end ContractNth

/- warning: fin.sigma_eq_of_eq_comp_cast -> Fin.sigma_eq_of_eq_comp_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} {b : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} (h : Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)), (Eq.{succ u1} ((Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> α) (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Function.comp.{1, 1, succ u1} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) α (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) (coeFn.{1, 1} (OrderIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b))) (fun (_x : RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a))) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)))) => (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b))) (RelIso.hasCoeToFun.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a))) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)))) (Fin.cast (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) h)))) -> (Eq.{succ u1} (Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)) a b)
but is expected to have type
  forall {α : Type.{u1}} {a : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} {b : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} (h : Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)), (Eq.{succ u1} ((Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> α) (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Function.comp.{1, 1, succ u1} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) α (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (fun (_x : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) (Fin.cast (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) h)))) -> (Eq.{succ u1} (Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)) a b)
Case conversion may be inaccurate. Consider using '#align fin.sigma_eq_of_eq_comp_cast Fin.sigma_eq_of_eq_comp_castₓ'. -/
/-- To show two sigma pairs of tuples agree, it to show the second elements are related via
`fin.cast`. -/
theorem sigma_eq_of_eq_comp_cast {α : Type _} :
    ∀ {a b : Σii, Fin ii → α} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.cast h → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    subst hi
    simpa using h
#align fin.sigma_eq_of_eq_comp_cast Fin.sigma_eq_of_eq_comp_cast

/- warning: fin.sigma_eq_iff_eq_comp_cast -> Fin.sigma_eq_iff_eq_comp_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} {b : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)}, Iff (Eq.{succ u1} (Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)) a b) (Exists.{0} (Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (h : Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => Eq.{succ u1} ((Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> α) (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Function.comp.{1, 1, succ u1} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) α (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) (coeFn.{1, 1} (OrderIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b))) (fun (_x : RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a))) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)))) => (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b))) (RelIso.hasCoeToFun.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a))) (LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (Fin.hasLe (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)))) (Fin.cast (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) h)))))
but is expected to have type
  forall {α : Type.{u1}} {a : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)} {b : Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)}, Iff (Eq.{succ u1} (Sigma.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α)) a b) (Exists.{0} (Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (h : Eq.{1} Nat (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => Eq.{succ u1} ((Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) -> α) (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Function.comp.{1, 1, succ u1} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) α (Sigma.snd.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (fun (_x : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{0, 0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a)) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) => LE.le.{0} (Fin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) (instLEFin (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b)) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) (Fin.cast (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) a) (Sigma.fst.{0, u1} Nat (fun (ii : Nat) => (Fin ii) -> α) b) h)))))
Case conversion may be inaccurate. Consider using '#align fin.sigma_eq_iff_eq_comp_cast Fin.sigma_eq_iff_eq_comp_castₓ'. -/
/-- `fin.sigma_eq_of_eq_comp_cast` as an `iff`. -/
theorem sigma_eq_iff_eq_comp_cast {α : Type _} {a b : Σii, Fin ii → α} :
    a = b ↔ ∃ h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast h :=
  ⟨fun h => h ▸ ⟨rfl, funext <| Fin.rec fun i hi => rfl⟩, fun ⟨h, h'⟩ =>
    sigma_eq_of_eq_comp_cast _ h'⟩
#align fin.sigma_eq_iff_eq_comp_cast Fin.sigma_eq_iff_eq_comp_cast

end Fin

