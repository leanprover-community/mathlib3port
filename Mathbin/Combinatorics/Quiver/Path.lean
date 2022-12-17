/-
Copyright (c) 2021 David Wärn,. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison

! This file was ported from Lean 3 source module combinatorics.quiver.path
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.Quiver.Basic
import Mathbin.Logic.Lemmas

/-!
# Paths in quivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/811
> Any changes to this file require a corresponding PR to mathlib4.

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/


open Function

universe v v₁ v₂ u u₁ u₂

namespace Quiver

#print Quiver.Path /-
/-- `G.path a b` is the type of paths from `a` to `b` through the arrows of `G`. -/
inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Sort max (u + 1) v
  | nil : path a
  | cons : ∀ {b c : V}, path b → (b ⟶ c) → path c
#align quiver.path Quiver.Path
-/

#print Quiver.Hom.toPath /-
/-- An arrow viewed as a path of length one. -/
def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e
#align quiver.hom.to_path Quiver.Hom.toPath
-/

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

/- warning: quiver.path.nil_ne_cons -> Quiver.Path.nil_ne_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) (e : Quiver.Hom.{u2, u1} V _inst_1 b a), Ne.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a a) (Quiver.Path.nil.{u2, u1} V _inst_1 a) (Quiver.Path.cons.{u2, u1} V _inst_1 a b a p e)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) (e : Quiver.Hom.{u1, u2} V _inst_1 b a), Ne.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a a) (Quiver.Path.nil.{u1, u2} V _inst_1 a) (Quiver.Path.cons.{u1, u2} V _inst_1 a b a p e)
Case conversion may be inaccurate. Consider using '#align quiver.path.nil_ne_cons Quiver.Path.nil_ne_consₓ'. -/
theorem nil_ne_cons (p : Path a b) (e : b ⟶ a) : path.nil ≠ p.cons e :=
  fun.
#align quiver.path.nil_ne_cons Quiver.Path.nil_ne_cons

/- warning: quiver.path.cons_ne_nil -> Quiver.Path.cons_ne_nil is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) (e : Quiver.Hom.{u2, u1} V _inst_1 b a), Ne.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a a) (Quiver.Path.cons.{u2, u1} V _inst_1 a b a p e) (Quiver.Path.nil.{u2, u1} V _inst_1 a)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) (e : Quiver.Hom.{u1, u2} V _inst_1 b a), Ne.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a a) (Quiver.Path.cons.{u1, u2} V _inst_1 a b a p e) (Quiver.Path.nil.{u1, u2} V _inst_1 a)
Case conversion may be inaccurate. Consider using '#align quiver.path.cons_ne_nil Quiver.Path.cons_ne_nilₓ'. -/
theorem cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e ≠ path.nil :=
  fun.
#align quiver.path.cons_ne_nil Quiver.Path.cons_ne_nil

/- warning: quiver.path.obj_eq_of_cons_eq_cons -> Quiver.Path.obj_eq_of_cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u2, u1} V _inst_1 a b} {p' : Quiver.Path.{u2, u1} V _inst_1 a c} {e : Quiver.Hom.{u2, u1} V _inst_1 b d} {e' : Quiver.Hom.{u2, u1} V _inst_1 c d}, (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a d) (Quiver.Path.cons.{u2, u1} V _inst_1 a b d p e) (Quiver.Path.cons.{u2, u1} V _inst_1 a c d p' e')) -> (Eq.{succ u1} V b c)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u1, u2} V _inst_1 a b} {p' : Quiver.Path.{u1, u2} V _inst_1 a c} {e : Quiver.Hom.{u1, u2} V _inst_1 b d} {e' : Quiver.Hom.{u1, u2} V _inst_1 c d}, (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a d) (Quiver.Path.cons.{u1, u2} V _inst_1 a b d p e) (Quiver.Path.cons.{u1, u2} V _inst_1 a c d p' e')) -> (Eq.{succ u2} V b c)
Case conversion may be inaccurate. Consider using '#align quiver.path.obj_eq_of_cons_eq_cons Quiver.Path.obj_eq_of_cons_eq_consₓ'. -/
theorem obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d}
    (h : p.cons e = p'.cons e') : b = c := by injection h
#align quiver.path.obj_eq_of_cons_eq_cons Quiver.Path.obj_eq_of_cons_eq_cons

/- warning: quiver.path.heq_of_cons_eq_cons -> Quiver.Path.heq_of_cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u2, u1} V _inst_1 a b} {p' : Quiver.Path.{u2, u1} V _inst_1 a c} {e : Quiver.Hom.{u2, u1} V _inst_1 b d} {e' : Quiver.Hom.{u2, u1} V _inst_1 c d}, (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a d) (Quiver.Path.cons.{u2, u1} V _inst_1 a b d p e) (Quiver.Path.cons.{u2, u1} V _inst_1 a c d p' e')) -> (HEq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) p (Quiver.Path.{u2, u1} V _inst_1 a c) p')
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u1, u2} V _inst_1 a b} {p' : Quiver.Path.{u1, u2} V _inst_1 a c} {e : Quiver.Hom.{u1, u2} V _inst_1 b d} {e' : Quiver.Hom.{u1, u2} V _inst_1 c d}, (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a d) (Quiver.Path.cons.{u1, u2} V _inst_1 a b d p e) (Quiver.Path.cons.{u1, u2} V _inst_1 a c d p' e')) -> (HEq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) p (Quiver.Path.{u1, u2} V _inst_1 a c) p')
Case conversion may be inaccurate. Consider using '#align quiver.path.heq_of_cons_eq_cons Quiver.Path.heq_of_cons_eq_consₓ'. -/
theorem heq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d}
    (h : p.cons e = p'.cons e') : HEq p p' := by injection h
#align quiver.path.heq_of_cons_eq_cons Quiver.Path.heq_of_cons_eq_cons

/- warning: quiver.path.hom_heq_of_cons_eq_cons -> Quiver.Path.hom_heq_of_cons_eq_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u2, u1} V _inst_1 a b} {p' : Quiver.Path.{u2, u1} V _inst_1 a c} {e : Quiver.Hom.{u2, u1} V _inst_1 b d} {e' : Quiver.Hom.{u2, u1} V _inst_1 c d}, (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a d) (Quiver.Path.cons.{u2, u1} V _inst_1 a b d p e) (Quiver.Path.cons.{u2, u1} V _inst_1 a c d p' e')) -> (HEq.{u2} (Quiver.Hom.{u2, u1} V _inst_1 b d) e (Quiver.Hom.{u2, u1} V _inst_1 c d) e')
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {d : V} {p : Quiver.Path.{u1, u2} V _inst_1 a b} {p' : Quiver.Path.{u1, u2} V _inst_1 a c} {e : Quiver.Hom.{u1, u2} V _inst_1 b d} {e' : Quiver.Hom.{u1, u2} V _inst_1 c d}, (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a d) (Quiver.Path.cons.{u1, u2} V _inst_1 a b d p e) (Quiver.Path.cons.{u1, u2} V _inst_1 a c d p' e')) -> (HEq.{u1} (Quiver.Hom.{u1, u2} V _inst_1 b d) e (Quiver.Hom.{u1, u2} V _inst_1 c d) e')
Case conversion may be inaccurate. Consider using '#align quiver.path.hom_heq_of_cons_eq_cons Quiver.Path.hom_heq_of_cons_eq_consₓ'. -/
theorem hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c} {e : b ⟶ d} {e' : c ⟶ d}
    (h : p.cons e = p'.cons e') : HEq e e' := by injection h
#align quiver.path.hom_heq_of_cons_eq_cons Quiver.Path.hom_heq_of_cons_eq_cons

#print Quiver.Path.length /-
/-- The length of a path is the number of arrows it uses. -/
def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, path.nil => 0
  | _, path.cons p _ => p.length + 1
#align quiver.path.length Quiver.Path.length
-/

instance {a : V} : Inhabited (Path a a) :=
  ⟨Path.nil⟩

/- warning: quiver.path.length_nil -> Quiver.Path.length_nil is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V}, Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 a a (Quiver.Path.nil.{u2, u1} V _inst_1 a)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V}, Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 a a (Quiver.Path.nil.{u1, u2} V _inst_1 a)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align quiver.path.length_nil Quiver.Path.length_nilₓ'. -/
@[simp]
theorem length_nil {a : V} : (Path.nil : Path a a).length = 0 :=
  rfl
#align quiver.path.length_nil Quiver.Path.length_nil

/- warning: quiver.path.length_cons -> Quiver.Path.length_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] (a : V) (b : V) (c : V) (p : Quiver.Path.{u2, u1} V _inst_1 a b) (e : Quiver.Hom.{u2, u1} V _inst_1 b c), Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 a c (Quiver.Path.cons.{u2, u1} V _inst_1 a b c p e)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Quiver.Path.length.{u1, u2} V _inst_1 a b p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] (a : V) (b : V) (c : V) (p : Quiver.Path.{u1, u2} V _inst_1 a b) (e : Quiver.Hom.{u1, u2} V _inst_1 b c), Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 a c (Quiver.Path.cons.{u1, u2} V _inst_1 a b c p e)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Quiver.Path.length.{u2, u1} V _inst_1 a b p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align quiver.path.length_cons Quiver.Path.length_consₓ'. -/
@[simp]
theorem length_cons (a b c : V) (p : Path a b) (e : b ⟶ c) : (p.cons e).length = p.length + 1 :=
  rfl
#align quiver.path.length_cons Quiver.Path.length_cons

/- warning: quiver.path.eq_of_length_zero -> Quiver.Path.eq_of_length_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b), (Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 a b p) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} V a b)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b), (Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 a b p) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u2} V a b)
Case conversion may be inaccurate. Consider using '#align quiver.path.eq_of_length_zero Quiver.Path.eq_of_length_zeroₓ'. -/
theorem eq_of_length_zero (p : Path a b) (hzero : p.length = 0) : a = b := by
  cases p
  · rfl
  · cases Nat.succ_ne_zero _ hzero
#align quiver.path.eq_of_length_zero Quiver.Path.eq_of_length_zero

#print Quiver.Path.comp /-
/-- Composition of paths. -/
def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
  | _, p, path.nil => p
  | _, p, path.cons q e => (p.comp q).cons e
#align quiver.path.comp Quiver.Path.comp
-/

/- warning: quiver.path.comp_cons -> Quiver.Path.comp_cons is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {d : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) (q : Quiver.Path.{u2, u1} V _inst_1 b c) (e : Quiver.Hom.{u2, u1} V _inst_1 c d), Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a d) (Quiver.Path.comp.{u1, u2} V _inst_1 a b d p (Quiver.Path.cons.{u2, u1} V _inst_1 b c d q e)) (Quiver.Path.cons.{u2, u1} V _inst_1 a c d (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q) e)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {d : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) (q : Quiver.Path.{u1, u2} V _inst_1 b c) (e : Quiver.Hom.{u1, u2} V _inst_1 c d), Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a d) (Quiver.Path.comp.{u2, u1} V _inst_1 a b d p (Quiver.Path.cons.{u1, u2} V _inst_1 b c d q e)) (Quiver.Path.cons.{u1, u2} V _inst_1 a c d (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q) e)
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_cons Quiver.Path.comp_consₓ'. -/
@[simp]
theorem comp_cons {a b c d : V} (p : Path a b) (q : Path b c) (e : c ⟶ d) :
    p.comp (q.cons e) = (p.comp q).cons e :=
  rfl
#align quiver.path.comp_cons Quiver.Path.comp_cons

/- warning: quiver.path.comp_nil -> Quiver.Path.comp_nil is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b), Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) (Quiver.Path.comp.{u1, u2} V _inst_1 a b b p (Quiver.Path.nil.{u2, u1} V _inst_1 b)) p
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b), Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) (Quiver.Path.comp.{u2, u1} V _inst_1 a b b p (Quiver.Path.nil.{u1, u2} V _inst_1 b)) p
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_nil Quiver.Path.comp_nilₓ'. -/
@[simp]
theorem comp_nil {a b : V} (p : Path a b) : p.comp Path.nil = p :=
  rfl
#align quiver.path.comp_nil Quiver.Path.comp_nil

/- warning: quiver.path.nil_comp -> Quiver.Path.nil_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b), Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) (Quiver.Path.comp.{u1, u2} V _inst_1 a a b (Quiver.Path.nil.{u2, u1} V _inst_1 a) p) p
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b), Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) (Quiver.Path.comp.{u2, u1} V _inst_1 a a b (Quiver.Path.nil.{u1, u2} V _inst_1 a) p) p
Case conversion may be inaccurate. Consider using '#align quiver.path.nil_comp Quiver.Path.nil_compₓ'. -/
@[simp]
theorem nil_comp {a : V} : ∀ {b} (p : Path a b), Path.nil.comp p = p
  | a, path.nil => rfl
  | b, path.cons p e => by rw [comp_cons, nil_comp]
#align quiver.path.nil_comp Quiver.Path.nil_comp

/- warning: quiver.path.comp_assoc -> Quiver.Path.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {d : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) (q : Quiver.Path.{u2, u1} V _inst_1 b c) (r : Quiver.Path.{u2, u1} V _inst_1 c d), Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a d) (Quiver.Path.comp.{u1, u2} V _inst_1 a c d (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q) r) (Quiver.Path.comp.{u1, u2} V _inst_1 a b d p (Quiver.Path.comp.{u1, u2} V _inst_1 b c d q r))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {d : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) (q : Quiver.Path.{u1, u2} V _inst_1 b c) (r : Quiver.Path.{u1, u2} V _inst_1 c d), Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a d) (Quiver.Path.comp.{u2, u1} V _inst_1 a c d (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q) r) (Quiver.Path.comp.{u2, u1} V _inst_1 a b d p (Quiver.Path.comp.{u2, u1} V _inst_1 b c d q r))
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_assoc Quiver.Path.comp_assocₓ'. -/
@[simp]
theorem comp_assoc {a b c : V} :
    ∀ {d} (p : Path a b) (q : Path b c) (r : Path c d), (p.comp q).comp r = p.comp (q.comp r)
  | c, p, q, path.nil => rfl
  | d, p, q, path.cons r e => by rw [comp_cons, comp_cons, comp_cons, comp_assoc]
#align quiver.path.comp_assoc Quiver.Path.comp_assoc

/- warning: quiver.path.length_comp -> Quiver.Path.length_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) {c : V} (q : Quiver.Path.{u2, u1} V _inst_1 b c), Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 a c (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Quiver.Path.length.{u1, u2} V _inst_1 a b p) (Quiver.Path.length.{u1, u2} V _inst_1 b c q))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) {c : V} (q : Quiver.Path.{u1, u2} V _inst_1 b c), Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 a c (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Quiver.Path.length.{u2, u1} V _inst_1 a b p) (Quiver.Path.length.{u2, u1} V _inst_1 b c q))
Case conversion may be inaccurate. Consider using '#align quiver.path.length_comp Quiver.Path.length_compₓ'. -/
@[simp]
theorem length_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).length = p.length + q.length
  | c, nil => rfl
  | c, cons q h => congr_arg Nat.succ q.length_comp
#align quiver.path.length_comp Quiver.Path.length_comp

/- warning: quiver.path.comp_inj -> Quiver.Path.comp_inj is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u2, u1} V _inst_1 a b} {p₂ : Quiver.Path.{u2, u1} V _inst_1 a b} {q₁ : Quiver.Path.{u2, u1} V _inst_1 b c} {q₂ : Quiver.Path.{u2, u1} V _inst_1 b c}, (Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 b c q₁) (Quiver.Path.length.{u1, u2} V _inst_1 b c q₂)) -> (Iff (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a c) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₁ q₁) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₂ q₂)) (And (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) p₁ p₂) (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 b c) q₁ q₂)))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u1, u2} V _inst_1 a b} {p₂ : Quiver.Path.{u1, u2} V _inst_1 a b} {q₁ : Quiver.Path.{u1, u2} V _inst_1 b c} {q₂ : Quiver.Path.{u1, u2} V _inst_1 b c}, (Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 b c q₁) (Quiver.Path.length.{u2, u1} V _inst_1 b c q₂)) -> (Iff (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a c) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₁ q₁) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₂ q₂)) (And (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) p₁ p₂) (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 b c) q₁ q₂)))
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_inj Quiver.Path.comp_injₓ'. -/
theorem comp_inj {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (hq : q₁.length = q₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by
  refine'
    ⟨fun h => _, by 
      rintro ⟨rfl, rfl⟩
      rfl⟩
  induction' q₁ with d₁ e₁ q₁ f₁ ih generalizing q₂ <;> obtain _ | ⟨q₂, f₂⟩ := q₂
  · exact ⟨h, rfl⟩
  · cases hq
  · cases hq
  simp only [comp_cons] at h
  obtain rfl := h.1
  obtain ⟨rfl, rfl⟩ := ih (Nat.succ.inj hq) h.2.1.Eq
  rw [h.2.2.Eq]
  exact ⟨rfl, rfl⟩
#align quiver.path.comp_inj Quiver.Path.comp_inj

/- warning: quiver.path.comp_inj' -> Quiver.Path.comp_inj' is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u2, u1} V _inst_1 a b} {p₂ : Quiver.Path.{u2, u1} V _inst_1 a b} {q₁ : Quiver.Path.{u2, u1} V _inst_1 b c} {q₂ : Quiver.Path.{u2, u1} V _inst_1 b c}, (Eq.{1} Nat (Quiver.Path.length.{u1, u2} V _inst_1 a b p₁) (Quiver.Path.length.{u1, u2} V _inst_1 a b p₂)) -> (Iff (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a c) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₁ q₁) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₂ q₂)) (And (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) p₁ p₂) (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 b c) q₁ q₂)))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u1, u2} V _inst_1 a b} {p₂ : Quiver.Path.{u1, u2} V _inst_1 a b} {q₁ : Quiver.Path.{u1, u2} V _inst_1 b c} {q₂ : Quiver.Path.{u1, u2} V _inst_1 b c}, (Eq.{1} Nat (Quiver.Path.length.{u2, u1} V _inst_1 a b p₁) (Quiver.Path.length.{u2, u1} V _inst_1 a b p₂)) -> (Iff (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a c) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₁ q₁) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₂ q₂)) (And (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) p₁ p₂) (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 b c) q₁ q₂)))
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_inj' Quiver.Path.comp_inj'ₓ'. -/
theorem comp_inj' {p₁ p₂ : Path a b} {q₁ q₂ : Path b c} (h : p₁.length = p₂.length) :
    p₁.comp q₁ = p₂.comp q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ :=
  ⟨fun h_eq => (comp_inj <| Nat.add_left_cancel <| by simpa [h] using congr_arg length h_eq).1 h_eq,
    by 
    rintro ⟨rfl, rfl⟩
    rfl⟩
#align quiver.path.comp_inj' Quiver.Path.comp_inj'

/- warning: quiver.path.comp_injective_left -> Quiver.Path.comp_injective_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} (q : Quiver.Path.{u2, u1} V _inst_1 b c), Function.Injective.{max (succ u1) u2, max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) (Quiver.Path.{u2, u1} V _inst_1 a c) (fun (p : Quiver.Path.{u2, u1} V _inst_1 a b) => Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} (q : Quiver.Path.{u1, u2} V _inst_1 b c), Function.Injective.{max (succ u2) u1, max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) (Quiver.Path.{u1, u2} V _inst_1 a c) (fun (p : Quiver.Path.{u1, u2} V _inst_1 a b) => Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q)
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_injective_left Quiver.Path.comp_injective_leftₓ'. -/
theorem comp_injective_left (q : Path b c) : Injective fun p : Path a b => p.comp q :=
  fun p₁ p₂ h => ((comp_inj rfl).1 h).1
#align quiver.path.comp_injective_left Quiver.Path.comp_injective_left

/- warning: quiver.path.comp_injective_right -> Quiver.Path.comp_injective_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b), Function.Injective.{max (succ u1) u2, max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 b c) (Quiver.Path.{u2, u1} V _inst_1 a c) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b), Function.Injective.{max (succ u2) u1, max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 b c) (Quiver.Path.{u1, u2} V _inst_1 a c) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p)
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_injective_right Quiver.Path.comp_injective_rightₓ'. -/
theorem comp_injective_right (p : Path a b) : Injective (p.comp : Path b c → Path a c) :=
  fun q₁ q₂ h => ((comp_inj' rfl).1 h).2
#align quiver.path.comp_injective_right Quiver.Path.comp_injective_right

/- warning: quiver.path.comp_inj_left -> Quiver.Path.comp_inj_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u2, u1} V _inst_1 a b} {p₂ : Quiver.Path.{u2, u1} V _inst_1 a b} {q : Quiver.Path.{u2, u1} V _inst_1 b c}, Iff (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a c) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₁ q) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p₂ q)) (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) p₁ p₂)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {p₁ : Quiver.Path.{u1, u2} V _inst_1 a b} {p₂ : Quiver.Path.{u1, u2} V _inst_1 a b} {q : Quiver.Path.{u1, u2} V _inst_1 b c}, Iff (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a c) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₁ q) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p₂ q)) (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) p₁ p₂)
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_inj_left Quiver.Path.comp_inj_leftₓ'. -/
@[simp]
theorem comp_inj_left {p₁ p₂ : Path a b} {q : Path b c} : p₁.comp q = p₂.comp q ↔ p₁ = p₂ :=
  q.comp_injective_left.eq_iff
#align quiver.path.comp_inj_left Quiver.Path.comp_inj_left

/- warning: quiver.path.comp_inj_right -> Quiver.Path.comp_inj_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} {c : V} {p : Quiver.Path.{u2, u1} V _inst_1 a b} {q₁ : Quiver.Path.{u2, u1} V _inst_1 b c} {q₂ : Quiver.Path.{u2, u1} V _inst_1 b c}, Iff (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a c) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q₁) (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q₂)) (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 b c) q₁ q₂)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} {c : V} {p : Quiver.Path.{u1, u2} V _inst_1 a b} {q₁ : Quiver.Path.{u1, u2} V _inst_1 b c} {q₂ : Quiver.Path.{u1, u2} V _inst_1 b c}, Iff (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a c) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q₁) (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q₂)) (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 b c) q₁ q₂)
Case conversion may be inaccurate. Consider using '#align quiver.path.comp_inj_right Quiver.Path.comp_inj_rightₓ'. -/
@[simp]
theorem comp_inj_right {p : Path a b} {q₁ q₂ : Path b c} : p.comp q₁ = p.comp q₂ ↔ q₁ = q₂ :=
  p.comp_injective_right.eq_iff
#align quiver.path.comp_inj_right Quiver.Path.comp_inj_right

#print Quiver.Path.toList /-
/-- Turn a path into a list. The list contains `a` at its head, but not `b` a priori. -/
@[simp]
def toList : ∀ {b : V}, Path a b → List V
  | b, nil => []
  | b, @cons _ _ _ c _ p f => c :: p.toList
#align quiver.path.to_list Quiver.Path.toList
-/

/- warning: quiver.path.to_list_comp -> Quiver.Path.toList_comp is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b) {c : V} (q : Quiver.Path.{u2, u1} V _inst_1 b c), Eq.{succ u1} (List.{u1} V) (Quiver.Path.toList.{u1, u2} V _inst_1 a c (Quiver.Path.comp.{u1, u2} V _inst_1 a b c p q)) (Append.append.{u1} (List.{u1} V) (List.hasAppend.{u1} V) (Quiver.Path.toList.{u1, u2} V _inst_1 b c q) (Quiver.Path.toList.{u1, u2} V _inst_1 a b p))
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b) {c : V} (q : Quiver.Path.{u1, u2} V _inst_1 b c), Eq.{succ u2} (List.{u2} V) (Quiver.Path.toList.{u2, u1} V _inst_1 a c (Quiver.Path.comp.{u2, u1} V _inst_1 a b c p q)) (HAppend.hAppend.{u2, u2, u2} (List.{u2} V) (List.{u2} V) (List.{u2} V) (instHAppend.{u2} (List.{u2} V) (List.instAppendList.{u2} V)) (Quiver.Path.toList.{u2, u1} V _inst_1 b c q) (Quiver.Path.toList.{u2, u1} V _inst_1 a b p))
Case conversion may be inaccurate. Consider using '#align quiver.path.to_list_comp Quiver.Path.toList_compₓ'. -/
/-- `quiver.path.to_list` is a contravariant functor. The inversion comes from `quiver.path` and
`list` having different preferred directions for adding elements. -/
@[simp]
theorem toList_comp (p : Path a b) : ∀ {c} (q : Path b c), (p.comp q).toList = q.toList ++ p.toList
  | c, nil => by simp
  | c, @cons _ _ _ d _ q f => by simp [to_list_comp]
#align quiver.path.to_list_comp Quiver.Path.toList_comp

/- warning: quiver.path.to_list_chain_nonempty -> Quiver.Path.toList_chain_nonempty is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} (p : Quiver.Path.{u2, u1} V _inst_1 a b), List.Chain.{u1} V (fun (x : V) (y : V) => Nonempty.{u2} (Quiver.Hom.{u2, u1} V _inst_1 y x)) b (Quiver.Path.toList.{u1, u2} V _inst_1 a b p)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} (p : Quiver.Path.{u1, u2} V _inst_1 a b), List.Chain.{u2} V (fun (x : V) (y : V) => Nonempty.{u1} (Quiver.Hom.{u1, u2} V _inst_1 y x)) b (Quiver.Path.toList.{u2, u1} V _inst_1 a b p)
Case conversion may be inaccurate. Consider using '#align quiver.path.to_list_chain_nonempty Quiver.Path.toList_chain_nonemptyₓ'. -/
theorem toList_chain_nonempty : ∀ {b} (p : Path a b), p.toList.Chain (fun x y => Nonempty (y ⟶ x)) b
  | b, nil => List.Chain.nil
  | b, cons p f => p.to_list_chain_nonempty.cons ⟨f⟩
#align quiver.path.to_list_chain_nonempty Quiver.Path.toList_chain_nonempty

variable [∀ a b : V, Subsingleton (a ⟶ b)]

/- warning: quiver.path.to_list_injective -> Quiver.Path.toList_injective is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] [_inst_2 : forall (a : V) (b : V), Subsingleton.{u2} (Quiver.Hom.{u2, u1} V _inst_1 a b)] (a : V) (b : V), Function.Injective.{max (succ u1) u2, succ u1} (Quiver.Path.{u2, u1} V _inst_1 a b) (List.{u1} V) (Quiver.Path.toList.{u1, u2} V _inst_1 a b)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] [_inst_2 : forall (a : V) (b : V), Subsingleton.{u1} (Quiver.Hom.{u1, u2} V _inst_1 a b)] (a : V) (b : V), Function.Injective.{max (succ u2) u1, succ u2} (Quiver.Path.{u1, u2} V _inst_1 a b) (List.{u2} V) (Quiver.Path.toList.{u2, u1} V _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align quiver.path.to_list_injective Quiver.Path.toList_injectiveₓ'. -/
theorem toList_injective (a : V) : ∀ b, Injective (toList : Path a b → List V)
  | b, nil, nil, h => rfl
  | b, nil, @cons _ _ _ c _ p f, h => by cases h
  | b, @cons _ _ _ c _ p f, nil, h => by cases h
  | b, @cons _ _ _ c _ p f, @cons _ _ s t u C D, h => by
    simp only [to_list] at h
    obtain ⟨rfl, hAC⟩ := h
    simp [to_list_injective _ hAC]
#align quiver.path.to_list_injective Quiver.Path.toList_injective

/- warning: quiver.path.to_list_inj -> Quiver.Path.toList_inj is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : Quiver.{u2, u1} V] {a : V} {b : V} [_inst_2 : forall (a : V) (b : V), Subsingleton.{u2} (Quiver.Hom.{u2, u1} V _inst_1 a b)] {p : Quiver.Path.{u2, u1} V _inst_1 a b} {q : Quiver.Path.{u2, u1} V _inst_1 a b}, Iff (Eq.{succ u1} (List.{u1} V) (Quiver.Path.toList.{u1, u2} V _inst_1 a b p) (Quiver.Path.toList.{u1, u2} V _inst_1 a b q)) (Eq.{max (succ u1) u2} (Quiver.Path.{u2, u1} V _inst_1 a b) p q)
but is expected to have type
  forall {V : Type.{u2}} [_inst_1 : Quiver.{u1, u2} V] {a : V} {b : V} [_inst_2 : forall (a : V) (b : V), Subsingleton.{u1} (Quiver.Hom.{u1, u2} V _inst_1 a b)] {p : Quiver.Path.{u1, u2} V _inst_1 a b} {q : Quiver.Path.{u1, u2} V _inst_1 a b}, Iff (Eq.{succ u2} (List.{u2} V) (Quiver.Path.toList.{u2, u1} V _inst_1 a b p) (Quiver.Path.toList.{u2, u1} V _inst_1 a b q)) (Eq.{max (succ u2) u1} (Quiver.Path.{u1, u2} V _inst_1 a b) p q)
Case conversion may be inaccurate. Consider using '#align quiver.path.to_list_inj Quiver.Path.toList_injₓ'. -/
@[simp]
theorem toList_inj {p q : Path a b} : p.toList = q.toList ↔ p = q :=
  (toList_injective _ _).eq_iff
#align quiver.path.to_list_inj Quiver.Path.toList_inj

end Path

end Quiver

namespace Prefunctor

open Quiver

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] (F : V ⥤q W)

#print Prefunctor.mapPath /-
/-- The image of a path under a prefunctor. -/
def mapPath {a : V} : ∀ {b : V}, Path a b → Path (F.obj a) (F.obj b)
  | _, path.nil => Path.nil
  | _, path.cons p e => Path.cons (map_path p) (F.map e)
#align prefunctor.map_path Prefunctor.mapPath
-/

#print Prefunctor.mapPath_nil /-
@[simp]
theorem mapPath_nil (a : V) : F.mapPath (Path.nil : Path a a) = path.nil :=
  rfl
#align prefunctor.map_path_nil Prefunctor.mapPath_nil
-/

#print Prefunctor.mapPath_cons /-
@[simp]
theorem mapPath_cons {a b c : V} (p : Path a b) (e : b ⟶ c) :
    F.mapPath (Path.cons p e) = Path.cons (F.mapPath p) (F.map e) :=
  rfl
#align prefunctor.map_path_cons Prefunctor.mapPath_cons
-/

#print Prefunctor.mapPath_comp /-
@[simp]
theorem mapPath_comp {a b : V} (p : Path a b) :
    ∀ {c : V} (q : Path b c), F.mapPath (p.comp q) = (F.mapPath p).comp (F.mapPath q)
  | _, path.nil => rfl
  | _, path.cons p e => by dsimp; rw [map_path_comp]
#align prefunctor.map_path_comp Prefunctor.mapPath_comp
-/

#print Prefunctor.mapPath_toPath /-
@[simp]
theorem mapPath_toPath {a b : V} (f : a ⟶ b) : F.mapPath f.toPath = (F.map f).toPath :=
  rfl
#align prefunctor.map_path_to_path Prefunctor.mapPath_toPath
-/

end Prefunctor

