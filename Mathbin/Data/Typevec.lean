/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon

! This file was ported from Lean 3 source module data.typevec
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Fin2
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Basic

/-!

# Tuples of types, and their categorical structure.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Features

* `typevec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `append_fun f g` - appends a function g to an n-tuple of functions
* `drop_fun f`     - drops the last function from an n+1-tuple
* `last_fun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/


universe u v w

#print TypeVec /-
/-- n-tuples of types, as a category
-/
def TypeVec (n : ℕ) :=
  Fin2 n → Type _
#align typevec TypeVec
-/

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace TypeVec

variable {n : ℕ}

#print TypeVec.Arrow /-
/-- arrow in the category of `typevec` -/
def Arrow (α β : TypeVec n) :=
  ∀ i : Fin2 n, α i → β i
#align typevec.arrow TypeVec.Arrow
-/

-- mathport name: typevec.arrow
scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow

#print TypeVec.Arrow.inhabited /-
instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩
#align typevec.arrow.inhabited TypeVec.Arrow.inhabited
-/

#print TypeVec.id /-
/-- identity of arrow composition -/
def id {α : TypeVec n} : α ⟹ α := fun i x => x
#align typevec.id TypeVec.id
-/

#print TypeVec.comp /-
/-- arrow composition in the category of `typevec` -/
def comp {α β γ : TypeVec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ := fun i x => g i (f i x)
#align typevec.comp TypeVec.comp
-/

-- mathport name: typevec.comp
scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp

/- warning: typevec.id_comp -> TypeVec.id_comp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {β : TypeVec.{u2} n} (f : TypeVec.Arrow.{u1, u2} n α β), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n α β) (TypeVec.comp.{u1, u2, u2} n α β β (TypeVec.id.{u2} n β) f) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {β : TypeVec.{u1} n} (f : TypeVec.Arrow.{u2, u1} n α β), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n α β) (TypeVec.comp.{u2, u1, u1} n α β β (TypeVec.id.{u1} n β) f) f
Case conversion may be inaccurate. Consider using '#align typevec.id_comp TypeVec.id_compₓ'. -/
-- type as \oo
@[simp]
theorem id_comp {α β : TypeVec n} (f : α ⟹ β) : id ⊚ f = f :=
  rfl
#align typevec.id_comp TypeVec.id_comp

/- warning: typevec.comp_id -> TypeVec.comp_id is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {β : TypeVec.{u2} n} (f : TypeVec.Arrow.{u1, u2} n α β), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n α β) (TypeVec.comp.{u1, u1, u2} n α α β f (TypeVec.id.{u1} n α)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {β : TypeVec.{u1} n} (f : TypeVec.Arrow.{u2, u1} n α β), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n α β) (TypeVec.comp.{u2, u2, u1} n α α β f (TypeVec.id.{u2} n α)) f
Case conversion may be inaccurate. Consider using '#align typevec.comp_id TypeVec.comp_idₓ'. -/
@[simp]
theorem comp_id {α β : TypeVec n} (f : α ⟹ β) : f ⊚ id = f :=
  rfl
#align typevec.comp_id TypeVec.comp_id

/- warning: typevec.comp_assoc -> TypeVec.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {β : TypeVec.{u2} n} {γ : TypeVec.{u3} n} {δ : TypeVec.{u4} n} (h : TypeVec.Arrow.{u3, u4} n γ δ) (g : TypeVec.Arrow.{u2, u3} n β γ) (f : TypeVec.Arrow.{u1, u2} n α β), Eq.{max 1 (succ u1) (succ u4)} (TypeVec.Arrow.{u1, u4} n α δ) (TypeVec.comp.{u1, u2, u4} n α β δ (TypeVec.comp.{u2, u3, u4} n β γ δ h g) f) (TypeVec.comp.{u1, u3, u4} n α γ δ h (TypeVec.comp.{u1, u2, u3} n α β γ g f))
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u4} n} {β : TypeVec.{u3} n} {γ : TypeVec.{u2} n} {δ : TypeVec.{u1} n} (h : TypeVec.Arrow.{u2, u1} n γ δ) (g : TypeVec.Arrow.{u3, u2} n β γ) (f : TypeVec.Arrow.{u4, u3} n α β), Eq.{max (succ u4) (succ u1)} (TypeVec.Arrow.{u4, u1} n α δ) (TypeVec.comp.{u4, u3, u1} n α β δ (TypeVec.comp.{u3, u2, u1} n β γ δ h g) f) (TypeVec.comp.{u4, u2, u1} n α γ δ h (TypeVec.comp.{u4, u3, u2} n α β γ g f))
Case conversion may be inaccurate. Consider using '#align typevec.comp_assoc TypeVec.comp_assocₓ'. -/
theorem comp_assoc {α β γ δ : TypeVec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
#align typevec.comp_assoc TypeVec.comp_assoc

#print TypeVec.append1 /-
/-- Support for extending a typevec by one element.
-/
def append1 (α : TypeVec n) (β : Type _) : TypeVec (n + 1)
  | Fin2.fs i => α i
  | Fin2.fz => β
#align typevec.append1 TypeVec.append1
-/

-- mathport name: typevec.append1
infixl:67 " ::: " => append1

#print TypeVec.drop /-
/-- retain only a `n-length` prefix of the argument -/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.fs
#align typevec.drop TypeVec.drop
-/

#print TypeVec.last /-
/-- take the last value of a `(n+1)-length` vector -/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α Fin2.fz
#align typevec.last TypeVec.last
-/

#print TypeVec.last.inhabited /-
instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨show α Fin2.fz from default⟩
#align typevec.last.inhabited TypeVec.last.inhabited
-/

#print TypeVec.drop_append1 /-
theorem drop_append1 {α : TypeVec n} {β : Type _} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl
#align typevec.drop_append1 TypeVec.drop_append1
-/

#print TypeVec.drop_append1' /-
theorem drop_append1' {α : TypeVec n} {β : Type _} : drop (append1 α β) = α := by
  ext <;> apply drop_append1
#align typevec.drop_append1' TypeVec.drop_append1'
-/

#print TypeVec.last_append1 /-
theorem last_append1 {α : TypeVec n} {β : Type _} : last (append1 α β) = β :=
  rfl
#align typevec.last_append1 TypeVec.last_append1
-/

#print TypeVec.append1_drop_last /-
@[simp]
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α :=
  funext fun i => by cases i <;> rfl
#align typevec.append1_drop_last TypeVec.append1_drop_last
-/

#print TypeVec.append1Cases /-
/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ] <;> apply H
#align typevec.append1_cases TypeVec.append1Cases
-/

/- warning: typevec.append1_cases_append1 -> TypeVec.append1_cases_append1 is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {C : (TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Sort.{u1}} (H : forall (α : TypeVec.{u2} n) (β : Type.{u2}), C (TypeVec.append1.{u2} n α β)) (α : TypeVec.{u2} n) (β : Type.{u2}), Eq.{u1} (C (TypeVec.append1.{u2} n α β)) (TypeVec.append1Cases.{u1, u2} n C H (TypeVec.append1.{u2} n α β)) (H α β)
but is expected to have type
  forall {n : Nat} {C : (TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Sort.{u2}} (H : forall (α : TypeVec.{u1} n) (β : Type.{u1}), C (TypeVec.append1.{u1} n α β)) (α : TypeVec.{u1} n) (β : Type.{u1}), Eq.{u2} (C (TypeVec.append1.{u1} n α β)) (TypeVec.append1Cases.{u2, u1} n C H (TypeVec.append1.{u1} n α β)) (H α β)
Case conversion may be inaccurate. Consider using '#align typevec.append1_cases_append1 TypeVec.append1_cases_append1ₓ'. -/
@[simp]
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl
#align typevec.append1_cases_append1 TypeVec.append1_cases_append1

#print TypeVec.splitFun /-
/-- append an arrow and a function for arbitrary source and target
type vectors -/
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | Fin2.fs i => f i
  | Fin2.fz => g
#align typevec.split_fun TypeVec.splitFun
-/

#print TypeVec.appendFun /-
/-- append an arrow and a function as well as their respective source
and target types / typevecs -/
def appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g
#align typevec.append_fun TypeVec.appendFun
-/

-- mathport name: typevec.append_fun
infixl:0 " ::: " => appendFun

#print TypeVec.dropFun /-
/-- split off the prefix of an arrow -/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.fs
#align typevec.drop_fun TypeVec.dropFun
-/

#print TypeVec.lastFun /-
/-- split off the last function of an arrow -/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz
#align typevec.last_fun TypeVec.lastFun
-/

#print TypeVec.nilFun /-
/-- arrow in the category of `0-length` vectors -/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => Fin2.elim0 i
#align typevec.nil_fun TypeVec.nilFun
-/

/- warning: typevec.eq_of_drop_last_eq -> TypeVec.eq_of_drop_last_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {β : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {f : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α β} {g : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α β}, (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n β)) (TypeVec.dropFun.{u1, u2} n α β f) (TypeVec.dropFun.{u1, u2} n α β g)) -> (Eq.{max (succ u1) (succ u2)} ((TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n β)) (TypeVec.lastFun.{u1, u2} n α β f) (TypeVec.lastFun.{u1, u2} n α β g)) -> (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α β) f g)
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {β : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {f : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α β} {g : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α β}, (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n β)) (TypeVec.dropFun.{u2, u1} n α β f) (TypeVec.dropFun.{u2, u1} n α β g)) -> (Eq.{max (succ u2) (succ u1)} ((TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n β)) (TypeVec.lastFun.{u2, u1} n α β f) (TypeVec.lastFun.{u2, u1} n α β g)) -> (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α β) f g)
Case conversion may be inaccurate. Consider using '#align typevec.eq_of_drop_last_eq TypeVec.eq_of_drop_last_eqₓ'. -/
theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  replace h₀ := congr_fun h₀ <;> ext1 ⟨⟩ <;> apply_assumption
#align typevec.eq_of_drop_last_eq TypeVec.eq_of_drop_last_eq

/- warning: typevec.drop_fun_split_fun -> TypeVec.dropFun_splitFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α' : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f : TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')) (g : (TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')) (TypeVec.dropFun.{u1, u2} n α α' (TypeVec.splitFun.{u1, u2} n α α' f g)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α' : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f : TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')) (g : (TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')) (TypeVec.dropFun.{u2, u1} n α α' (TypeVec.splitFun.{u2, u1} n α α' f g)) f
Case conversion may be inaccurate. Consider using '#align typevec.drop_fun_split_fun TypeVec.dropFun_splitFunₓ'. -/
@[simp]
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f :=
  rfl
#align typevec.drop_fun_split_fun TypeVec.dropFun_splitFun

#print TypeVec.Arrow.mp /-
/-- turn an equality into an arrow -/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | i => Eq.mp (congr_fun h _)
#align typevec.arrow.mp TypeVec.Arrow.mp
-/

#print TypeVec.Arrow.mpr /-
/-- turn an equality into an arrow, with reverse direction -/
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | i => Eq.mpr (congr_fun h _)
#align typevec.arrow.mpr TypeVec.Arrow.mpr
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.toAppend1DropLast /-
/-- decompose a vector into its prefix appended with its last element -/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)
#align typevec.to_append1_drop_last TypeVec.toAppend1DropLast
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.fromAppend1DropLast /-
/-- stitch two bits of a vector back together -/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)
#align typevec.from_append1_drop_last TypeVec.fromAppend1DropLast
-/

/- warning: typevec.last_fun_split_fun -> TypeVec.lastFun_splitFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α' : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f : TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')) (g : (TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')), Eq.{max (succ u1) (succ u2)} ((TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')) (TypeVec.lastFun.{u1, u2} n α α' (TypeVec.splitFun.{u1, u2} n α α' f g)) g
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α' : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f : TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')) (g : (TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')), Eq.{max (succ u2) (succ u1)} ((TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')) (TypeVec.lastFun.{u2, u1} n α α' (TypeVec.splitFun.{u2, u1} n α α' f g)) g
Case conversion may be inaccurate. Consider using '#align typevec.last_fun_split_fun TypeVec.lastFun_splitFunₓ'. -/
@[simp]
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g :=
  rfl
#align typevec.last_fun_split_fun TypeVec.lastFun_splitFun

/- warning: typevec.drop_fun_append_fun -> TypeVec.dropFun_appendFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {α' : TypeVec.{u2} n} {β : Type.{u1}} {β' : Type.{u2}} (f : TypeVec.Arrow.{u1, u2} n α α') (g : β -> β'), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α β)) (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α' β'))) (TypeVec.dropFun.{u1, u2} n (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β') (TypeVec.appendFun.{u1, u2} n α α' β β' f g)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {α' : TypeVec.{u1} n} {β : Type.{u2}} {β' : Type.{u1}} (f : TypeVec.Arrow.{u2, u1} n α α') (g : β -> β'), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α β)) (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α' β'))) (TypeVec.dropFun.{u2, u1} n (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β') (TypeVec.appendFun.{u2, u1} n α α' β β' f g)) f
Case conversion may be inaccurate. Consider using '#align typevec.drop_fun_append_fun TypeVec.dropFun_appendFunₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f :=
  rfl
#align typevec.drop_fun_append_fun TypeVec.dropFun_appendFun

/- warning: typevec.last_fun_append_fun -> TypeVec.lastFun_appendFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {α' : TypeVec.{u2} n} {β : Type.{u1}} {β' : Type.{u2}} (f : TypeVec.Arrow.{u1, u2} n α α') (g : β -> β'), Eq.{max (succ u1) (succ u2)} ((TypeVec.last.{u1} n (TypeVec.append1.{u1} n α β)) -> (TypeVec.last.{u2} n (TypeVec.append1.{u2} n α' β'))) (TypeVec.lastFun.{u1, u2} n (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β') (TypeVec.appendFun.{u1, u2} n α α' β β' f g)) g
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {α' : TypeVec.{u1} n} {β : Type.{u2}} {β' : Type.{u1}} (f : TypeVec.Arrow.{u2, u1} n α α') (g : β -> β'), Eq.{max (succ u2) (succ u1)} ((TypeVec.last.{u2} n (TypeVec.append1.{u2} n α β)) -> (TypeVec.last.{u1} n (TypeVec.append1.{u1} n α' β'))) (TypeVec.lastFun.{u2, u1} n (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β') (TypeVec.appendFun.{u2, u1} n α α' β β' f g)) g
Case conversion may be inaccurate. Consider using '#align typevec.last_fun_append_fun TypeVec.lastFun_appendFunₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type _} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g :=
  rfl
#align typevec.last_fun_append_fun TypeVec.lastFun_appendFun

/- warning: typevec.split_drop_fun_last_fun -> TypeVec.split_dropFun_lastFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α' : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α α'), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α α') (TypeVec.splitFun.{u1, u2} n α α' (TypeVec.dropFun.{u1, u2} n α α' f) (TypeVec.lastFun.{u1, u2} n α α' f)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α' : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α α'), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α α') (TypeVec.splitFun.{u2, u1} n α α' (TypeVec.dropFun.{u2, u1} n α α' f) (TypeVec.lastFun.{u2, u1} n α α' f)) f
Case conversion may be inaccurate. Consider using '#align typevec.split_drop_fun_last_fun TypeVec.split_dropFun_lastFunₓ'. -/
theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
#align typevec.split_drop_fun_last_fun TypeVec.split_dropFun_lastFun

/- warning: typevec.split_fun_inj -> TypeVec.splitFun_inj is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α' : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {f : TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')} {f' : TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')} {g : (TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')} {g' : (TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')}, (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α α') (TypeVec.splitFun.{u1, u2} n α α' f g) (TypeVec.splitFun.{u1, u2} n α α' f' g')) -> (And (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α) (TypeVec.drop.{u2} n α')) f f') (Eq.{max (succ u1) (succ u2)} ((TypeVec.last.{u1} n α) -> (TypeVec.last.{u2} n α')) g g'))
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α' : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {f : TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')} {f' : TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')} {g : (TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')} {g' : (TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')}, (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α α') (TypeVec.splitFun.{u2, u1} n α α' f g) (TypeVec.splitFun.{u2, u1} n α α' f' g')) -> (And (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α) (TypeVec.drop.{u1} n α')) f f') (Eq.{max (succ u2) (succ u1)} ((TypeVec.last.{u2} n α) -> (TypeVec.last.{u1} n α')) g g'))
Case conversion may be inaccurate. Consider using '#align typevec.split_fun_inj TypeVec.splitFun_injₓ'. -/
theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H] <;> simp
#align typevec.split_fun_inj TypeVec.splitFun_inj

/- warning: typevec.append_fun_inj -> TypeVec.appendFun_inj is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {α' : TypeVec.{u2} n} {β : Type.{u1}} {β' : Type.{u2}} {f : TypeVec.Arrow.{u1, u2} n α α'} {f' : TypeVec.Arrow.{u1, u2} n α α'} {g : β -> β'} {g' : β -> β'}, (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β')) (TypeVec.appendFun.{u1, u2} n α α' β β' f g) (TypeVec.appendFun.{u1, u2} n α α' β β' f' g')) -> (And (Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} n α α') f f') (Eq.{max (succ u1) (succ u2)} (β -> β') g g'))
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {α' : TypeVec.{u1} n} {β : Type.{u2}} {β' : Type.{u1}} {f : TypeVec.Arrow.{u2, u1} n α α'} {f' : TypeVec.Arrow.{u2, u1} n α α'} {g : β -> β'} {g' : β -> β'}, (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β')) (TypeVec.appendFun.{u2, u1} n α α' β β' f g) (TypeVec.appendFun.{u2, u1} n α α' β β' f' g')) -> (And (Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n α α') f f') (Eq.{max (succ u2) (succ u1)} (β -> β') g g'))
Case conversion may be inaccurate. Consider using '#align typevec.append_fun_inj TypeVec.appendFun_injₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem appendFun_inj {α α' : TypeVec n} {β β' : Type _} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g) = (f' ::: g') → f = f' ∧ g = g' :=
  split_fun_inj
#align typevec.append_fun_inj TypeVec.appendFun_inj

/- warning: typevec.split_fun_comp -> TypeVec.splitFun_comp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α₀ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₂ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f₀ : TypeVec.Arrow.{u1, u2} n (TypeVec.drop.{u1} n α₀) (TypeVec.drop.{u2} n α₁)) (f₁ : TypeVec.Arrow.{u2, u3} n (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u3} n α₂)) (g₀ : (TypeVec.last.{u1} n α₀) -> (TypeVec.last.{u2} n α₁)) (g₁ : (TypeVec.last.{u2} n α₁) -> (TypeVec.last.{u3} n α₂)), Eq.{max 1 (succ u1) (succ u3)} (TypeVec.Arrow.{u1, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₂) (TypeVec.splitFun.{u1, u3} n α₀ α₂ (TypeVec.comp.{u1, u2, u3} n (TypeVec.drop.{u1} n α₀) (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u3} n α₂) f₁ f₀) (Function.comp.{succ u1, succ u2, succ u3} (TypeVec.last.{u1} n α₀) (TypeVec.last.{u2} n α₁) (TypeVec.last.{u3} n α₂) g₁ g₀)) (TypeVec.comp.{u1, u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₁ α₂ (TypeVec.splitFun.{u2, u3} n α₁ α₂ f₁ g₁) (TypeVec.splitFun.{u1, u2} n α₀ α₁ f₀ g₀))
but is expected to have type
  forall {n : Nat} {α₀ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₂ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f₀ : TypeVec.Arrow.{u3, u2} n (TypeVec.drop.{u3} n α₀) (TypeVec.drop.{u2} n α₁)) (f₁ : TypeVec.Arrow.{u2, u1} n (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u1} n α₂)) (g₀ : (TypeVec.last.{u3} n α₀) -> (TypeVec.last.{u2} n α₁)) (g₁ : (TypeVec.last.{u2} n α₁) -> (TypeVec.last.{u1} n α₂)), Eq.{max (succ u3) (succ u1)} (TypeVec.Arrow.{u3, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₂) (TypeVec.splitFun.{u3, u1} n α₀ α₂ (TypeVec.comp.{u3, u2, u1} n (TypeVec.drop.{u3} n α₀) (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u1} n α₂) f₁ f₀) (Function.comp.{succ u3, succ u2, succ u1} (TypeVec.last.{u3} n α₀) (TypeVec.last.{u2} n α₁) (TypeVec.last.{u1} n α₂) g₁ g₀)) (TypeVec.comp.{u3, u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₁ α₂ (TypeVec.splitFun.{u2, u1} n α₁ α₂ f₁ g₁) (TypeVec.splitFun.{u3, u2} n α₀ α₁ f₀ g₀))
Case conversion may be inaccurate. Consider using '#align typevec.split_fun_comp TypeVec.splitFun_compₓ'. -/
theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
    (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl
#align typevec.split_fun_comp TypeVec.splitFun_comp

/- warning: typevec.append_fun_comp_split_fun -> TypeVec.appendFun_comp_splitFun is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {γ : TypeVec.{u2} n} {β : Type.{u1}} {δ : Type.{u2}} {ε : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f₀ : TypeVec.Arrow.{u3, u1} n (TypeVec.drop.{u3} n ε) α) (f₁ : TypeVec.Arrow.{u1, u2} n α γ) (g₀ : (TypeVec.last.{u3} n ε) -> β) (g₁ : β -> δ), Eq.{max 1 (succ u3) (succ u2)} (TypeVec.Arrow.{u3, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ε (TypeVec.append1.{u2} n γ δ)) (TypeVec.comp.{u3, u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ε (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n γ δ) (TypeVec.appendFun.{u1, u2} n α γ β δ f₁ g₁) (TypeVec.splitFun.{u3, u1} n ε (TypeVec.append1.{u1} n α β) f₀ g₀)) (TypeVec.splitFun.{u3, u2} n ε (TypeVec.append1.{u2} n γ δ) (TypeVec.comp.{u3, u1, u2} n (TypeVec.drop.{u3} n ε) α (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n γ δ)) f₁ f₀) (Function.comp.{succ u3, succ u1, succ u2} (TypeVec.last.{u3} n ε) β (TypeVec.last.{u2} n (TypeVec.append1.{u2} n γ δ)) g₁ g₀))
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u3} n} {γ : TypeVec.{u2} n} {β : Type.{u3}} {δ : Type.{u2}} {ε : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f₀ : TypeVec.Arrow.{u1, u3} n (TypeVec.drop.{u1} n ε) α) (f₁ : TypeVec.Arrow.{u3, u2} n α γ) (g₀ : (TypeVec.last.{u1} n ε) -> β) (g₁ : β -> δ), Eq.{max (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) ε (TypeVec.append1.{u2} n γ δ)) (TypeVec.comp.{u1, u3, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) ε (TypeVec.append1.{u3} n α β) (TypeVec.append1.{u2} n γ δ) (TypeVec.appendFun.{u3, u2} n α γ β δ f₁ g₁) (TypeVec.splitFun.{u1, u3} n ε (TypeVec.append1.{u3} n α β) f₀ g₀)) (TypeVec.splitFun.{u1, u2} n ε (TypeVec.append1.{u2} n γ δ) (TypeVec.comp.{u1, u3, u2} n (TypeVec.drop.{u1} n ε) α (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n γ δ)) f₁ f₀) (Function.comp.{succ u1, succ u3, succ u2} (TypeVec.last.{u1} n ε) β (TypeVec.last.{u2} n (TypeVec.append1.{u2} n γ δ)) g₁ g₀))
Case conversion may be inaccurate. Consider using '#align typevec.append_fun_comp_split_fun TypeVec.appendFun_comp_splitFunₓ'. -/
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type _} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm
#align typevec.append_fun_comp_split_fun TypeVec.appendFun_comp_splitFun

/- warning: typevec.append_fun_comp -> TypeVec.appendFun_comp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α₀ : TypeVec.{u1} n} {α₁ : TypeVec.{u2} n} {α₂ : TypeVec.{u3} n} {β₀ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (f₀ : TypeVec.Arrow.{u1, u2} n α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u3} n α₁ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂), Eq.{max 1 (succ u1) (succ u3)} (TypeVec.Arrow.{u1, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α₀ β₀) (TypeVec.append1.{u3} n α₂ β₂)) (TypeVec.appendFun.{u1, u3} n α₀ α₂ β₀ β₂ (TypeVec.comp.{u1, u2, u3} n α₀ α₁ α₂ f₁ f₀) (Function.comp.{succ u1, succ u2, succ u3} β₀ β₁ β₂ g₁ g₀)) (TypeVec.comp.{u1, u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α₀ β₀) (TypeVec.append1.{u2} n α₁ β₁) (TypeVec.append1.{u3} n α₂ β₂) (TypeVec.appendFun.{u2, u3} n α₁ α₂ β₁ β₂ f₁ g₁) (TypeVec.appendFun.{u1, u2} n α₀ α₁ β₀ β₁ f₀ g₀))
but is expected to have type
  forall {n : Nat} {α₀ : TypeVec.{u3} n} {α₁ : TypeVec.{u2} n} {α₂ : TypeVec.{u1} n} {β₀ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} (f₀ : TypeVec.Arrow.{u3, u2} n α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u1} n α₁ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂), Eq.{max (succ u3) (succ u1)} (TypeVec.Arrow.{u3, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u3} n α₀ β₀) (TypeVec.append1.{u1} n α₂ β₂)) (TypeVec.appendFun.{u3, u1} n α₀ α₂ β₀ β₂ (TypeVec.comp.{u3, u2, u1} n α₀ α₁ α₂ f₁ f₀) (Function.comp.{succ u3, succ u2, succ u1} β₀ β₁ β₂ g₁ g₀)) (TypeVec.comp.{u3, u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u3} n α₀ β₀) (TypeVec.append1.{u2} n α₁ β₁) (TypeVec.append1.{u1} n α₂ β₂) (TypeVec.appendFun.{u2, u1} n α₁ α₂ β₁ β₂ f₁ g₁) (TypeVec.appendFun.{u3, u2} n α₀ α₁ β₀ β₁ f₀ g₀))
Case conversion may be inaccurate. Consider using '#align typevec.append_fun_comp TypeVec.appendFun_compₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem appendFun_comp {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) : (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp TypeVec.appendFun_comp

/- warning: typevec.append_fun_comp' -> TypeVec.appendFun_comp' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α₀ : TypeVec.{u1} n} {α₁ : TypeVec.{u2} n} {α₂ : TypeVec.{u3} n} {β₀ : Type.{u1}} {β₁ : Type.{u2}} {β₂ : Type.{u3}} (f₀ : TypeVec.Arrow.{u1, u2} n α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u3} n α₁ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂), Eq.{max 1 (succ u1) (succ u3)} (TypeVec.Arrow.{u1, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α₀ β₀) (TypeVec.append1.{u3} n α₂ β₂)) (TypeVec.comp.{u1, u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α₀ β₀) (TypeVec.append1.{u2} n α₁ β₁) (TypeVec.append1.{u3} n α₂ β₂) (TypeVec.appendFun.{u2, u3} n α₁ α₂ β₁ β₂ f₁ g₁) (TypeVec.appendFun.{u1, u2} n α₀ α₁ β₀ β₁ f₀ g₀)) (TypeVec.appendFun.{u1, u3} n α₀ α₂ β₀ β₂ (TypeVec.comp.{u1, u2, u3} n α₀ α₁ α₂ f₁ f₀) (Function.comp.{succ u1, succ u2, succ u3} β₀ β₁ β₂ g₁ g₀))
but is expected to have type
  forall {n : Nat} {α₀ : TypeVec.{u3} n} {α₁ : TypeVec.{u2} n} {α₂ : TypeVec.{u1} n} {β₀ : Type.{u3}} {β₁ : Type.{u2}} {β₂ : Type.{u1}} (f₀ : TypeVec.Arrow.{u3, u2} n α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u1} n α₁ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂), Eq.{max (succ u3) (succ u1)} (TypeVec.Arrow.{u3, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u3} n α₀ β₀) (TypeVec.append1.{u1} n α₂ β₂)) (TypeVec.comp.{u3, u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u3} n α₀ β₀) (TypeVec.append1.{u2} n α₁ β₁) (TypeVec.append1.{u1} n α₂ β₂) (TypeVec.appendFun.{u2, u1} n α₁ α₂ β₁ β₂ f₁ g₁) (TypeVec.appendFun.{u3, u2} n α₀ α₁ β₀ β₁ f₀ g₀)) (TypeVec.appendFun.{u3, u1} n α₀ α₂ β₀ β₂ (TypeVec.comp.{u3, u2, u1} n α₀ α₁ α₂ f₁ f₀) (Function.comp.{succ u3, succ u2, succ u1} β₀ β₁ β₂ g₁ g₀))
Case conversion may be inaccurate. Consider using '#align typevec.append_fun_comp' TypeVec.appendFun_comp'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type _} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) : (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp' TypeVec.appendFun_comp'

/- warning: typevec.nil_fun_comp -> TypeVec.nilFun_comp is a dubious translation:
lean 3 declaration is
  forall {α₀ : TypeVec.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))} (f₀ : TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α₀ (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2}))), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α₀ (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2}))) (TypeVec.comp.{u1, u2, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α₀ (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})) (TypeVec.nilFun.{u2, u2} (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2}))) f₀) f₀
but is expected to have type
  forall {α₀ : TypeVec.{u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))} (f₀ : TypeVec.Arrow.{u2, u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α₀ (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1}))), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α₀ (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1}))) (TypeVec.comp.{u2, u1, u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α₀ (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1})) (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1})) (TypeVec.nilFun.{u1, u1} (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1})) (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u1}))) f₀) f₀
Case conversion may be inaccurate. Consider using '#align typevec.nil_fun_comp TypeVec.nilFun_compₓ'. -/
theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nil_fun ⊚ f₀ = f₀ :=
  funext fun x => Fin2.elim0 x
#align typevec.nil_fun_comp TypeVec.nilFun_comp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.appendFun_comp_id /-
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type _} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_comp_id TypeVec.appendFun_comp_id
-/

/- warning: typevec.drop_fun_comp -> TypeVec.dropFun_comp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α₀ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₂ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f₀ : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₁ α₂), Eq.{max 1 (succ u1) (succ u3)} (TypeVec.Arrow.{u1, u3} n (TypeVec.drop.{u1} n α₀) (TypeVec.drop.{u3} n α₂)) (TypeVec.dropFun.{u1, u3} n α₀ α₂ (TypeVec.comp.{u1, u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₁ α₂ f₁ f₀)) (TypeVec.comp.{u1, u2, u3} n (TypeVec.drop.{u1} n α₀) (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u3} n α₂) (TypeVec.dropFun.{u2, u3} n α₁ α₂ f₁) (TypeVec.dropFun.{u1, u2} n α₀ α₁ f₀))
but is expected to have type
  forall {n : Nat} {α₀ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₂ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f₀ : TypeVec.Arrow.{u3, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₁ α₂), Eq.{max (succ u3) (succ u1)} (TypeVec.Arrow.{u3, u1} n (TypeVec.drop.{u3} n α₀) (TypeVec.drop.{u1} n α₂)) (TypeVec.dropFun.{u3, u1} n α₀ α₂ (TypeVec.comp.{u3, u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₁ α₂ f₁ f₀)) (TypeVec.comp.{u3, u2, u1} n (TypeVec.drop.{u3} n α₀) (TypeVec.drop.{u2} n α₁) (TypeVec.drop.{u1} n α₂) (TypeVec.dropFun.{u2, u1} n α₁ α₂ f₁) (TypeVec.dropFun.{u3, u2} n α₀ α₁ f₀))
Case conversion may be inaccurate. Consider using '#align typevec.drop_fun_comp TypeVec.dropFun_compₓ'. -/
@[simp]
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl
#align typevec.drop_fun_comp TypeVec.dropFun_comp

/- warning: typevec.last_fun_comp -> TypeVec.lastFun_comp is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α₀ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {α₂ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} (f₀ : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₁ α₂), Eq.{max (succ u1) (succ u3)} ((TypeVec.last.{u1} n α₀) -> (TypeVec.last.{u3} n α₂)) (TypeVec.lastFun.{u1, u3} n α₀ α₂ (TypeVec.comp.{u1, u2, u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α₀ α₁ α₂ f₁ f₀)) (Function.comp.{succ u1, succ u2, succ u3} (TypeVec.last.{u1} n α₀) (TypeVec.last.{u2} n α₁) (TypeVec.last.{u3} n α₂) (TypeVec.lastFun.{u2, u3} n α₁ α₂ f₁) (TypeVec.lastFun.{u1, u2} n α₀ α₁ f₀))
but is expected to have type
  forall {n : Nat} {α₀ : TypeVec.{u3} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₁ : TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {α₂ : TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} (f₀ : TypeVec.Arrow.{u3, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₁) (f₁ : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₁ α₂), Eq.{max (succ u3) (succ u1)} ((TypeVec.last.{u3} n α₀) -> (TypeVec.last.{u1} n α₂)) (TypeVec.lastFun.{u3, u1} n α₀ α₂ (TypeVec.comp.{u3, u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α₀ α₁ α₂ f₁ f₀)) (Function.comp.{succ u3, succ u2, succ u1} (TypeVec.last.{u3} n α₀) (TypeVec.last.{u2} n α₁) (TypeVec.last.{u1} n α₂) (TypeVec.lastFun.{u2, u1} n α₁ α₂ f₁) (TypeVec.lastFun.{u3, u2} n α₀ α₁ f₀))
Case conversion may be inaccurate. Consider using '#align typevec.last_fun_comp TypeVec.lastFun_compₓ'. -/
@[simp]
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl
#align typevec.last_fun_comp TypeVec.lastFun_comp

/- warning: typevec.append_fun_aux -> TypeVec.appendFun_aux is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {α' : TypeVec.{u2} n} {β : Type.{u1}} {β' : Type.{u2}} (f : TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β')), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α β)) (TypeVec.last.{u1} n (TypeVec.append1.{u1} n α β))) (TypeVec.append1.{u2} n (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α' β')) (TypeVec.last.{u2} n (TypeVec.append1.{u2} n α' β')))) (TypeVec.appendFun.{u1, u2} n (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α β)) (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α' β')) (TypeVec.last.{u1} n (TypeVec.append1.{u1} n α β)) (TypeVec.last.{u2} n (TypeVec.append1.{u2} n α' β')) (TypeVec.dropFun.{u1, u2} n (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β') f) (TypeVec.lastFun.{u1, u2} n (TypeVec.append1.{u1} n α β) (TypeVec.append1.{u2} n α' β') f)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {α' : TypeVec.{u1} n} {β : Type.{u2}} {β' : Type.{u1}} (f : TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β')), Eq.{max (succ u1) (succ u2)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α β)) (TypeVec.last.{u2} n (TypeVec.append1.{u2} n α β))) (TypeVec.append1.{u1} n (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α' β')) (TypeVec.last.{u1} n (TypeVec.append1.{u1} n α' β')))) (TypeVec.appendFun.{u2, u1} n (TypeVec.drop.{u2} n (TypeVec.append1.{u2} n α β)) (TypeVec.drop.{u1} n (TypeVec.append1.{u1} n α' β')) (TypeVec.last.{u2} n (TypeVec.append1.{u2} n α β)) (TypeVec.last.{u1} n (TypeVec.append1.{u1} n α' β')) (TypeVec.dropFun.{u2, u1} n (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β') f) (TypeVec.lastFun.{u2, u1} n (TypeVec.append1.{u2} n α β) (TypeVec.append1.{u1} n α' β') f)) f
Case conversion may be inaccurate. Consider using '#align typevec.append_fun_aux TypeVec.appendFun_auxₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem appendFun_aux {α α' : TypeVec n} {β β' : Type _} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_aux TypeVec.appendFun_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.appendFun_id_id /-
theorem appendFun_id_id {α : TypeVec n} {β : Type _} : (@TypeVec.id n α ::: @id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl
#align typevec.append_fun_id_id TypeVec.appendFun_id_id
-/

#print TypeVec.subsingleton0 /-
instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun a b => funext fun a => Fin2.elim0 a⟩
#align typevec.subsingleton0 TypeVec.subsingleton0
-/

run_cmd
  do
    mk_simp_attr `typevec
    tactic.add_doc_string `simp_attr.typevec
        "simp set for the manipulation of typevec and arrow expressions"

-- mathport name: «expr♯ »
local prefix:0 "♯" => cast (by try simp <;> congr 1 <;> try simp)

#print TypeVec.casesNil /-
/-- cases distinction for 0-length type vector -/
protected def casesNil {β : TypeVec 0 → Sort _} (f : β Fin2.elim0) : ∀ v, β v := fun v => ♯f
#align typevec.cases_nil TypeVec.casesNil
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.casesCons /-
/-- cases distinction for (n+1)-length type vector -/
protected def casesCons (n : ℕ) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) : ∀ v, β v := fun v : TypeVec (n + 1) =>
  ♯f v.last v.drop
#align typevec.cases_cons TypeVec.casesCons
-/

/- warning: typevec.cases_nil_append1 -> TypeVec.casesNil_append1 is a dubious translation:
lean 3 declaration is
  forall {β : (TypeVec.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> Sort.{u2}} (f : β (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1}))), Eq.{u2} (β (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1}))) (TypeVec.casesNil.{u1, u2} β f (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1}))) f
but is expected to have type
  forall {β : (TypeVec.{u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> Sort.{u1}} (f : β (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2}))), Eq.{u1} (β (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2}))) (TypeVec.casesNil.{u2, u1} β f (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2}))) f
Case conversion may be inaccurate. Consider using '#align typevec.cases_nil_append1 TypeVec.casesNil_append1ₓ'. -/
protected theorem casesNil_append1 {β : TypeVec 0 → Sort _} (f : β Fin2.elim0) :
    TypeVec.casesNil f Fin2.elim0 = f :=
  rfl
#align typevec.cases_nil_append1 TypeVec.casesNil_append1

/- warning: typevec.cases_cons_append1 -> TypeVec.casesCons_append1 is a dubious translation:
lean 3 declaration is
  forall (n : Nat) {β : (TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Sort.{u2}} (f : forall (t : Type.{u1}) (v : TypeVec.{u1} n), β (TypeVec.append1.{u1} n v t)) (v : TypeVec.{u1} n) (α : Type.{u1}), Eq.{u2} (β (TypeVec.append1.{u1} n v α)) (TypeVec.casesCons.{u1, u2} n β f (TypeVec.append1.{u1} n v α)) (f α v)
but is expected to have type
  forall (n : Nat) {β : (TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Sort.{u1}} (f : forall (t : Type.{u2}) (v : TypeVec.{u2} n), β (TypeVec.append1.{u2} n v t)) (v : TypeVec.{u2} n) (α : Type.{u2}), Eq.{u1} (β (TypeVec.append1.{u2} n v α)) (TypeVec.casesCons.{u2, u1} n β f (TypeVec.append1.{u2} n v α)) (f α v)
Case conversion may be inaccurate. Consider using '#align typevec.cases_cons_append1 TypeVec.casesCons_append1ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
protected theorem casesCons_append1 (n : ℕ) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl
#align typevec.cases_cons_append1 TypeVec.casesCons_append1

#print TypeVec.typevecCasesNil₃ /-
/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort _}
    (f : β Fin2.elim0 Fin2.elim0 nilFun) : ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine' cast _ f <;> congr 1 <;> ext <;> try intros <;> casesm Fin2 0; rfl
#align typevec.typevec_cases_nil₃ TypeVec.typevecCasesNil₃
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.typevecCasesCons₃ /-
/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₃ (n : ℕ) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort _}
    (F :
      ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_drop_fun_last_fun fs]
  apply F
#align typevec.typevec_cases_cons₃ TypeVec.typevecCasesCons₃
-/

#print TypeVec.typevecCasesNil₂ /-
/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevecCasesNil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort _} (f : β nilFun) : ∀ f, β f :=
  by
  intro g; have : g = nil_fun; ext ⟨⟩
  rw [this]; exact f
#align typevec.typevec_cases_nil₂ TypeVec.typevecCasesNil₂
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.typevecCasesCons₂ /-
/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevecCasesCons₂ (n : ℕ) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _} (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) :
    ∀ fs, β fs := by
  intro fs
  rw [← split_drop_fun_last_fun fs]
  apply F
#align typevec.typevec_cases_cons₂ TypeVec.typevecCasesCons₂
-/

/- warning: typevec.typevec_cases_nil₂_append_fun -> TypeVec.typevecCasesNil₂_appendFun is a dubious translation:
lean 3 declaration is
  forall {β : (TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2}))) -> Sort.{u3}} (f : β (TypeVec.nilFun.{u1, u2} (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})))), Eq.{u3} (β (TypeVec.nilFun.{u1, u2} (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})))) (TypeVec.typevecCasesNil₂.{u1, u2, u3} β f (TypeVec.nilFun.{u1, u2} (Fin2.elim0.{succ (succ u1)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u1})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Type.{u2})))) f
but is expected to have type
  forall {β : (TypeVec.Arrow.{u3, u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Fin2.elim0.{succ (succ u3)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u3})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2}))) -> Sort.{u1}} (f : β (TypeVec.nilFun.{u3, u2} (Fin2.elim0.{succ (succ u3)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u3})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2})))), Eq.{u1} (β (TypeVec.nilFun.{u3, u2} (Fin2.elim0.{succ (succ u3)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u3})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2})))) (TypeVec.typevecCasesNil₂.{u3, u2, u1} β f (TypeVec.nilFun.{u3, u2} (Fin2.elim0.{succ (succ u3)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u3})) (Fin2.elim0.{succ (succ u2)} (fun (ᾰ : Fin2 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Type.{u2})))) f
Case conversion may be inaccurate. Consider using '#align typevec.typevec_cases_nil₂_append_fun TypeVec.typevecCasesNil₂_appendFunₓ'. -/
theorem typevecCasesNil₂_appendFun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort _} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl
#align typevec.typevec_cases_nil₂_append_fun TypeVec.typevecCasesNil₂_appendFun

/- warning: typevec.typevec_cases_cons₂_append_fun -> TypeVec.typevecCasesCons₂_appendFun is a dubious translation:
lean 3 declaration is
  forall (n : Nat) (t : Type.{u1}) (t' : Type.{u2}) (v : TypeVec.{u1} n) (v' : TypeVec.{u2} n) {β : (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n v t) (TypeVec.append1.{u2} n v' t')) -> Sort.{u3}} (F : forall (f : t -> t') (fs : TypeVec.Arrow.{u1, u2} n v v'), β (TypeVec.appendFun.{u1, u2} n v v' t t' fs f)) (f : t -> t') (fs : TypeVec.Arrow.{u1, u2} n v v'), Eq.{u3} (β (TypeVec.appendFun.{u1, u2} n v v' t t' fs f)) (TypeVec.typevecCasesCons₂.{u1, u2, u3} n t t' v v' β F (TypeVec.appendFun.{u1, u2} n v v' t t' fs f)) (F f fs)
but is expected to have type
  forall (n : Nat) (t : Type.{u3}) (t' : Type.{u2}) (v : TypeVec.{u3} n) (v' : TypeVec.{u2} n) {β : (TypeVec.Arrow.{u3, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u3} n v t) (TypeVec.append1.{u2} n v' t')) -> Sort.{u1}} (F : forall (f : t -> t') (fs : TypeVec.Arrow.{u3, u2} n v v'), β (TypeVec.appendFun.{u3, u2} n v v' t t' fs f)) (f : t -> t') (fs : TypeVec.Arrow.{u3, u2} n v v'), Eq.{u1} (β (TypeVec.appendFun.{u3, u2} n v v' t t' fs f)) (TypeVec.typevecCasesCons₂.{u3, u2, u1} n t t' v v' β F (TypeVec.appendFun.{u3, u2} n v v' t t' fs f)) (F f fs)
Case conversion may be inaccurate. Consider using '#align typevec.typevec_cases_cons₂_append_fun TypeVec.typevecCasesCons₂_appendFunₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem typevecCasesCons₂_appendFun (n : ℕ) (t t' : Type _) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort _} (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl
#align typevec.typevec_cases_cons₂_append_fun TypeVec.typevecCasesCons₂_appendFun

#print TypeVec.PredLast /-
-- for lifting predicates and relations
/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def PredLast (α : TypeVec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | Fin2.fs i => fun x => True
  | Fin2.fz => p
#align typevec.pred_last TypeVec.PredLast
-/

#print TypeVec.RelLast /-
/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and
all the other elements are equal. -/
def RelLast (α : TypeVec n) {β γ : Type _} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
  | Fin2.fs i => Eq
  | Fin2.fz => r
#align typevec.rel_last TypeVec.RelLast
-/

section Liftp'

open Nat

#print TypeVec.repeat /-
/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def repeat : ∀ (n : ℕ) (t : Sort _), TypeVec n
  | 0, t => Fin2.elim0
  | Nat.succ i, t => append1 (repeat i t) t
#align typevec.repeat TypeVec.repeat
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.prod /-
/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : ∀ {n} (α β : TypeVec.{u} n), TypeVec n
  | 0, α, β => Fin2.elim0
  | n + 1, α, β => Prod (drop α) (drop β) ::: last α × last β
#align typevec.prod TypeVec.prod
-/

-- mathport name: typevec.prod
scoped[MvFunctor] infixl:45 " ⊗ " => TypeVec.prod

#print TypeVec.const /-
/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ repeat _ β
  | succ n, α, Fin2.fs i => const (drop α) _
  | succ n, α, Fin2.fz => fun _ => x
#align typevec.const TypeVec.const
-/

open Function (uncurry)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.repeatEq /-
/-- vector of equality on a product of vectors -/
def repeatEq : ∀ {n} (α : TypeVec n), α ⊗ α ⟹ repeat _ Prop
  | 0, α => nilFun
  | succ n, α => repeat_eq (drop α) ::: uncurry Eq
#align typevec.repeat_eq TypeVec.repeatEq
-/

/- warning: typevec.const_append1 -> TypeVec.const_append1 is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} (x : γ) {n : Nat} (α : TypeVec.{u1} n), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β) (TypeVec.repeat.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) γ)) (TypeVec.const.{u2, u1} γ x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β)) (TypeVec.appendFun.{u1, u2} n α (TypeVec.repeat.{u2} (Nat.add n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) γ) β γ (TypeVec.const.{u2, u1} γ x n α) (fun (_x : β) => x))
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u1}} (x : γ) {n : Nat} (α : TypeVec.{u2} n), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β) (TypeVec.repeat.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) γ)) (TypeVec.const.{u1, u2} γ x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β)) (TypeVec.appendFun.{u2, u1} n α (TypeVec.repeat.{u1} n γ) β γ (TypeVec.const.{u1, u2} γ x n α) (fun (_x : β) => x))
Case conversion may be inaccurate. Consider using '#align typevec.const_append1 TypeVec.const_append1ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := by
  ext i : 1 <;> cases i <;> rfl
#align typevec.const_append1 TypeVec.const_append1

/- warning: typevec.eq_nil_fun -> TypeVec.eq_nilFun is a dubious translation:
lean 3 declaration is
  forall {α : TypeVec.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))} {β : TypeVec.{u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))} (f : TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α β), Eq.{max 1 (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α β) f (TypeVec.nilFun.{u1, u2} α β)
but is expected to have type
  forall {α : TypeVec.{u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))} {β : TypeVec.{u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))} (f : TypeVec.Arrow.{u2, u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α β), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α β) f (TypeVec.nilFun.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align typevec.eq_nil_fun TypeVec.eq_nilFunₓ'. -/
theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nil_fun := by ext x <;> cases x
#align typevec.eq_nil_fun TypeVec.eq_nilFun

#print TypeVec.id_eq_nilFun /-
theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nil_fun := by ext x <;> cases x
#align typevec.id_eq_nil_fun TypeVec.id_eq_nilFun
-/

/- warning: typevec.const_nil -> TypeVec.const_nil is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} (x : β) (α : TypeVec.{u2} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), Eq.{max 1 (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α (TypeVec.repeat.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) β)) (TypeVec.const.{u1, u2} β x (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) α) (TypeVec.nilFun.{u2, u1} α (TypeVec.repeat.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) β))
but is expected to have type
  forall {β : Type.{u2}} (x : β) (α : TypeVec.{u1} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), Eq.{max (succ u1) (succ u2)} (TypeVec.Arrow.{u1, u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α (TypeVec.repeat.{u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) β)) (TypeVec.const.{u2, u1} β x (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) α) (TypeVec.nilFun.{u1, u2} α (TypeVec.repeat.{u2} (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) β))
Case conversion may be inaccurate. Consider using '#align typevec.const_nil TypeVec.const_nilₓ'. -/
theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nil_fun := by
  ext i : 1 <;> cases i <;> rfl
#align typevec.const_nil TypeVec.const_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.repeat_eq_append1 /-
@[typevec]
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) :
    repeatEq (α ::: β) = splitFun (repeatEq α) (uncurry Eq) := by induction n <;> rfl
#align typevec.repeat_eq_append1 TypeVec.repeat_eq_append1
-/

#print TypeVec.repeat_eq_nil /-
@[typevec]
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nil_fun := by ext i : 1 <;> cases i <;> rfl
#align typevec.repeat_eq_nil TypeVec.repeat_eq_nil
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.PredLast' /-
/-- predicate on a type vector to constrain only the last object -/
def PredLast' (α : TypeVec n) {β : Type _} (p : β → Prop) : (α ::: β) ⟹ repeat (n + 1) Prop :=
  splitFun (TypeVec.const True α) p
#align typevec.pred_last' TypeVec.PredLast'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.RelLast' /-
/-- predicate on the product of two type vectors to constrain only their last object -/
def RelLast' (α : TypeVec n) {β : Type _} (p : β → β → Prop) :
    (α ::: β) ⊗ (α ::: β) ⟹ repeat (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)
#align typevec.rel_last' TypeVec.RelLast'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.Curry /-
/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def Curry (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)
#align typevec.curry TypeVec.Curry
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.Curry.inhabited /-
instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I
#align typevec.curry.inhabited TypeVec.Curry.inhabited
-/

#print TypeVec.dropRepeat /-
/-- arrow to remove one element of a `repeat` vector -/
def dropRepeat (α : Type _) : ∀ {n}, drop (repeat (succ n) α) ⟹ repeat n α
  | succ n, Fin2.fs i => drop_repeat i
  | succ n, Fin2.fz => id
#align typevec.drop_repeat TypeVec.dropRepeat
-/

#print TypeVec.ofRepeat /-
/-- projection for a repeat vector -/
def ofRepeat {α : Sort _} : ∀ {n i}, repeat n α i → α
  | _, Fin2.fz => id
  | _, Fin2.fs i => @of_repeat _ i
#align typevec.of_repeat TypeVec.ofRepeat
-/

#print TypeVec.const_iff_true /-
theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := by
  induction i <;> [rfl, erw [TypeVec.const, @i_ih (drop α) x]]
#align typevec.const_iff_true TypeVec.const_iff_true
-/

-- variables  {F : typevec.{u} n → Type*} [mvfunctor F]
variable {α β γ : TypeVec.{u} n}

variable (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

#print TypeVec.prod.fst /-
/-- left projection of a `prod` vector -/
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | succ n, α, β, Fin2.fs i => @Prod.fst _ (drop α) (drop β) i
  | succ n, α, β, Fin2.fz => Prod.fst
#align typevec.prod.fst TypeVec.prod.fst
-/

#print TypeVec.prod.snd /-
/-- right projection of a `prod` vector -/
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | succ n, α, β, Fin2.fs i => @Prod.snd _ (drop α) (drop β) i
  | succ n, α, β, Fin2.fz => Prod.snd
#align typevec.prod.snd TypeVec.prod.snd
-/

#print TypeVec.prod.diag /-
/-- introduce a product where both components are the same -/
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | succ n, α, Fin2.fs i, x => @prod.diag _ (drop α) _ x
  | succ n, α, Fin2.fz, x => (x, x)
#align typevec.prod.diag TypeVec.prod.diag
-/

#print TypeVec.prod.mk /-
/-- constructor for `prod` -/
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i → β i → (α ⊗ β) i
  | succ n, α, β, Fin2.fs i => Prod.mk i
  | succ n, α, β, Fin2.fz => Prod.mk
#align typevec.prod.mk TypeVec.prod.mk
-/

#print TypeVec.prod_fst_mk /-
@[simp]
theorem prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by induction i <;> simp_all [Prod.fst, Prod.mk]
#align typevec.prod_fst_mk TypeVec.prod_fst_mk
-/

#print TypeVec.prod_snd_mk /-
@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by induction i <;> simp_all [Prod.snd, Prod.mk]
#align typevec.prod_snd_mk TypeVec.prod_snd_mk
-/

#print TypeVec.prod.map /-
/-- `prod` is functorial -/
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | succ n, α, α', β, β', x, y, Fin2.fs i, a =>
    @Prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ n, α, α', β, β', x, y, Fin2.fz, a => (x _ a.1, y _ a.2)
#align typevec.prod.map TypeVec.prod.map
-/

-- mathport name: typevec.prod.map
scoped[MvFunctor] infixl:45 " ⊗' " => TypeVec.prod.map

#print TypeVec.fst_prod_mk /-
theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  ext i <;> induction i <;> [rfl, apply i_ih]
#align typevec.fst_prod_mk TypeVec.fst_prod_mk
-/

#print TypeVec.snd_prod_mk /-
theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  ext i <;> induction i <;> [rfl, apply i_ih]
#align typevec.snd_prod_mk TypeVec.snd_prod_mk
-/

#print TypeVec.fst_diag /-
theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  ext i <;> induction i <;> [rfl, apply i_ih]
#align typevec.fst_diag TypeVec.fst_diag
-/

#print TypeVec.snd_diag /-
theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  ext i <;> induction i <;> [rfl, apply i_ih]
#align typevec.snd_diag TypeVec.snd_diag
-/

#print TypeVec.repeatEq_iff_eq /-
theorem repeatEq_iff_eq {α : TypeVec n} {i x y} : ofRepeat (repeatEq α i (prod.mk _ x y)) ↔ x = y :=
  by induction i <;> [rfl, erw [repeat_eq, @i_ih (drop α) x y]]
#align typevec.repeat_eq_iff_eq TypeVec.repeatEq_iff_eq
-/

#print TypeVec.Subtype_ /-
/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def Subtype_ : ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ repeat n Prop), TypeVec n
  | _, α, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, α, p, Fin2.fs i => subtype_ (dropFun p) i
#align typevec.subtype_ TypeVec.Subtype_
-/

#print TypeVec.subtypeVal /-
/-- projection on `subtype_` -/
def subtypeVal : ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ repeat n Prop), Subtype_ p ⟹ α
  | succ n, α, p, Fin2.fs i => @subtype_val n _ _ i
  | succ n, α, p, Fin2.fz => Subtype.val
#align typevec.subtype_val TypeVec.subtypeVal
-/

#print TypeVec.toSubtype /-
/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def toSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ repeat n Prop),
      (fun i : Fin2 n => { x // of_repeat <| p i x }) ⟹ Subtype_ p
  | succ n, α, p, Fin2.fs i, x => to_subtype (dropFun p) i x
  | succ n, α, p, Fin2.fz, x => x
#align typevec.to_subtype TypeVec.toSubtype
-/

#print TypeVec.ofSubtype /-
/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def ofSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ repeat n Prop),
      Subtype_ p ⟹ fun i : Fin2 n => { x // of_repeat <| p i x }
  | succ n, α, p, Fin2.fs i, x => of_subtype _ i x
  | succ n, α, p, Fin2.fz, x => x
#align typevec.of_subtype TypeVec.ofSubtype
-/

#print TypeVec.toSubtype' /-
/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def toSubtype' :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ repeat n Prop),
      (fun i : Fin2 n => { x : α i × α i // of_repeat <| p i (prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | succ n, α, p, Fin2.fs i, x => to_subtype' (dropFun p) i x
  | succ n, α, p, Fin2.fz, x => ⟨x.val, cast (by congr <;> simp [Prod.mk]) x.property⟩
#align typevec.to_subtype' TypeVec.toSubtype'
-/

#print TypeVec.ofSubtype' /-
/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def ofSubtype' :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ repeat n Prop),
      Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // of_repeat <| p i (prod.mk _ x.1 x.2) }
  | _, α, p, Fin2.fs i, x => of_subtype' _ i x
  | _, α, p, Fin2.fz, x => ⟨x.val, cast (by congr <;> simp [Prod.mk]) x.property⟩
#align typevec.of_subtype' TypeVec.ofSubtype'
-/

#print TypeVec.diagSub /-
/-- similar to `diag` but the target vector is a `subtype_`
guaranteeing the equality of the components -/
def diagSub : ∀ {n} {α : TypeVec.{u} n}, α ⟹ Subtype_ (repeatEq α)
  | succ n, α, Fin2.fs i, x => @diag_sub _ (drop α) _ x
  | succ n, α, Fin2.fz, x => ⟨(x, x), rfl⟩
#align typevec.diag_sub TypeVec.diagSub
-/

#print TypeVec.subtypeVal_nil /-
theorem subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ repeat 0 Prop) :
    TypeVec.subtypeVal ps = nil_fun :=
  funext <| by rintro ⟨⟩ <;> rfl
#align typevec.subtype_val_nil TypeVec.subtypeVal_nil
-/

#print TypeVec.diag_sub_val /-
theorem diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diag_sub = prod.diag := by
  ext i <;> induction i <;> [rfl, apply i_ih]
#align typevec.diag_sub_val TypeVec.diag_sub_val
-/

#print TypeVec.prod_id /-
theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) :=
  by
  intros ; ext (i a); induction i
  · cases a
    rfl
  · apply i_ih
#align typevec.prod_id TypeVec.prod_id
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print TypeVec.append_prod_appendFun /-
theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u} {f₀ : α ⟹ α'}
    {g₀ : β ⟹ β'} {f₁ : φ → φ'} {g₁ : ψ → ψ'} :
    (f₀ ⊗' g₀ ::: Prod.map f₁ g₁) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  ext (i a) <;> cases i <;> [cases a, skip] <;> rfl
#align typevec.append_prod_append_fun TypeVec.append_prod_appendFun
-/

end Liftp'

#print TypeVec.dropFun_diag /-
@[simp]
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag :=
  by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.drop_fun_diag TypeVec.dropFun_diag
-/

#print TypeVec.dropFun_subtypeVal /-
@[simp]
theorem dropFun_subtypeVal {α} (p : α ⟹ repeat (n + 1) Prop) :
    dropFun (subtypeVal p) = subtypeVal _ :=
  rfl
#align typevec.drop_fun_subtype_val TypeVec.dropFun_subtypeVal
-/

#print TypeVec.lastFun_subtypeVal /-
@[simp]
theorem lastFun_subtypeVal {α} (p : α ⟹ repeat (n + 1) Prop) :
    lastFun (subtypeVal p) = Subtype.val :=
  rfl
#align typevec.last_fun_subtype_val TypeVec.lastFun_subtypeVal
-/

#print TypeVec.dropFun_toSubtype /-
@[simp]
theorem dropFun_toSubtype {α} (p : α ⟹ repeat (n + 1) Prop) : dropFun (toSubtype p) = toSubtype _ :=
  by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.drop_fun_to_subtype TypeVec.dropFun_toSubtype
-/

#print TypeVec.lastFun_toSubtype /-
@[simp]
theorem lastFun_toSubtype {α} (p : α ⟹ repeat (n + 1) Prop) : lastFun (toSubtype p) = _root_.id :=
  by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.last_fun_to_subtype TypeVec.lastFun_toSubtype
-/

#print TypeVec.dropFun_of_subtype /-
@[simp]
theorem dropFun_of_subtype {α} (p : α ⟹ repeat (n + 1) Prop) :
    dropFun (ofSubtype p) = ofSubtype _ := by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.drop_fun_of_subtype TypeVec.dropFun_of_subtype
-/

#print TypeVec.lastFun_of_subtype /-
@[simp]
theorem lastFun_of_subtype {α} (p : α ⟹ repeat (n + 1) Prop) : lastFun (ofSubtype p) = _root_.id :=
  by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.last_fun_of_subtype TypeVec.lastFun_of_subtype
-/

#print TypeVec.dropFun_RelLast' /-
@[simp]
theorem dropFun_RelLast' {α : TypeVec n} {β} (R : β → β → Prop) :
    dropFun (RelLast' α R) = repeatEq α :=
  rfl
#align typevec.drop_fun_rel_last TypeVec.dropFun_RelLast'
-/

attribute [simp] drop_append1'

open MvFunctor

#print TypeVec.dropFun_prod /-
@[simp]
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') :=
  by
  ext i : 2
  induction i <;> simp [drop_fun, *] <;> rfl
#align typevec.drop_fun_prod TypeVec.dropFun_prod
-/

#print TypeVec.lastFun_prod /-
@[simp]
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') :=
  by
  ext i : 1
  induction i <;> simp [last_fun, *] <;> rfl
#align typevec.last_fun_prod TypeVec.lastFun_prod
-/

#print TypeVec.dropFun_from_append1_drop_last /-
@[simp]
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl
#align typevec.drop_fun_from_append1_drop_last TypeVec.dropFun_from_append1_drop_last
-/

#print TypeVec.lastFun_from_append1_drop_last /-
@[simp]
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl
#align typevec.last_fun_from_append1_drop_last TypeVec.lastFun_from_append1_drop_last
-/

#print TypeVec.dropFun_id /-
@[simp]
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl
#align typevec.drop_fun_id TypeVec.dropFun_id
-/

#print TypeVec.prod_map_id /-
@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id :=
  by
  ext i : 2
  induction i <;> simp only [TypeVec.prod.map, *, drop_fun_id]
  cases x
  rfl
  rfl
#align typevec.prod_map_id TypeVec.prod_map_id
-/

#print TypeVec.subtypeVal_diagSub /-
@[simp]
theorem subtypeVal_diagSub {α : TypeVec n} : subtypeVal (repeatEq α) ⊚ diag_sub = prod.diag :=
  by
  clear * -
  ext i
  induction i <;> [rfl, apply i_ih]
#align typevec.subtype_val_diag_sub TypeVec.subtypeVal_diagSub
-/

#print TypeVec.toSubtype_of_subtype /-
@[simp]
theorem toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ repeat n Prop) :
    toSubtype p ⊚ ofSubtype p = id := by
  ext (i x) <;> induction i <;> dsimp only [id, to_subtype, comp, of_subtype] at * <;> simp [*]
#align typevec.to_subtype_of_subtype TypeVec.toSubtype_of_subtype
-/

#print TypeVec.subtypeVal_toSubtype /-
@[simp]
theorem subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ repeat n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := by
  ext (i x) <;> induction i <;> dsimp only [to_subtype, comp, subtype_val] at * <;> simp [*]
#align typevec.subtype_val_to_subtype TypeVec.subtypeVal_toSubtype
-/

/- warning: typevec.to_subtype_of_subtype_assoc -> TypeVec.toSubtype_of_subtype_assoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : TypeVec.{u1} n} {β : TypeVec.{u2} n} (p : TypeVec.Arrow.{u1, 0} n α (TypeVec.repeat.{0} n Prop)) (f : TypeVec.Arrow.{u2, u1} n β (TypeVec.Subtype_.{u1} n α p)), Eq.{max 1 (succ u2) (succ u1)} (TypeVec.Arrow.{u2, u1} n β (TypeVec.Subtype_.{u1} n α p)) (TypeVec.comp.{u2, u1, u1} n β (fun (i : Fin2 n) => Subtype.{succ u1} (α i) (fun (x : α i) => TypeVec.ofRepeat.{0} Prop n i (p i x))) (TypeVec.Subtype_.{u1} n α p) (TypeVec.toSubtype.{u1} n α p) (TypeVec.comp.{u2, u1, u1} n β (TypeVec.Subtype_.{u1} n (fun (i : Fin2 n) => α i) (fun (i : Fin2 n) (x : α i) => p i x)) (fun (i : Fin2 n) => Subtype.{succ u1} (α i) (fun (x : α i) => TypeVec.ofRepeat.{0} Prop n i (p i x))) (TypeVec.ofSubtype.{u1} n (fun (i : Fin2 n) => α i) (fun (i : Fin2 n) (x : α i) => p i x)) f)) f
but is expected to have type
  forall {n : Nat} {α : TypeVec.{u2} n} {β : TypeVec.{u1} n} (p : TypeVec.Arrow.{u2, 0} n α (TypeVec.repeat.{0} n Prop)) (f : TypeVec.Arrow.{u1, u2} n β (TypeVec.Subtype_.{u2} n α p)), Eq.{max (succ u2) (succ u1)} (TypeVec.Arrow.{u1, u2} n β (TypeVec.Subtype_.{u2} n α p)) (TypeVec.comp.{u1, u2, u2} n β (fun (i : Fin2 n) => Subtype.{succ u2} (α i) (fun (x : α i) => TypeVec.ofRepeat.{0} Prop n i (p i x))) (TypeVec.Subtype_.{u2} n α p) (TypeVec.toSubtype.{u2} n α p) (TypeVec.comp.{u1, u2, u2} n β (TypeVec.Subtype_.{u2} n (fun (i : Fin2 n) => α i) (fun (i : Fin2 n) (x : α i) => p i x)) (fun (i : Fin2 n) => Subtype.{succ u2} (α i) (fun (x : α i) => TypeVec.ofRepeat.{0} Prop n i (p i x))) (TypeVec.ofSubtype.{u2} n (fun (i : Fin2 n) => α i) (fun (i : Fin2 n) (x : α i) => p i x)) f)) f
Case conversion may be inaccurate. Consider using '#align typevec.to_subtype_of_subtype_assoc TypeVec.toSubtype_of_subtype_assocₓ'. -/
@[simp]
theorem toSubtype_of_subtype_assoc {α β : TypeVec n} (p : α ⟹ repeat n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := by rw [← comp_assoc, to_subtype_of_subtype] <;> simp
#align typevec.to_subtype_of_subtype_assoc TypeVec.toSubtype_of_subtype_assoc

#print TypeVec.toSubtype'_of_subtype' /-
@[simp]
theorem toSubtype'_of_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ repeat n Prop) :
    toSubtype' r ⊚ ofSubtype' r = id := by
  ext (i x) <;> induction i <;> dsimp only [id, to_subtype', comp, of_subtype'] at * <;>
    simp [Subtype.eta, *]
#align typevec.to_subtype'_of_subtype' TypeVec.toSubtype'_of_subtype'
-/

#print TypeVec.subtypeVal_toSubtype' /-
theorem subtypeVal_toSubtype' {α : TypeVec n} (r : α ⊗ α ⟹ repeat n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd := by
  ext (i x) <;> induction i <;> dsimp only [id, to_subtype', comp, subtype_val, Prod.mk] at * <;>
    simp [*]
#align typevec.subtype_val_to_subtype' TypeVec.subtypeVal_toSubtype'
-/

end TypeVec

