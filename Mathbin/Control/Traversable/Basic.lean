/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.traversable.basic
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Functor
import Mathbin.Tactic.Ext

/-!
# Traversable type class

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/788
> Any changes to this file require a corresponding PR to mathlib4.

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `list`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → io response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : list email`, using calling
`invite` using `map` gives us the following: `map invite guests : list
(io response)`.  It is not what we need. We need something of type `io
(list response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : io (list response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `io` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
  * `traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`,
    turns a collection of effects into an effect returning a collection
  * `is_lawful_traversable` - laws for a traversable functor
  * `applicative_transformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
   Journal of Functional Programming 18:1 (2008) 1-13, online at
   <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
   in Mathematically-Structured Functional Programming, 2006, online at
   <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
   in Mathematically-Structured Functional Programming, 2012,
   online at <http://arxiv.org/pdf/1202.2919>
-/


open Function hiding comp

universe u v w

section ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

variable (G : Type u → Type w) [Applicative G] [LawfulApplicative G]

/- warning: applicative_transformation -> ApplicativeTransformation is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1} -> Type.{u2}) [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] (G : Type.{u1} -> Type.{u3}) [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3], Type.{max (succ u1) u2 u3}
but is expected to have type
  forall (F : Type.{u1} -> Type.{u2}) [_inst_1 : Applicative.{u1, u2} F] (_inst_2 : Type.{u1} -> Type.{u3}) [G : Applicative.{u1, u3} _inst_2], Type.{max (succ u1) u2 u3}
Case conversion may be inaccurate. Consider using '#align applicative_transformation ApplicativeTransformationₓ'. -/
/-- A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `has_pure.pure` and
`functor.map` (`<*>`) operations. See
`applicative_transformation.preserves_map` for naturality. -/
structure ApplicativeTransformation : Type max (u + 1) v w where
  app : ∀ α : Type u, F α → G α
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y
#align applicative_transformation ApplicativeTransformation

end ApplicativeTransformation

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

variable (G : Type u → Type w) [Applicative G] [LawfulApplicative G]

instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨ApplicativeTransformation.app⟩

variable {F G}

/- warning: applicative_transformation.app_eq_coe -> ApplicativeTransformation.app_eq_coe is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4), Eq.{max (succ (succ u1)) (succ u2) (succ u3)} (forall (α : Type.{u1}), (F α) -> (G α)) (ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4 η) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G), Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (forall (α : Type.{u1}), (F α) -> (_inst_2 α)) (ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3) (fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245)
Case conversion may be inaccurate. Consider using '#align applicative_transformation.app_eq_coe ApplicativeTransformation.app_eq_coeₓ'. -/
@[simp]
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl
#align applicative_transformation.app_eq_coe ApplicativeTransformation.app_eq_coe

/- warning: applicative_transformation.coe_mk -> ApplicativeTransformation.coe_mk is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (f : forall (α : Type.{u1}), (F α) -> (G α)) (pp : forall {α : Type.{u1}} (x : α), Eq.{succ u3} (G α) (f α (Pure.pure.{u1, u2} (fun (α : Type.{u1}) => F α) (Applicative.toHasPure.{u1, u2} (fun (α : Type.{u1}) => F α) _inst_1) α x)) (Pure.pure.{u1, u3} (fun (α : Type.{u1}) => G α) (Applicative.toHasPure.{u1, u3} (fun (α : Type.{u1}) => G α) _inst_3) α x)) (ps : forall {α : Type.{u1}} {β : Type.{u1}} (x : F (α -> β)) (y : F α), Eq.{succ u3} (G β) (f β (Seq.seq.{u1, u2} (fun (α : Type.{u1}) => F α) (Applicative.toHasSeq.{u1, u2} (fun (α : Type.{u1}) => F α) _inst_1) α β x y)) (Seq.seq.{u1, u3} (fun (α : Type.{u1}) => G α) (Applicative.toHasSeq.{u1, u3} (fun (α : Type.{u1}) => G α) _inst_3) α β (f (α -> β) x) (f α y))), Eq.{max (succ (succ u1)) (succ u2) (succ u3)} (forall {α : Type.{u1}}, (F α) -> (G α)) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 _inst_2 (fun (α : Type.{u1}) => G α) _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 _inst_2 (fun (α : Type.{u1}) => G α) _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 _inst_2 (fun (α : Type.{u1}) => G α) _inst_3 _inst_4) (ApplicativeTransformation.mk.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 _inst_2 (fun (α : Type.{u1}) => G α) _inst_3 _inst_4 f pp ps)) f
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : forall (α : Type.{u1}), (F α) -> (_inst_2 α)) (_inst_4 : forall {α : Type.{u1}} (x : α), Eq.{succ u3} (_inst_2 α) (_inst_3 α (Pure.pure.{u1, u2} (fun (α : Type.{u1}) => F α) (Applicative.toPure.{u1, u2} (fun (α : Type.{u1}) => F α) _inst_1) α x)) (Pure.pure.{u1, u3} (fun (α : Type.{u1}) => _inst_2 α) (Applicative.toPure.{u1, u3} (fun (α : Type.{u1}) => _inst_2 α) G) α x)) (f : forall {α : Type.{u1}} {ᾰ : Type.{u1}} (x : F (α -> ᾰ)) (y : F α), Eq.{succ u3} (_inst_2 ᾰ) (_inst_3 ᾰ (Seq.seq.{u1, u2} (fun (α : Type.{u1}) => F α) (Applicative.toSeq.{u1, u2} (fun (α : Type.{u1}) => F α) _inst_1) α ᾰ x (fun (x._@.Mathlib.Control.Traversable.Basic._hyg.113 : Unit) => y))) (Seq.seq.{u1, u3} (fun (α : Type.{u1}) => _inst_2 α) (Applicative.toSeq.{u1, u3} (fun (α : Type.{u1}) => _inst_2 α) G) α ᾰ (_inst_3 (α -> ᾰ) x) (fun (x._@.Mathlib.Control.Traversable.Basic._hyg.127 : Unit) => _inst_3 α y))), Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (forall {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}}, (F α._@.Mathlib.Control.Traversable.Basic._hyg.245) -> (_inst_2 α._@.Mathlib.Control.Traversable.Basic._hyg.245)) (fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 (fun (α : Type.{u1}) => _inst_2 α) G (ApplicativeTransformation.mk.{u1, u2, u3} (fun (α : Type.{u1}) => F α) _inst_1 (fun (α : Type.{u1}) => _inst_2 α) G _inst_3 _inst_4 f) α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_3
Case conversion may be inaccurate. Consider using '#align applicative_transformation.coe_mk ApplicativeTransformation.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : ∀ α : Type u, F α → G α) (pp ps) :
    ⇑(ApplicativeTransformation.mk f pp ps) = f :=
  rfl
#align applicative_transformation.coe_mk ApplicativeTransformation.coe_mk

/- warning: applicative_transformation.congr_fun -> ApplicativeTransformation.congr_fun is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (η' : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4), (Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η η') -> (forall {α : Type.{u1}} (x : F α), Eq.{succ u3} (G α) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α x) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η' α x))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) (_inst_4 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G), (Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) _inst_3 _inst_4) -> (forall {η' : Type.{u1}} (h : F η'), Eq.{succ u3} (_inst_2 η') ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) η' h) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_4 α._@.Mathlib.Control.Traversable.Basic._hyg.245) η' h))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.congr_fun ApplicativeTransformation.congr_funₓ'. -/
protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
    (x : F α) : η x = η' x :=
  congr_arg (fun η'' : ApplicativeTransformation F G => η'' x) h
#align applicative_transformation.congr_fun ApplicativeTransformation.congr_fun

/- warning: applicative_transformation.congr_arg -> ApplicativeTransformation.congr_arg is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) {α : Type.{u1}} {x : F α} {y : F α}, (Eq.{succ u2} (F α) x y) -> (Eq.{succ u3} (G α) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α x) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α y))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) {_inst_4 : Type.{u1}} {η : F _inst_4} {α : F _inst_4}, (Eq.{succ u2} (F _inst_4) η α) -> (Eq.{succ u3} (_inst_2 _inst_4) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_4 η) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_4 α))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.congr_arg ApplicativeTransformation.congr_argₓ'. -/
protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congr_arg (fun z : F α => η z) h
#align applicative_transformation.congr_arg ApplicativeTransformation.congr_arg

/- warning: applicative_transformation.coe_inj -> ApplicativeTransformation.coe_inj is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {{η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4}} {{η' : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4}}, (Eq.{max (succ (succ u1)) (succ u2) (succ u3)} ((fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) η) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η')) -> (Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η η')
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {{_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G}} {{_inst_4 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G}}, (Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (forall {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}}, (F α._@.Mathlib.Control.Traversable.Basic._hyg.245) -> (_inst_2 α._@.Mathlib.Control.Traversable.Basic._hyg.245)) (fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) (fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_4 α._@.Mathlib.Control.Traversable.Basic._hyg.245)) -> (Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align applicative_transformation.coe_inj ApplicativeTransformation.coe_injₓ'. -/
theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : ∀ α, F α → G α) = η') : η = η' :=
  by 
  cases η
  cases η'
  congr
  exact h
#align applicative_transformation.coe_inj ApplicativeTransformation.coe_inj

/- warning: applicative_transformation.ext -> ApplicativeTransformation.ext is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {{η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4}} {{η' : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4}}, (forall (α : Type.{u1}) (x : F α), Eq.{succ u3} (G α) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α x) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η' α x)) -> (Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η η')
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {{_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G}} {{_inst_4 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G}}, (forall (α : Type.{u1}) (x : F α), Eq.{succ u3} (_inst_2 α) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) α x) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_4 α._@.Mathlib.Control.Traversable.Basic._hyg.245) α x)) -> (Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align applicative_transformation.ext ApplicativeTransformation.extₓ'. -/
@[ext]
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
    η = η' := by 
  apply coe_inj
  ext1 α
  exact funext (h α)
#align applicative_transformation.ext ApplicativeTransformation.ext

/- warning: applicative_transformation.ext_iff -> ApplicativeTransformation.ext_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4} {η' : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4}, Iff (Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η η') (forall (α : Type.{u1}) (x : F α), Eq.{succ u3} (G α) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α x) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η' α x))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G} {_inst_4 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G}, Iff (Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) _inst_3 _inst_4) (forall (α : Type.{u1}) (x : F α), Eq.{succ u3} (_inst_2 α) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) α x) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_4 α._@.Mathlib.Control.Traversable.Basic._hyg.245) α x))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.ext_iff ApplicativeTransformation.ext_iffₓ'. -/
theorem ext_iff {η η' : ApplicativeTransformation F G} :
    η = η' ↔ ∀ (α : Type u) (x : F α), η x = η' x :=
  ⟨fun h α x => h ▸ rfl, fun h => ext h⟩
#align applicative_transformation.ext_iff ApplicativeTransformation.ext_iff

section Preserves

variable (η : ApplicativeTransformation F G)

/- warning: applicative_transformation.preserves_pure -> ApplicativeTransformation.preserves_pure is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) {α : Type.{u1}} (x : α), Eq.{succ u3} (G α) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α (Pure.pure.{u1, u2} F (Applicative.toHasPure.{u1, u2} F _inst_1) α x)) (Pure.pure.{u1, u3} G (Applicative.toHasPure.{u1, u3} G _inst_3) α x)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) {_inst_4 : Type.{u1}} (η : _inst_4), Eq.{succ u3} (_inst_2 _inst_4) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_4 (Pure.pure.{u1, u2} F (Applicative.toPure.{u1, u2} F _inst_1) _inst_4 η)) (Pure.pure.{u1, u3} _inst_2 (Applicative.toPure.{u1, u3} _inst_2 G) _inst_4 η)
Case conversion may be inaccurate. Consider using '#align applicative_transformation.preserves_pure ApplicativeTransformation.preserves_pureₓ'. -/
@[functor_norm]
theorem preserves_pure {α} : ∀ x : α, η (pure x) = pure x :=
  η.preserves_pure'
#align applicative_transformation.preserves_pure ApplicativeTransformation.preserves_pure

/- warning: applicative_transformation.preserves_seq -> ApplicativeTransformation.preserves_seq is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) {α : Type.{u1}} {β : Type.{u1}} (x : F (α -> β)) (y : F α), Eq.{succ u3} (G β) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η β (Seq.seq.{u1, u2} F (Applicative.toHasSeq.{u1, u2} F _inst_1) α β x y)) (Seq.seq.{u1, u3} G (Applicative.toHasSeq.{u1, u3} G _inst_3) α β (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η (α -> β) x) (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α y))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) {_inst_4 : Type.{u1}} {η : Type.{u1}} (α : F (_inst_4 -> η)) (β : F _inst_4), Eq.{succ u3} (_inst_2 η) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) η (Seq.seq.{u1, u2} F (Applicative.toSeq.{u1, u2} F _inst_1) _inst_4 η α (fun (x._@.Mathlib.Control.Traversable.Basic._hyg.754 : Unit) => β))) (Seq.seq.{u1, u3} _inst_2 (Applicative.toSeq.{u1, u3} _inst_2 G) _inst_4 η ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) (_inst_4 -> η) α) (fun (x._@.Mathlib.Control.Traversable.Basic._hyg.767 : Unit) => (fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_4 β))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.preserves_seq ApplicativeTransformation.preserves_seqₓ'. -/
@[functor_norm]
theorem preserves_seq {α β : Type u} : ∀ (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'
#align applicative_transformation.preserves_seq ApplicativeTransformation.preserves_seq

#print ApplicativeTransformation.preserves_map /-
@[functor_norm]
theorem preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y := by
  rw [← pure_seq_eq_map, η.preserves_seq] <;> simp [functor_norm]
#align applicative_transformation.preserves_map ApplicativeTransformation.preserves_map
-/

#print ApplicativeTransformation.preserves_map' /-
theorem preserves_map' {α β} (x : α → β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  exact preserves_map η x y
#align applicative_transformation.preserves_map' ApplicativeTransformation.preserves_map'
-/

end Preserves

#print ApplicativeTransformation.idTransformation /-
/-- The identity applicative transformation from an applicative functor to itself. -/
def idTransformation : ApplicativeTransformation F
      F where 
  app α := id
  preserves_pure' := by simp
  preserves_seq' α β x y := by simp
#align applicative_transformation.id_transformation ApplicativeTransformation.idTransformation
-/

instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩

universe s t

variable {H : Type u → Type s} [Applicative H] [LawfulApplicative H]

/- warning: applicative_transformation.comp -> ApplicativeTransformation.comp is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {H : Type.{u1} -> Type.{u4}} [_inst_5 : Applicative.{u1, u4} H] [_inst_6 : LawfulApplicative.{u1, u4} H _inst_5], (ApplicativeTransformation.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) -> (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) -> (ApplicativeTransformation.{u1, u2, u4} F _inst_1 _inst_2 H _inst_5 _inst_6)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {_inst_3 : Type.{u1} -> Type.{u4}} [_inst_4 : Applicative.{u1, u4} _inst_3], (ApplicativeTransformation.{u1, u3, u4} _inst_2 G _inst_3 _inst_4) -> (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) -> (ApplicativeTransformation.{u1, u2, u4} F _inst_1 _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align applicative_transformation.comp ApplicativeTransformation.compₓ'. -/
/-- The composition of applicative transformations. -/
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    ApplicativeTransformation F H where 
  app α x := η' (η x)
  preserves_pure' α x := by simp [functor_norm]
  preserves_seq' α β x y := by simp [functor_norm]
#align applicative_transformation.comp ApplicativeTransformation.comp

/- warning: applicative_transformation.comp_apply -> ApplicativeTransformation.comp_apply is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {H : Type.{u1} -> Type.{u4}} [_inst_5 : Applicative.{u1, u4} H] [_inst_6 : LawfulApplicative.{u1, u4} H _inst_5] (η' : ApplicativeTransformation.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) {α : Type.{u1}} (x : F α), Eq.{succ u4} (H α) (coeFn.{succ (max (succ u1) u2 u4), max (succ (succ u1)) (succ u2) (succ u4)} (ApplicativeTransformation.{u1, u2, u4} F _inst_1 _inst_2 H _inst_5 _inst_6) (fun (_x : ApplicativeTransformation.{u1, u2, u4} F _inst_1 _inst_2 H _inst_5 _inst_6) => forall {α : Type.{u1}}, (F α) -> (H α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u4} F _inst_1 _inst_2 H _inst_5 _inst_6) (ApplicativeTransformation.comp.{u1, u2, u3, u4} F _inst_1 _inst_2 G _inst_3 _inst_4 H _inst_5 _inst_6 η' η) α x) (coeFn.{succ (max (succ u1) u3 u4), max (succ (succ u1)) (succ u3) (succ u4)} (ApplicativeTransformation.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) (fun (_x : ApplicativeTransformation.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) => forall {α : Type.{u1}}, (G α) -> (H α)) (ApplicativeTransformation.hasCoeToFun.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) η' α (coeFn.{succ (max (succ u1) u2 u3), max (succ (succ u1)) (succ u2) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (fun (_x : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) => forall {α : Type.{u1}}, (F α) -> (G α)) (ApplicativeTransformation.hasCoeToFun.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) η α x))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {_inst_3 : Type.{u1} -> Type.{u4}} [_inst_4 : Applicative.{u1, u4} _inst_3] (H : ApplicativeTransformation.{u1, u3, u4} _inst_2 G _inst_3 _inst_4) (_inst_5 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) {_inst_6 : Type.{u1}} (η' : F _inst_6), Eq.{succ u4} (_inst_3 _inst_6) ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u4} F _inst_1 _inst_3 _inst_4 (ApplicativeTransformation.comp.{u1, u2, u3, u4} F _inst_1 _inst_2 G _inst_3 _inst_4 H _inst_5) α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_6 η') ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u3, u4} _inst_2 G _inst_3 _inst_4 H α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_6 ((fun {α._@.Mathlib.Control.Traversable.Basic._hyg.245 : Type.{u1}} => ApplicativeTransformation.app.{u1, u2, u3} F _inst_1 _inst_2 G _inst_5 α._@.Mathlib.Control.Traversable.Basic._hyg.245) _inst_6 η'))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.comp_apply ApplicativeTransformation.comp_applyₓ'. -/
@[simp]
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
    {α : Type u} (x : F α) : η'.comp η x = η' (η x) :=
  rfl
#align applicative_transformation.comp_apply ApplicativeTransformation.comp_apply

/- warning: applicative_transformation.comp_assoc -> ApplicativeTransformation.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] {H : Type.{u1} -> Type.{u4}} [_inst_5 : Applicative.{u1, u4} H] [_inst_6 : LawfulApplicative.{u1, u4} H _inst_5] {I : Type.{u1} -> Type.{u5}} [_inst_7 : Applicative.{u1, u5} I] [_inst_8 : LawfulApplicative.{u1, u5} I _inst_7] (η'' : ApplicativeTransformation.{u1, u4, u5} H _inst_5 _inst_6 I _inst_7 _inst_8) (η' : ApplicativeTransformation.{u1, u3, u4} G _inst_3 _inst_4 H _inst_5 _inst_6) (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4), Eq.{succ (max (succ u1) u2 u5)} (ApplicativeTransformation.{u1, u2, u5} F _inst_1 _inst_2 I _inst_7 _inst_8) (ApplicativeTransformation.comp.{u1, u2, u3, u5} F _inst_1 _inst_2 G _inst_3 _inst_4 I _inst_7 _inst_8 (ApplicativeTransformation.comp.{u1, u3, u4, u5} G _inst_3 _inst_4 H _inst_5 _inst_6 I _inst_7 _inst_8 η'' η') η) (ApplicativeTransformation.comp.{u1, u2, u4, u5} F _inst_1 _inst_2 H _inst_5 _inst_6 I _inst_7 _inst_8 η'' (ApplicativeTransformation.comp.{u1, u2, u3, u4} F _inst_1 _inst_2 G _inst_3 _inst_4 H _inst_5 _inst_6 η' η))
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] {_inst_3 : Type.{u1} -> Type.{u4}} [_inst_4 : Applicative.{u1, u4} _inst_3] {H : Type.{u1} -> Type.{u5}} [_inst_5 : Applicative.{u1, u5} H] (_inst_6 : ApplicativeTransformation.{u1, u4, u5} _inst_3 _inst_4 H _inst_5) (I : ApplicativeTransformation.{u1, u3, u4} _inst_2 G _inst_3 _inst_4) (_inst_7 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G), Eq.{max (max (succ u5) (succ (succ u1))) (succ u2)} (ApplicativeTransformation.{u1, u2, u5} F _inst_1 H _inst_5) (ApplicativeTransformation.comp.{u1, u2, u3, u5} F _inst_1 _inst_2 G H _inst_5 (ApplicativeTransformation.comp.{u1, u3, u4, u5} _inst_2 G _inst_3 _inst_4 H _inst_5 _inst_6 I) _inst_7) (ApplicativeTransformation.comp.{u1, u2, u4, u5} F _inst_1 _inst_3 _inst_4 H _inst_5 _inst_6 (ApplicativeTransformation.comp.{u1, u2, u3, u4} F _inst_1 _inst_2 G _inst_3 _inst_4 I _inst_7))
Case conversion may be inaccurate. Consider using '#align applicative_transformation.comp_assoc ApplicativeTransformation.comp_assocₓ'. -/
theorem comp_assoc {I : Type u → Type t} [Applicative I] [LawfulApplicative I]
    (η'' : ApplicativeTransformation H I) (η' : ApplicativeTransformation G H)
    (η : ApplicativeTransformation F G) : (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl
#align applicative_transformation.comp_assoc ApplicativeTransformation.comp_assoc

/- warning: applicative_transformation.comp_id -> ApplicativeTransformation.comp_id is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4), Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (ApplicativeTransformation.comp.{u1, u2, u2, u3} F _inst_1 _inst_2 F _inst_1 _inst_2 G _inst_3 _inst_4 η (ApplicativeTransformation.idTransformation.{u1, u2} F _inst_1 _inst_2)) η
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G), Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) (ApplicativeTransformation.comp.{u1, u2, u2, u3} F _inst_1 F _inst_1 _inst_2 G _inst_3 (ApplicativeTransformation.idTransformation.{u1, u2} F _inst_1)) _inst_3
Case conversion may be inaccurate. Consider using '#align applicative_transformation.comp_id ApplicativeTransformation.comp_idₓ'. -/
@[simp]
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun α x => rfl
#align applicative_transformation.comp_id ApplicativeTransformation.comp_id

/- warning: applicative_transformation.id_comp -> ApplicativeTransformation.id_comp is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {G : Type.{u1} -> Type.{u3}} [_inst_3 : Applicative.{u1, u3} G] [_inst_4 : LawfulApplicative.{u1, u3} G _inst_3] (η : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4), Eq.{succ (max (succ u1) u2 u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G _inst_3 _inst_4) (ApplicativeTransformation.comp.{u1, u2, u3, u3} F _inst_1 _inst_2 G _inst_3 _inst_4 G _inst_3 _inst_4 (ApplicativeTransformation.idTransformation.{u1, u3} G _inst_3 _inst_4) η) η
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] {_inst_2 : Type.{u1} -> Type.{u3}} [G : Applicative.{u1, u3} _inst_2] (_inst_3 : ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G), Eq.{max (max (succ (succ u1)) (succ u2)) (succ u3)} (ApplicativeTransformation.{u1, u2, u3} F _inst_1 _inst_2 G) (ApplicativeTransformation.comp.{u1, u2, u3, u3} F _inst_1 _inst_2 G _inst_2 G (ApplicativeTransformation.idTransformation.{u1, u3} _inst_2 G) _inst_3) _inst_3
Case conversion may be inaccurate. Consider using '#align applicative_transformation.id_comp ApplicativeTransformation.id_compₓ'. -/
@[simp]
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun α x => rfl
#align applicative_transformation.id_comp ApplicativeTransformation.id_comp

end ApplicativeTransformation

open ApplicativeTransformation

#print Traversable /-
/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `list` and `m` is the applicative functor
`io`, then given a function `f : α → io β`, the function `functor.map f` is
`list α → list (io β)`, but `traverse f` is `list α → io (list β)`. -/
class Traversable (t : Type u → Type u) extends Functor t where
  traverse : ∀ {m : Type u → Type u} [Applicative m] {α β}, (α → m β) → t α → m (t β)
#align traversable Traversable
-/

open Functor

export Traversable (traverse)

section Functions

variable {t : Type u → Type u}

variable {m : Type u → Type v} [Applicative m]

variable {α β : Type u}

variable {f : Type u → Type u} [Applicative f]

#print sequence /-
/-- A traversable functor commutes with all applicative functors. -/
def sequence [Traversable t] : t (f α) → f (t α) :=
  traverse id
#align sequence sequence
-/

end Functions

#print IsLawfulTraversable /-
/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `id.mk` to `id.mk`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `λ x, f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
class IsLawfulTraversable (t : Type u → Type u) [Traversable t] extends IsLawfulFunctor t :
  Type (u + 1) where
  id_traverse : ∀ {α} (x : t α), traverse id.mk x = x
  comp_traverse :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ}
      (f : β → F γ) (g : α → G β) (x : t α),
      traverse (comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α), traverse (id.mk ∘ f) x = id.mk (f <$> x)
  naturality :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α → F β) (x : t α),
      η (traverse f x) = traverse (@η _ ∘ f) x
#align is_lawful_traversable IsLawfulTraversable
-/

instance : Traversable id :=
  ⟨fun _ _ _ _ => id⟩

instance : IsLawfulTraversable id := by refine' { .. } <;> intros <;> rfl

section

variable {F : Type u → Type v} [Applicative F]

instance : Traversable Option :=
  ⟨@Option.traverse⟩

instance : Traversable List :=
  ⟨@List.traverse⟩

end

namespace Sum

variable {σ : Type u}

variable {F : Type u → Type u}

variable [Applicative F]

#print Sum.traverse /-
/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `traversable` instance for the functor `σ ⊕ -`. -/
protected def traverse {α β} (f : α → F β) : Sum σ α → F (Sum σ β)
  | Sum.inl x => pure (Sum.inl x)
  | Sum.inr x => Sum.inr <$> f x
#align sum.traverse Sum.traverse
-/

end Sum

instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverse _⟩

