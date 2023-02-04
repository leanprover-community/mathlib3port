/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison

! This file was ported from Lean 3 source module data.finsupp.defs
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.IndicatorFunction
import Mathbin.GroupTheory.Submonoid.Basic

/-!
# Type of functions with finite support

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For any type `α` and any type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements, which is defined in
`algebra/big_operators/finsupp`.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `finsupp`: The type of finitely supported functions from `α` to `β`.
* `finsupp.single`: The `finsupp` which is nonzero in exactly one point.
* `finsupp.update`: Changes one value of a `finsupp`.
* `finsupp.erase`: Replaces one value of a `finsupp` by `0`.
* `finsupp.on_finset`: The restriction of a function to a `finset` as a `finsupp`.
* `finsupp.map_range`: Composition of a `zero_hom` with a `finsupp`.
* `finsupp.emb_domain`: Maps the domain of a `finsupp` by an embedding.
* `finsupp.zip_with`: Postcomposition of two `finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

open BigOperators

variable {α β γ ι M M' N P G H R S : Type _}

#print Finsupp /-
/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type _) (M : Type _) [Zero M] where
  support : Finset α
  toFun : α → M
  mem_support_toFun : ∀ a, a ∈ support ↔ to_fun a ≠ 0
#align finsupp Finsupp
-/

-- mathport name: «expr →₀ »
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `finsupp` -/


section Basic

variable [Zero M]

#print Finsupp.funLike /-
instance funLike : FunLike (α →₀ M) α fun _ => M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩
#align finsupp.fun_like Finsupp.funLike
-/

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →₀ M) fun _ => α → M :=
  FunLike.hasCoeToFun

/- warning: finsupp.ext -> Finsupp.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, (forall (a : α), Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g a)) -> (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g a)) -> (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.ext Finsupp.extₓ'. -/
@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h
#align finsupp.ext Finsupp.ext

/- warning: finsupp.ext_iff -> Finsupp.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g) (forall (a : α), Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g) (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g a))
Case conversion may be inaccurate. Consider using '#align finsupp.ext_iff Finsupp.ext_iffₓ'. -/
/-- Deprecated. Use `fun_like.ext_iff` instead. -/
theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a :=
  FunLike.ext_iff
#align finsupp.ext_iff Finsupp.ext_iff

/- warning: finsupp.coe_fn_inj -> Finsupp.coeFn_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g)) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g)) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.coe_fn_inj Finsupp.coeFn_injₓ'. -/
/-- Deprecated. Use `fun_like.coe_fn_eq` instead. -/
theorem coeFn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  FunLike.coe_fn_eq
#align finsupp.coe_fn_inj Finsupp.coeFn_inj

#print Finsupp.coeFn_injective /-
/-- Deprecated. Use `fun_like.coe_injective` instead. -/
theorem coeFn_injective : @Function.Injective (α →₀ M) (α → M) coeFn :=
  FunLike.coe_injective
#align finsupp.coe_fn_injective Finsupp.coeFn_injective
-/

/- warning: finsupp.congr_fun -> Finsupp.congr_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g) -> (forall (a : α), Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g) -> (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g a))
Case conversion may be inaccurate. Consider using '#align finsupp.congr_fun Finsupp.congr_funₓ'. -/
/-- Deprecated. Use `fun_like.congr_fun` instead. -/
theorem congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  FunLike.congr_fun h _
#align finsupp.congr_fun Finsupp.congr_fun

/- warning: finsupp.coe_mk -> Finsupp.coe_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : α -> M) (s : Finset.{u1} α) (h : forall (a : α), Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))), Eq.{max (succ u1) (succ u2)} (α -> M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.mk.{u1, u2} α M _inst_1 s f h)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : α -> M) (s : Finset.{u2} α) (h : forall (a : α), Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.mk.{u2, u1} α M _inst_1 s f h)) f
Case conversion may be inaccurate. Consider using '#align finsupp.coe_mk Finsupp.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl
#align finsupp.coe_mk Finsupp.coe_mk

instance : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨False.elim, fun H => H rfl⟩⟩⟩

/- warning: finsupp.coe_zero -> Finsupp.coe_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M], Eq.{succ (max u1 u2)} (α -> M) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))) (OfNat.ofNat.{max u1 u2} (α -> M) 0 (OfNat.mk.{max u1 u2} (α -> M) 0 (Zero.zero.{max u1 u2} (α -> M) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))) (OfNat.ofNat.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) 0 (Zero.toOfNat0.{max u2 u1} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (Pi.instZero.{u2, u1} α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (fun (i : α) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_zero Finsupp.coe_zeroₓ'. -/
@[simp]
theorem coe_zero : ⇑(0 : α →₀ M) = 0 :=
  rfl
#align finsupp.coe_zero Finsupp.coe_zero

#print Finsupp.zero_apply /-
theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl
#align finsupp.zero_apply Finsupp.zero_apply
-/

/- warning: finsupp.support_zero -> Finsupp.support_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M], Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M], Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))
Case conversion may be inaccurate. Consider using '#align finsupp.support_zero Finsupp.support_zeroₓ'. -/
@[simp]
theorem support_zero : (0 : α →₀ M).support = ∅ :=
  rfl
#align finsupp.support_zero Finsupp.support_zero

instance : Inhabited (α →₀ M) :=
  ⟨0⟩

/- warning: finsupp.mem_support_iff -> Finsupp.mem_support_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M _inst_1 f)) (Ne.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M _inst_1 f)) (Ne.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.mem_support_iff Finsupp.mem_support_iffₓ'. -/
@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  f.mem_support_toFun
#align finsupp.mem_support_iff Finsupp.mem_support_iff

/- warning: finsupp.fun_support_eq -> Finsupp.fun_support_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α M _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Finsupp.support.{u1, u2} α M _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1), Eq.{succ u2} (Set.{u2} α) (Function.support.{u2, u1} α M _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f)) (Finset.toSet.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f))
Case conversion may be inaccurate. Consider using '#align finsupp.fun_support_eq Finsupp.fun_support_eqₓ'. -/
@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun x => mem_support_iff.symm
#align finsupp.fun_support_eq Finsupp.fun_support_eq

/- warning: finsupp.not_mem_support_iff -> Finsupp.not_mem_support_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M _inst_1 f))) (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M _inst_1 f))) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.not_mem_support_iff Finsupp.not_mem_support_iffₓ'. -/
theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm
#align finsupp.not_mem_support_iff Finsupp.not_mem_support_iff

/- warning: finsupp.coe_eq_zero -> Finsupp.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f) (OfNat.ofNat.{max u1 u2} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) f) 0 (OfNat.mk.{max u1 u2} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) f) 0 (Zero.zero.{max u1 u2} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) f) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f) (OfNat.ofNat.{max u2 u1} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{max u2 u1} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (Pi.instZero.{u2, u1} α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (fun (i : α) => _inst_1))))) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_eq_zero Finsupp.coe_eq_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, coe_fn_inj]
#align finsupp.coe_eq_zero Finsupp.coe_eq_zero

/- warning: finsupp.ext_iff' -> Finsupp.ext_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g) (And (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Finsupp.support.{u1, u2} α M _inst_1 g)) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finsupp.support.{u1, u2} α M _inst_1 f)) -> (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g x))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g) (And (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Finsupp.support.{u2, u1} α M _inst_1 g)) (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finsupp.support.{u2, u1} α M _inst_1 f)) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g x))))
Case conversion may be inaccurate. Consider using '#align finsupp.ext_iff' Finsupp.ext_iff'ₓ'. -/
theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical exact
          if h : a ∈ f.support then h₂ a h
          else by
            have hf : f a = 0 := not_mem_support_iff.1 h
            have hg : g a = 0 := by rwa [h₁, not_mem_support_iff] at h
            rw [hf, hg]⟩
#align finsupp.ext_iff' Finsupp.ext_iff'

/- warning: finsupp.support_eq_empty -> Finsupp.support_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_eq_empty Finsupp.support_eq_emptyₓ'. -/
@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 := by
  exact_mod_cast @Function.support_eq_empty_iff _ _ _ f
#align finsupp.support_eq_empty Finsupp.support_eq_empty

/- warning: finsupp.support_nonempty_iff -> Finsupp.support_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Finset.Nonempty.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (Ne.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Finset.Nonempty.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (Ne.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_nonempty_iff Finsupp.support_nonempty_iffₓ'. -/
theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne.def]
#align finsupp.support_nonempty_iff Finsupp.support_nonempty_iff

/- warning: finsupp.nonzero_iff_exists -> Finsupp.nonzero_iff_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Ne.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))) (Exists.{succ u1} α (fun (a : α) => Ne.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Ne.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))) (Exists.{succ u2} α (fun (a : α) => Ne.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.nonzero_iff_exists Finsupp.nonzero_iff_existsₓ'. -/
theorem nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 := by
  simp [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_not_mem]
#align finsupp.nonzero_iff_exists Finsupp.nonzero_iff_exists

/- warning: finsupp.card_support_eq_zero -> Finsupp.card_support_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_support_eq_zero Finsupp.card_support_eq_zeroₓ'. -/
theorem card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 := by simp
#align finsupp.card_support_eq_zero Finsupp.card_support_eq_zero

instance [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm

/- warning: finsupp.finite_support -> Finsupp.finite_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1), Set.Finite.{u1} α (Function.support.{u1, u2} α M _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1), Set.Finite.{u2} α (Function.support.{u2, u1} α M _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f))
Case conversion may be inaccurate. Consider using '#align finsupp.finite_support Finsupp.finite_supportₓ'. -/
theorem finite_support (f : α →₀ M) : Set.Finite (Function.support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_toSet
#align finsupp.finite_support Finsupp.finite_support

/- warning: finsupp.support_subset_iff -> Finsupp.support_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {s : Set.{u1} α} {f : Finsupp.{u1, u2} α M _inst_1}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Finsupp.support.{u1, u2} α M _inst_1 f)) s) (forall (a : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {s : Set.{u2} α} {f : Finsupp.{u2, u1} α M _inst_1}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) s) (forall (a : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_subset_iff Finsupp.support_subset_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ∉ » s) -/
theorem support_subset_iff {s : Set α} {f : α →₀ M} : ↑f.support ⊆ s ↔ ∀ (a) (_ : a ∉ s), f a = 0 :=
  by
  simp only [Set.subset_def, mem_coe, mem_support_iff] <;> exact forall_congr' fun a => not_imp_comm
#align finsupp.support_subset_iff Finsupp.support_subset_iff

#print Finsupp.equivFunOnFinite /-
/-- Given `finite α`, `equiv_fun_on_finite` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M)
    where
  toFun := coeFn
  invFun f := mk (Function.support f).toFinite.toFinset f fun a => Set.Finite.mem_toFinset _
  left_inv f := ext fun x => rfl
  right_inv f := rfl
#align finsupp.equiv_fun_on_finite Finsupp.equivFunOnFinite
-/

#print Finsupp.equivFunOnFinite_symm_coe /-
@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f
#align finsupp.equiv_fun_on_finite_symm_coe Finsupp.equivFunOnFinite_symm_coe
-/

#print Equiv.finsuppUnique /-
/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps]
noncomputable def Equiv.finsuppUnique {ι : Type _} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)
#align equiv.finsupp_unique Equiv.finsuppUnique
-/

/- warning: finsupp.unique_ext -> Finsupp.unique_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : Unique.{succ u1} α] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2)))) -> (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : Unique.{succ u2} α] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2)))) -> (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.unique_ext Finsupp.unique_extₓ'. -/
@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]
#align finsupp.unique_ext Finsupp.unique_ext

/- warning: finsupp.unique_ext_iff -> Finsupp.unique_ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : Unique.{succ u1} α] {f : Finsupp.{u1, u2} α M _inst_1} {g : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f g) (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : Unique.{succ u2} α] {f : Finsupp.{u2, u1} α M _inst_1} {g : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f g) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) g (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align finsupp.unique_ext_iff Finsupp.unique_ext_iffₓ'. -/
theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩
#align finsupp.unique_ext_iff Finsupp.unique_ext_iff

end Basic

/-! ### Declarations about `single` -/


section Single

variable [Zero M] {a a' : α} {b : M}

#print Finsupp.single /-
/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M
    where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by
    classical
      obtain rfl | hb := eq_or_ne b 0
      · simp
      rw [if_neg hb, mem_singleton]
      obtain rfl | ha := eq_or_ne a' a
      · simp [hb]
      simp [Pi.single_eq_of_ne', ha]
#align finsupp.single Finsupp.single
-/

/- warning: finsupp.single_apply -> Finsupp.single_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {a' : α} {b : M} [_inst_2 : Decidable (Eq.{succ u1} α a a')], Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b) a') (ite.{succ u2} M (Eq.{succ u1} α a a') _inst_2 b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {a' : α} {b : M} [_inst_2 : Decidable (Eq.{succ u2} α a a')], Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b) a') (ite.{succ u1} M (Eq.{succ u2} α a a') _inst_2 b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.single_apply Finsupp.single_applyₓ'. -/
theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
    simp_rw [@eq_comm _ a a']
    convert Pi.single_apply _ _ _
#align finsupp.single_apply Finsupp.single_apply

/- warning: finsupp.single_apply_left -> Finsupp.single_apply_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (x : α) (z : α) (y : M), Eq.{succ u3} M (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (fun (_x : Finsupp.{u2, u3} β M _inst_1) => β -> M) (Finsupp.hasCoeToFun.{u2, u3} β M _inst_1) (Finsupp.single.{u2, u3} β M _inst_1 (f x) y) (f z)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) (fun (_x : Finsupp.{u1, u3} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u3} α M _inst_1) (Finsupp.single.{u1, u3} α M _inst_1 x y) z))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : α -> β}, (Function.Injective.{succ u3, succ u2} α β f) -> (forall (x : α) (z : α) (y : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) (f z)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} β M _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) _x) (Finsupp.funLike.{u2, u1} β M _inst_1) (Finsupp.single.{u2, u1} β M _inst_1 (f x) y) (f z)) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Finsupp.{u3, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u3, u1} α M _inst_1) (Finsupp.single.{u3, u1} α M _inst_1 x y) z))
Case conversion may be inaccurate. Consider using '#align finsupp.single_apply_left Finsupp.single_apply_leftₓ'. -/
theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]
#align finsupp.single_apply_left Finsupp.single_apply_left

/- warning: finsupp.single_eq_indicator -> Finsupp.single_eq_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {b : M}, Eq.{max (succ u1) (succ u2)} (α -> M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b)) (Set.indicator.{u1, u2} α M _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (fun (_x : α) => b))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {b : M}, Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b)) (Set.indicator.{u2, u1} α M _inst_1 (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) (fun (_x : α) => b))
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_indicator Finsupp.single_eq_indicatorₓ'. -/
theorem single_eq_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b := by
  classical
    ext
    simp [single_apply, Set.indicator, @eq_comm _ a]
#align finsupp.single_eq_indicator Finsupp.single_eq_indicator

#print Finsupp.single_eq_same /-
@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b := by classical exact Pi.single_eq_same a b
#align finsupp.single_eq_same Finsupp.single_eq_same
-/

/- warning: finsupp.single_eq_of_ne -> Finsupp.single_eq_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {a' : α} {b : M}, (Ne.{succ u1} α a a') -> (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b) a') (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {a' : α} {b : M}, (Ne.{succ u2} α a a') -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b) a') (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a') 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a') _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_of_ne Finsupp.single_eq_of_neₓ'. -/
@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _
#align finsupp.single_eq_of_ne Finsupp.single_eq_of_ne

/- warning: finsupp.single_eq_update -> Finsupp.single_eq_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] (a : α) (b : M), Eq.{max (succ u1) (succ u2)} (α -> M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b)) (Function.update.{succ u1, succ u2} α (fun (a : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{max u1 u2} (α -> M) 0 (OfNat.mk.{max u1 u2} (α -> M) 0 (Zero.zero.{max u1 u2} (α -> M) (Pi.instZero.{u1, u2} α (fun (a : α) => M) (fun (i : α) => _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] (a : α) (b : M), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b)) (Function.update.{succ u2, succ u1} α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{max u2 u1} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{max u2 u1} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (Pi.instZero.{u2, u1} α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (fun (i : α) => _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_update Finsupp.single_eq_updateₓ'. -/
theorem single_eq_update [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Function.update 0 a b :=
  by rw [single_eq_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]
#align finsupp.single_eq_update Finsupp.single_eq_update

/- warning: finsupp.single_eq_pi_single -> Finsupp.single_eq_pi_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] (a : α) (b : M), Eq.{max (succ u1) (succ u2)} (α -> M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b)) (Pi.single.{u1, u2} α (fun (a : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) a b)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] (a : α) (b : M), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b)) (Pi.single.{u2, u1} α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_pi_single Finsupp.single_eq_pi_singleₓ'. -/
theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b
#align finsupp.single_eq_pi_single Finsupp.single_eq_pi_single

/- warning: finsupp.single_zero -> Finsupp.single_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.single_zero Finsupp.single_zeroₓ'. -/
@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  coeFn_injective <| by
    classical simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)
#align finsupp.single_zero Finsupp.single_zero

/- warning: finsupp.single_of_single_apply -> Finsupp.single_of_single_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α) (a' : α) (b : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a' b) a)) (coeFn.{max (succ u1) (succ (max u1 u2)), max (succ u1) (succ (max u1 u2))} (Finsupp.{u1, max u1 u2} α (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)) (fun (_x : Finsupp.{u1, max u1 u2} α (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)) => α -> (Finsupp.{u1, u2} α M _inst_1)) (Finsupp.hasCoeToFun.{u1, max u1 u2} α (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)) (Finsupp.single.{u1, max u1 u2} α (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1) a' (Finsupp.single.{u1, u2} α M _inst_1 a' b)) a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α) (a' : α) (b : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1) (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1 a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a' b) a)) (FunLike.coe.{max (succ u2) (succ (max u2 u1)), succ u2, succ (max u2 u1)} (Finsupp.{u2, max u2 u1} α (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => Finsupp.{u2, u1} α M _inst_1) _x) (Finsupp.funLike.{u2, max u2 u1} α (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)) (Finsupp.single.{u2, max u1 u2} α (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1) a' (Finsupp.single.{u2, u1} α M _inst_1 a' b)) a)
Case conversion may be inaccurate. Consider using '#align finsupp.single_of_single_apply Finsupp.single_of_single_applyₓ'. -/
theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
    rw [single_apply, single_apply]
    ext
    split_ifs
    · rw [h]
    · rw [zero_apply, single_apply, if_t_t]
#align finsupp.single_of_single_apply Finsupp.single_of_single_apply

#print Finsupp.support_single_ne_zero /-
theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} := by
  classical exact if_neg hb
#align finsupp.support_single_ne_zero Finsupp.support_single_ne_zero
-/

/- warning: finsupp.support_single_subset -> Finsupp.support_single_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {b : M}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 a b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {b : M}, HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.single.{u2, u1} α M _inst_1 a b)) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)
Case conversion may be inaccurate. Consider using '#align finsupp.support_single_subset Finsupp.support_single_subsetₓ'. -/
theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical
    show ite _ _ _ ⊆ _
    split_ifs <;> [exact empty_subset _, exact subset.refl _]
#align finsupp.support_single_subset Finsupp.support_single_subset

#print Finsupp.single_apply_mem /-
theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp, simp [single_eq_of_ne hx]]
#align finsupp.single_apply_mem Finsupp.single_apply_mem
-/

#print Finsupp.range_single_subset /-
theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem
#align finsupp.range_single_subset Finsupp.range_single_subset
-/

#print Finsupp.single_injective /-
/-- `finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq =>
  by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [Eq]
  rwa [single_eq_same, single_eq_same] at this
#align finsupp.single_injective Finsupp.single_injective
-/

#print Finsupp.single_apply_eq_zero /-
theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_indicator]
#align finsupp.single_apply_eq_zero Finsupp.single_apply_eq_zero
-/

#print Finsupp.single_apply_ne_zero /-
theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]
#align finsupp.single_apply_ne_zero Finsupp.single_apply_ne_zero
-/

/- warning: finsupp.mem_support_single -> Finsupp.mem_support_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α) (a' : α) (b : M), Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 a' b))) (And (Eq.{succ u1} α a a') (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α) (a' : α) (b : M), Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.single.{u2, u1} α M _inst_1 a' b))) (And (Eq.{succ u2} α a a') (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.mem_support_single Finsupp.mem_support_singleₓ'. -/
theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero, not_or]
#align finsupp.mem_support_single Finsupp.mem_support_single

/- warning: finsupp.eq_single_iff -> Finsupp.eq_single_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α} {b : M}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a b)) (And (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) b))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α} {b : M}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α M _inst_1 a b)) (And (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) b))
Case conversion may be inaccurate. Consider using '#align finsupp.eq_single_iff Finsupp.eq_single_iffₓ'. -/
theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b :=
  by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne.def, not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)
#align finsupp.eq_single_iff Finsupp.eq_single_iff

/- warning: finsupp.single_eq_single_iff -> Finsupp.single_eq_single_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a₁ : α) (a₂ : α) (b₁ : M) (b₂ : M), Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a₁ b₁) (Finsupp.single.{u1, u2} α M _inst_1 a₂ b₂)) (Or (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u2} M b₁ b₂)) (And (Eq.{succ u2} M b₁ (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (Eq.{succ u2} M b₂ (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a₁ : α) (a₂ : α) (b₁ : M) (b₂ : M), Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a₁ b₁) (Finsupp.single.{u2, u1} α M _inst_1 a₂ b₂)) (Or (And (Eq.{succ u2} α a₁ a₂) (Eq.{succ u1} M b₁ b₂)) (And (Eq.{succ u1} M b₁ (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (Eq.{succ u1} M b₂ (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_single_iff Finsupp.single_eq_single_iffₓ'. -/
theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 :=
  by
  constructor
  · intro eq
    by_cases a₁ = a₂
    · refine' Or.inl ⟨h, _⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [ext_iff] at eq
      have h₁ := Eq a₁
      have h₂ := Eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [single_zero, single_zero]
#align finsupp.single_eq_single_iff Finsupp.single_eq_single_iff

#print Finsupp.single_left_injective /-
/-- `finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun a a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left
#align finsupp.single_left_injective Finsupp.single_left_injective
-/

#print Finsupp.single_left_inj /-
theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff
#align finsupp.single_left_inj Finsupp.single_left_inj
-/

/- warning: finsupp.support_single_ne_bot -> Finsupp.support_single_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {b : M} (i : α), (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Ne.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 i b)) (Bot.bot.{u1} (Finset.{u1} α) (GeneralizedBooleanAlgebra.toHasBot.{u1} (Finset.{u1} α) (Finset.generalizedBooleanAlgebra.{u1} α (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {b : M} (i : α), (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1))) -> (Ne.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 i b)) (Bot.bot.{u1} (Finset.{u1} α) (OrderBot.toBot.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_single_ne_bot Finsupp.support_single_ne_botₓ'. -/
theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _
#align finsupp.support_single_ne_bot Finsupp.support_single_ne_bot

/- warning: finsupp.support_single_disjoint -> Finsupp.support_single_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {b : M} {b' : M}, (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Ne.{succ u2} M b' (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (forall {i : α} {j : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 i b)) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 j b'))) (Ne.{succ u1} α i j))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {b : M} {b' : M}, (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1))) -> (Ne.{succ u2} M b' (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1))) -> (forall {i : α} {j : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 i b)) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.single.{u1, u2} α M _inst_1 j b'))) (Ne.{succ u1} α i j))
Case conversion may be inaccurate. Consider using '#align finsupp.support_single_disjoint Finsupp.support_single_disjointₓ'. -/
theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]
#align finsupp.support_single_disjoint Finsupp.support_single_disjoint

/- warning: finsupp.single_eq_zero -> Finsupp.single_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {b : M}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))) (Eq.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {b : M}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.single_eq_zero Finsupp.single_eq_zeroₓ'. -/
@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by simp [ext_iff, single_eq_indicator]
#align finsupp.single_eq_zero Finsupp.single_eq_zero

#print Finsupp.single_swap /-
theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical
    simp only [single_apply]
    ac_rfl
#align finsupp.single_swap Finsupp.single_swap
-/

instance [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) :=
  by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

/- warning: finsupp.unique_single -> Finsupp.unique_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : Unique.{succ u1} α] (x : Finsupp.{u1, u2} α M _inst_1), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) x (Finsupp.single.{u1, u2} α M _inst_1 (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) x (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : Unique.{succ u2} α] (x : Finsupp.{u2, u1} α M _inst_1), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) x (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))) _inst_1 (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) x (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align finsupp.unique_single Finsupp.unique_singleₓ'. -/
theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm
#align finsupp.unique_single Finsupp.unique_single

/- warning: finsupp.unique_single_eq_iff -> Finsupp.unique_single_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {a' : α} {b : M} [_inst_2 : Unique.{succ u1} α] {b' : M}, Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.single.{u1, u2} α M _inst_1 a b) (Finsupp.single.{u1, u2} α M _inst_1 a' b')) (Eq.{succ u2} M b b')
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {a' : α} {b : M} [_inst_2 : Unique.{succ u2} α] {b' : M}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.single.{u2, u1} α M _inst_1 a b) (Finsupp.single.{u2, u1} α M _inst_1 a' b')) (Eq.{succ u1} M b b')
Case conversion may be inaccurate. Consider using '#align finsupp.unique_single_eq_iff Finsupp.unique_single_eq_iffₓ'. -/
@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]
#align finsupp.unique_single_eq_iff Finsupp.unique_single_eq_iff

/- warning: finsupp.support_eq_singleton -> Finsupp.support_eq_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (And (Ne.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (And (Ne.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1 a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_eq_singleton Finsupp.support_eq_singletonₓ'. -/
theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero _ h.1⟩
#align finsupp.support_eq_singleton Finsupp.support_eq_singleton

/- warning: finsupp.support_eq_singleton' -> Finsupp.support_eq_singleton' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Exists.{succ u2} M (fun (b : M) => Exists.{0} (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (fun (H : Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a b))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (Exists.{succ u1} M (fun (b : M) => Exists.{0} (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (fun (H : Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α M _inst_1 a b))))
Case conversion may be inaccurate. Consider using '#align finsupp.support_eq_singleton' Finsupp.support_eq_singleton'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ≠ » 0) -/
theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ (b : _)(_ : b ≠ 0), f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩
#align finsupp.support_eq_singleton' Finsupp.support_eq_singleton'

/- warning: finsupp.card_support_eq_one -> Finsupp.card_support_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Exists.{succ u1} α (fun (a : α) => And (Ne.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Exists.{succ u2} α (fun (a : α) => And (Ne.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1 a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a)))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_support_eq_one Finsupp.card_support_eq_oneₓ'. -/
theorem card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
  by simp only [card_eq_one, support_eq_singleton]
#align finsupp.card_support_eq_one Finsupp.card_support_eq_one

/- warning: finsupp.card_support_eq_one' -> Finsupp.card_support_eq_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} M (fun (b : M) => Exists.{0} (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (fun (H : Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a b)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (Eq.{1} Nat (Finset.card.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} M (fun (b : M) => Exists.{0} (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (fun (H : Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α M _inst_1 a b)))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_support_eq_one' Finsupp.card_support_eq_one'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr ≠ » 0) -/
theorem card_support_eq_one' {f : α →₀ M} :
    card f.support = 1 ↔ ∃ (a : _)(b : _)(_ : b ≠ 0), f = single a b := by
  simp only [card_eq_one, support_eq_singleton']
#align finsupp.card_support_eq_one' Finsupp.card_support_eq_one'

/- warning: finsupp.support_subset_singleton -> Finsupp.support_subset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1 a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a)))
Case conversion may be inaccurate. Consider using '#align finsupp.support_subset_singleton Finsupp.support_subset_singletonₓ'. -/
theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩
#align finsupp.support_subset_singleton Finsupp.support_subset_singleton

/- warning: finsupp.support_subset_singleton' -> Finsupp.support_subset_singleton' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 f) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Exists.{succ u2} M (fun (b : M) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 f) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (Exists.{succ u1} M (fun (b : M) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α M _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align finsupp.support_subset_singleton' Finsupp.support_subset_singleton'ₓ'. -/
theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩
#align finsupp.support_subset_singleton' Finsupp.support_subset_singleton'

/- warning: finsupp.card_support_le_one -> Finsupp.card_support_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : Nonempty.{succ u1} α] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Exists.{succ u1} α (fun (a : α) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : Nonempty.{succ u2} α] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (LE.le.{0} Nat instLENat (Finset.card.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Exists.{succ u2} α (fun (a : α) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1 a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_support_le_one Finsupp.card_support_le_oneₓ'. -/
theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]
#align finsupp.card_support_le_one Finsupp.card_support_le_one

/- warning: finsupp.card_support_le_one' -> Finsupp.card_support_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : Nonempty.{succ u1} α] {f : Finsupp.{u1, u2} α M _inst_1}, Iff (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Finsupp.support.{u1, u2} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} M (fun (b : M) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) f (Finsupp.single.{u1, u2} α M _inst_1 a b))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : Nonempty.{succ u2} α] {f : Finsupp.{u2, u1} α M _inst_1}, Iff (LE.le.{0} Nat instLENat (Finset.card.{u2} α (Finsupp.support.{u2, u1} α M _inst_1 f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} M (fun (b : M) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) f (Finsupp.single.{u2, u1} α M _inst_1 a b))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_support_le_one' Finsupp.card_support_le_one'ₓ'. -/
theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']
#align finsupp.card_support_le_one' Finsupp.card_support_le_one'

/- warning: finsupp.equiv_fun_on_finite_single -> Finsupp.equivFunOnFinite_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : Finite.{succ u1} α] (x : α) (m : M), Eq.{max (succ u1) (succ u2)} (α -> M) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (α -> M)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (α -> M)) => (Finsupp.{u1, u2} α M _inst_1) -> α -> M) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (α -> M)) (Finsupp.equivFunOnFinite.{u1, u2} α M _inst_1 _inst_3) (Finsupp.single.{u1, u2} α M _inst_1 x m)) (Pi.single.{u1, u2} α (fun (ᾰ : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) x m)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Finite.{succ u2} α] (x : α) (m : M), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u2, u1} α M _inst_1) => α -> M) (Finsupp.single.{u2, u1} α M _inst_1 x m)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (α -> M)) (Finsupp.{u2, u1} α M _inst_1) (fun (_x : Finsupp.{u2, u1} α M _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u2, u1} α M _inst_1) => α -> M) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u2, u1} α M _inst_1) (α -> M)) (Finsupp.equivFunOnFinite.{u2, u1} α M _inst_1 _inst_3) (Finsupp.single.{u2, u1} α M _inst_1 x m)) (Pi.single.{u2, u1} α (fun (ᾰ : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) x m)
Case conversion may be inaccurate. Consider using '#align finsupp.equiv_fun_on_finite_single Finsupp.equivFunOnFinite_singleₓ'. -/
@[simp]
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m :=
  by
  ext
  simp [Finsupp.single_eq_pi_single]
#align finsupp.equiv_fun_on_finite_single Finsupp.equivFunOnFinite_single

/- warning: finsupp.equiv_fun_on_finite_symm_single -> Finsupp.equivFunOnFinite_symm_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : Finite.{succ u1} α] (x : α) (m : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> M) (Finsupp.{u1, u2} α M _inst_1)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> M) (Finsupp.{u1, u2} α M _inst_1)) => (α -> M) -> (Finsupp.{u1, u2} α M _inst_1)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> M) (Finsupp.{u1, u2} α M _inst_1)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (α -> M) (Finsupp.equivFunOnFinite.{u1, u2} α M _inst_1 _inst_3)) (Pi.single.{u1, u2} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) x m)) (Finsupp.single.{u1, u2} α M _inst_1 x m)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Finite.{succ u2} α] (x : α) (m : M), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α -> M) => Finsupp.{u2, u1} α M _inst_1) (Pi.single.{u2, u1} α (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.1847 : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) x m)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> M) (Finsupp.{u2, u1} α M _inst_1)) (α -> M) (fun (_x : α -> M) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α -> M) => Finsupp.{u2, u1} α M _inst_1) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (α -> M) (Finsupp.{u2, u1} α M _inst_1)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u2, u1} α M _inst_1) (α -> M) (Finsupp.equivFunOnFinite.{u2, u1} α M _inst_1 _inst_3)) (Pi.single.{u2, u1} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (fun (i : α) => _inst_1) x m)) (Finsupp.single.{u2, u1} α M _inst_1 x m)
Case conversion may be inaccurate. Consider using '#align finsupp.equiv_fun_on_finite_symm_single Finsupp.equivFunOnFinite_symm_singleₓ'. -/
@[simp]
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equiv_fun_on_finite_single, Equiv.symm_apply_apply]
#align finsupp.equiv_fun_on_finite_symm_single Finsupp.equivFunOnFinite_symm_single

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

#print Finsupp.update /-
/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `finsupp.support`.
Otherwise, if `a` was not in the `finsupp.support`, it is added to it.

This is the finitely-supported version of `function.update`. -/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M
    where
  support := by
    haveI := Classical.decEq α <;> haveI := Classical.decEq M <;>
      exact if b = 0 then f.support.erase a else insert a f.support
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    simp only [Function.update_apply, Ne.def]
    split_ifs with hb ha ha hb <;> simp [ha, hb]
#align finsupp.update Finsupp.update
-/

/- warning: finsupp.coe_update -> Finsupp.coe_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1) (a : α) (b : M) [_inst_2 : DecidableEq.{succ u1} α], Eq.{max (succ u1) (succ u2)} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.update.{u1, u2} α M _inst_1 f a b)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.update.{u1, u2} α M _inst_1 f a b)) (Function.update.{succ u1, succ u2} α (fun (ᾰ : α) => M) (fun (a : α) (b : α) => _inst_2 a b) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f) a b)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1) (a : α) (b : M) [_inst_2 : DecidableEq.{succ u2} α], Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.update.{u2, u1} α M _inst_1 f a b)) (Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (fun (a : α) (b : α) => _inst_2 a b) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f) a b)
Case conversion may be inaccurate. Consider using '#align finsupp.coe_update Finsupp.coe_updateₓ'. -/
@[simp]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  convert rfl
#align finsupp.coe_update Finsupp.coe_update

/- warning: finsupp.update_self -> Finsupp.update_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1) (a : α), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.update.{u1, u2} α M _inst_1 f a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1) (a : α), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.update.{u2, u1} α M _inst_1 f a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a)) f
Case conversion may be inaccurate. Consider using '#align finsupp.update_self Finsupp.update_selfₓ'. -/
@[simp]
theorem update_self : f.update a (f a) = f := by
  classical
    ext
    simp
#align finsupp.update_self Finsupp.update_self

/- warning: finsupp.zero_update -> Finsupp.zero_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α) (b : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.update.{u1, u2} α M _inst_1 (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1)))) a b) (Finsupp.single.{u1, u2} α M _inst_1 a b)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α) (b : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.update.{u2, u1} α M _inst_1 (OfNat.ofNat.{max u1 u2} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u1 u2} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1))) a b) (Finsupp.single.{u2, u1} α M _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align finsupp.zero_update Finsupp.zero_updateₓ'. -/
@[simp]
theorem zero_update : update 0 a b = single a b := by
  classical
    ext
    rw [single_eq_update]
    rfl
#align finsupp.zero_update Finsupp.zero_update

/- warning: finsupp.support_update -> Finsupp.support_update is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1) (a : α) (b : M) [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : DecidableEq.{succ u2} M], Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.update.{u1, u2} α M _inst_1 f a b)) (ite.{succ u1} (Finset.{u1} α) (Eq.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (_inst_3 b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u1, u2} α M _inst_1 f) a) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a (Finsupp.support.{u1, u2} α M _inst_1 f)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1) (a : α) (b : M) [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : DecidableEq.{succ u1} M], Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.update.{u2, u1} α M _inst_1 f a b)) (ite.{succ u2} (Finset.{u2} α) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (_inst_3 b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u2, u1} α M _inst_1 f) a) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a (Finsupp.support.{u2, u1} α M _inst_1 f)))
Case conversion may be inaccurate. Consider using '#align finsupp.support_update Finsupp.support_updateₓ'. -/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.eraseₓ a else insert a f.support := by
  convert rfl
#align finsupp.support_update Finsupp.support_update

/- warning: finsupp.support_update_zero -> Finsupp.support_update_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1) (a : α) [_inst_2 : DecidableEq.{succ u1} α], Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.update.{u1, u2} α M _inst_1 f a (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u1, u2} α M _inst_1 f) a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1) (a : α) [_inst_2 : DecidableEq.{succ u2} α], Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.update.{u2, u1} α M _inst_1 f a (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u2, u1} α M _inst_1 f) a)
Case conversion may be inaccurate. Consider using '#align finsupp.support_update_zero Finsupp.support_update_zeroₓ'. -/
@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.eraseₓ a := by
  convert if_pos rfl
#align finsupp.support_update_zero Finsupp.support_update_zero

variable {b}

/- warning: finsupp.support_update_ne_zero -> Finsupp.support_update_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1) (a : α) {b : M} [_inst_2 : DecidableEq.{succ u1} α], (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.update.{u1, u2} α M _inst_1 f a b)) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a (Finsupp.support.{u1, u2} α M _inst_1 f)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1) (a : α) {b : M} [_inst_2 : DecidableEq.{succ u2} α], (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) -> (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.update.{u2, u1} α M _inst_1 f a b)) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a (Finsupp.support.{u2, u1} α M _inst_1 f)))
Case conversion may be inaccurate. Consider using '#align finsupp.support_update_ne_zero Finsupp.support_update_ne_zeroₓ'. -/
theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) :
    support (f.update a b) = insert a f.support := by classical convert if_neg h
#align finsupp.support_update_ne_zero Finsupp.support_update_ne_zero

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

#print Finsupp.erase /-
/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M
    where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    rw [mem_erase, mem_support_iff] <;> split_ifs <;>
      [exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩, exact and_iff_right h]
#align finsupp.erase Finsupp.erase
-/

/- warning: finsupp.support_erase -> Finsupp.support_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] {a : α} {f : Finsupp.{u1, u2} α M _inst_1}, Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.erase.{u1, u2} α M _inst_1 a f)) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u1, u2} α M _inst_1 f) a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] {a : α} {f : Finsupp.{u2, u1} α M _inst_1}, Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.erase.{u2, u1} α M _inst_1 a f)) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (Finsupp.support.{u2, u1} α M _inst_1 f) a)
Case conversion may be inaccurate. Consider using '#align finsupp.support_erase Finsupp.support_eraseₓ'. -/
@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} :
    (f.eraseₓ a).support = f.support.eraseₓ a := by convert rfl
#align finsupp.support_erase Finsupp.support_erase

/- warning: finsupp.erase_same -> Finsupp.erase_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {f : Finsupp.{u1, u2} α M _inst_1}, Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a f) a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {f : Finsupp.{u2, u1} α M _inst_1}, Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a f) a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_same Finsupp.erase_sameₓ'. -/
@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.eraseₓ a) a = 0 := by convert if_pos rfl
#align finsupp.erase_same Finsupp.erase_same

/- warning: finsupp.erase_ne -> Finsupp.erase_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {a' : α} {f : Finsupp.{u1, u2} α M _inst_1}, (Ne.{succ u1} α a' a) -> (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a f) a') (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f a'))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {a' : α} {f : Finsupp.{u2, u1} α M _inst_1}, (Ne.{succ u2} α a' a) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a f) a') (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f a'))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_ne Finsupp.erase_neₓ'. -/
@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.eraseₓ a) a' = f a' := by
  classical convert if_neg h
#align finsupp.erase_ne Finsupp.erase_ne

/- warning: finsupp.erase_single -> Finsupp.erase_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {b : M}, Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a (Finsupp.single.{u1, u2} α M _inst_1 a b)) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {b : M}, Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a (Finsupp.single.{u2, u1} α M _inst_1 a b)) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_single Finsupp.erase_singleₓ'. -/
@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 :=
  by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same]
    rfl
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)
#align finsupp.erase_single Finsupp.erase_single

/- warning: finsupp.erase_single_ne -> Finsupp.erase_single_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {a : α} {a' : α} {b : M}, (Ne.{succ u1} α a a') -> (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a (Finsupp.single.{u1, u2} α M _inst_1 a' b)) (Finsupp.single.{u1, u2} α M _inst_1 a' b))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {a : α} {a' : α} {b : M}, (Ne.{succ u2} α a a') -> (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a (Finsupp.single.{u2, u1} α M _inst_1 a' b)) (Finsupp.single.{u2, u1} α M _inst_1 a' b))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_single_ne Finsupp.erase_single_neₓ'. -/
theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b :=
  by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
  · rw [erase_ne hs]
#align finsupp.erase_single_ne Finsupp.erase_single_ne

/- warning: finsupp.erase_of_not_mem_support -> Finsupp.erase_of_not_mem_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {a : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M _inst_1 f))) -> (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a f) f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {a : α}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M _inst_1 f))) -> (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a f) f)
Case conversion may be inaccurate. Consider using '#align finsupp.erase_of_not_mem_support Finsupp.erase_of_not_mem_supportₓ'. -/
@[simp]
theorem erase_of_not_mem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f :=
  by
  ext b; by_cases hab : b = a
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
  · rw [erase_ne hab]
#align finsupp.erase_of_not_mem_support Finsupp.erase_of_not_mem_support

/- warning: finsupp.erase_zero -> Finsupp.erase_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.erase.{u1, u2} α M _inst_1 a (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.erase.{u2, u1} α M _inst_1 a (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.hasZero.{u2, u1} α M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_zero Finsupp.erase_zeroₓ'. -/
@[simp]
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  classical rw [← support_eq_empty, support_erase, support_zero, erase_empty]
#align finsupp.erase_zero Finsupp.erase_zero

end Erase

/-! ### Declarations about `on_finset` -/


section OnFinset

variable [Zero M]

#print Finsupp.onFinset /-
/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M
    where
  support :=
    haveI := Classical.decEq M
    s.filter fun a => f a ≠ 0
  toFun := f
  mem_support_toFun := by simpa
#align finsupp.on_finset Finsupp.onFinset
-/

/- warning: finsupp.on_finset_apply -> Finsupp.onFinset_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {s : Finset.{u1} α} {f : α -> M} {hf : forall (a : α), (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)} {a : α}, Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.onFinset.{u1, u2} α M _inst_1 s f hf) a) (f a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {s : Finset.{u2} α} {f : α -> M} {hf : forall (a : α), (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) -> (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)} {a : α}, Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.onFinset.{u2, u1} α M _inst_1 s f hf) a) (f a)
Case conversion may be inaccurate. Consider using '#align finsupp.on_finset_apply Finsupp.onFinset_applyₓ'. -/
@[simp]
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl
#align finsupp.on_finset_apply Finsupp.onFinset_apply

/- warning: finsupp.support_on_finset_subset -> Finsupp.support_onFinset_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {s : Finset.{u1} α} {f : α -> M} {hf : forall (a : α), (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.onFinset.{u1, u2} α M _inst_1 s f hf)) s
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {s : Finset.{u2} α} {f : α -> M} {hf : forall (a : α), (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) -> (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)}, HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.onFinset.{u2, u1} α M _inst_1 s f hf)) s
Case conversion may be inaccurate. Consider using '#align finsupp.support_on_finset_subset Finsupp.support_onFinset_subsetₓ'. -/
@[simp]
theorem support_onFinset_subset {s : Finset α} {f : α → M} {hf} : (onFinset s f hf).support ⊆ s :=
  by convert filter_subset _ _
#align finsupp.support_on_finset_subset Finsupp.support_onFinset_subset

/- warning: finsupp.mem_support_on_finset -> Finsupp.mem_support_onFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {s : Finset.{u1} α} {f : α -> M} (hf : forall (a : α), (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M _inst_1 (Finsupp.onFinset.{u1, u2} α M _inst_1 s f hf))) (Ne.{succ u2} M (f a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {s : Finset.{u2} α} {f : α -> M} (hf : forall (a : α), (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) -> (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) {a : α}, Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M _inst_1 (Finsupp.onFinset.{u2, u1} α M _inst_1 s f hf))) (Ne.{succ u1} M (f a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.mem_support_on_finset Finsupp.mem_support_onFinsetₓ'. -/
@[simp]
theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply]
#align finsupp.mem_support_on_finset Finsupp.mem_support_onFinset

#print Finsupp.support_onFinset /-
theorem support_onFinset [DecidableEq M] {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).support = s.filterₓ fun a => f a ≠ 0 := by convert rfl
#align finsupp.support_on_finset Finsupp.support_onFinset
-/

end OnFinset

section OfSupportFinite

variable [Zero M]

#print Finsupp.ofSupportFinite /-
/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M
    where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset
#align finsupp.of_support_finite Finsupp.ofSupportFinite
-/

/- warning: finsupp.of_support_finite_coe -> Finsupp.ofSupportFinite_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : α -> M} {hf : Set.Finite.{u1} α (Function.support.{u1, u2} α M _inst_1 f)}, Eq.{max (succ u1) (succ u2)} ((fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.ofSupportFinite.{u1, u2} α M _inst_1 f hf)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (Finsupp.ofSupportFinite.{u1, u2} α M _inst_1 f hf)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : α -> M} {hf : Set.Finite.{u2} α (Function.support.{u2, u1} α M _inst_1 f)}, Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (Finsupp.ofSupportFinite.{u2, u1} α M _inst_1 f hf)) f
Case conversion may be inaccurate. Consider using '#align finsupp.of_support_finite_coe Finsupp.ofSupportFinite_coeₓ'. -/
theorem ofSupportFinite_coe {f : α → M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl
#align finsupp.of_support_finite_coe Finsupp.ofSupportFinite_coe

#print Finsupp.canLift /-
instance canLift : CanLift (α → M) (α →₀ M) coeFn fun f => (Function.support f).Finite
    where prf f hf := ⟨ofSupportFinite f hf, rfl⟩
#align finsupp.can_lift Finsupp.canLift
-/

end OfSupportFinite

/-! ### Declarations about `map_range` -/


section MapRange

variable [Zero M] [Zero N] [Zero P]

#print Finsupp.mapRange /-
/-- The composition of `f : M → N` and `g : α →₀ M` is `map_range f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `data/finsupp/basic`):

* `finsupp.map_range.equiv`
* `finsupp.map_range.zero_hom`
* `finsupp.map_range.add_monoid_hom`
* `finsupp.map_range.add_equiv`
* `finsupp.map_range.linear_map`
* `finsupp.map_range.linear_equiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff, not_imp_not] <;> exact fun H => (congr_arg f H).trans hf
#align finsupp.map_range Finsupp.mapRange
-/

#print Finsupp.mapRange_apply /-
@[simp]
theorem mapRange_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl
#align finsupp.map_range_apply Finsupp.mapRange_apply
-/

#print Finsupp.mapRange_zero /-
@[simp]
theorem mapRange_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun a => by simp only [hf, zero_apply, map_range_apply]
#align finsupp.map_range_zero Finsupp.mapRange_zero
-/

/- warning: finsupp.map_range_id -> Finsupp.mapRange_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (g : Finsupp.{u1, u2} α M _inst_1), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.mapRange.{u1, u2, u2} α M M _inst_1 _inst_1 (id.{succ u2} M) (rfl.{succ u2} M (id.{succ u2} M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))) g) g
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (g : Finsupp.{u2, u1} α M _inst_1), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.mapRange.{u2, u1, u1} α M M _inst_1 _inst_1 (id.{succ u1} M) (rfl.{succ u1} M (id.{succ u1} M (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))) g) g
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_id Finsupp.mapRange_idₓ'. -/
@[simp]
theorem mapRange_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl
#align finsupp.map_range_id Finsupp.mapRange_id

#print Finsupp.mapRange_comp /-
theorem mapRange_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α →₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl
#align finsupp.map_range_comp Finsupp.mapRange_comp
-/

#print Finsupp.support_mapRange /-
theorem support_mapRange {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    (mapRange f hf g).support ⊆ g.support :=
  support_onFinset_subset
#align finsupp.support_map_range Finsupp.support_mapRange
-/

#print Finsupp.mapRange_single /-
@[simp]
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) :=
  ext fun a' => by
    classical simpa only [single_eq_pi_single] using Pi.apply_single _ (fun _ => hf) a _ a'
#align finsupp.map_range_single Finsupp.mapRange_single
-/

#print Finsupp.support_mapRange_of_injective /-
theorem support_mapRange_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support :=
  by
  ext
  simp only [Finsupp.mem_support_iff, Ne.def, Finsupp.mapRange_apply]
  exact he.ne_iff' he0
#align finsupp.support_map_range_of_injective Finsupp.support_mapRange_of_injective
-/

end MapRange

/-! ### Declarations about `emb_domain` -/


section EmbDomain

variable [Zero M] [Zero N]

#print Finsupp.embDomain /-
/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M
    where
  support := v.support.map f
  toFun a₂ :=
    haveI := Classical.decEq β
    if h : a₂ ∈ v.support.map f then
      v
        (v.support.choose (fun a₁ => f a₁ = a₂)
          (by
            rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
            exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb))
    else 0
  mem_support_toFun a₂ := by
    split_ifs
    · simp only [h, true_iff_iff, Ne.def]
      rw [← not_mem_support_iff, Classical.not_not]
      apply Finset.choose_mem
    · simp only [h, Ne.def, ne_self_iff_false]
#align finsupp.emb_domain Finsupp.embDomain
-/

/- warning: finsupp.support_emb_domain -> Finsupp.support_embDomain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) (v : Finsupp.{u1, u3} α M _inst_1), Eq.{succ u2} (Finset.{u2} β) (Finsupp.support.{u2, u3} β M _inst_1 (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f v)) (Finset.map.{u1, u2} α β f (Finsupp.support.{u1, u3} α M _inst_1 v))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) (v : Finsupp.{u3, u1} α M _inst_1), Eq.{succ u2} (Finset.{u2} β) (Finsupp.support.{u2, u1} β M _inst_1 (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f v)) (Finset.map.{u3, u2} α β f (Finsupp.support.{u3, u1} α M _inst_1 v))
Case conversion may be inaccurate. Consider using '#align finsupp.support_emb_domain Finsupp.support_embDomainₓ'. -/
@[simp]
theorem support_embDomain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).support = v.support.map f :=
  rfl
#align finsupp.support_emb_domain Finsupp.support_embDomain

/- warning: finsupp.emb_domain_zero -> Finsupp.embDomain_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f (OfNat.ofNat.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) 0 (OfNat.mk.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) 0 (Zero.zero.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) (Finsupp.hasZero.{u1, u3} α M _inst_1))))) (OfNat.ofNat.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) 0 (OfNat.mk.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) 0 (Zero.zero.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.hasZero.{u2, u3} β M _inst_1))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f (OfNat.ofNat.{max u3 u1} (Finsupp.{u3, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u3 u1} (Finsupp.{u3, u1} α M _inst_1) (Finsupp.hasZero.{u3, u1} α M _inst_1)))) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} β M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.hasZero.{u2, u1} β M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_zero Finsupp.embDomain_zeroₓ'. -/
@[simp]
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl
#align finsupp.emb_domain_zero Finsupp.embDomain_zero

/- warning: finsupp.emb_domain_apply -> Finsupp.embDomain_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) (v : Finsupp.{u1, u3} α M _inst_1) (a : α), Eq.{succ u3} M (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (fun (_x : Finsupp.{u2, u3} β M _inst_1) => β -> M) (Finsupp.hasCoeToFun.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f v) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) (fun (_x : Finsupp.{u1, u3} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u3} α M _inst_1) v a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) (v : Finsupp.{u3, u1} α M _inst_1) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} β M _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) _x) (Finsupp.funLike.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f v) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f a)) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Finsupp.{u3, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u3, u1} α M _inst_1) v a)
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_apply Finsupp.embDomain_applyₓ'. -/
@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  classical
    change dite _ _ _ = _
    split_ifs <;> rw [Finset.mem_map' f] at h
    · refine' congr_arg (v : α → M) (f.inj' _)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    · exact (not_mem_support_iff.1 h).symm
#align finsupp.emb_domain_apply Finsupp.embDomain_apply

/- warning: finsupp.emb_domain_notin_range -> Finsupp.embDomain_notin_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) (v : Finsupp.{u1, u3} α M _inst_1) (a : β), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)))) -> (Eq.{succ u3} M (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (fun (_x : Finsupp.{u2, u3} β M _inst_1) => β -> M) (Finsupp.hasCoeToFun.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f v) a) (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M _inst_1))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) (v : Finsupp.{u3, u1} α M _inst_1) (a : β), (Not (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a (Set.range.{u2, succ u3} β α (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f)))) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} β M _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) _x) (Finsupp.funLike.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f v) a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : β) => M) a) _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_notin_range Finsupp.embDomain_notin_rangeₓ'. -/
theorem embDomain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = 0 := by
  classical
    refine' dif_neg (mt (fun h => _) h)
    rcases Finset.mem_map.1 h with ⟨a, h, rfl⟩
    exact Set.mem_range_self a
#align finsupp.emb_domain_notin_range Finsupp.embDomain_notin_range

/- warning: finsupp.emb_domain_injective -> Finsupp.embDomain_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β), Function.Injective.{max (succ u1) (succ u3), max (succ u2) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β), Function.Injective.{max (succ u3) (succ u1), max (succ u2) (succ u1)} (Finsupp.{u3, u1} α M _inst_1) (Finsupp.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f)
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_injective Finsupp.embDomain_injectiveₓ'. -/
theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [emb_domain_apply] using ext_iff.1 h (f a)
#align finsupp.emb_domain_injective Finsupp.embDomain_injective

/- warning: finsupp.emb_domain_inj -> Finsupp.embDomain_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] {f : Function.Embedding.{succ u1, succ u2} α β} {l₁ : Finsupp.{u1, u3} α M _inst_1} {l₂ : Finsupp.{u1, u3} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f l₁) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f l₂)) (Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) l₁ l₂)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Function.Embedding.{succ u3, succ u2} α β} {l₁ : Finsupp.{u3, u1} α M _inst_1} {l₂ : Finsupp.{u3, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f l₁) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f l₂)) (Eq.{max (succ u3) (succ u1)} (Finsupp.{u3, u1} α M _inst_1) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_inj Finsupp.embDomain_injₓ'. -/
@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff
#align finsupp.emb_domain_inj Finsupp.embDomain_inj

/- warning: finsupp.emb_domain_eq_zero -> Finsupp.embDomain_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] {f : Function.Embedding.{succ u1, succ u2} α β} {l : Finsupp.{u1, u3} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f l) (OfNat.ofNat.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) 0 (OfNat.mk.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) 0 (Zero.zero.{max u2 u3} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.hasZero.{u2, u3} β M _inst_1))))) (Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) l (OfNat.ofNat.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) 0 (OfNat.mk.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) 0 (Zero.zero.{max u1 u3} (Finsupp.{u1, u3} α M _inst_1) (Finsupp.hasZero.{u1, u3} α M _inst_1)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Function.Embedding.{succ u3, succ u2} α β} {l : Finsupp.{u3, u1} α M _inst_1}, Iff (Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f l) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} β M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.hasZero.{u2, u1} β M _inst_1)))) (Eq.{max (succ u3) (succ u1)} (Finsupp.{u3, u1} α M _inst_1) l (OfNat.ofNat.{max u3 u1} (Finsupp.{u3, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u3 u1} (Finsupp.{u3, u1} α M _inst_1) (Finsupp.hasZero.{u3, u1} α M _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_eq_zero Finsupp.embDomain_eq_zeroₓ'. -/
@[simp]
theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (embDomain_injective f).eq_iff' <| embDomain_zero f
#align finsupp.emb_domain_eq_zero Finsupp.embDomain_eq_zero

/- warning: finsupp.emb_domain_map_range -> Finsupp.embDomain_mapRange is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : Zero.{u3} M] [_inst_2 : Zero.{u4} N] (f : Function.Embedding.{succ u1, succ u2} α β) (g : M -> N) (p : Finsupp.{u1, u3} α M _inst_1) (hg : Eq.{succ u4} N (g (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M _inst_1)))) (OfNat.ofNat.{u4} N 0 (OfNat.mk.{u4} N 0 (Zero.zero.{u4} N _inst_2)))), Eq.{max (succ u2) (succ u4)} (Finsupp.{u2, u4} β N _inst_2) (Finsupp.embDomain.{u1, u2, u4} α β N _inst_2 f (Finsupp.mapRange.{u1, u3, u4} α M N _inst_1 _inst_2 g hg p)) (Finsupp.mapRange.{u2, u3, u4} β M N _inst_1 _inst_2 g hg (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f p))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Zero.{u2} M] [_inst_2 : Zero.{u1} N] (f : Function.Embedding.{succ u4, succ u3} α β) (g : M -> N) (p : Finsupp.{u4, u2} α M _inst_1) (hg : Eq.{succ u1} N (g (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1))) (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N _inst_2))), Eq.{max (succ u3) (succ u1)} (Finsupp.{u3, u1} β N _inst_2) (Finsupp.embDomain.{u4, u3, u1} α β N _inst_2 f (Finsupp.mapRange.{u4, u2, u1} α M N _inst_1 _inst_2 g hg p)) (Finsupp.mapRange.{u3, u2, u1} β M N _inst_1 _inst_2 g hg (Finsupp.embDomain.{u4, u3, u2} α β M _inst_1 f p))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_map_range Finsupp.embDomain_mapRangeₓ'. -/
theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) :=
  by
  ext a
  by_cases a ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply]
  · rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ← hg] <;> assumption
#align finsupp.emb_domain_map_range Finsupp.embDomain_mapRange

/- warning: finsupp.single_of_emb_domain_single -> Finsupp.single_of_embDomain_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (l : Finsupp.{u1, u3} α M _inst_1) (f : Function.Embedding.{succ u1, succ u2} α β) (a : β) (b : M), (Ne.{succ u3} M b (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M _inst_1)))) -> (Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f l) (Finsupp.single.{u2, u3} β M _inst_1 a b)) -> (Exists.{succ u1} α (fun (x : α) => And (Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α M _inst_1) l (Finsupp.single.{u1, u3} α M _inst_1 x b)) (Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f x) a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (l : Finsupp.{u3, u2} α M _inst_1) (f : Function.Embedding.{succ u3, succ u1} α β) (a : β) (b : M), (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1))) -> (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} β M _inst_1) (Finsupp.embDomain.{u3, u1, u2} α β M _inst_1 f l) (Finsupp.single.{u1, u2} β M _inst_1 a b)) -> (Exists.{succ u3} α (fun (x : α) => And (Eq.{max (succ u3) (succ u2)} (Finsupp.{u3, u2} α M _inst_1) l (Finsupp.single.{u3, u2} α M _inst_1 x b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Function.Embedding.{succ u3, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u1} α β)) f x) a)))
Case conversion may be inaccurate. Consider using '#align finsupp.single_of_emb_domain_single Finsupp.single_of_embDomain_singleₓ'. -/
theorem single_of_embDomain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_emb_domain, h, support_single_ne_zero _ hb] <;> rfl
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← emb_domain_apply f l, h]
      by_cases h_cases : c = d
      · simp only [Eq.symm h_cases, hc₂, single_eq_same]
      · rw [single_apply, single_apply, if_neg, if_neg h_cases]
        by_contra hfd
        exact h_cases (f.injective (hc₂.trans hfd))
    · exact hc₂
#align finsupp.single_of_emb_domain_single Finsupp.single_of_embDomain_single

/- warning: finsupp.emb_domain_single -> Finsupp.embDomain_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) (a : α) (m : M), Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M _inst_1) (Finsupp.embDomain.{u1, u2, u3} α β M _inst_1 f (Finsupp.single.{u1, u3} α M _inst_1 a m)) (Finsupp.single.{u2, u3} β M _inst_1 (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) m)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) (a : α) (m : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} β M _inst_1) (Finsupp.embDomain.{u3, u2, u1} α β M _inst_1 f (Finsupp.single.{u3, u1} α M _inst_1 a m)) (Finsupp.single.{u2, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) M _inst_1 (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f a) m)
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_single Finsupp.embDomain_singleₓ'. -/
@[simp]
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) : embDomain f (single a m) = single (f a) m :=
  by
  classical
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a', rfl⟩
      simp [single_apply]
    · simp only [emb_domain_notin_range, h, single_apply, not_false_iff]
      rw [if_neg]
      rintro rfl
      simpa using h
#align finsupp.emb_domain_single Finsupp.embDomain_single

end EmbDomain

/-! ### Declarations about `zip_with` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

#print Finsupp.zipWith /-
/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`zip_with f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  onFinset
    (haveI := Classical.decEq α
    g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a)) fun a H =>
    by
    simp only [mem_union, mem_support_iff, Ne]; rw [← not_and_or]
    rintro ⟨h₁, h₂⟩; rw [h₁, h₂] at H; exact H hf
#align finsupp.zip_with Finsupp.zipWith
-/

/- warning: finsupp.zip_with_apply -> Finsupp.zipWith_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : Zero.{u2} M] [_inst_2 : Zero.{u3} N] [_inst_3 : Zero.{u4} P] {f : M -> N -> P} {hf : Eq.{succ u4} P (f (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))) (OfNat.ofNat.{u3} N 0 (OfNat.mk.{u3} N 0 (Zero.zero.{u3} N _inst_2)))) (OfNat.ofNat.{u4} P 0 (OfNat.mk.{u4} P 0 (Zero.zero.{u4} P _inst_3)))} {g₁ : Finsupp.{u1, u2} α M _inst_1} {g₂ : Finsupp.{u1, u3} α N _inst_2} {a : α}, Eq.{succ u4} P (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (Finsupp.{u1, u4} α P _inst_3) (fun (_x : Finsupp.{u1, u4} α P _inst_3) => α -> P) (Finsupp.hasCoeToFun.{u1, u4} α P _inst_3) (Finsupp.zipWith.{u1, u2, u3, u4} α M N P _inst_1 _inst_2 _inst_3 f hf g₁ g₂) a) (f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) g₁ a) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Finsupp.{u1, u3} α N _inst_2) (fun (_x : Finsupp.{u1, u3} α N _inst_2) => α -> N) (Finsupp.hasCoeToFun.{u1, u3} α N _inst_2) g₂ a))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u4}} [_inst_1 : Zero.{u3} M] [_inst_2 : Zero.{u2} N] [_inst_3 : Zero.{u4} P] {f : M -> N -> P} {hf : Eq.{succ u4} P (f (OfNat.ofNat.{u3} M 0 (Zero.toOfNat0.{u3} M _inst_1)) (OfNat.ofNat.{u2} N 0 (Zero.toOfNat0.{u2} N _inst_2))) (OfNat.ofNat.{u4} P 0 (Zero.toOfNat0.{u4} P _inst_3))} {g₁ : Finsupp.{u1, u3} α M _inst_1} {g₂ : Finsupp.{u1, u2} α N _inst_2} {a : α}, Eq.{succ u4} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => P) a) (FunLike.coe.{max (succ u1) (succ u4), succ u1, succ u4} (Finsupp.{u1, u4} α P _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => P) _x) (Finsupp.funLike.{u1, u4} α P _inst_3) (Finsupp.zipWith.{u1, u3, u2, u4} α M N P _inst_1 _inst_2 _inst_3 f hf g₁ g₂) a) (f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Finsupp.{u1, u3} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u1, u3} α M _inst_1) g₁ a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α N _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u1, u2} α N _inst_2) g₂ a))
Case conversion may be inaccurate. Consider using '#align finsupp.zip_with_apply Finsupp.zipWith_applyₓ'. -/
@[simp]
theorem zipWith_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl
#align finsupp.zip_with_apply Finsupp.zipWith_apply

/- warning: finsupp.support_zip_with -> Finsupp.support_zipWith is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : Zero.{u2} M] [_inst_2 : Zero.{u3} N] [_inst_3 : Zero.{u4} P] [D : DecidableEq.{succ u1} α] {f : M -> N -> P} {hf : Eq.{succ u4} P (f (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))) (OfNat.ofNat.{u3} N 0 (OfNat.mk.{u3} N 0 (Zero.zero.{u3} N _inst_2)))) (OfNat.ofNat.{u4} P 0 (OfNat.mk.{u4} P 0 (Zero.zero.{u4} P _inst_3)))} {g₁ : Finsupp.{u1, u2} α M _inst_1} {g₂ : Finsupp.{u1, u3} α N _inst_2}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u4} α P _inst_3 (Finsupp.zipWith.{u1, u2, u3, u4} α M N P _inst_1 _inst_2 _inst_3 f hf g₁ g₂)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => D a b)) (Finsupp.support.{u1, u2} α M _inst_1 g₁) (Finsupp.support.{u1, u3} α N _inst_2 g₂))
but is expected to have type
  forall {α : Type.{u4}} {M : Type.{u2}} {N : Type.{u1}} {P : Type.{u3}} [_inst_1 : Zero.{u2} M] [_inst_2 : Zero.{u1} N] [_inst_3 : Zero.{u3} P] [D : DecidableEq.{succ u4} α] {f : M -> N -> P} {hf : Eq.{succ u3} P (f (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_1)) (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N _inst_2))) (OfNat.ofNat.{u3} P 0 (Zero.toOfNat0.{u3} P _inst_3))} {g₁ : Finsupp.{u4, u2} α M _inst_1} {g₂ : Finsupp.{u4, u1} α N _inst_2}, HasSubset.Subset.{u4} (Finset.{u4} α) (Finset.instHasSubsetFinset.{u4} α) (Finsupp.support.{u4, u3} α P _inst_3 (Finsupp.zipWith.{u4, u2, u1, u3} α M N P _inst_1 _inst_2 _inst_3 f hf g₁ g₂)) (Union.union.{u4} (Finset.{u4} α) (Finset.instUnionFinset.{u4} α (fun (a : α) (b : α) => D a b)) (Finsupp.support.{u4, u2} α M _inst_1 g₁) (Finsupp.support.{u4, u1} α N _inst_2 g₂))
Case conversion may be inaccurate. Consider using '#align finsupp.support_zip_with Finsupp.support_zipWithₓ'. -/
theorem support_zipWith [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  rw [Subsingleton.elim D] <;> exact support_on_finset_subset
#align finsupp.support_zip_with Finsupp.support_zipWith

end ZipWith

/-! ### Additive monoid structure on `α →₀ M` -/


section AddZeroClass

variable [AddZeroClass M]

instance : Add (α →₀ M) :=
  ⟨zipWith (· + ·) (add_zero 0)⟩

/- warning: finsupp.coe_add -> Finsupp.coe_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (g : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), Eq.{succ (max u1 u2)} (α -> M) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) f g)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHAdd.{max u1 u2} (α -> M) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => AddZeroClass.toHasAdd.{u2} M _inst_1))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) g))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (g : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) f g)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (instHAdd.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (Pi.instAdd.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) ᾰ) (fun (i : α) => AddZeroClass.toAdd.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) i) _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) g))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_add Finsupp.coe_addₓ'. -/
@[simp]
theorem coe_add (f g : α →₀ M) : ⇑(f + g) = f + g :=
  rfl
#align finsupp.coe_add Finsupp.coe_add

/- warning: finsupp.add_apply -> Finsupp.add_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (g₁ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (g₂ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (a : α), Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) g₁ g₂) a) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M _inst_1)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) g₁ a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) g₂ a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (g₁ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (g₂ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) g₁ g₂) a) (HAdd.hAdd.{u1, u1, u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (instHAdd.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toAdd.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) g₁ a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) g₂ a))
Case conversion may be inaccurate. Consider using '#align finsupp.add_apply Finsupp.add_applyₓ'. -/
theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a :=
  rfl
#align finsupp.add_apply Finsupp.add_apply

/- warning: finsupp.support_add -> Finsupp.support_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] {g₁ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)} {g₂ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) g₁ g₂)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₁) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₂))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] {g₁ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)} {g₂ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)}, HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) g₁ g₂)) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₁) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₂))
Case conversion may be inaccurate. Consider using '#align finsupp.support_add Finsupp.support_addₓ'. -/
theorem support_add [DecidableEq α] {g₁ g₂ : α →₀ M} :
    (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith
#align finsupp.support_add Finsupp.support_add

/- warning: finsupp.support_add_eq -> Finsupp.support_add_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] {g₁ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)} {g₂ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₁) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₂)) -> (Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) g₁ g₂)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₁) (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) g₂)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] {g₁ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)} {g₂ : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)}, (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₁) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₂)) -> (Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) g₁ g₂)) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₁) (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) g₂)))
Case conversion may be inaccurate. Consider using '#align finsupp.support_add_eq Finsupp.support_add_eqₓ'. -/
theorem support_add_eq [DecidableEq α] {g₁ g₂ : α →₀ M} (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.support := disjoint_left.1 h ha
        simp only [mem_support_iff, Classical.not_not] at * <;>
          simpa only [add_apply, this, add_zero] )
      fun ha => by
      have : a ∉ g₁.support := disjoint_right.1 h ha
      simp only [mem_support_iff, Classical.not_not] at * <;> simpa only [add_apply, this, zero_add]
#align finsupp.support_add_eq Finsupp.support_add_eq

/- warning: finsupp.single_add -> Finsupp.single_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (a : α) (b₁ : M) (b₂ : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M _inst_1)) b₁ b₂)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b₁) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b₂))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (a : α) (b₁ : M) (b₂ : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M _inst_1)) b₁ b₂)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b₁) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b₂))
Case conversion may be inaccurate. Consider using '#align finsupp.single_add Finsupp.single_addₓ'. -/
@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  ext fun a' => by
    by_cases h : a = a'
    · rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same]
    · rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add]
#align finsupp.single_add Finsupp.single_add

instance : AddZeroClass (α →₀ M) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

/- warning: finsupp.single_add_hom -> Finsupp.singleAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.single_add_hom Finsupp.singleAddHomₓ'. -/
/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` in `linear_algebra/finsupp` for the stronger version as a linear map. -/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M :=
  ⟨single a, single_zero a, single_add a⟩
#align finsupp.single_add_hom Finsupp.singleAddHom

/- warning: finsupp.apply_add_hom -> Finsupp.applyAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{max u1 u2, u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) M (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_1)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{max u2 u1, u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) M (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_1)
Case conversion may be inaccurate. Consider using '#align finsupp.apply_add_hom Finsupp.applyAddHomₓ'. -/
/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` in `linear_algebra/finsupp` for the stronger version as a linear map. -/
@[simps apply]
def applyAddHom (a : α) : (α →₀ M) →+ M :=
  ⟨fun g => g a, zero_apply, fun _ _ => add_apply _ _ _⟩
#align finsupp.apply_add_hom Finsupp.applyAddHom

/- warning: finsupp.coe_fn_add_hom -> Finsupp.coeFnAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], AddMonoidHom.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (α -> M) (Finsupp.addZeroClass.{u1, u2} α M _inst_1) (Pi.addZeroClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], AddMonoidHom.{max u2 u1, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (α -> M) (Finsupp.addZeroClass.{u1, u2} α M _inst_1) (Pi.addZeroClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_fn_add_hom Finsupp.coeFnAddHomₓ'. -/
/-- Coercion from a `finsupp` to a function type is an `add_monoid_hom`. -/
@[simps]
noncomputable def coeFnAddHom : (α →₀ M) →+ α → M
    where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align finsupp.coe_fn_add_hom Finsupp.coeFnAddHom

/- warning: finsupp.update_eq_single_add_erase -> Finsupp.update_eq_single_add_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (a : α) (b : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.update.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) f a b) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (a : α) (b : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.update.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) f a b) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f))
Case conversion may be inaccurate. Consider using '#align finsupp.update_eq_single_add_erase Finsupp.update_eq_single_add_eraseₓ'. -/
theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
    f.update a b = single a b + f.eraseₓ a := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_single_add_erase Finsupp.update_eq_single_add_erase

/- warning: finsupp.update_eq_erase_add_single -> Finsupp.update_eq_erase_add_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (a : α) (b : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.update.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) f a b) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (a : α) (b : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.update.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) f a b) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align finsupp.update_eq_erase_add_single Finsupp.update_eq_erase_add_singleₓ'. -/
theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
    f.update a b = f.eraseₓ a + single a b := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_erase_add_single Finsupp.update_eq_erase_add_single

/- warning: finsupp.single_add_erase -> Finsupp.single_add_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (a : α) (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), Eq.{succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) f a)) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (a : α) (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1) a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) f a)) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f)) f
Case conversion may be inaccurate. Consider using '#align finsupp.single_add_erase Finsupp.single_add_eraseₓ'. -/
theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.eraseₓ a = f := by
  rw [← update_eq_single_add_erase, update_self]
#align finsupp.single_add_erase Finsupp.single_add_erase

/- warning: finsupp.erase_add_single -> Finsupp.erase_add_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (a : α) (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), Eq.{succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) f a))) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (a : α) (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f) (Finsupp.single.{u2, u1} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (AddZeroClass.toZero.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1) a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) f a))) f
Case conversion may be inaccurate. Consider using '#align finsupp.erase_add_single Finsupp.erase_add_singleₓ'. -/
theorem erase_add_single (a : α) (f : α →₀ M) : f.eraseₓ a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]
#align finsupp.erase_add_single Finsupp.erase_add_single

/- warning: finsupp.erase_add -> Finsupp.erase_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] (a : α) (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (f' : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) f f')) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f) (Finsupp.erase.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a f'))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (a : α) (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (f' : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) f f')) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f) (Finsupp.erase.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a f'))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_add Finsupp.erase_addₓ'. -/
@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' :=
  by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]
#align finsupp.erase_add Finsupp.erase_add

/- warning: finsupp.erase_add_hom -> Finsupp.eraseAddHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], α -> (AddMonoidHom.{max u2 u1, max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_add_hom Finsupp.eraseAddHomₓ'. -/
/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M
    where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a
#align finsupp.erase_add_hom Finsupp.eraseAddHom

/- warning: finsupp.induction -> Finsupp.induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] {p : (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> Prop} (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (p (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasZero.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))))) -> (forall (a : α) (b : M) (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) f))) -> (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M _inst_1))))) -> (p f) -> (p (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b) f))) -> (p f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] {p : (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) -> Prop} (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (p (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.hasZero.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1))))) -> (forall (a : α) (b : M) (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) f))) -> (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddZeroClass.toZero.{u1} M _inst_1)))) -> (p f) -> (p (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b) f))) -> (p f)
Case conversion may be inaccurate. Consider using '#align finsupp.induction Finsupp.inductionₓ'. -/
@[elab_as_elim]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf =>
    by
    suffices p (single a (f a) + f.eraseₓ a) by rwa [single_add_erase] at this
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction Finsupp.induction

/- warning: finsupp.induction₂ -> Finsupp.induction₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] {p : (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> Prop} (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (p (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasZero.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))))) -> (forall (a : α) (b : M) (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) f))) -> (Ne.{succ u2} M b (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M _inst_1))))) -> (p f) -> (p (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) f (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b)))) -> (p f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] {p : (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) -> Prop} (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (p (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.hasZero.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1))))) -> (forall (a : α) (b : M) (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) f))) -> (Ne.{succ u1} M b (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddZeroClass.toZero.{u1} M _inst_1)))) -> (p f) -> (p (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) f (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b)))) -> (p f)
Case conversion may be inaccurate. Consider using '#align finsupp.induction₂ Finsupp.induction₂ₓ'. -/
theorem induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf =>
    by
    suffices p (f.eraseₓ a + single a (f a)) by rwa [erase_add_single] at this
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction₂ Finsupp.induction₂

/- warning: finsupp.induction_linear -> Finsupp.induction_linear is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M] {p : (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> Prop} (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (p (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasZero.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))))) -> (forall (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (g : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), (p f) -> (p g) -> (p (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) f g))) -> (forall (a : α) (b : M), p (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b)) -> (p f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] {p : (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) -> Prop} (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (p (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.hasZero.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1))))) -> (forall (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (g : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), (p f) -> (p g) -> (p (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} α M _inst_1)) f g))) -> (forall (a : α) (b : M), p (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b)) -> (p f)
Case conversion may be inaccurate. Consider using '#align finsupp.induction_linear Finsupp.induction_linearₓ'. -/
theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) : p f :=
  induction₂ f h0 fun a b f _ _ w => hadd _ _ w (hsingle _ _)
#align finsupp.induction_linear Finsupp.induction_linear

/- warning: finsupp.add_closure_set_of_eq_single -> Finsupp.add_closure_setOf_eq_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddZeroClass.{u2} M], Eq.{succ (max u1 u2)} (AddSubmonoid.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (AddSubmonoid.closure.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1) (setOf.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (fun (f : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) => Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} M (fun (b : M) => Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) f (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) a b)))))) (Top.top.{max u1 u2} (AddSubmonoid.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (AddSubmonoid.hasTop.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M], Eq.{max (succ u2) (succ u1)} (AddSubmonoid.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.addZeroClass.{u2, u1} α M _inst_1)) (AddSubmonoid.closure.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.addZeroClass.{u2, u1} α M _inst_1) (setOf.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (fun (f : Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) => Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} M (fun (b : M) => Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) f (Finsupp.single.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1) a b)))))) (Top.top.{max u2 u1} (AddSubmonoid.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.addZeroClass.{u2, u1} α M _inst_1)) (AddSubmonoid.instTopAddSubmonoid.{max u2 u1} (Finsupp.{u2, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.addZeroClass.{u2, u1} α M _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.add_closure_set_of_eq_single Finsupp.add_closure_setOf_eq_singleₓ'. -/
@[simp]
theorem add_closure_setOf_eq_single :
    AddSubmonoid.closure { f : α →₀ M | ∃ a b, f = single a b } = ⊤ :=
  top_unique fun x hx =>
    Finsupp.induction x (AddSubmonoid.zero_mem _) fun a b f ha hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| ⟨a, b, rfl⟩) hf
#align finsupp.add_closure_set_of_eq_single Finsupp.add_closure_setOf_eq_single

/- warning: finsupp.add_hom_ext -> Finsupp.addHom_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {{f : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}} {{g : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}}, (forall (x : α) (y : M), Eq.{succ u3} N (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (fun (_x : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) => (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> N) (AddMonoidHom.hasCoeToFun.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) f (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) x y)) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (fun (_x : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) => (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> N) (AddMonoidHom.hasCoeToFun.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) g (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) x y))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) f g)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {{f : AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}} {{g : AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}}, (forall (x : α) (y : M), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => N) (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (succ u1) (succ u2), succ u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => N) _x) (AddHomClass.toFunLike.{max (max u1 u2) u3, max u1 u2, u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (AddZeroClass.toAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (AddZeroClass.toAdd.{u3} N _inst_2) (AddMonoidHomClass.toAddHomClass.{max (max u1 u2) u3, max u1 u2, u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 (AddMonoidHom.addMonoidHomClass.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2))) f (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y)) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (succ u1) (succ u2), succ u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => N) _x) (AddHomClass.toFunLike.{max (max u1 u2) u3, max u1 u2, u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (AddZeroClass.toAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (AddZeroClass.toAdd.{u3} N _inst_2) (AddMonoidHomClass.toAddHomClass.{max (max u1 u2) u3, max u1 u2, u3} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 (AddMonoidHom.addMonoidHomClass.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2))) g (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y))) -> (Eq.{max (max (succ u1) (succ u2)) (succ u3)} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.add_hom_ext Finsupp.addHom_extₓ'. -/
/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal. -/
theorem addHom_ext [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x y, f (single x y) = g (single x y)) : f = g :=
  by
  refine' AddMonoidHom.eq_of_eqOn_denseM add_closure_set_of_eq_single _
  rintro _ ⟨x, y, rfl⟩
  apply H
#align finsupp.add_hom_ext Finsupp.addHom_ext

/- warning: finsupp.add_hom_ext' -> Finsupp.addHom_ext' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {{f : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}} {{g : AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}}, (forall (x : α), Eq.{max (succ u3) (succ u2)} (AddMonoidHom.{u2, u3} M N _inst_1 _inst_2) (AddMonoidHom.comp.{u2, max u1 u2, u3} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 f (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x)) (AddMonoidHom.comp.{u2, max u1 u2, u3} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 g (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (AddMonoidHom.{max u1 u2, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) f g)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {{f : AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}} {{g : AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2}}, (forall (x : α), Eq.{max (succ u2) (succ u3)} (AddMonoidHom.{u2, u3} M N _inst_1 _inst_2) (AddMonoidHom.comp.{u2, max u1 u2, u3} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 f (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x)) (AddMonoidHom.comp.{u2, max u1 u2, u3} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2 g (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x))) -> (Eq.{max (max (succ u1) (succ u2)) (succ u3)} (AddMonoidHom.{max u2 u1, u3} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) N (Finsupp.addZeroClass.{u1, u2} α M _inst_1) _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.add_hom_ext' Finsupp.addHom_ext'ₓ'. -/
/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext]
theorem addHom_ext' [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x => AddMonoidHom.congr_fun (H x)
#align finsupp.add_hom_ext' Finsupp.addHom_ext'

/- warning: finsupp.mul_hom_ext -> Finsupp.mulHom_ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {{f : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}} {{g : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}}, (forall (x : α) (y : M), Eq.{succ u3} N (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (fun (_x : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) => (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) -> N) (MonoidHom.hasCoeToFun.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) f (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (fun (_x : Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) => (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (Equiv.hasCoeToFun.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (Multiplicative.ofAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) x y))) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u3)} (MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (fun (_x : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) => (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) -> N) (MonoidHom.hasCoeToFun.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) g (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (fun (_x : Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) => (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) -> (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (Equiv.hasCoeToFun.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)))) (Multiplicative.ofAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1) x y)))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) f g)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {{f : MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}} {{g : MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}}, (forall (x : α) (y : M), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) => N) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Equiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (fun (a : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) a) (Equiv.instFunLikeEquiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Multiplicative.ofAdd.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (succ u1) (succ u2), succ u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (fun (_x : Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) => N) _x) (MulHomClass.toFunLike.{max (max u1 u2) u3, max u1 u2, u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (MulOneClass.toMul.{max u1 u2} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{max (max u1 u2) u3, max u1 u2, u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 (MonoidHom.monoidHomClass.{max u1 u2, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2))) f (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Equiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Multiplicative.ofAdd.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (succ u1) (succ u2), succ u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (fun (_x : Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) => N) _x) (MulHomClass.toFunLike.{max (max u1 u2) u3, max u1 u2, u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (MulOneClass.toMul.{max u1 u2} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))) (MulOneClass.toMul.{u3} N _inst_2) (MonoidHomClass.toMulHomClass.{max (max u1 u2) u3, max u1 u2, u3} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 (MonoidHom.monoidHomClass.{max u1 u2, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2))) g (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Equiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (fun (_x : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) => Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ (max u2 u1), succ (max u2 u1)} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)))) (Multiplicative.ofAdd.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1) x y)))) -> (Eq.{max (max (succ u1) (succ u2)) (succ u3)} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.mul_hom_ext Finsupp.mulHom_extₓ'. -/
theorem mulHom_ext [MulOneClass N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
    (H : ∀ x y, f (Multiplicative.ofAdd <| single x y) = g (Multiplicative.ofAdd <| single x y)) :
    f = g :=
  MonoidHom.ext <|
    AddMonoidHom.congr_fun <| @addHom_ext α M (Additive N) _ _ f.toAdditive'' g.toAdditive'' H
#align finsupp.mul_hom_ext Finsupp.mulHom_ext

/- warning: finsupp.mul_hom_ext' -> Finsupp.mulHom_ext' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {f : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2} {g : MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}, (forall (x : α), Eq.{max (succ u3) (succ u2)} (MonoidHom.{u2, u3} (Multiplicative.{u2} M) N (Multiplicative.mulOneClass.{u2} M _inst_1) _inst_2) (MonoidHom.comp.{u2, max u1 u2, u3} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 f (coeFn.{max 1 (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (Equiv.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) => (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) -> (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.toMultiplicative.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x))) (MonoidHom.comp.{u2, max u1 u2, u3} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 g (coeFn.{max 1 (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (Equiv.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (fun (_x : Equiv.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) => (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) -> (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (Equiv.hasCoeToFun.{max (succ (max u1 u2)) (succ u2), max (succ (max u1 u2)) (succ u2)} (AddMonoidHom.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u1 u2} (Multiplicative.{u2} M) (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.toMultiplicative.{u2, max u1 u2} M (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x)))) -> (Eq.{max (succ u3) (succ (max u1 u2))} (MonoidHom.{max u1 u2, u3} (Multiplicative.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) f g)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] {f : MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2} {g : MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2}, (forall (x : α), Eq.{max (succ u2) (succ u3)} (MonoidHom.{u2, u3} (Multiplicative.{u2} M) N (Multiplicative.mulOneClass.{u2} M _inst_1) _inst_2) (MonoidHom.comp.{u2, max u1 u2, u3} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 f (FunLike.coe.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (Equiv.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (fun (_x : AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) => MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))) _x) (Equiv.instFunLikeEquiv.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.toMultiplicative.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x))) (MonoidHom.comp.{u2, max u1 u2, u3} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2 g (FunLike.coe.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (Equiv.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (fun (_x : AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) => MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1))) _x) (Equiv.instFunLikeEquiv.{max (succ (max u2 u1)) (succ u2), max (succ (max u2 u1)) (succ u2)} (AddMonoidHom.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (MonoidHom.{u2, max u2 u1} (Multiplicative.{u2} M) (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) (Multiplicative.mulOneClass.{u2} M _inst_1) (Multiplicative.mulOneClass.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)))) (AddMonoidHom.toMultiplicative.{u2, max u2 u1} M (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) _inst_1 (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) (Finsupp.singleAddHom.{u1, u2} α M _inst_1 x)))) -> (Eq.{max (max (succ u1) (succ u2)) (succ u3)} (MonoidHom.{max u2 u1, u3} (Multiplicative.{max u2 u1} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1))) N (Multiplicative.mulOneClass.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.addZeroClass.{u1, u2} α M _inst_1)) _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align finsupp.mul_hom_ext' Finsupp.mulHom_ext'ₓ'. -/
@[ext]
theorem mulHom_ext' [MulOneClass N] {f g : Multiplicative (α →₀ M) →* N}
    (H : ∀ x, f.comp (singleAddHom x).toMultiplicative = g.comp (singleAddHom x).toMultiplicative) :
    f = g :=
  mulHom_ext fun x => MonoidHom.congr_fun (H x)
#align finsupp.mul_hom_ext' Finsupp.mulHom_ext'

/- warning: finsupp.map_range_add -> Finsupp.mapRange_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {f : M -> N} {hf : Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M _inst_1))))) (OfNat.ofNat.{u3} N 0 (OfNat.mk.{u3} N 0 (Zero.zero.{u3} N (AddZeroClass.toHasZero.{u3} N _inst_2))))}, (forall (x : M) (y : M), Eq.{succ u3} N (f (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M _inst_1)) x y)) (HAdd.hAdd.{u3, u3, u3} N N N (instHAdd.{u3} N (AddZeroClass.toHasAdd.{u3} N _inst_2)) (f x) (f y))) -> (forall (v₁ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (v₂ : Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α N (AddZeroClass.toHasZero.{u3} N _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toHasZero.{u2} M _inst_1) (AddZeroClass.toHasZero.{u3} N _inst_2) f hf (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M _inst_1)) (Finsupp.hasAdd.{u1, u2} α M _inst_1)) v₁ v₂)) (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α N (AddZeroClass.toHasZero.{u3} N _inst_2)) (Finsupp.{u1, u3} α N (AddZeroClass.toHasZero.{u3} N _inst_2)) (Finsupp.{u1, u3} α N (AddZeroClass.toHasZero.{u3} N _inst_2)) (instHAdd.{max u1 u3} (Finsupp.{u1, u3} α N (AddZeroClass.toHasZero.{u3} N _inst_2)) (Finsupp.hasAdd.{u1, u3} α N _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toHasZero.{u2} M _inst_1) (AddZeroClass.toHasZero.{u3} N _inst_2) f hf v₁) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toHasZero.{u2} M _inst_1) (AddZeroClass.toHasZero.{u3} N _inst_2) f hf v₂)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u3} N] {f : M -> N} {hf : Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddZeroClass.toZero.{u2} M _inst_1)))) (OfNat.ofNat.{u3} N 0 (Zero.toOfNat0.{u3} N (AddZeroClass.toZero.{u3} N _inst_2)))}, (forall (x : M) (y : M), Eq.{succ u3} N (f (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M _inst_1)) x y)) (HAdd.hAdd.{u3, u3, u3} N N N (instHAdd.{u3} N (AddZeroClass.toAdd.{u3} N _inst_2)) (f x) (f y))) -> (forall (v₁ : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (v₂ : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α N (AddZeroClass.toZero.{u3} N _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u3} N _inst_2) f hf (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u1, u2} α M _inst_1)) v₁ v₂)) (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α N (AddZeroClass.toZero.{u3} N _inst_2)) (Finsupp.{u1, u3} α N (AddZeroClass.toZero.{u3} N _inst_2)) (Finsupp.{u1, u3} α N (AddZeroClass.toZero.{u3} N _inst_2)) (instHAdd.{max u1 u3} (Finsupp.{u1, u3} α N (AddZeroClass.toZero.{u3} N _inst_2)) (Finsupp.instAddFinsuppToZero.{u1, u3} α N _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u3} N _inst_2) f hf v₁) (Finsupp.mapRange.{u1, u2, u3} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u3} N _inst_2) f hf v₂)))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_add Finsupp.mapRange_addₓ'. -/
theorem mapRange_add [AddZeroClass N] {f : M → N} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, map_range_apply]
#align finsupp.map_range_add Finsupp.mapRange_add

/- warning: finsupp.map_range_add' -> Finsupp.mapRange_add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : AddZeroClass.{u3} M] [_inst_2 : AddZeroClass.{u4} N] [_inst_3 : AddMonoidHomClass.{u2, u3, u4} β M N _inst_1 _inst_2] {f : β} (v₁ : Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (v₂ : Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)), Eq.{max (succ u1) (succ u4)} (Finsupp.{u1, u4} α N (AddZeroClass.toHasZero.{u4} N _inst_2)) (Finsupp.mapRange.{u1, u3, u4} α M N (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => M -> N) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β M (fun (_x : M) => N) (AddHomClass.toFunLike.{u2, u3, u4} β M N (AddZeroClass.toHasAdd.{u3} M _inst_1) (AddZeroClass.toHasAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3))) f) (map_zero.{u3, u4, u2} M N β (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3) f) (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (instHAdd.{max u1 u3} (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.hasAdd.{u1, u3} α M _inst_1)) v₁ v₂)) (HAdd.hAdd.{max u1 u4, max u1 u4, max u1 u4} (Finsupp.{u1, u4} α N (AddZeroClass.toHasZero.{u4} N _inst_2)) (Finsupp.{u1, u4} α N (AddZeroClass.toHasZero.{u4} N _inst_2)) (Finsupp.{u1, u4} α N (AddZeroClass.toHasZero.{u4} N _inst_2)) (instHAdd.{max u1 u4} (Finsupp.{u1, u4} α N (AddZeroClass.toHasZero.{u4} N _inst_2)) (Finsupp.hasAdd.{u1, u4} α N _inst_2)) (Finsupp.mapRange.{u1, u3, u4} α M N (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => M -> N) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β M (fun (_x : M) => N) (AddHomClass.toFunLike.{u2, u3, u4} β M N (AddZeroClass.toHasAdd.{u3} M _inst_1) (AddZeroClass.toHasAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3))) f) (map_zero.{u3, u4, u2} M N β (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3) f) v₁) (Finsupp.mapRange.{u1, u3, u4} α M N (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => M -> N) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β M (fun (_x : M) => N) (AddHomClass.toFunLike.{u2, u3, u4} β M N (AddZeroClass.toHasAdd.{u3} M _inst_1) (AddZeroClass.toHasAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3))) f) (map_zero.{u3, u4, u2} M N β (AddZeroClass.toHasZero.{u3} M _inst_1) (AddZeroClass.toHasZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β M N _inst_1 _inst_2 _inst_3) f) v₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {M : Type.{u2}} {N : Type.{u4}} [_inst_1 : AddZeroClass.{u2} M] [_inst_2 : AddZeroClass.{u4} N] [_inst_3 : AddMonoidHomClass.{u3, u2, u4} β M N _inst_1 _inst_2] {f : β} (v₁ : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (v₂ : Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)), Eq.{max (succ u1) (succ u4)} (Finsupp.{u1, u4} α N (AddZeroClass.toZero.{u4} N _inst_2)) (Finsupp.mapRange.{u1, u2, u4} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (FunLike.coe.{succ u3, succ u2, succ u4} β M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : M) => N) _x) (AddHomClass.toFunLike.{u3, u2, u4} β M N (AddZeroClass.toAdd.{u2} M _inst_1) (AddZeroClass.toAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3)) f) (map_zero.{u4, u2, u3} M N β (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3) f) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toZero.{u2} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u1, u2} α M _inst_1)) v₁ v₂)) (HAdd.hAdd.{max u1 u4, max u1 u4, max u1 u4} (Finsupp.{u1, u4} α N (AddZeroClass.toZero.{u4} N _inst_2)) (Finsupp.{u1, u4} α N (AddZeroClass.toZero.{u4} N _inst_2)) (Finsupp.{u1, u4} α N (AddZeroClass.toZero.{u4} N _inst_2)) (instHAdd.{max u1 u4} (Finsupp.{u1, u4} α N (AddZeroClass.toZero.{u4} N _inst_2)) (Finsupp.instAddFinsuppToZero.{u1, u4} α N _inst_2)) (Finsupp.mapRange.{u1, u2, u4} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (FunLike.coe.{succ u3, succ u2, succ u4} β M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : M) => N) _x) (AddHomClass.toFunLike.{u3, u2, u4} β M N (AddZeroClass.toAdd.{u2} M _inst_1) (AddZeroClass.toAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3)) f) (map_zero.{u4, u2, u3} M N β (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3) f) v₁) (Finsupp.mapRange.{u1, u2, u4} α M N (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (FunLike.coe.{succ u3, succ u2, succ u4} β M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : M) => N) _x) (AddHomClass.toFunLike.{u3, u2, u4} β M N (AddZeroClass.toAdd.{u2} M _inst_1) (AddZeroClass.toAdd.{u4} N _inst_2) (AddMonoidHomClass.toAddHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3)) f) (map_zero.{u4, u2, u3} M N β (AddZeroClass.toZero.{u2} M _inst_1) (AddZeroClass.toZero.{u4} N _inst_2) (AddMonoidHomClass.toZeroHomClass.{u3, u2, u4} β M N _inst_1 _inst_2 _inst_3) f) v₂))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_add' Finsupp.mapRange_add'ₓ'. -/
theorem mapRange_add' [AddZeroClass N] [AddMonoidHomClass β M N] {f : β} (v₁ v₂ : α →₀ M) :
    mapRange f (map_zero f) (v₁ + v₂) = mapRange f (map_zero f) v₁ + mapRange f (map_zero f) v₂ :=
  mapRange_add (map_add f) v₁ v₂
#align finsupp.map_range_add' Finsupp.mapRange_add'

/- warning: finsupp.emb_domain.add_monoid_hom -> Finsupp.embDomain.addMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : AddZeroClass.{u3} M], (Function.Embedding.{succ u1, succ u2} α β) -> (AddMonoidHom.{max u1 u3, max u2 u3} (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.addZeroClass.{u1, u3} α M _inst_1) (Finsupp.addZeroClass.{u2, u3} β M _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : AddZeroClass.{u3} M], (Function.Embedding.{succ u1, succ u2} α β) -> (AddMonoidHom.{max u3 u1, max u3 u2} (Finsupp.{u1, u3} α M (AddZeroClass.toZero.{u3} M _inst_1)) (Finsupp.{u2, u3} β M (AddZeroClass.toZero.{u3} M _inst_1)) (Finsupp.addZeroClass.{u1, u3} α M _inst_1) (Finsupp.addZeroClass.{u2, u3} β M _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain.add_monoid_hom Finsupp.embDomain.addMonoidHomₓ'. -/
/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : α ↪ β) : (α →₀ M) →+ β →₀ M
    where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp [emb_domain_notin_range, h]
#align finsupp.emb_domain.add_monoid_hom Finsupp.embDomain.addMonoidHom

/- warning: finsupp.emb_domain_add -> Finsupp.embDomain_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : AddZeroClass.{u3} M] (f : Function.Embedding.{succ u1, succ u2} α β) (v : Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (w : Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)), Eq.{max (succ u2) (succ u3)} (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.embDomain.{u1, u2, u3} α β M (AddZeroClass.toHasZero.{u3} M _inst_1) f (HAdd.hAdd.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (instHAdd.{max u1 u3} (Finsupp.{u1, u3} α M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.hasAdd.{u1, u3} α M _inst_1)) v w)) (HAdd.hAdd.{max u2 u3, max u2 u3, max u2 u3} (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (instHAdd.{max u2 u3} (Finsupp.{u2, u3} β M (AddZeroClass.toHasZero.{u3} M _inst_1)) (Finsupp.hasAdd.{u2, u3} β M _inst_1)) (Finsupp.embDomain.{u1, u2, u3} α β M (AddZeroClass.toHasZero.{u3} M _inst_1) f v) (Finsupp.embDomain.{u1, u2, u3} α β M (AddZeroClass.toHasZero.{u3} M _inst_1) f w))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddZeroClass.{u1} M] (f : Function.Embedding.{succ u3, succ u2} α β) (v : Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (w : Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} β M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.embDomain.{u3, u2, u1} α β M (AddZeroClass.toZero.{u1} M _inst_1) f (HAdd.hAdd.{max u3 u1, max u3 u1, max u3 u1} (Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u3 u1} (Finsupp.{u3, u1} α M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u3, u1} α M _inst_1)) v w)) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} β M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} β M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.{u2, u1} β M (AddZeroClass.toZero.{u1} M _inst_1)) (instHAdd.{max u2 u1} (Finsupp.{u2, u1} β M (AddZeroClass.toZero.{u1} M _inst_1)) (Finsupp.instAddFinsuppToZero.{u2, u1} β M _inst_1)) (Finsupp.embDomain.{u3, u2, u1} α β M (AddZeroClass.toZero.{u1} M _inst_1) f v) (Finsupp.embDomain.{u3, u2, u1} α β M (AddZeroClass.toZero.{u1} M _inst_1) f w))
Case conversion may be inaccurate. Consider using '#align finsupp.emb_domain_add Finsupp.embDomain_addₓ'. -/
@[simp]
theorem embDomain_add (f : α ↪ β) (v w : α →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w :=
  (embDomain.addMonoidHom f).map_add v w
#align finsupp.emb_domain_add Finsupp.embDomain_add

end AddZeroClass

section AddMonoid

variable [AddMonoid M]

/- warning: finsupp.has_nat_scalar -> Finsupp.hasNatScalar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddMonoid.{u2} M], SMul.{0, max u1 u2} Nat (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddMonoid.{u2} M], SMul.{0, max u2 u1} Nat (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.has_nat_scalar Finsupp.hasNatScalarₓ'. -/
/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar : SMul ℕ (α →₀ M) :=
  ⟨fun n v => v.mapRange ((· • ·) n) (nsmul_zero _)⟩
#align finsupp.has_nat_scalar Finsupp.hasNatScalar

instance : AddMonoid (α →₀ M) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance [AddCommMonoid M] : AddCommMonoid (α →₀ M) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

instance [NegZeroClass G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg neg_zero⟩

/- warning: finsupp.coe_neg -> Finsupp.coe_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : NegZeroClass.{u2} G] (g : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)), Eq.{succ (max u1 u2)} (α -> G) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (fun (_x : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (Finsupp.hasNeg.{u1, u2} α G _inst_1) g)) (Neg.neg.{max u1 u2} (α -> G) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => NegZeroClass.toHasNeg.{u2} G _inst_1)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (fun (_x : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) g))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : NegZeroClass.{u2} G] (g : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) (Finsupp.instNegFinsuppToZero.{u1, u2} α G _inst_1) g)) (Neg.neg.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (fun (i : α) => NegZeroClass.toNeg.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) i) _inst_1)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) g))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_neg Finsupp.coe_negₓ'. -/
@[simp]
theorem coe_neg [NegZeroClass G] (g : α →₀ G) : ⇑(-g) = -g :=
  rfl
#align finsupp.coe_neg Finsupp.coe_neg

/- warning: finsupp.neg_apply -> Finsupp.neg_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : NegZeroClass.{u2} G] (g : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (a : α), Eq.{succ u2} G (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (fun (_x : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (Finsupp.hasNeg.{u1, u2} α G _inst_1) g) a) (Neg.neg.{u2} G (NegZeroClass.toHasNeg.{u2} G _inst_1) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (fun (_x : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) g a))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : NegZeroClass.{u2} G] (g : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) (Finsupp.instNegFinsuppToZero.{u1, u2} α G _inst_1) g) a) (Neg.neg.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (NegZeroClass.toNeg.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G _inst_1)) g a))
Case conversion may be inaccurate. Consider using '#align finsupp.neg_apply Finsupp.neg_applyₓ'. -/
theorem neg_apply [NegZeroClass G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl
#align finsupp.neg_apply Finsupp.neg_apply

/- warning: finsupp.map_range_neg -> Finsupp.mapRange_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {H : Type.{u3}} [_inst_1 : NegZeroClass.{u2} G] [_inst_2 : NegZeroClass.{u3} H] {f : G -> H} {hf : Eq.{succ u3} H (f (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (NegZeroClass.toHasZero.{u2} G _inst_1))))) (OfNat.ofNat.{u3} H 0 (OfNat.mk.{u3} H 0 (Zero.zero.{u3} H (NegZeroClass.toHasZero.{u3} H _inst_2))))}, (forall (x : G), Eq.{succ u3} H (f (Neg.neg.{u2} G (NegZeroClass.toHasNeg.{u2} G _inst_1) x)) (Neg.neg.{u3} H (NegZeroClass.toHasNeg.{u3} H _inst_2) (f x))) -> (forall (v : Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α H (NegZeroClass.toHasZero.{u3} H _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α G H (NegZeroClass.toHasZero.{u2} G _inst_1) (NegZeroClass.toHasZero.{u3} H _inst_2) f hf (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toHasZero.{u2} G _inst_1)) (Finsupp.hasNeg.{u1, u2} α G _inst_1) v)) (Neg.neg.{max u1 u3} (Finsupp.{u1, u3} α H (NegZeroClass.toHasZero.{u3} H _inst_2)) (Finsupp.hasNeg.{u1, u3} α H _inst_2) (Finsupp.mapRange.{u1, u2, u3} α G H (NegZeroClass.toHasZero.{u2} G _inst_1) (NegZeroClass.toHasZero.{u3} H _inst_2) f hf v)))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u3}} {H : Type.{u2}} [_inst_1 : NegZeroClass.{u3} G] [_inst_2 : NegZeroClass.{u2} H] {f : G -> H} {hf : Eq.{succ u2} H (f (OfNat.ofNat.{u3} G 0 (Zero.toOfNat0.{u3} G (NegZeroClass.toZero.{u3} G _inst_1)))) (OfNat.ofNat.{u2} H 0 (Zero.toOfNat0.{u2} H (NegZeroClass.toZero.{u2} H _inst_2)))}, (forall (x : G), Eq.{succ u2} H (f (Neg.neg.{u3} G (NegZeroClass.toNeg.{u3} G _inst_1) x)) (Neg.neg.{u2} H (NegZeroClass.toNeg.{u2} H _inst_2) (f x))) -> (forall (v : Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G _inst_1)), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H _inst_2)) (Finsupp.mapRange.{u1, u3, u2} α G H (NegZeroClass.toZero.{u3} G _inst_1) (NegZeroClass.toZero.{u2} H _inst_2) f hf (Neg.neg.{max u1 u3} (Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G _inst_1)) (Finsupp.instNegFinsuppToZero.{u1, u3} α G _inst_1) v)) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H _inst_2)) (Finsupp.instNegFinsuppToZero.{u1, u2} α H _inst_2) (Finsupp.mapRange.{u1, u3, u2} α G H (NegZeroClass.toZero.{u3} G _inst_1) (NegZeroClass.toZero.{u2} H _inst_2) f hf v)))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_neg Finsupp.mapRange_negₓ'. -/
theorem mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : α →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, map_range_apply]
#align finsupp.map_range_neg Finsupp.mapRange_neg

/- warning: finsupp.map_range_neg' -> Finsupp.mapRange_neg' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} {H : Type.{u4}} [_inst_1 : AddGroup.{u3} G] [_inst_2 : SubtractionMonoid.{u4} H] [_inst_3 : AddMonoidHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))] {f : β} (v : Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))), Eq.{max (succ u1) (succ u4)} (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.mapRange.{u1, u3, u4} α G H (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => G -> H) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β G (fun (_x : G) => H) (AddHomClass.toFunLike.{u2, u3, u4} β G H (AddZeroClass.toHasAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasAdd.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3))) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3) f) (Neg.neg.{max u1 u3} (Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (Finsupp.hasNeg.{u1, u3} α G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (AddGroup.toSubtractionMonoid.{u3} G _inst_1)))) v)) (Neg.neg.{max u1 u4} (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.hasNeg.{u1, u4} α H (SubNegZeroMonoid.toNegZeroClass.{u4} H (SubtractionMonoid.toSubNegZeroMonoid.{u4} H _inst_2))) (Finsupp.mapRange.{u1, u3, u4} α G H (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => G -> H) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β G (fun (_x : G) => H) (AddHomClass.toFunLike.{u2, u3, u4} β G H (AddZeroClass.toHasAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasAdd.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3))) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3) f) v))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u4}} {H : Type.{u3}} [_inst_1 : AddGroup.{u4} G] [_inst_2 : SubtractionMonoid.{u3} H] [_inst_3 : AddMonoidHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))] {f : β} (v : Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.mapRange.{u1, u4, u3} α G H (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (FunLike.coe.{succ u2, succ u4, succ u3} β G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : G) => H) _x) (AddHomClass.toFunLike.{u2, u4, u3} β G H (AddZeroClass.toAdd.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toAdd.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3)) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3) f) (Neg.neg.{max u1 u4} (Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (Finsupp.instNegFinsuppToZero.{u1, u4} α G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1)))) v)) (Neg.neg.{max u1 u3} (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.instNegFinsuppToZero.{u1, u3} α H (SubNegZeroMonoid.toNegZeroClass.{u3} H (SubtractionMonoid.toSubNegZeroMonoid.{u3} H _inst_2))) (Finsupp.mapRange.{u1, u4, u3} α G H (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (FunLike.coe.{succ u2, succ u4, succ u3} β G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : G) => H) _x) (AddHomClass.toFunLike.{u2, u4, u3} β G H (AddZeroClass.toAdd.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toAdd.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3)) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3) f) v))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_neg' Finsupp.mapRange_neg'ₓ'. -/
theorem mapRange_neg' [AddGroup G] [SubtractionMonoid H] [AddMonoidHomClass β G H] {f : β}
    (v : α →₀ G) : mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v
#align finsupp.map_range_neg' Finsupp.mapRange_neg'

instance [SubNegZeroMonoid G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

/- warning: finsupp.coe_sub -> Finsupp.coe_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : SubNegZeroMonoid.{u2} G] (g₁ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (g₂ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))), Eq.{succ (max u1 u2)} (α -> G) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasSub.{u1, u2} α G _inst_1)) g₁ g₂)) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHSub.{max u1 u2} (α -> G) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => SubNegMonoid.toHasSub.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) g₁) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) g₂))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : SubNegZeroMonoid.{u2} G] (g₁ : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (g₂ : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u2} α G _inst_1)) g₁ g₂)) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (instHSub.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) ᾰ) (fun (i : α) => SubNegMonoid.toSub.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) i) (SubNegZeroMonoid.toSubNegMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) i) _inst_1)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) g₁) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) g₂))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_sub Finsupp.coe_subₓ'. -/
@[simp]
theorem coe_sub [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl
#align finsupp.coe_sub Finsupp.coe_sub

/- warning: finsupp.sub_apply -> Finsupp.sub_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : SubNegZeroMonoid.{u2} G] (g₁ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (g₂ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (a : α), Eq.{succ u2} G (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasSub.{u1, u2} α G _inst_1)) g₁ g₂) a) (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toHasSub.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) g₁ a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) g₂ a))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : SubNegZeroMonoid.{u2} G] (g₁ : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (g₂ : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u2} α G _inst_1)) g₁ g₂) a) (HSub.hSub.{u2, u2, u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (instHSub.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegMonoid.toSub.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegZeroMonoid.toSubNegMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) g₁ a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G _inst_1))) g₂ a))
Case conversion may be inaccurate. Consider using '#align finsupp.sub_apply Finsupp.sub_applyₓ'. -/
theorem sub_apply [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl
#align finsupp.sub_apply Finsupp.sub_apply

/- warning: finsupp.map_range_sub -> Finsupp.mapRange_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {H : Type.{u3}} [_inst_1 : SubNegZeroMonoid.{u2} G] [_inst_2 : SubNegZeroMonoid.{u3} H] {f : G -> H} {hf : Eq.{succ u3} H (f (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1)))))))) (OfNat.ofNat.{u3} H 0 (OfNat.mk.{u3} H 0 (Zero.zero.{u3} H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2)))))))}, (forall (x : G) (y : G), Eq.{succ u3} H (f (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toHasSub.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))) x y)) (HSub.hSub.{u3, u3, u3} H H H (instHSub.{u3} H (SubNegMonoid.toHasSub.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))) (f x) (f y))) -> (forall (v₁ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (v₂ : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.mapRange.{u1, u2, u3} α G H (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1)))) (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2)))) f hf (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasSub.{u1, u2} α G _inst_1)) v₁ v₂)) (HSub.hSub.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.{u1, u3} α H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.{u1, u3} α H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))))) (instHSub.{max u1 u3} (Finsupp.{u1, u3} α H (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.hasSub.{u1, u3} α H _inst_2)) (Finsupp.mapRange.{u1, u2, u3} α G H (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1)))) (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2)))) f hf v₁) (Finsupp.mapRange.{u1, u2, u3} α G H (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (SubNegZeroMonoid.toSubNegMonoid.{u2} G _inst_1)))) (AddZeroClass.toHasZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubNegZeroMonoid.toSubNegMonoid.{u3} H _inst_2)))) f hf v₂)))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u3}} {H : Type.{u2}} [_inst_1 : SubNegZeroMonoid.{u3} G] [_inst_2 : SubNegZeroMonoid.{u2} H] {f : G -> H} {hf : Eq.{succ u2} H (f (OfNat.ofNat.{u3} G 0 (Zero.toOfNat0.{u3} G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))))) (OfNat.ofNat.{u2} H 0 (Zero.toOfNat0.{u2} H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))))}, (forall (x : G) (y : G), Eq.{succ u2} H (f (HSub.hSub.{u3, u3, u3} G G G (instHSub.{u3} G (SubNegMonoid.toSub.{u3} G (SubNegZeroMonoid.toSubNegMonoid.{u3} G _inst_1))) x y)) (HSub.hSub.{u2, u2, u2} H H H (instHSub.{u2} H (SubNegMonoid.toSub.{u2} H (SubNegZeroMonoid.toSubNegMonoid.{u2} H _inst_2))) (f x) (f y))) -> (forall (v₁ : Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))) (v₂ : Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))) (Finsupp.mapRange.{u1, u3, u2} α G H (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1)) (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2)) f hf (HSub.hSub.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))) (Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))) (Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))) (instHSub.{max u1 u3} (Finsupp.{u1, u3} α G (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u3} α G _inst_1)) v₁ v₂)) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))) (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))) (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α H (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u2} α H _inst_2)) (Finsupp.mapRange.{u1, u3, u2} α G H (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1)) (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2)) f hf v₁) (Finsupp.mapRange.{u1, u3, u2} α G H (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G _inst_1)) (NegZeroClass.toZero.{u2} H (SubNegZeroMonoid.toNegZeroClass.{u2} H _inst_2)) f hf v₂)))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_sub Finsupp.mapRange_subₓ'. -/
theorem mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : α →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, map_range_apply]
#align finsupp.map_range_sub Finsupp.mapRange_sub

/- warning: finsupp.map_range_sub' -> Finsupp.mapRange_sub' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} {H : Type.{u4}} [_inst_1 : AddGroup.{u3} G] [_inst_2 : SubtractionMonoid.{u4} H] [_inst_3 : AddMonoidHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))] {f : β} (v₁ : Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (v₂ : Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))), Eq.{max (succ u1) (succ u4)} (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.mapRange.{u1, u3, u4} α G H (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => G -> H) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β G (fun (_x : G) => H) (AddHomClass.toFunLike.{u2, u3, u4} β G H (AddZeroClass.toHasAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasAdd.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3))) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3) f) (HSub.hSub.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (instHSub.{max u1 u3} (Finsupp.{u1, u3} α G (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))))) (Finsupp.hasSub.{u1, u3} α G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (AddGroup.toSubtractionMonoid.{u3} G _inst_1)))) v₁ v₂)) (HSub.hSub.{max u1 u4, max u1 u4, max u1 u4} (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (instHSub.{max u1 u4} (Finsupp.{u1, u4} α H (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))))) (Finsupp.hasSub.{u1, u4} α H (SubtractionMonoid.toSubNegZeroMonoid.{u4} H _inst_2))) (Finsupp.mapRange.{u1, u3, u4} α G H (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => G -> H) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β G (fun (_x : G) => H) (AddHomClass.toFunLike.{u2, u3, u4} β G H (AddZeroClass.toHasAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasAdd.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3))) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3) f) v₁) (Finsupp.mapRange.{u1, u3, u4} α G H (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (coeFn.{succ u2, max (succ u3) (succ u4)} β (fun (_x : β) => G -> H) (FunLike.hasCoeToFun.{succ u2, succ u3, succ u4} β G (fun (_x : G) => H) (AddHomClass.toFunLike.{u2, u3, u4} β G H (AddZeroClass.toHasAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasAdd.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3))) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toHasZero.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1)))) (AddZeroClass.toHasZero.{u4} H (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u3, u4} β G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_1))) (AddMonoid.toAddZeroClass.{u4} H (SubNegMonoid.toAddMonoid.{u4} H (SubtractionMonoid.toSubNegMonoid.{u4} H _inst_2))) _inst_3) f) v₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u4}} {H : Type.{u3}} [_inst_1 : AddGroup.{u4} G] [_inst_2 : SubtractionMonoid.{u3} H] [_inst_3 : AddMonoidHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))] {f : β} (v₁ : Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (v₂ : Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))), Eq.{max (succ u1) (succ u3)} (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.mapRange.{u1, u4, u3} α G H (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (FunLike.coe.{succ u2, succ u4, succ u3} β G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : G) => H) _x) (AddHomClass.toFunLike.{u2, u4, u3} β G H (AddZeroClass.toAdd.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toAdd.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3)) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3) f) (HSub.hSub.{max u1 u4, max u1 u4, max u1 u4} (Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (instHSub.{max u1 u4} (Finsupp.{u1, u4} α G (NegZeroClass.toZero.{u4} G (SubNegZeroMonoid.toNegZeroClass.{u4} G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1))))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u4} α G (SubtractionMonoid.toSubNegZeroMonoid.{u4} G (AddGroup.toSubtractionMonoid.{u4} G _inst_1)))) v₁ v₂)) (HSub.hSub.{max u1 u3, max u1 u3, max u1 u3} (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (instHSub.{max u1 u3} (Finsupp.{u1, u3} α H (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u3} α H (SubtractionMonoid.toSubNegZeroMonoid.{u3} H _inst_2))) (Finsupp.mapRange.{u1, u4, u3} α G H (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (FunLike.coe.{succ u2, succ u4, succ u3} β G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : G) => H) _x) (AddHomClass.toFunLike.{u2, u4, u3} β G H (AddZeroClass.toAdd.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toAdd.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3)) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3) f) v₁) (Finsupp.mapRange.{u1, u4, u3} α G H (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (FunLike.coe.{succ u2, succ u4, succ u3} β G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : G) => H) _x) (AddHomClass.toFunLike.{u2, u4, u3} β G H (AddZeroClass.toAdd.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toAdd.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toAddHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3)) f) (map_zero.{u3, u4, u2} G H β (AddZeroClass.toZero.{u4} G (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)))) (AddZeroClass.toZero.{u3} H (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2)))) (AddMonoidHomClass.toZeroHomClass.{u2, u4, u3} β G H (AddMonoid.toAddZeroClass.{u4} G (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1))) (AddMonoid.toAddZeroClass.{u3} H (SubNegMonoid.toAddMonoid.{u3} H (SubtractionMonoid.toSubNegMonoid.{u3} H _inst_2))) _inst_3) f) v₂))
Case conversion may be inaccurate. Consider using '#align finsupp.map_range_sub' Finsupp.mapRange_sub'ₓ'. -/
theorem mapRange_sub' [AddGroup G] [SubtractionMonoid H] [AddMonoidHomClass β G H] {f : β}
    (v₁ v₂ : α →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂
#align finsupp.map_range_sub' Finsupp.mapRange_sub'

/- warning: finsupp.has_int_scalar -> Finsupp.hasIntScalar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G], SMul.{0, max u1 u2} Int (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G], SMul.{0, max u2 u1} Int (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finsupp.has_int_scalar Finsupp.hasIntScalarₓ'. -/
/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [AddGroup G] : SMul ℤ (α →₀ G) :=
  ⟨fun n v => v.mapRange ((· • ·) n) (zsmul_zero _)⟩
#align finsupp.has_int_scalar Finsupp.hasIntScalar

instance [AddGroup G] : AddGroup (α →₀ G) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommGroup G] : AddCommGroup (α →₀ G) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

/- warning: finsupp.single_add_single_eq_single_add_single -> Finsupp.single_add_single_eq_single_add_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {k : α} {l : α} {m : α} {n : α} {u : M} {v : M}, (Ne.{succ u2} M u (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))))) -> (Ne.{succ u2} M v (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))))) -> (Iff (Eq.{succ (max u1 u2)} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.hasAdd.{u1, u2} α M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) k u) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) l v)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.hasAdd.{u1, u2} α M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) m u) (Finsupp.single.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) n v))) (Or (And (Eq.{succ u1} α k m) (Eq.{succ u1} α l n)) (Or (And (Eq.{succ u2} M u v) (And (Eq.{succ u1} α k n) (Eq.{succ u1} α l m))) (And (Eq.{succ u2} M (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) u v) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))))) (And (Eq.{succ u1} α k l) (Eq.{succ u1} α m n))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {k : α} {l : α} {m : α} {n : α} {u : M} {v : M}, (Ne.{succ u2} M u (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))) -> (Ne.{succ u2} M v (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))) -> (Iff (Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.instAddFinsuppToZero.{u1, u2} α M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.single.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)) k u) (Finsupp.single.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)) l v)) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))) (Finsupp.instAddFinsuppToZero.{u1, u2} α M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Finsupp.single.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)) m u) (Finsupp.single.{u1, u2} α M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)) n v))) (Or (And (Eq.{succ u1} α k m) (Eq.{succ u1} α l n)) (Or (And (Eq.{succ u2} M u v) (And (Eq.{succ u1} α k n) (Eq.{succ u1} α l m))) (And (Eq.{succ u2} M (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) u v) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))))) (And (Eq.{succ u1} α k l) (Eq.{succ u1} α m n))))))
Case conversion may be inaccurate. Consider using '#align finsupp.single_add_single_eq_single_add_single Finsupp.single_add_single_eq_single_add_singleₓ'. -/
theorem single_add_single_eq_single_add_single [AddCommMonoid M] {k l m n : α} {u v : M}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n :=
  by
  classical
    simp_rw [FunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv
#align finsupp.single_add_single_eq_single_add_single Finsupp.single_add_single_eq_single_add_single

/- warning: finsupp.support_neg -> Finsupp.support_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))), Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasNeg.{u1, u2} α G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f)) (Finsupp.support.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))), Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) (Neg.neg.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.instNegFinsuppToZero.{u1, u2} α G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f)) (Finsupp.support.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align finsupp.support_neg Finsupp.support_negₓ'. -/
@[simp]
theorem support_neg [AddGroup G] (f : α →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange
      )
#align finsupp.support_neg Finsupp.support_neg

/- warning: finsupp.support_sub -> Finsupp.support_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : AddGroup.{u2} G] {f : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))} {g : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2))))) (Finsupp.hasSub.{u1, u2} α G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) f g)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finsupp.support.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) f) (Finsupp.support.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) g))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : AddGroup.{u1} G] {f : Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))} {g : Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))}, HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finsupp.support.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2)))) (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))) (Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))) (Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))) (instHSub.{max u2 u1} (Finsupp.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2))))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u2, u1} α G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2)))) f g)) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) (Finsupp.support.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2)))) f) (Finsupp.support.{u2, u1} α G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_2)))) g))
Case conversion may be inaccurate. Consider using '#align finsupp.support_sub Finsupp.support_subₓ'. -/
theorem support_sub [DecidableEq α] [AddGroup G] {f g : α →₀ G} :
    support (f - g) ⊆ support f ∪ support g :=
  by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add
#align finsupp.support_sub Finsupp.support_sub

/- warning: finsupp.erase_eq_sub_single -> Finsupp.erase_eq_sub_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (a : α), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.erase.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) a f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasSub.{u1, u2} α G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f (Finsupp.single.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) f a)))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (a : α), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.erase.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) a f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (NegZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (AddGroup.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1))))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u2} α G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f (Finsupp.single.{u1, u2} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (NegZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (AddGroup.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1)))) a (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) f a)))
Case conversion may be inaccurate. Consider using '#align finsupp.erase_eq_sub_single Finsupp.erase_eq_sub_singleₓ'. -/
theorem erase_eq_sub_single [AddGroup G] (f : α →₀ G) (a : α) : f.eraseₓ a = f - single a (f a) :=
  by
  ext a'
  rcases eq_or_ne a a' with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h]
#align finsupp.erase_eq_sub_single Finsupp.erase_eq_sub_single

/- warning: finsupp.update_eq_sub_add_single -> Finsupp.update_eq_sub_add_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (a : α) (b : G), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.update.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) f a b) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasAdd.{u1, u2} α G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (Finsupp.hasSub.{u1, u2} α G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f (Finsupp.single.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (fun (_x : Finsupp.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) => α -> G) (Finsupp.hasCoeToFun.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) f a))) (Finsupp.single.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : AddGroup.{u2} G] (f : Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (a : α) (b : G), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.update.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f a b) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (instHAdd.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.instAddFinsuppToZero.{u1, u2} α G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.{u1, u2} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (NegZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (AddGroup.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1))))) (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (instHSub.{max u1 u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) (Finsupp.instSubFinsuppToZeroToNegZeroClass.{u1, u2} α G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) f (Finsupp.single.{u1, u2} α ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (NegZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) (AddGroup.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) a) _inst_1)))) a (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => G) _x) (Finsupp.funLike.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))) f a))) (Finsupp.single.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align finsupp.update_eq_sub_add_single Finsupp.update_eq_sub_add_singleₓ'. -/
theorem update_eq_sub_add_single [AddGroup G] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]
#align finsupp.update_eq_sub_add_single Finsupp.update_eq_sub_add_single

end Finsupp

