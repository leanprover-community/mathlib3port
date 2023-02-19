/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.group
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.NeZero
import Mathbin.Algebra.Group.Basic
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Data.FunLike.Basic

/-!
# Monoid and group homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the bundled structures for monoid and group homomorphisms. Namely, we define
`monoid_hom` (resp., `add_monoid_hom`) to be bundled homomorphisms between multiplicative (resp.,
additive) monoids or groups.

We also define coercion to a function, and  usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

This file also defines the lesser-used (and notation-less) homomorphism types which are used as
building blocks for other homomorphisms:

* `zero_hom`
* `one_hom`
* `add_hom`
* `mul_hom`
* `monoid_with_zero_hom`

## Notations

* `→+`: Bundled `add_monoid` homs. Also use for `add_group` homs.
* `→*`: Bundled `monoid` homs. Also use for `group` homs.
* `→*₀`: Bundled `monoid_with_zero` homs. Also use for `group_with_zero` homs.
* `→ₙ*`: Bundled `semigroup` homs.

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `group_hom` -- the idea is that `monoid_hom` is used.
The constructor for `monoid_hom` needs a proof of `map_one` as well
as `map_mul`; a separate constructor `monoid_hom.mk'` will construct
group homs (i.e. monoid homs between groups) given only a proof
that multiplication is preserved,

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `monoid_hom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

Historically this file also included definitions of unbundled homomorphism classes; they were
deprecated and moved to `deprecated/group`.

## Tags

monoid_hom, add_monoid_hom

-/


variable {α β M N P : Type _}

-- monoids
variable {G : Type _} {H : Type _}

-- groups
variable {F : Type _}

-- homs
-- for easy multiple inheritance
section Zero

#print ZeroHom /-
/-- `zero_hom M N` is the type of functions `M → N` that preserve zero.

When possible, instead of parametrizing results over `(f : zero_hom M N)`,
you should parametrize over `(F : Type*) [zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `zero_hom_class`.
-/
structure ZeroHom (M : Type _) (N : Type _) [Zero M] [Zero N] where
  toFun : M → N
  map_zero' : to_fun 0 = 0
#align zero_hom ZeroHom
-/

#print ZeroHomClass /-
/-- `zero_hom_class F M N` states that `F` is a type of zero-preserving homomorphisms.

You should extend this typeclass when you extend `zero_hom`.
-/
class ZeroHomClass (F : Type _) (M N : outParam <| Type _) [Zero M] [Zero N] extends
  FunLike F M fun _ => N where
  map_zero : ∀ f : F, f 0 = 0
#align zero_hom_class ZeroHomClass
-/

-- Instances and lemmas are defined below through `@[to_additive]`.
end Zero

namespace NeZero

/- warning: ne_zero.of_map -> NeZero.of_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u2} R] [_inst_2 : Zero.{u3} M] [_inst_3 : ZeroHomClass.{u1, u2, u3} F R M _inst_1 _inst_2] (f : F) {r : R} [_inst_4 : NeZero.{u3} M _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => R -> M) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F R (fun (_x : R) => M) (ZeroHomClass.toFunLike.{u1, u2, u3} F R M _inst_1 _inst_2 _inst_3)) f r)], NeZero.{u2} R _inst_1 r
but is expected to have type
  forall {F : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Zero.{u3} R] [_inst_2 : Zero.{u2} M] [_inst_3 : ZeroHomClass.{u1, u3, u2} F R M _inst_1 _inst_2] (f : F) {r : R} [_inst_4 : NeZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : R) => M) r) _inst_2 (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : R) => M) _x) (ZeroHomClass.toFunLike.{u1, u3, u2} F R M _inst_1 _inst_2 _inst_3) f r)], NeZero.{u3} R _inst_1 r
Case conversion may be inaccurate. Consider using '#align ne_zero.of_map NeZero.of_mapₓ'. -/
theorem of_map {R M} [Zero R] [Zero M] [ZeroHomClass F R M] (f : F) {r : R} [NeZero (f r)] :
    NeZero r :=
  ⟨fun h => ne (f r) <| by convert ZeroHomClass.map_zero f⟩
#align ne_zero.of_map NeZero.of_map

/- warning: ne_zero.of_injective -> NeZero.of_injective is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Zero.{u2} R] {r : R} [_inst_2 : NeZero.{u2} R _inst_1 r] [_inst_3 : Zero.{u3} M] [_inst_4 : ZeroHomClass.{u1, u2, u3} F R M _inst_1 _inst_3] {f : F}, (Function.Injective.{succ u2, succ u3} R M (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => R -> M) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F R (fun (_x : R) => M) (ZeroHomClass.toFunLike.{u1, u2, u3} F R M _inst_1 _inst_3 _inst_4)) f)) -> (NeZero.{u3} M _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => R -> M) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F R (fun (_x : R) => M) (ZeroHomClass.toFunLike.{u1, u2, u3} F R M _inst_1 _inst_3 _inst_4)) f r))
but is expected to have type
  forall {F : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Zero.{u3} R] {r : R} [_inst_2 : NeZero.{u3} R _inst_1 r] [_inst_3 : Zero.{u2} M] [_inst_4 : ZeroHomClass.{u1, u3, u2} F R M _inst_1 _inst_3] {f : F}, (Function.Injective.{succ u3, succ u2} R M (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : R) => M) _x) (ZeroHomClass.toFunLike.{u1, u3, u2} F R M _inst_1 _inst_3 _inst_4) f)) -> (NeZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : R) => M) r) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : R) => M) _x) (ZeroHomClass.toFunLike.{u1, u3, u2} F R M _inst_1 _inst_3 _inst_4) f r))
Case conversion may be inaccurate. Consider using '#align ne_zero.of_injective NeZero.of_injectiveₓ'. -/
theorem of_injective {R M} [Zero R] {r : R} [NeZero r] [Zero M] [ZeroHomClass F R M] {f : F}
    (hf : Function.Injective f) : NeZero (f r) :=
  ⟨by
    rw [← ZeroHomClass.map_zero f]
    exact hf.ne (Ne r)⟩
#align ne_zero.of_injective NeZero.of_injective

end NeZero

section Add

#print AddHom /-
/-- `add_hom M N` is the type of functions `M → N` that preserve addition.

When possible, instead of parametrizing results over `(f : add_hom M N)`,
you should parametrize over `(F : Type*) [add_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_hom_class`.
-/
structure AddHom (M : Type _) (N : Type _) [Add M] [Add N] where
  toFun : M → N
  map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y
#align add_hom AddHom
-/

#print AddHomClass /-
/-- `add_hom_class F M N` states that `F` is a type of addition-preserving homomorphisms.
You should declare an instance of this typeclass when you extend `add_hom`.
-/
class AddHomClass (F : Type _) (M N : outParam <| Type _) [Add M] [Add N] extends
  FunLike F M fun _ => N where
  map_add : ∀ (f : F) (x y : M), f (x + y) = f x + f y
#align add_hom_class AddHomClass
-/

-- Instances and lemmas are defined below through `@[to_additive]`.
end Add

section add_zero

#print AddMonoidHom /-
/-- `M →+ N` is the type of functions `M → N` that preserve the `add_zero_class` structure.

`add_monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [add_monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `add_monoid_hom_class`.
-/
structure AddMonoidHom (M : Type _) (N : Type _) [AddZeroClass M] [AddZeroClass N] extends
  ZeroHom M N, AddHom M N
#align add_monoid_hom AddMonoidHom
-/

attribute [nolint doc_blame] AddMonoidHom.toAddHom

attribute [nolint doc_blame] AddMonoidHom.toZeroHom

-- mathport name: «expr →+ »
infixr:25 " →+ " => AddMonoidHom

#print AddMonoidHomClass /-
/-- `add_monoid_hom_class F M N` states that `F` is a type of `add_zero_class`-preserving
homomorphisms.

You should also extend this typeclass when you extend `add_monoid_hom`.
-/
class AddMonoidHomClass (F : Type _) (M N : outParam <| Type _) [AddZeroClass M]
  [AddZeroClass N] extends AddHomClass F M N, ZeroHomClass F M N
#align add_monoid_hom_class AddMonoidHomClass
-/

-- Instances and lemmas are defined below through `@[to_additive]`.
end add_zero

section One

variable [One M] [One N]

#print OneHom /-
/-- `one_hom M N` is the type of functions `M → N` that preserve one.

When possible, instead of parametrizing results over `(f : one_hom M N)`,
you should parametrize over `(F : Type*) [one_hom_class F M N] (f : F)`.

When you extend this structure, make sure to also extend `one_hom_class`.
-/
@[to_additive]
structure OneHom (M : Type _) (N : Type _) [One M] [One N] where
  toFun : M → N
  map_one' : to_fun 1 = 1
#align one_hom OneHom
#align zero_hom ZeroHom
-/

#print OneHomClass /-
/-- `one_hom_class F M N` states that `F` is a type of one-preserving homomorphisms.
You should extend this typeclass when you extend `one_hom`.
-/
@[to_additive]
class OneHomClass (F : Type _) (M N : outParam <| Type _) [One M] [One N] extends
  FunLike F M fun _ => N where
  map_one : ∀ f : F, f 1 = 1
#align one_hom_class OneHomClass
#align zero_hom_class ZeroHomClass
-/

#print OneHom.oneHomClass /-
@[to_additive]
instance OneHom.oneHomClass : OneHomClass (OneHom M N) M N
    where
  coe := OneHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_one := OneHom.map_one'
#align one_hom.one_hom_class OneHom.oneHomClass
#align zero_hom.zero_hom_class ZeroHom.zeroHomClass
-/

/- warning: map_one -> map_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : OneHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (OneHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] [_inst_3 : OneHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align map_one map_oneₓ'. -/
@[simp, to_additive]
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 :=
  OneHomClass.map_one f
#align map_one map_one
#align map_zero map_zero

/- warning: map_eq_one_iff -> map_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : OneHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), (Function.Injective.{succ u1, succ u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (OneHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f)) -> (forall {x : M}, Iff (Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (OneHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))) (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] [_inst_3 : OneHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), (Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f)) -> (forall {x : M}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) _inst_2))) (Eq.{succ u2} M x (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align map_eq_one_iff map_eq_one_iffₓ'. -/
@[to_additive]
theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f) {x : M} :
    f x = 1 ↔ x = 1 :=
  hf.eq_iff' (map_one f)
#align map_eq_one_iff map_eq_one_iff
#align map_eq_zero_iff map_eq_zero_iff

/- warning: map_ne_one_iff -> map_ne_one_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_3 : One.{u1} R] [_inst_4 : One.{u2} S] [_inst_5 : OneHomClass.{u3, u1, u2} F R S _inst_3 _inst_4] (f : F), (Function.Injective.{succ u1, succ u2} R S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (OneHomClass.toFunLike.{u3, u1, u2} F R S _inst_3 _inst_4 _inst_5)) f)) -> (forall {x : R}, Iff (Ne.{succ u2} S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (OneHomClass.toFunLike.{u3, u1, u2} F R S _inst_3 _inst_4 _inst_5)) f x) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S _inst_4)))) (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R _inst_3)))))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {F : Type.{u1}} [_inst_3 : One.{u3} R] [_inst_4 : One.{u2} S] [_inst_5 : OneHomClass.{u1, u3, u2} F R S _inst_3 _inst_4] (f : F), (Function.Injective.{succ u3, succ u2} R S (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) _x) (OneHomClass.toFunLike.{u1, u3, u2} F R S _inst_3 _inst_4 _inst_5) f)) -> (forall {x : R}, Iff (Ne.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) _x) (OneHomClass.toFunLike.{u1, u3, u2} F R S _inst_3 _inst_4 _inst_5) f x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) _inst_4))) (Ne.{succ u3} R x (OfNat.ofNat.{u3} R 1 (One.toOfNat1.{u3} R _inst_3))))
Case conversion may be inaccurate. Consider using '#align map_ne_one_iff map_ne_one_iffₓ'. -/
@[to_additive]
theorem map_ne_one_iff {R S F : Type _} [One R] [One S] [OneHomClass F R S] (f : F)
    (hf : Function.Injective f) {x : R} : f x ≠ 1 ↔ x ≠ 1 :=
  (map_eq_one_iff f hf).Not
#align map_ne_one_iff map_ne_one_iff
#align map_ne_zero_iff map_ne_zero_iff

/- warning: ne_one_of_map -> ne_one_of_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_3 : One.{u1} R] [_inst_4 : One.{u2} S] [_inst_5 : OneHomClass.{u3, u1, u2} F R S _inst_3 _inst_4] {f : F} {x : R}, (Ne.{succ u2} S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (OneHomClass.toFunLike.{u3, u1, u2} F R S _inst_3 _inst_4 _inst_5)) f x) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S _inst_4)))) -> (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R _inst_3))))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {F : Type.{u1}} [_inst_3 : One.{u3} R] [_inst_4 : One.{u2} S] [_inst_5 : OneHomClass.{u1, u3, u2} F R S _inst_3 _inst_4] {f : F} {x : R}, (Ne.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) _x) (OneHomClass.toFunLike.{u1, u3, u2} F R S _inst_3 _inst_4 _inst_5) f x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : R) => S) x) _inst_4))) -> (Ne.{succ u3} R x (OfNat.ofNat.{u3} R 1 (One.toOfNat1.{u3} R _inst_3)))
Case conversion may be inaccurate. Consider using '#align ne_one_of_map ne_one_of_mapₓ'. -/
@[to_additive]
theorem ne_one_of_map {R S F : Type _} [One R] [One S] [OneHomClass F R S] {f : F} {x : R}
    (hx : f x ≠ 1) : x ≠ 1 :=
  ne_of_apply_ne f <| ne_of_ne_of_eq hx (map_one f).symm
#align ne_one_of_map ne_one_of_map
#align ne_zero_of_map ne_zero_of_map

@[to_additive]
instance [OneHomClass F M N] : CoeTC F (OneHom M N) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f }⟩

/- warning: one_hom.coe_coe -> OneHom.coe_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : OneHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u1) (succ u2)} ((fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (OneHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (OneHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u2} (OneHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => N) (OneHomClass.toFunLike.{max u2 u1, u1, u2} (OneHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u1, u2} M N _inst_1 _inst_2))) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (OneHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (OneHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (OneHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] [_inst_3 : OneHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) (OneHomClass.toOneHom.{u2, u1, u3} M N F _inst_1 _inst_2 _inst_3 f)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f)
Case conversion may be inaccurate. Consider using '#align one_hom.coe_coe OneHom.coe_coeₓ'. -/
@[simp, to_additive]
theorem OneHom.coe_coe [OneHomClass F M N] (f : F) : ((f : OneHom M N) : M → N) = f :=
  rfl
#align one_hom.coe_coe OneHom.coe_coe
#align zero_hom.coe_coe ZeroHom.coe_coe

end One

section Mul

variable [Mul M] [Mul N]

#print MulHom /-
/-- `M →ₙ* N` is the type of functions `M → N` that preserve multiplication. The `ₙ` in the notation
stands for "non-unital" because it is intended to match the notation for `non_unital_alg_hom` and
`non_unital_ring_hom`, so a `mul_hom` is a non-unital monoid hom.

When possible, instead of parametrizing results over `(f : M →ₙ* N)`,
you should parametrize over `(F : Type*) [mul_hom_class F M N] (f : F)`.
When you extend this structure, make sure to extend `mul_hom_class`.
-/
@[to_additive]
structure MulHom (M : Type _) (N : Type _) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y
#align mul_hom MulHom
#align add_hom AddHom
-/

-- mathport name: «expr →ₙ* »
infixr:25 " →ₙ* " => MulHom

#print MulHomClass /-
/-- `mul_hom_class F M N` states that `F` is a type of multiplication-preserving homomorphisms.

You should declare an instance of this typeclass when you extend `mul_hom`.
-/
@[to_additive]
class MulHomClass (F : Type _) (M N : outParam <| Type _) [Mul M] [Mul N] extends
  FunLike F M fun _ => N where
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y
#align mul_hom_class MulHomClass
#align add_hom_class AddHomClass
-/

#print MulHom.mulHomClass /-
@[to_additive]
instance MulHom.mulHomClass : MulHomClass (M →ₙ* N) M N
    where
  coe := MulHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_mul := MulHom.map_mul'
#align mul_hom.mul_hom_class MulHom.mulHomClass
#align add_hom.add_hom_class AddHom.addHomClass
-/

/- warning: map_mul -> map_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : MulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) (x : M) (y : M), Eq.{succ u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f x) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] [_inst_3 : MulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F) (x : M) (y : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) y) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) _inst_2) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f x) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f y))
Case conversion may be inaccurate. Consider using '#align map_mul map_mulₓ'. -/
@[simp, to_additive]
theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y :=
  MulHomClass.map_mul f x y
#align map_mul map_mul
#align map_add map_add

@[to_additive]
instance [MulHomClass F M N] : CoeTC F (M →ₙ* N) :=
  ⟨fun f =>
    { toFun := f
      map_mul' := map_mul f }⟩

/- warning: mul_hom.coe_coe -> MulHom.coe_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : MulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u1) (succ u2)} ((fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MulHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MulHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => N) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (MulHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} M N _inst_1 _inst_2))) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MulHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MulHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] [_inst_3 : MulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) (MulHomClass.toMulHom.{u2, u1, u3} M N F _inst_1 _inst_2 _inst_3 f)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f)
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_coe MulHom.coe_coeₓ'. -/
@[simp, to_additive]
theorem MulHom.coe_coe [MulHomClass F M N] (f : F) : ((f : MulHom M N) : M → N) = f :=
  rfl
#align mul_hom.coe_coe MulHom.coe_coe
#align add_hom.coe_coe AddHom.coe_coe

end Mul

section mul_one

variable [MulOneClass M] [MulOneClass N]

#print MonoidHom /-
/-- `M →* N` is the type of functions `M → N` that preserve the `monoid` structure.
`monoid_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →+ N)`,
you should parametrize over `(F : Type*) [monoid_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_hom_class`.
-/
@[to_additive]
structure MonoidHom (M : Type _) (N : Type _) [MulOneClass M] [MulOneClass N] extends OneHom M N,
  M →ₙ* N
#align monoid_hom MonoidHom
#align add_monoid_hom AddMonoidHom
-/

attribute [nolint doc_blame] MonoidHom.toMulHom

attribute [nolint doc_blame] MonoidHom.toOneHom

-- mathport name: «expr →* »
infixr:25 " →* " => MonoidHom

#print MonoidHomClass /-
/-- `monoid_hom_class F M N` states that `F` is a type of `monoid`-preserving homomorphisms.
You should also extend this typeclass when you extend `monoid_hom`. -/
@[to_additive
      "`add_monoid_hom_class F M N` states that `F` is a type of `add_monoid`-preserving homomorphisms.\nYou should also extend this typeclass when you extend `add_monoid_hom`."]
class MonoidHomClass (F : Type _) (M N : outParam <| Type _) [MulOneClass M] [MulOneClass N] extends
  MulHomClass F M N, OneHomClass F M N
#align monoid_hom_class MonoidHomClass
#align add_monoid_hom_class AddMonoidHomClass
-/

#print MonoidHom.monoidHomClass /-
@[to_additive]
instance MonoidHom.monoidHomClass : MonoidHomClass (M →* N) M N
    where
  coe := MonoidHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_mul := MonoidHom.map_mul'
  map_one := MonoidHom.map_one'
#align monoid_hom.monoid_hom_class MonoidHom.monoidHomClass
#align add_monoid_hom.add_monoid_hom_class AddMonoidHom.addMonoidHomClass
-/

@[to_additive]
instance [MonoidHomClass F M N] : CoeTC F (M →* N) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_mul' := map_mul f }⟩

/- warning: monoid_hom.coe_coe -> MonoidHom.coe_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => N) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u1, u2} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u1, u2} M N _inst_1 _inst_2)))) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3))) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] [_inst_3 : MonoidHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) (MonoidHomClass.toMonoidHom.{u2, u1, u3} M N F _inst_1 _inst_2 _inst_3 f)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3)) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_coe MonoidHom.coe_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((f : M →* N) : M → N) = f :=
  rfl
#align monoid_hom.coe_coe MonoidHom.coe_coe
#align add_monoid_hom.coe_coe AddMonoidHom.coe_coe

/- warning: map_mul_eq_one -> map_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F) {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3))) f a) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3))) f b)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] [_inst_3 : MonoidHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F) {a : M} {b : M}, (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) a b) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3)) f a) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3)) f b)) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2))))
Case conversion may be inaccurate. Consider using '#align map_mul_eq_one map_mul_eq_oneₓ'. -/
@[to_additive]
theorem map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} (h : a * b = 1) : f a * f b = 1 :=
  by rw [← map_mul, h, map_one]
#align map_mul_eq_one map_mul_eq_one
#align map_add_eq_zero map_add_eq_zero

/- warning: map_div' -> map_div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : DivInvMonoid.{u1} G] [_inst_4 : DivInvMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))] (f : F), (forall (a : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_3) a)) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H _inst_4) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f a))) -> (forall (a : G) (b : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_3)) a b)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toHasDiv.{u2} H _inst_4)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f a) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f b)))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : DivInvMonoid.{u3} G] [_inst_4 : DivInvMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))] (f : F), (forall (a : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (Inv.inv.{u3} G (DivInvMonoid.toInv.{u3} G _inst_3) a)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f (Inv.inv.{u3} G (DivInvMonoid.toInv.{u3} G _inst_3) a)) (Inv.inv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivInvMonoid.toInv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f a))) -> (forall (a : G) (b : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HDiv.hDiv.{u3, u3, u3} G G G (instHDiv.{u3} G (DivInvMonoid.toDiv.{u3} G _inst_3)) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f (HDiv.hDiv.{u3, u3, u3} G G G (instHDiv.{u3} G (DivInvMonoid.toDiv.{u3} G _inst_3)) a b)) (HDiv.hDiv.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHDiv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivInvMonoid.toDiv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f a) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f b)))
Case conversion may be inaccurate. Consider using '#align map_div' map_div'ₓ'. -/
@[to_additive]
theorem map_div' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
    (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, hf]
#align map_div' map_div'
#align map_sub' map_sub'

/- warning: map_inv -> map_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : Group.{u1} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) a)) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f a))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : Group.{u3} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (Inv.inv.{u3} G (InvOneClass.toInv.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3)))) a)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f (Inv.inv.{u3} G (InvOneClass.toInv.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3)))) a)) (Inv.inv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (InvOneClass.toInv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivInvOneMonoid.toInvOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivisionMonoid.toDivInvOneMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f a))
Case conversion may be inaccurate. Consider using '#align map_inv map_invₓ'. -/
/-- Group homomorphisms preserve inverse. -/
@[simp, to_additive "Additive group homomorphisms preserve negation."]
theorem map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    f a⁻¹ = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| map_mul_eq_one f <| inv_mul_self _
#align map_inv map_inv
#align map_neg map_neg

/- warning: map_mul_inv -> map_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : Group.{u1} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G) (b : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) b))) (HMul.hMul.{u2, u2, u2} H H H (instHMul.{u2} H (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))))) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f a) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f b)))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : Group.{u3} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G) (b : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HMul.hMul.{u3, u3, u3} G G G (instHMul.{u3} G (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))))) a (Inv.inv.{u3} G (InvOneClass.toInv.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3)))) b))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f (HMul.hMul.{u3, u3, u3} G G G (instHMul.{u3} G (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))))) a (Inv.inv.{u3} G (InvOneClass.toInv.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3)))) b))) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (Monoid.toMulOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivInvMonoid.toMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivisionMonoid.toDivInvMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4))))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f a) (Inv.inv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) (InvOneClass.toInv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) (DivInvOneMonoid.toInvOneClass.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) (DivisionMonoid.toDivInvOneMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) _inst_4))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f b)))
Case conversion may be inaccurate. Consider using '#align map_mul_inv map_mul_invₓ'. -/
/-- Group homomorphisms preserve division. -/
@[simp, to_additive "Additive group homomorphisms preserve subtraction."]
theorem map_mul_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (a b : G) :
    f (a * b⁻¹) = f a * (f b)⁻¹ := by rw [map_mul, map_inv]
#align map_mul_inv map_mul_inv
#align map_add_neg map_add_neg

/- warning: map_div -> map_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : Group.{u1} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G) (b : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) a b)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toHasDiv.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f a) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f b))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : Group.{u3} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (a : G) (b : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HDiv.hDiv.{u3, u3, u3} G G G (instHDiv.{u3} G (DivInvMonoid.toDiv.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f (HDiv.hDiv.{u3, u3, u3} G G G (instHDiv.{u3} G (DivInvMonoid.toDiv.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) a b)) (HDiv.hDiv.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHDiv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivInvMonoid.toDiv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (DivisionMonoid.toDivInvMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f a) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f b))
Case conversion may be inaccurate. Consider using '#align map_div map_divₓ'. -/
/-- Group homomorphisms preserve division. -/
@[simp, to_additive "Additive group homomorphisms preserve subtraction."]
theorem map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) :
    ∀ a b, f (a / b) = f a / f b :=
  map_div' _ <| map_inv f
#align map_div map_div
#align map_sub map_sub

/- warning: map_pow -> map_pow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : Monoid.{u1} G] [_inst_4 : Monoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4)] (f : F) (a : G) (n : Nat), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G _inst_3)) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H _inst_4)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4) _inst_5))) f (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G _inst_3)) a n)) (HPow.hPow.{u2, 0, u2} H Nat H (instHPow.{u2, 0} H Nat (Monoid.Pow.{u2} H _inst_4)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G _inst_3)) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H _inst_4)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4) _inst_5))) f a) n)
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : Monoid.{u3} G] [_inst_4 : Monoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4)] (f : F) (a : G) (n : Nat), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HPow.hPow.{u3, 0, u3} G Nat G (instHPow.{u3, 0} G Nat (Monoid.Pow.{u3} G _inst_3)) a n)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G _inst_3)) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H _inst_4)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4) _inst_5)) f (HPow.hPow.{u3, 0, u3} G Nat G (instHPow.{u3, 0} G Nat (Monoid.Pow.{u3} G _inst_3)) a n)) (HPow.hPow.{u2, 0, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHPow.{u2, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) Nat (Monoid.Pow.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G _inst_3)) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H _inst_4)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G _inst_3) (Monoid.toMulOneClass.{u2} H _inst_4) _inst_5)) f a) n)
Case conversion may be inaccurate. Consider using '#align map_pow map_powₓ'. -/
-- to_additive puts the arguments in the wrong order, so generate an auxiliary lemma, then
-- swap its arguments.
@[to_additive map_nsmul.aux, simp]
theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow]
#align map_pow map_pow
#align map_nsmul map_nsmul

/- warning: map_nsmul -> map_nsmul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : AddMonoid.{u1} G] [_inst_4 : AddMonoid.{u2} H] [_inst_5 : AddMonoidHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4)] (f : F) (n : Nat) (a : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (AddHomClass.toFunLike.{u3, u1, u2} F G H (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G _inst_3)) (AddZeroClass.toHasAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H _inst_4)) (AddMonoidHomClass.toAddHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4) _inst_5))) f (SMul.smul.{0, u1} Nat G (AddMonoid.SMul.{u1} G _inst_3) n a)) (SMul.smul.{0, u2} Nat H (AddMonoid.SMul.{u2} H _inst_4) n (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (AddHomClass.toFunLike.{u3, u1, u2} F G H (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G _inst_3)) (AddZeroClass.toHasAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H _inst_4)) (AddMonoidHomClass.toAddHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4) _inst_5))) f a))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : AddMonoid.{u3} G] [_inst_4 : AddMonoid.{u2} H] [_inst_5 : AddMonoidHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4)] (f : F) (n : Nat) (a : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HSMul.hSMul.{0, u3, u3} Nat G G (instHSMul.{0, u3} Nat G (AddMonoid.SMul.{u3} G _inst_3)) n a)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (AddHomClass.toFunLike.{u1, u3, u2} F G H (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G _inst_3)) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H _inst_4)) (AddMonoidHomClass.toAddHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4) _inst_5)) f (HSMul.hSMul.{0, u3, u3} Nat G G (instHSMul.{0, u3} Nat G (AddMonoid.SMul.{u3} G _inst_3)) n a)) (HSMul.hSMul.{0, u2, u2} Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHSMul.{0, u2} Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (AddMonoid.SMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)) n (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (AddHomClass.toFunLike.{u1, u3, u2} F G H (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G _inst_3)) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H _inst_4)) (AddMonoidHomClass.toAddHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G _inst_3) (AddMonoid.toAddZeroClass.{u2} H _inst_4) _inst_5)) f a))
Case conversion may be inaccurate. Consider using '#align map_nsmul map_nsmulₓ'. -/
@[simp]
theorem map_nsmul [AddMonoid G] [AddMonoid H] [AddMonoidHomClass F G H] (f : F) (n : ℕ) (a : G) :
    f (n • a) = n • f a :=
  map_nsmul.aux f a n
#align map_nsmul map_nsmul

attribute [to_additive_reorder 8, to_additive] map_pow

/- warning: map_zpow' -> map_zpow' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : DivInvMonoid.{u1} G] [_inst_4 : DivInvMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))] (f : F), (forall (x : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_3) x)) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H _inst_4) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f x))) -> (forall (a : G) (n : Int), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G _inst_3)) a n)) (HPow.hPow.{u2, 0, u2} H Int H (instHPow.{u2, 0} H Int (DivInvMonoid.Pow.{u2} H _inst_4)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5))) f a) n))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : DivInvMonoid.{u3} G] [_inst_4 : DivInvMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))] (f : F), (forall (x : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (Inv.inv.{u3} G (DivInvMonoid.toInv.{u3} G _inst_3) x)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f (Inv.inv.{u3} G (DivInvMonoid.toInv.{u3} G _inst_3) x)) (Inv.inv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) x) (DivInvMonoid.toInv.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) x) _inst_4) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f x))) -> (forall (a : G) (n : Int), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HPow.hPow.{u3, 0, u3} G Int G (instHPow.{u3, 0} G Int (DivInvMonoid.Pow.{u3} G _inst_3)) a n)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f (HPow.hPow.{u3, 0, u3} G Int G (instHPow.{u3, 0} G Int (DivInvMonoid.Pow.{u3} G _inst_3)) a n)) (HPow.hPow.{u2, 0, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (instHPow.{u2, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) Int (DivInvMonoid.Pow.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G _inst_3)) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H _inst_4)) _inst_5)) f a) n))
Case conversion may be inaccurate. Consider using '#align map_zpow' map_zpow'ₓ'. -/
@[to_additive]
theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H] (f : F)
    (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by rw [zpow_ofNat, map_pow, zpow_ofNat]
  | -[n+1] => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc]
#align map_zpow' map_zpow'
#align map_zsmul' map_zsmul'

/- warning: map_zpow -> map_zpow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : Group.{u1} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (g : G) (n : Int), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) g n)) (HPow.hPow.{u2, 0, u2} H Int H (instHPow.{u2, 0} H Int (DivInvMonoid.Pow.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u3, u1, u2} F G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5))) f g) n)
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : Group.{u3} G] [_inst_4 : DivisionMonoid.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))] (f : F) (g : G) (n : Int), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HPow.hPow.{u3, 0, u3} G Int G (instHPow.{u3, 0} G Int (DivInvMonoid.Pow.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) g n)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f (HPow.hPow.{u3, 0, u3} G Int G (instHPow.{u3, 0} G Int (DivInvMonoid.Pow.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) g n)) (HPow.hPow.{u2, 0, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) (instHPow.{u2, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) Int (DivInvMonoid.Pow.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) (DivisionMonoid.toDivInvMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) _inst_4))) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_4))) _inst_5)) f g) n)
Case conversion may be inaccurate. Consider using '#align map_zpow map_zpowₓ'. -/
-- to_additive puts the arguments in the wrong order, so generate an auxiliary lemma, then
-- swap its arguments.
/-- Group homomorphisms preserve integer power. -/
@[to_additive map_zsmul.aux, simp]
theorem map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f : F) (g : G) (n : ℤ) :
    f (g ^ n) = f g ^ n :=
  map_zpow' f (map_inv f) g n
#align map_zpow map_zpow
#align map_zsmul map_zsmul

/- warning: map_zsmul -> map_zsmul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} {F : Type.{u3}} [_inst_3 : AddGroup.{u1} G] [_inst_4 : SubtractionMonoid.{u2} H] [_inst_5 : AddMonoidHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))] (f : F) (n : Int) (g : G), Eq.{succ u2} H (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (AddHomClass.toFunLike.{u3, u1, u2} F G H (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3)))) (AddZeroClass.toHasAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))) (AddMonoidHomClass.toAddHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4))) _inst_5))) f (SMul.smul.{0, u1} Int G (SubNegMonoid.SMulInt.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3)) n g)) (SMul.smul.{0, u2} Int H (SubNegMonoid.SMulInt.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)) n (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F G (fun (_x : G) => H) (AddHomClass.toFunLike.{u3, u1, u2} F G H (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3)))) (AddZeroClass.toHasAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))) (AddMonoidHomClass.toAddHomClass.{u3, u1, u2} F G H (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4))) _inst_5))) f g))
but is expected to have type
  forall {G : Type.{u3}} {H : Type.{u2}} {F : Type.{u1}} [_inst_3 : AddGroup.{u3} G] [_inst_4 : SubtractionMonoid.{u2} H] [_inst_5 : AddMonoidHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))] (f : F) (n : Int) (g : G), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) (HSMul.hSMul.{0, u3, u3} Int G G (instHSMul.{0, u3} Int G (SubNegMonoid.SMulInt.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3))) n g)) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (AddHomClass.toFunLike.{u1, u3, u2} F G H (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3)))) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4))) _inst_5)) f (HSMul.hSMul.{0, u3, u3} Int G G (instHSMul.{0, u3} Int G (SubNegMonoid.SMulInt.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3))) n g)) (HSMul.hSMul.{0, u2, u2} Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) (instHSMul.{0, u2} Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) (SubNegMonoid.SMulInt.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) (SubtractionMonoid.toSubNegMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) g) _inst_4))) n (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (AddHomClass.toFunLike.{u1, u3, u2} F G H (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3)))) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4)))) (AddMonoidHomClass.toAddHomClass.{u1, u3, u2} F G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G _inst_3))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (SubtractionMonoid.toSubNegMonoid.{u2} H _inst_4))) _inst_5)) f g))
Case conversion may be inaccurate. Consider using '#align map_zsmul map_zsmulₓ'. -/
/-- Additive group homomorphisms preserve integer scaling. -/
theorem map_zsmul [AddGroup G] [SubtractionMonoid H] [AddMonoidHomClass F G H] (f : F) (n : ℤ)
    (g : G) : f (n • g) = n • f g :=
  map_zsmul.aux f g n
#align map_zsmul map_zsmul

attribute [to_additive_reorder 8, to_additive] map_zpow

end mul_one

section MulZeroOne

variable [MulZeroOneClass M] [MulZeroOneClass N]

#print MonoidWithZeroHom /-
/-- `M →*₀ N` is the type of functions `M → N` that preserve
the `monoid_with_zero` structure.

`monoid_with_zero_hom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : M →*₀ N)`,
you should parametrize over `(F : Type*) [monoid_with_zero_hom_class F M N] (f : F)`.

When you extend this structure, make sure to extend `monoid_with_zero_hom_class`.
-/
structure MonoidWithZeroHom (M : Type _) (N : Type _) [MulZeroOneClass M]
  [MulZeroOneClass N] extends ZeroHom M N, MonoidHom M N
#align monoid_with_zero_hom MonoidWithZeroHom
-/

attribute [nolint doc_blame] MonoidWithZeroHom.toMonoidHom

attribute [nolint doc_blame] MonoidWithZeroHom.toZeroHom

-- mathport name: «expr →*₀ »
infixr:25 " →*₀ " => MonoidWithZeroHom

#print MonoidWithZeroHomClass /-
/-- `monoid_with_zero_hom_class F M N` states that `F` is a type of
`monoid_with_zero`-preserving homomorphisms.

You should also extend this typeclass when you extend `monoid_with_zero_hom`.
-/
class MonoidWithZeroHomClass (F : Type _) (M N : outParam <| Type _) [MulZeroOneClass M]
  [MulZeroOneClass N] extends MonoidHomClass F M N, ZeroHomClass F M N
#align monoid_with_zero_hom_class MonoidWithZeroHomClass
-/

#print MonoidWithZeroHom.monoidWithZeroHomClass /-
instance MonoidWithZeroHom.monoidWithZeroHomClass : MonoidWithZeroHomClass (M →*₀ N) M N
    where
  coe := MonoidWithZeroHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero := MonoidWithZeroHom.map_zero'
#align monoid_with_zero_hom.monoid_with_zero_hom_class MonoidWithZeroHom.monoidWithZeroHomClass
-/

instance [MonoidWithZeroHomClass F M N] : CoeTC F (M →*₀ N) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f }⟩

/- warning: monoid_with_zero_hom.coe_coe -> MonoidWithZeroHom.coe_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MonoidWithZeroHomClass.{u3, u1, u2} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u2} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) M (fun (_x : M) => N) (MulHomClass.toFunLike.{max u2 u1, u1, u2} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) M N (MulOneClass.toHasMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u1, u2} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u1, u2} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u2} M N _inst_1 _inst_2))))) ((fun (a : Type.{u3}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{succ u3, max (succ u2) (succ u1)} a b] => self.0) F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (HasLiftT.mk.{succ u3, max (succ u2) (succ u1)} F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (CoeTCₓ.coe.{succ u3, max (succ u2) (succ u1)} F (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.hasCoeT.{u1, u2, u3} M N F _inst_1 _inst_2 _inst_3))) f)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u1, u2} F M N _inst_1 _inst_2 _inst_3)))) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {F : Type.{u3}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] [_inst_3 : MonoidWithZeroHomClass.{u3, u2, u1} F M N _inst_1 _inst_2] (f : F), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) (MonoidWithZeroHomClass.toMonoidWithZeroHom.{u2, u1, u3} M N F _inst_1 _inst_2 _inst_3 f)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3))) f)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.coe_coe MonoidWithZeroHom.coe_coeₓ'. -/
@[simp]
theorem MonoidWithZeroHom.coe_coe [MonoidWithZeroHomClass F M N] (f : F) :
    ((f : M →*₀ N) : M → N) = f :=
  rfl
#align monoid_with_zero_hom.coe_coe MonoidWithZeroHom.coe_coe

end MulZeroOne

-- completely uninteresting lemmas about coercion to function, that all homs need
section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/


/- warning: monoid_hom.has_coe_to_one_hom -> MonoidHom.coeToOneHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N mM mN) (OneHom.{u1, u2} M N (MulOneClass.toHasOne.{u1} M mM) (MulOneClass.toHasOne.{u2} N mN))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N mM mN) (OneHom.{u1, u2} M N (MulOneClass.toOne.{u1} M mM) (MulOneClass.toOne.{u2} N mN))
Case conversion may be inaccurate. Consider using '#align monoid_hom.has_coe_to_one_hom MonoidHom.coeToOneHomₓ'. -/
@[to_additive]
instance MonoidHom.coeToOneHom {mM : MulOneClass M} {mN : MulOneClass N} :
    Coe (M →* N) (OneHom M N) :=
  ⟨MonoidHom.toOneHom⟩
#align monoid_hom.has_coe_to_one_hom MonoidHom.coeToOneHom
#align add_monoid_hom.has_coe_to_zero_hom AddMonoidHom.coeToZeroHom

/- warning: monoid_hom.has_coe_to_mul_hom -> MonoidHom.coeToMulHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N mM mN) (MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M mM) (MulOneClass.toHasMul.{u2} N mN))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N mM mN) (MulHom.{u1, u2} M N (MulOneClass.toMul.{u1} M mM) (MulOneClass.toMul.{u2} N mN))
Case conversion may be inaccurate. Consider using '#align monoid_hom.has_coe_to_mul_hom MonoidHom.coeToMulHomₓ'. -/
@[to_additive]
instance MonoidHom.coeToMulHom {mM : MulOneClass M} {mN : MulOneClass N} : Coe (M →* N) (M →ₙ* N) :=
  ⟨MonoidHom.toMulHom⟩
#align monoid_hom.has_coe_to_mul_hom MonoidHom.coeToMulHom
#align add_monoid_hom.has_coe_to_add_hom AddMonoidHom.coeToAddHom

#print MonoidWithZeroHom.coeToMonoidHom /-
instance MonoidWithZeroHom.coeToMonoidHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} :
    Coe (M →*₀ N) (M →* N) :=
  ⟨MonoidWithZeroHom.toMonoidHom⟩
#align monoid_with_zero_hom.has_coe_to_monoid_hom MonoidWithZeroHom.coeToMonoidHom
-/

/- warning: monoid_with_zero_hom.has_coe_to_zero_hom -> MonoidWithZeroHom.coeToZeroHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulZeroOneClass.{u1} M} {mN : MulZeroOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N mM mN) (ZeroHom.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M mM)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N mN)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulZeroOneClass.{u1} M} {mN : MulZeroOneClass.{u2} N}, Coe.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N mM mN) (ZeroHom.{u1, u2} M N (MulZeroOneClass.toZero.{u1} M mM) (MulZeroOneClass.toZero.{u2} N mN))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.has_coe_to_zero_hom MonoidWithZeroHom.coeToZeroHomₓ'. -/
instance MonoidWithZeroHom.coeToZeroHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} :
    Coe (M →*₀ N) (ZeroHom M N) :=
  ⟨MonoidWithZeroHom.toZeroHom⟩
#align monoid_with_zero_hom.has_coe_to_zero_hom MonoidWithZeroHom.coeToZeroHom

/-! The simp-normal form of morphism coercion is `f.to_..._hom`. This choice is primarily because
this is the way things were before the above coercions were introduced. Bundled morphisms defined
elsewhere in Mathlib may choose `↑f` as their simp-normal form instead. -/


@[simp, to_additive]
theorem MonoidHom.coe_eq_toOneHom {mM : MulOneClass M} {mN : MulOneClass N} (f : M →* N) :
    (f : OneHom M N) = f.toOneHom :=
  rfl
#align monoid_hom.coe_eq_to_one_hom MonoidHom.coe_eq_toOneHom
#align add_monoid_hom.coe_eq_to_zero_hom AddMonoidHom.coe_eq_to_zero_hom

@[simp, to_additive]
theorem MonoidHom.coe_eq_toMulHom {mM : MulOneClass M} {mN : MulOneClass N} (f : M →* N) :
    (f : M →ₙ* N) = f.toMulHom :=
  rfl
#align monoid_hom.coe_eq_to_mul_hom MonoidHom.coe_eq_toMulHom
#align add_monoid_hom.coe_eq_to_add_hom AddMonoidHom.coe_eq_to_add_hom

@[simp]
theorem MonoidWithZeroHom.coe_eq_toMonoidHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N}
    (f : M →*₀ N) : (f : M →* N) = f.toMonoidHom :=
  rfl
#align monoid_with_zero_hom.coe_eq_to_monoid_hom MonoidWithZeroHom.coe_eq_toMonoidHom

@[simp]
theorem MonoidWithZeroHom.coe_eq_toZeroHom {mM : MulZeroOneClass M} {mN : MulZeroOneClass N}
    (f : M →*₀ N) : (f : ZeroHom M N) = f.toZeroHom :=
  rfl
#align monoid_with_zero_hom.coe_eq_to_zero_hom MonoidWithZeroHom.coe_eq_toZeroHom

-- Fallback `has_coe_to_fun` instances to help the elaborator
@[to_additive]
instance {mM : One M} {mN : One N} : CoeFun (OneHom M N) fun _ => M → N :=
  ⟨OneHom.toFun⟩

@[to_additive]
instance {mM : Mul M} {mN : Mul N} : CoeFun (M →ₙ* N) fun _ => M → N :=
  ⟨MulHom.toFun⟩

@[to_additive]
instance {mM : MulOneClass M} {mN : MulOneClass N} : CoeFun (M →* N) fun _ => M → N :=
  ⟨MonoidHom.toFun⟩

instance {mM : MulZeroOneClass M} {mN : MulZeroOneClass N} : CoeFun (M →*₀ N) fun _ => M → N :=
  ⟨MonoidWithZeroHom.toFun⟩

-- these must come after the coe_to_fun definitions
initialize_simps_projections ZeroHom (toFun → apply)

initialize_simps_projections AddHom (toFun → apply)

initialize_simps_projections AddMonoidHom (toFun → apply)

initialize_simps_projections OneHom (toFun → apply)

initialize_simps_projections MulHom (toFun → apply)

initialize_simps_projections MonoidHom (toFun → apply)

initialize_simps_projections MonoidWithZeroHom (toFun → apply)

/- warning: one_hom.to_fun_eq_coe -> OneHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (M -> N) (OneHom.toFun.{u1, u2} M N _inst_1 _inst_2 f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (M -> N) (OneHom.toFun.{u2, u1} M N _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align one_hom.to_fun_eq_coe OneHom.toFun_eq_coeₓ'. -/
@[simp, to_additive]
theorem OneHom.toFun_eq_coe [One M] [One N] (f : OneHom M N) : f.toFun = f :=
  rfl
#align one_hom.to_fun_eq_coe OneHom.toFun_eq_coe
#align zero_hom.to_fun_eq_coe ZeroHom.toFun_eq_coe

/- warning: mul_hom.to_fun_eq_coe -> MulHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (M -> N) (MulHom.toFun.{u1, u2} M N _inst_1 _inst_2 f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (M -> N) (MulHom.toFun.{u2, u1} M N _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align mul_hom.to_fun_eq_coe MulHom.toFun_eq_coeₓ'. -/
@[simp, to_additive]
theorem MulHom.toFun_eq_coe [Mul M] [Mul N] (f : M →ₙ* N) : f.toFun = f :=
  rfl
#align mul_hom.to_fun_eq_coe MulHom.toFun_eq_coe
#align add_hom.to_fun_eq_coe AddHom.toFun_eq_coe

/- warning: monoid_hom.to_fun_eq_coe -> MonoidHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (M -> N) (MonoidHom.toFun.{u1, u2} M N _inst_1 _inst_2 f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (M -> N) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (MonoidHom.toOneHom.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_fun_eq_coe MonoidHom.toFun_eq_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.toFun_eq_coe [MulOneClass M] [MulOneClass N] (f : M →* N) : f.toFun = f :=
  rfl
#align monoid_hom.to_fun_eq_coe MonoidHom.toFun_eq_coe
#align add_monoid_hom.to_fun_eq_coe AddMonoidHom.toFun_eq_coe

@[simp]
theorem MonoidWithZeroHom.toFun_eq_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f.toFun = f :=
  rfl
#align monoid_with_zero_hom.to_fun_eq_coe MonoidWithZeroHom.toFun_eq_coe

/- warning: one_hom.coe_mk -> OneHom.coe_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : M -> N) (h1 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))), Eq.{max (succ u1) (succ u2)} ((fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.mk.{u1, u2} M N _inst_1 _inst_2 f h1)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (OneHom.mk.{u1, u2} M N _inst_1 _inst_2 f h1)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : M -> N) (h1 : Eq.{succ u1} N (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N _inst_2))), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) (OneHom.mk.{u2, u1} M N _inst_1 _inst_2 f h1)) f
Case conversion may be inaccurate. Consider using '#align one_hom.coe_mk OneHom.coe_mkₓ'. -/
@[simp, to_additive]
theorem OneHom.coe_mk [One M] [One N] (f : M → N) (h1) : (OneHom.mk f h1 : M → N) = f :=
  rfl
#align one_hom.coe_mk OneHom.coe_mk
#align zero_hom.coe_mk ZeroHom.coe_mk

/- warning: mul_hom.coe_mk -> MulHom.coe_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : M -> N) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (f x) (f y))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.mk.{u1, u2} M N _inst_1 _inst_2 f hmul)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (MulHom.mk.{u1, u2} M N _inst_1 _inst_2 f hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : M -> N) (hmul : forall (x : M) (y : M), Eq.{succ u1} N (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (f x) (f y))), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) (MulHom.mk.{u2, u1} M N _inst_1 _inst_2 f hmul)) f
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_mk MulHom.coe_mkₓ'. -/
@[simp, to_additive]
theorem MulHom.coe_mk [Mul M] [Mul N] (f : M → N) (hmul) : (MulHom.mk f hmul : M → N) = f :=
  rfl
#align mul_hom.coe_mk MulHom.coe_mk
#align add_hom.coe_mk AddHom.coe_mk

/- warning: monoid_hom.coe_mk -> MonoidHom.coe_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : M -> N) (h1 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2)) (f x) (f y))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.mk.{u1, u2} M N _inst_1 _inst_2 f h1 hmul)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.mk.{u1, u2} M N _inst_1 _inst_2 f h1 hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) (h1 : forall (x : M) (y : M), Eq.{succ u1} N (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N _inst_2)) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) f x) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) f y))), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) (MonoidHom.mk.{u2, u1} M N _inst_1 _inst_2 f h1)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) a) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (OneHom.oneHomClass.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_mk MonoidHom.coe_mkₓ'. -/
@[simp, to_additive]
theorem MonoidHom.coe_mk [MulOneClass M] [MulOneClass N] (f : M → N) (h1 hmul) :
    (MonoidHom.mk f h1 hmul : M → N) = f :=
  rfl
#align monoid_hom.coe_mk MonoidHom.coe_mk
#align add_monoid_hom.coe_mk AddMonoidHom.coe_mk

/- warning: monoid_with_zero_hom.coe_mk -> MonoidWithZeroHom.coe_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : M -> N) (h0 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2)))))) (h1 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)))))) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2))) (f x) (f y))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.mk.{u1, u2} M N _inst_1 _inst_2 f h0 h1 hmul)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.mk.{u1, u2} M N _inst_1 _inst_2 f h0 h1 hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) (h0 : Eq.{succ u1} N (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2))))) (h1 : forall (x : M) (y : M), Eq.{succ u1} N (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2))) (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) f x) (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) f y))), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u1 u2, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) (MonoidWithZeroHom.mk.{u2, u1} M N _inst_1 _inst_2 f h0 h1)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => N) a) (ZeroHomClass.toFunLike.{max u2 u1, u2, u1} (ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHom.zeroHomClass.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.coe_mk MonoidWithZeroHom.coe_mkₓ'. -/
@[simp]
theorem MonoidWithZeroHom.coe_mk [MulZeroOneClass M] [MulZeroOneClass N] (f : M → N) (h0 h1 hmul) :
    (MonoidWithZeroHom.mk f h0 h1 hmul : M → N) = f :=
  rfl
#align monoid_with_zero_hom.coe_mk MonoidWithZeroHom.coe_mk

/- warning: monoid_hom.to_one_hom_coe -> MonoidHom.toOneHom_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : OneHom.{u1, u2} M N (MulOneClass.toHasOne.{u1} M _inst_1) (MulOneClass.toHasOne.{u2} N _inst_2)) => M -> N) (MonoidHom.toOneHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N (MulOneClass.toHasOne.{u1} M _inst_1) (MulOneClass.toHasOne.{u2} N _inst_2)) (fun (_x : OneHom.{u1, u2} M N (MulOneClass.toHasOne.{u1} M _inst_1) (MulOneClass.toHasOne.{u2} N _inst_2)) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasOne.{u1} M _inst_1) (MulOneClass.toHasOne.{u2} N _inst_2)) (MonoidHom.toOneHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (OneHom.oneHomClass.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2))) (MonoidHom.toOneHom.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_one_hom_coe MonoidHom.toOneHom_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.toOneHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (f.toOneHom : M → N) = f :=
  rfl
#align monoid_hom.to_one_hom_coe MonoidHom.toOneHom_coe
#align add_monoid_hom.to_zero_hom_coe AddMonoidHom.toZeroHom_coe

/- warning: monoid_hom.to_mul_hom_coe -> MonoidHom.toMulHom_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) => M -> N) (MonoidHom.toMulHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (fun (_x : MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (MonoidHom.toMulHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (M -> N) (MulHom.toFun.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHom.toMulHom.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_mul_hom_coe MonoidHom.toMulHom_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.toMulHom_coe [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (f.toMulHom : M → N) = f :=
  rfl
#align monoid_hom.to_mul_hom_coe MonoidHom.toMulHom_coe
#align add_monoid_hom.to_add_hom_coe AddMonoidHom.toAddHom_coe

/- warning: monoid_with_zero_hom.to_zero_hom_coe -> MonoidWithZeroHom.toZeroHom_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : ZeroHom.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) => M -> N) (MonoidWithZeroHom.toZeroHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (ZeroHom.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) (fun (_x : ZeroHom.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) => M -> N) (ZeroHom.hasCoeToFun.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) (MonoidWithZeroHom.toZeroHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : M) => N) _x) (ZeroHomClass.toFunLike.{max u2 u1, u2, u1} (ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHom.zeroHomClass.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2))) (MonoidWithZeroHom.toZeroHom.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.to_zero_hom_coe MonoidWithZeroHom.toZeroHom_coeₓ'. -/
@[simp]
theorem MonoidWithZeroHom.toZeroHom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    (f.toZeroHom : M → N) = f :=
  rfl
#align monoid_with_zero_hom.to_zero_hom_coe MonoidWithZeroHom.toZeroHom_coe

/- warning: monoid_with_zero_hom.to_monoid_hom_coe -> MonoidWithZeroHom.toMonoidHom_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidWithZeroHom.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidWithZeroHom.toMonoidHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (M -> N) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toOne.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHom.toOneHom.{u2, u1} M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHom.toMonoidHom.{u2, u1} M N _inst_1 _inst_2 f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.to_monoid_hom_coe MonoidWithZeroHom.toMonoidHom_coeₓ'. -/
@[simp]
theorem MonoidWithZeroHom.toMonoidHom_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    (f.toMonoidHom : M → N) = f :=
  rfl
#align monoid_with_zero_hom.to_monoid_hom_coe MonoidWithZeroHom.toMonoidHom_coe

/- warning: one_hom.ext -> OneHom.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] {{f : OneHom.{u1, u2} M N _inst_1 _inst_2}} {{g : OneHom.{u1, u2} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x)) -> (Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] {{f : OneHom.{u2, u1} M N _inst_1 _inst_2}} {{g : OneHom.{u2, u1} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) g x)) -> (Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align one_hom.ext OneHom.extₓ'. -/
@[ext, to_additive]
theorem OneHom.ext [One M] [One N] ⦃f g : OneHom M N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align one_hom.ext OneHom.ext
#align zero_hom.ext ZeroHom.ext

/- warning: mul_hom.ext -> MulHom.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {{f : MulHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MulHom.{u1, u2} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x)) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {{f : MulHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MulHom.{u2, u1} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) g x)) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align mul_hom.ext MulHom.extₓ'. -/
@[ext, to_additive]
theorem MulHom.ext [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align mul_hom.ext MulHom.ext
#align add_hom.ext AddHom.ext

/- warning: monoid_hom.ext -> MonoidHom.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {{f : MonoidHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MonoidHom.{u1, u2} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x)) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {{f : MonoidHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MonoidHom.{u2, u1} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) g x)) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.ext MonoidHom.extₓ'. -/
@[ext, to_additive]
theorem MonoidHom.ext [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align monoid_hom.ext MonoidHom.ext
#align add_monoid_hom.ext AddMonoidHom.ext

/- warning: monoid_with_zero_hom.ext -> MonoidWithZeroHom.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] {{f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x)) -> (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] {{f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}}, (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) g x)) -> (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext MonoidWithZeroHom.extₓ'. -/
@[ext]
theorem MonoidWithZeroHom.ext [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : M →*₀ N⦄
    (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align monoid_with_zero_hom.ext MonoidWithZeroHom.ext

section Deprecated

/- warning: one_hom.congr_fun -> OneHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] {f : OneHom.{u1, u2} M N _inst_1 _inst_2} {g : OneHom.{u1, u2} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] {f : OneHom.{u2, u1} M N _inst_1 _inst_2} {g : OneHom.{u2, u1} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align one_hom.congr_fun OneHom.congr_funₓ'. -/
/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem OneHom.congr_fun [One M] [One N] {f g : OneHom M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align one_hom.congr_fun OneHom.congr_fun
#align zero_hom.congr_fun ZeroHom.congr_fun

/- warning: mul_hom.congr_fun -> MulHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2} {g : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2} {g : MulHom.{u2, u1} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align mul_hom.congr_fun MulHom.congr_funₓ'. -/
/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem MulHom.congr_fun [Mul M] [Mul N] {f g : M →ₙ* N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align mul_hom.congr_fun MulHom.congr_fun
#align add_hom.congr_fun AddHom.congr_fun

/- warning: monoid_hom.congr_fun -> MonoidHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {f : MonoidHom.{u1, u2} M N _inst_1 _inst_2} {g : MonoidHom.{u1, u2} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {f : MonoidHom.{u2, u1} M N _inst_1 _inst_2} {g : MonoidHom.{u2, u1} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.congr_fun MonoidHom.congr_funₓ'. -/
/-- Deprecated: use `fun_like.congr_fun` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_fun` instead."]
theorem MonoidHom.congr_fun [MulOneClass M] [MulOneClass N] {f g : M →* N} (h : f = g) (x : M) :
    f x = g x :=
  FunLike.congr_fun h x
#align monoid_hom.congr_fun MonoidHom.congr_fun
#align add_monoid_hom.congr_fun AddMonoidHom.congr_fun

/- warning: monoid_with_zero_hom.congr_fun -> MonoidWithZeroHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] {f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2} {g : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] {f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2} {g : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.congr_fun MonoidWithZeroHom.congr_funₓ'. -/
/-- Deprecated: use `fun_like.congr_fun` instead. -/
theorem MonoidWithZeroHom.congr_fun [MulZeroOneClass M] [MulZeroOneClass N] {f g : M →*₀ N}
    (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align monoid_with_zero_hom.congr_fun MonoidWithZeroHom.congr_fun

/- warning: one_hom.congr_arg -> OneHom.congr_arg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u1} M x y) -> (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u2} M x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f y))
Case conversion may be inaccurate. Consider using '#align one_hom.congr_arg OneHom.congr_argₓ'. -/
/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem OneHom.congr_arg [One M] [One N] (f : OneHom M N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align one_hom.congr_arg OneHom.congr_arg
#align zero_hom.congr_arg ZeroHom.congr_arg

/- warning: mul_hom.congr_arg -> MulHom.congr_arg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u1} M x y) -> (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u2} M x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f y))
Case conversion may be inaccurate. Consider using '#align mul_hom.congr_arg MulHom.congr_argₓ'. -/
/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem MulHom.congr_arg [Mul M] [Mul N] (f : M →ₙ* N) {x y : M} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align mul_hom.congr_arg MulHom.congr_arg
#align add_hom.congr_arg AddHom.congr_arg

/- warning: monoid_hom.congr_arg -> MonoidHom.congr_arg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u1} M x y) -> (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u2} M x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f y))
Case conversion may be inaccurate. Consider using '#align monoid_hom.congr_arg MonoidHom.congr_argₓ'. -/
/-- Deprecated: use `fun_like.congr_arg` instead. -/
@[to_additive "Deprecated: use `fun_like.congr_arg` instead."]
theorem MonoidHom.congr_arg [MulOneClass M] [MulOneClass N] (f : M →* N) {x y : M} (h : x = y) :
    f x = f y :=
  FunLike.congr_arg f h
#align monoid_hom.congr_arg MonoidHom.congr_arg
#align add_monoid_hom.congr_arg AddMonoidHom.congr_arg

/- warning: monoid_with_zero_hom.congr_arg -> MonoidWithZeroHom.congr_arg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u1} M x y) -> (Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : M}, (Eq.{succ u2} M x y) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f y))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.congr_arg MonoidWithZeroHom.congr_argₓ'. -/
/-- Deprecated: use `fun_like.congr_arg` instead. -/
theorem MonoidWithZeroHom.congr_arg [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) {x y : M}
    (h : x = y) : f x = f y :=
  FunLike.congr_arg f h
#align monoid_with_zero_hom.congr_arg MonoidWithZeroHom.congr_arg

/- warning: one_hom.coe_inj -> OneHom.coe_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] {{f : OneHom.{u1, u2} M N _inst_1 _inst_2}} {{g : OneHom.{u1, u2} M N _inst_1 _inst_2}}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g)) -> (Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] {{f : OneHom.{u2, u1} M N _inst_1 _inst_2}} {{g : OneHom.{u2, u1} M N _inst_1 _inst_2}}, (Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) g)) -> (Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align one_hom.coe_inj OneHom.coe_injₓ'. -/
/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
theorem OneHom.coe_inj [One M] [One N] ⦃f g : OneHom M N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h
#align one_hom.coe_inj OneHom.coe_inj
#align zero_hom.coe_inj ZeroHom.coe_inj

/- warning: mul_hom.coe_inj -> MulHom.coe_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {{f : MulHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MulHom.{u1, u2} M N _inst_1 _inst_2}}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g)) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {{f : MulHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MulHom.{u2, u1} M N _inst_1 _inst_2}}, (Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) g)) -> (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_inj MulHom.coe_injₓ'. -/
/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
theorem MulHom.coe_inj [Mul M] [Mul N] ⦃f g : M →ₙ* N⦄ (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h
#align mul_hom.coe_inj MulHom.coe_inj
#align add_hom.coe_inj AddHom.coe_inj

/- warning: monoid_hom.coe_inj -> MonoidHom.coe_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {{f : MonoidHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MonoidHom.{u1, u2} M N _inst_1 _inst_2}}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g)) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {{f : MonoidHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MonoidHom.{u2, u1} M N _inst_1 _inst_2}}, (Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) g)) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_inj MonoidHom.coe_injₓ'. -/
/-- Deprecated: use `fun_like.coe_injective` instead. -/
@[to_additive "Deprecated: use `fun_like.coe_injective` instead."]
theorem MonoidHom.coe_inj [MulOneClass M] [MulOneClass N] ⦃f g : M →* N⦄ (h : (f : M → N) = g) :
    f = g :=
  FunLike.coe_injective h
#align monoid_hom.coe_inj MonoidHom.coe_inj
#align add_monoid_hom.coe_inj AddMonoidHom.coe_inj

/- warning: monoid_with_zero_hom.coe_inj -> MonoidWithZeroHom.coe_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] {{f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}} {{g : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g)) -> (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] {{f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}} {{g : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}}, (Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) g)) -> (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.coe_inj MonoidWithZeroHom.coe_injₓ'. -/
/-- Deprecated: use `fun_like.coe_injective` instead. -/
theorem MonoidWithZeroHom.coe_inj [MulZeroOneClass M] [MulZeroOneClass N] ⦃f g : M →*₀ N⦄
    (h : (f : M → N) = g) : f = g :=
  FunLike.coe_injective h
#align monoid_with_zero_hom.coe_inj MonoidWithZeroHom.coe_inj

/- warning: one_hom.ext_iff -> OneHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] {f : OneHom.{u1, u2} M N _inst_1 _inst_2} {g : OneHom.{u1, u2} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] {f : OneHom.{u2, u1} M N _inst_1 _inst_2} {g : OneHom.{u2, u1} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align one_hom.ext_iff OneHom.ext_iffₓ'. -/
/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive "Deprecated: use `fun_like.ext_iff` instead."]
theorem OneHom.ext_iff [One M] [One N] {f g : OneHom M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align one_hom.ext_iff OneHom.ext_iff
#align zero_hom.ext_iff ZeroHom.ext_iff

/- warning: mul_hom.ext_iff -> MulHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulHom.{u1, u2} M N _inst_1 _inst_2} {g : MulHom.{u1, u2} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulHom.{u2, u1} M N _inst_1 _inst_2} {g : MulHom.{u2, u1} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align mul_hom.ext_iff MulHom.ext_iffₓ'. -/
/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive "Deprecated: use `fun_like.ext_iff` instead."]
theorem MulHom.ext_iff [Mul M] [Mul N] {f g : M →ₙ* N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_hom.ext_iff MulHom.ext_iff
#align add_hom.ext_iff AddHom.ext_iff

/- warning: monoid_hom.ext_iff -> MonoidHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] {f : MonoidHom.{u1, u2} M N _inst_1 _inst_2} {g : MonoidHom.{u1, u2} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] {f : MonoidHom.{u2, u1} M N _inst_1 _inst_2} {g : MonoidHom.{u2, u1} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.ext_iff MonoidHom.ext_iffₓ'. -/
/-- Deprecated: use `fun_like.ext_iff` instead. -/
@[to_additive "Deprecated: use `fun_like.ext_iff` instead."]
theorem MonoidHom.ext_iff [MulOneClass M] [MulOneClass N] {f g : M →* N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align monoid_hom.ext_iff MonoidHom.ext_iff
#align add_monoid_hom.ext_iff AddMonoidHom.ext_iff

/- warning: monoid_with_zero_hom.ext_iff -> MonoidWithZeroHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] {f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2} {g : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] {f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2} {g : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.ext_iff MonoidWithZeroHom.ext_iffₓ'. -/
/-- Deprecated: use `fun_like.ext_iff` instead. -/
theorem MonoidWithZeroHom.ext_iff [MulZeroOneClass M] [MulZeroOneClass N] {f g : M →*₀ N} :
    f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align monoid_with_zero_hom.ext_iff MonoidWithZeroHom.ext_iff

end Deprecated

/- warning: one_hom.mk_coe -> OneHom.mk_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2) (h1 : Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))), Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.mk.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) h1) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2) (h1 : Eq.{succ u1} N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N _inst_2))), Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) (OneHom.mk.{u2, u1} M N _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f) h1) f
Case conversion may be inaccurate. Consider using '#align one_hom.mk_coe OneHom.mk_coeₓ'. -/
@[simp, to_additive]
theorem OneHom.mk_coe [One M] [One N] (f : OneHom M N) (h1) : OneHom.mk f h1 = f :=
  OneHom.ext fun _ => rfl
#align one_hom.mk_coe OneHom.mk_coe
#align zero_hom.mk_coe ZeroHom.mk_coe

/- warning: mul_hom.mk_coe -> MulHom.mk_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.mk.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) hmul) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (hmul : forall (x : M) (y : M), Eq.{succ u1} N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f y))), Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) (MulHom.mk.{u2, u1} M N _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f) hmul) f
Case conversion may be inaccurate. Consider using '#align mul_hom.mk_coe MulHom.mk_coeₓ'. -/
@[simp, to_additive]
theorem MulHom.mk_coe [Mul M] [Mul N] (f : M →ₙ* N) (hmul) : MulHom.mk f hmul = f :=
  MulHom.ext fun _ => rfl
#align mul_hom.mk_coe MulHom.mk_coe
#align add_hom.mk_coe AddHom.mk_coe

/- warning: monoid_hom.mk_coe -> MonoidHom.mk_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (h1 : Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.mk.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) h1 hmul) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (h1 : forall (x : M) (y : M), Eq.{succ u1} N (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (OneHomClass.toOneHom.{u2, u1, max u2 u1} M N (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (MonoidHomClass.toOneHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N _inst_2)) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (OneHomClass.toOneHom.{u2, u1, max u2 u1} M N (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (MonoidHomClass.toOneHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2)) f) x) (OneHom.toFun.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (OneHomClass.toOneHom.{u2, u1, max u2 u1} M N (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (MonoidHomClass.toOneHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2)) f) y))), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.mk.{u2, u1} M N _inst_1 _inst_2 (OneHomClass.toOneHom.{u2, u1, max u2 u1} M N (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2) (MonoidHomClass.toOneHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2)) f) h1) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.mk_coe MonoidHom.mk_coeₓ'. -/
@[simp, to_additive]
theorem MonoidHom.mk_coe [MulOneClass M] [MulOneClass N] (f : M →* N) (h1 hmul) :
    MonoidHom.mk f h1 hmul = f :=
  MonoidHom.ext fun _ => rfl
#align monoid_hom.mk_coe MonoidHom.mk_coe
#align add_monoid_hom.mk_coe AddMonoidHom.mk_coe

/- warning: monoid_with_zero_hom.mk_coe -> MonoidWithZeroHom.mk_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (h0 : Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2)))))) (h1 : Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)))))) (hmul : forall (x : M) (y : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.mk.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f) h0 h1 hmul) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (h0 : Eq.{succ u1} N (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHomClass.toZeroHom.{u2, u1, max u2 u1} M N (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (MonoidWithZeroHomClass.toZeroHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (MulOneClass.toOne.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2))))) (h1 : forall (x : M) (y : M), Eq.{succ u1} N (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHomClass.toZeroHom.{u2, u1, max u2 u1} M N (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (MonoidWithZeroHomClass.toZeroHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)) f) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2))) (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHomClass.toZeroHom.{u2, u1, max u2 u1} M N (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (MonoidWithZeroHomClass.toZeroHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)) f) x) (ZeroHom.toFun.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (ZeroHomClass.toZeroHom.{u2, u1, max u2 u1} M N (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (MonoidWithZeroHomClass.toZeroHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)) f) y))), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MonoidWithZeroHom.mk.{u2, u1} M N _inst_1 _inst_2 (ZeroHomClass.toZeroHom.{u2, u1, max u2 u1} M N (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2) (MonoidWithZeroHomClass.toZeroHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)) f) h0 h1) f
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.mk_coe MonoidWithZeroHom.mk_coeₓ'. -/
@[simp]
theorem MonoidWithZeroHom.mk_coe [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N)
    (h0 h1 hmul) : MonoidWithZeroHom.mk f h0 h1 hmul = f :=
  MonoidWithZeroHom.ext fun _ => rfl
#align monoid_with_zero_hom.mk_coe MonoidWithZeroHom.mk_coe

end Coes

#print OneHom.copy /-
/-- Copy of a `one_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
      "Copy of a `zero_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def OneHom.copy {hM : One M} {hN : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    OneHom M N where
  toFun := f'
  map_one' := h.symm ▸ f.map_one'
#align one_hom.copy OneHom.copy
#align zero_hom.copy ZeroHom.copy
-/

@[simp, to_additive]
theorem OneHom.coe_copy {hM : One M} {hN : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    ⇑(f.copy f' h) = f' :=
  rfl
#align one_hom.coe_copy OneHom.coe_copy
#align zero_hom.coe_copy ZeroHom.coe_copy

@[to_additive]
theorem OneHom.coe_copy_eq {hM : One M} {hN : One N} (f : OneHom M N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  FunLike.ext' h
#align one_hom.coe_copy_eq OneHom.coe_copy_eq
#align zero_hom.coe_copy_eq ZeroHom.coe_copy_eq

#print MulHom.copy /-
/-- Copy of a `mul_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_additive
      "Copy of an `add_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def MulHom.copy {hM : Mul M} {hN : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    M →ₙ* N where
  toFun := f'
  map_mul' := h.symm ▸ f.map_mul'
#align mul_hom.copy MulHom.copy
#align add_hom.copy AddHom.copy
-/

@[simp, to_additive]
theorem MulHom.coe_copy {hM : Mul M} {hN : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    ⇑(f.copy f' h) = f' :=
  rfl
#align mul_hom.coe_copy MulHom.coe_copy
#align add_hom.coe_copy AddHom.coe_copy

@[to_additive]
theorem MulHom.coe_copy_eq {hM : Mul M} {hN : Mul N} (f : M →ₙ* N) (f' : M → N) (h : f' = f) :
    f.copy f' h = f :=
  FunLike.ext' h
#align mul_hom.coe_copy_eq MulHom.coe_copy_eq
#align add_hom.coe_copy_eq AddHom.coe_copy_eq

/- warning: monoid_hom.copy -> MonoidHom.copy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {hM : MulOneClass.{u1} M} {hN : MulOneClass.{u2} N} (f : MonoidHom.{u1, u2} M N hM hN) (f' : M -> N), (Eq.{max (succ u1) (succ u2)} (M -> N) f' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N hM hN) (fun (_x : MonoidHom.{u1, u2} M N hM hN) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N hM hN) f)) -> (MonoidHom.{u1, u2} M N hM hN)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {hM : MulOneClass.{u1} M} {hN : MulOneClass.{u2} N} (f : MonoidHom.{u1, u2} M N hM hN) (f' : M -> N), (Eq.{max (succ u1) (succ u2)} (M -> N) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} M N hM hN) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N hM hN) M N (MulOneClass.toMul.{u1} M hM) (MulOneClass.toMul.{u2} N hN) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} M N hM hN) M N hM hN (MonoidHom.monoidHomClass.{u1, u2} M N hM hN))) f)) -> (MonoidHom.{u1, u2} M N hM hN)
Case conversion may be inaccurate. Consider using '#align monoid_hom.copy MonoidHom.copyₓ'. -/
/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
@[to_additive
      "Copy of an `add_monoid_hom` with a new `to_fun` equal to the old one. Useful to fix\ndefinitional equalities."]
protected def MonoidHom.copy {hM : MulOneClass M} {hN : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : M →* N :=
  { f.toOneHom.copy f' h, f.toMulHom.copy f' h with }
#align monoid_hom.copy MonoidHom.copy
#align add_monoid_hom.copy AddMonoidHom.copy

@[simp, to_additive]
theorem MonoidHom.coe_copy {hM : MulOneClass M} {hN : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align monoid_hom.coe_copy MonoidHom.coe_copy
#align add_monoid_hom.coe_copy AddMonoidHom.coe_copy

@[to_additive]
theorem MonoidHom.copy_eq {hM : MulOneClass M} {hN : MulOneClass N} (f : M →* N) (f' : M → N)
    (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align monoid_hom.copy_eq MonoidHom.copy_eq
#align add_monoid_hom.copy_eq AddMonoidHom.copy_eq

/- warning: monoid_with_zero_hom.copy -> MonoidWithZeroHom.copy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {hM : MulZeroOneClass.{u1} M} {hN : MulZeroOneClass.{u2} N} (f : MonoidWithZeroHom.{u1, u2} M N hM hN) (f' : M -> N), (Eq.{max (succ u1) (succ u2)} (M -> N) f' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N hM hN) (fun (_x : MonoidWithZeroHom.{u1, u2} M N hM hN) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N hM hN) f)) -> (MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M hM) (MulZeroOneClass.toMulOneClass.{u2} N hN))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {hM : MulZeroOneClass.{u1} M} {hN : MulZeroOneClass.{u2} N} (f : MonoidWithZeroHom.{u1, u2} M N hM hN) (f' : M -> N), (Eq.{max (succ u1) (succ u2)} (M -> N) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidWithZeroHom.{u1, u2} M N hM hN) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} M N hM hN) M N (MulOneClass.toMul.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M hM)) (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N hN)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} M N hM hN) M N (MulZeroOneClass.toMulOneClass.{u1} M hM) (MulZeroOneClass.toMulOneClass.{u2} N hN) (MonoidWithZeroHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (MonoidWithZeroHom.{u1, u2} M N hM hN) M N hM hN (MonoidWithZeroHom.monoidWithZeroHomClass.{u1, u2} M N hM hN)))) f)) -> (MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M hM) (MulZeroOneClass.toMulOneClass.{u2} N hN))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.copy MonoidWithZeroHom.copyₓ'. -/
/-- Copy of a `monoid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def MonoidWithZeroHom.copy {hM : MulZeroOneClass M} {hN : MulZeroOneClass N} (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : M →* N :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }
#align monoid_with_zero_hom.copy MonoidWithZeroHom.copy

@[simp]
theorem MonoidWithZeroHom.coe_copy {hM : MulZeroOneClass M} {hN : MulZeroOneClass N} (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align monoid_with_zero_hom.coe_copy MonoidWithZeroHom.coe_copy

theorem MonoidWithZeroHom.copy_eq {hM : MulZeroOneClass M} {hN : MulZeroOneClass N} (f : M →*₀ N)
    (f' : M → N) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align monoid_with_zero_hom.copy_eq MonoidWithZeroHom.copy_eq

/- warning: one_hom.map_one -> OneHom.map_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_1)))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align one_hom.map_one OneHom.map_oneₓ'. -/
@[to_additive]
protected theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 :=
  f.map_one'
#align one_hom.map_one OneHom.map_one
#align zero_hom.map_zero ZeroHom.map_zero

/- warning: monoid_hom.map_one -> MonoidHom.map_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_1)))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_one MonoidHom.map_oneₓ'. -/
/-- If `f` is a monoid homomorphism then `f 1 = 1`. -/
@[to_additive]
protected theorem MonoidHom.map_one [MulOneClass M] [MulOneClass N] (f : M →* N) : f 1 = 1 :=
  f.map_one'
#align monoid_hom.map_one MonoidHom.map_one
#align add_monoid_hom.map_zero AddMonoidHom.map_zero

/- warning: monoid_with_zero_hom.map_one -> MonoidWithZeroHom.map_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) (MulZeroOneClass.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))) _inst_2))))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.map_one MonoidWithZeroHom.map_oneₓ'. -/
protected theorem MonoidWithZeroHom.map_one [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f 1 = 1 :=
  f.map_one'
#align monoid_with_zero_hom.map_one MonoidWithZeroHom.map_one

/-- If `f` is an additive monoid homomorphism then `f 0 = 0`. -/
add_decl_doc AddMonoidHom.map_zero

/- warning: monoid_with_zero_hom.map_zero -> MonoidWithZeroHom.map_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (MulZeroOneClass.toZero.{u2} M _inst_1)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (MulZeroOneClass.toZero.{u2} M _inst_1)))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (MulZeroOneClass.toZero.{u2} M _inst_1)))) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (MulZeroOneClass.toZero.{u2} M _inst_1)))) (MulZeroOneClass.toZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (MulZeroOneClass.toZero.{u2} M _inst_1)))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.map_zero MonoidWithZeroHom.map_zeroₓ'. -/
protected theorem MonoidWithZeroHom.map_zero [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f 0 = 0 :=
  f.map_zero'
#align monoid_with_zero_hom.map_zero MonoidWithZeroHom.map_zero

/- warning: mul_hom.map_mul -> MulHom.map_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) a b)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) a b)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) f b))
Case conversion may be inaccurate. Consider using '#align mul_hom.map_mul MulHom.map_mulₓ'. -/
@[to_additive]
protected theorem MulHom.map_mul [Mul M] [Mul N] (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b
#align mul_hom.map_mul MulHom.map_mul
#align add_hom.map_add AddHom.map_add

/- warning: monoid_hom.map_mul -> MonoidHom.map_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) f b))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_mul MonoidHom.map_mulₓ'. -/
/-- If `f` is a monoid homomorphism then `f (a * b) = f a * f b`. -/
@[to_additive]
protected theorem MonoidHom.map_mul [MulOneClass M] [MulOneClass N] (f : M →* N) (a b : M) :
    f (a * b) = f a * f b :=
  f.map_mul' a b
#align monoid_hom.map_mul MonoidHom.map_mul
#align add_monoid_hom.map_add AddMonoidHom.map_add

/- warning: monoid_with_zero_hom.map_mul -> MonoidWithZeroHom.map_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1))) a b)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulZeroClass.toHasMul.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (a : M) (b : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toMul.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1))) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toMul.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1))) a b)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulZeroClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulZeroOneClass.toMulZeroClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} M N _inst_1 _inst_2)))) f b))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.map_mul MonoidWithZeroHom.map_mulₓ'. -/
protected theorem MonoidWithZeroHom.map_mul [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N)
    (a b : M) : f (a * b) = f a * f b :=
  f.map_mul' a b
#align monoid_with_zero_hom.map_mul MonoidWithZeroHom.map_mul

/-- If `f` is an additive monoid homomorphism then `f (a + b) = f a + f b`. -/
add_decl_doc AddMonoidHom.map_add

namespace MonoidHom

variable {mM : MulOneClass M} {mN : MulOneClass N} [MonoidHomClass F M N]

include mM mN

/- warning: monoid_hom.map_exists_right_inv -> MonoidHom.map_exists_right_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N} [_inst_1 : MonoidHomClass.{u3, u1, u2} F M N mM mN] (f : F) {x : M}, (Exists.{succ u1} M (fun (y : M) => Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M mM)) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M mM)))))) -> (Exists.{succ u2} N (fun (y : N) => Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N mN)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M mM) (MulOneClass.toHasMul.{u2} N mN) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N mM mN _inst_1))) f x) y) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N mN))))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {F : Type.{u1}} {mM : MulOneClass.{u3} M} {mN : MulOneClass.{u2} N} [_inst_1 : MonoidHomClass.{u1, u3, u2} F M N mM mN] (f : F) {x : M}, (Exists.{succ u3} M (fun (y : M) => Eq.{succ u3} M (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulOneClass.toMul.{u3} M mM)) x y) (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M (MulOneClass.toOne.{u3} M mM))))) -> (Exists.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (fun (y : (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) => Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN)) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M mM) (MulOneClass.toMul.{u2} N mN) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N mM mN _inst_1)) f x) y) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_exists_right_inv MonoidHom.map_exists_right_invₓ'. -/
/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a right inverse,
then `f x` has a right inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na right inverse, then `f x` has a right inverse too."]
theorem map_exists_right_inv (f : F) {x : M} (hx : ∃ y, x * y = 1) : ∃ y, f x * y = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩
#align monoid_hom.map_exists_right_inv MonoidHom.map_exists_right_inv
#align add_monoid_hom.map_exists_right_neg AddMonoidHom.map_exists_right_neg

/- warning: monoid_hom.map_exists_left_inv -> MonoidHom.map_exists_left_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} {mM : MulOneClass.{u1} M} {mN : MulOneClass.{u2} N} [_inst_1 : MonoidHomClass.{u3, u1, u2} F M N mM mN] (f : F) {x : M}, (Exists.{succ u1} M (fun (y : M) => Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M mM)) y x) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M mM)))))) -> (Exists.{succ u2} N (fun (y : N) => Eq.{succ u2} N (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N mN)) y (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M mM) (MulOneClass.toHasMul.{u2} N mN) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N mM mN _inst_1))) f x)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N mN))))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {F : Type.{u1}} {mM : MulOneClass.{u3} M} {mN : MulOneClass.{u2} N} [_inst_1 : MonoidHomClass.{u1, u3, u2} F M N mM mN] (f : F) {x : M}, (Exists.{succ u3} M (fun (y : M) => Eq.{succ u3} M (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulOneClass.toMul.{u3} M mM)) y x) (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M (MulOneClass.toOne.{u3} M mM))))) -> (Exists.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (fun (y : (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) => Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN)) y (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M mM) (MulOneClass.toMul.{u2} N mN) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F M N mM mN _inst_1)) f x)) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_exists_left_inv MonoidHom.map_exists_left_invₓ'. -/
/-- Given a monoid homomorphism `f : M →* N` and an element `x : M`, if `x` has a left inverse,
then `f x` has a left inverse too. For elements invertible on both sides see `is_unit.map`. -/
@[to_additive
      "Given an add_monoid homomorphism `f : M →+ N` and an element `x : M`, if `x` has\na left inverse, then `f x` has a left inverse too. For elements invertible on both sides see\n`is_add_unit.map`."]
theorem map_exists_left_inv (f : F) {x : M} (hx : ∃ y, y * x = 1) : ∃ y, y * f x = 1 :=
  let ⟨y, hy⟩ := hx
  ⟨f y, map_mul_eq_one f hy⟩
#align monoid_hom.map_exists_left_inv MonoidHom.map_exists_left_inv
#align add_monoid_hom.map_exists_left_neg AddMonoidHom.map_exists_left_neg

end MonoidHom

section DivisionCommMonoid

variable [DivisionCommMonoid α]

#print invMonoidHom /-
/-- Inversion on a commutative group, considered as a monoid homomorphism. -/
@[to_additive
      "Negation on a commutative additive group, considered as an additive monoid\nhomomorphism."]
def invMonoidHom : α →* α where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' := mul_inv
#align inv_monoid_hom invMonoidHom
#align neg_add_monoid_hom negAddMonoidHom
-/

/- warning: coe_inv_monoid_hom -> coe_invMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α], Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) => α -> α) (invMonoidHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (fun (_x : MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) => α -> α) (MonoidHom.hasCoeToFun.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (invMonoidHom.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α], Eq.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (MonoidHom.monoidHomClass.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))))) (invMonoidHom.{u1} α _inst_1)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align coe_inv_monoid_hom coe_invMonoidHomₓ'. -/
@[simp]
theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv :=
  rfl
#align coe_inv_monoid_hom coe_invMonoidHom

/- warning: inv_monoid_hom_apply -> invMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (fun (_x : MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) => α -> α) (MonoidHom.hasCoeToFun.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (invMonoidHom.{u1} α _inst_1) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (MonoidHom.monoidHomClass.{u1, u1} α α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))))) (invMonoidHom.{u1} α _inst_1) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align inv_monoid_hom_apply invMonoidHom_applyₓ'. -/
@[simp]
theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ :=
  rfl
#align inv_monoid_hom_apply invMonoidHom_apply

end DivisionCommMonoid

#print OneHom.id /-
/-- The identity map from a type with 1 to itself. -/
@[to_additive, simps]
def OneHom.id (M : Type _) [One M] : OneHom M M
    where
  toFun x := x
  map_one' := rfl
#align one_hom.id OneHom.id
#align zero_hom.id ZeroHom.id
-/

#print MulHom.id /-
/-- The identity map from a type with multiplication to itself. -/
@[to_additive, simps]
def MulHom.id (M : Type _) [Mul M] : M →ₙ* M
    where
  toFun x := x
  map_mul' _ _ := rfl
#align mul_hom.id MulHom.id
#align add_hom.id AddHom.id
-/

#print MonoidHom.id /-
/-- The identity map from a monoid to itself. -/
@[to_additive, simps]
def MonoidHom.id (M : Type _) [MulOneClass M] : M →* M
    where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_hom.id MonoidHom.id
#align add_monoid_hom.id AddMonoidHom.id
-/

#print MonoidWithZeroHom.id /-
/-- The identity map from a monoid_with_zero to itself. -/
@[simps]
def MonoidWithZeroHom.id (M : Type _) [MulZeroOneClass M] : M →*₀ M
    where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
#align monoid_with_zero_hom.id MonoidWithZeroHom.id
-/

/-- The identity map from an type with zero to itself. -/
add_decl_doc ZeroHom.id

/-- The identity map from an type with addition to itself. -/
add_decl_doc AddHom.id

/-- The identity map from an additive monoid to itself. -/
add_decl_doc AddMonoidHom.id

#print OneHom.comp /-
/-- Composition of `one_hom`s as a `one_hom`. -/
@[to_additive]
def OneHom.comp [One M] [One N] [One P] (hnp : OneHom N P) (hmn : OneHom M N) : OneHom M P
    where
  toFun := hnp ∘ hmn
  map_one' := by simp
#align one_hom.comp OneHom.comp
#align zero_hom.comp ZeroHom.comp
-/

#print MulHom.comp /-
/-- Composition of `mul_hom`s as a `mul_hom`. -/
@[to_additive]
def MulHom.comp [Mul M] [Mul N] [Mul P] (hnp : N →ₙ* P) (hmn : M →ₙ* N) : M →ₙ* P
    where
  toFun := hnp ∘ hmn
  map_mul' := by simp
#align mul_hom.comp MulHom.comp
#align add_hom.comp AddHom.comp
-/

#print MonoidHom.comp /-
/-- Composition of monoid morphisms as a monoid morphism. -/
@[to_additive]
def MonoidHom.comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (hnp : N →* P) (hmn : M →* N) :
    M →* P where
  toFun := hnp ∘ hmn
  map_one' := by simp
  map_mul' := by simp
#align monoid_hom.comp MonoidHom.comp
#align add_monoid_hom.comp AddMonoidHom.comp
-/

#print MonoidWithZeroHom.comp /-
/-- Composition of `monoid_with_zero_hom`s as a `monoid_with_zero_hom`. -/
def MonoidWithZeroHom.comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (hnp : N →*₀ P) (hmn : M →*₀ N) : M →*₀ P
    where
  toFun := hnp ∘ hmn
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by simp
#align monoid_with_zero_hom.comp MonoidWithZeroHom.comp
-/

/-- Composition of `zero_hom`s as a `zero_hom`. -/
add_decl_doc ZeroHom.comp

/-- Composition of `add_hom`s as a `add_hom`. -/
add_decl_doc AddHom.comp

/-- Composition of additive monoid morphisms as an additive monoid morphism. -/
add_decl_doc AddMonoidHom.comp

/- warning: one_hom.coe_comp -> OneHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] (g : OneHom.{u2, u3} N P _inst_2 _inst_3) (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (M -> P) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : OneHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (OneHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u1, succ u2, succ u3} M N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (OneHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : OneHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (OneHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] (g : OneHom.{u2, u1} N P _inst_2 _inst_3) (f : OneHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (M -> P) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => P) _x) (OneHomClass.toFunLike.{max u3 u1, u3, u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (OneHom.oneHomClass.{u3, u1} M P _inst_1 _inst_3)) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u3, succ u2, succ u1} M N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : N) => P) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (OneHom.oneHomClass.{u2, u1} N P _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u3 u2, u3, u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u3, u2} M N _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align one_hom.coe_comp OneHom.coe_compₓ'. -/
@[simp, to_additive]
theorem OneHom.coe_comp [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) :
    ⇑(g.comp f) = g ∘ f :=
  rfl
#align one_hom.coe_comp OneHom.coe_comp
#align zero_hom.coe_comp ZeroHom.coe_comp

/- warning: mul_hom.coe_comp -> MulHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (g : MulHom.{u2, u3} N P _inst_2 _inst_3) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (M -> P) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u1, succ u2, succ u3} M N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MulHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MulHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MulHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (g : MulHom.{u2, u1} N P _inst_2 _inst_3) (f : MulHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (M -> P) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulHom.mulHomClass.{u3, u1} M P _inst_1 _inst_3)) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u3, succ u2, succ u1} M N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MulHom.mulHomClass.{u2, u1} N P _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_comp MulHom.coe_compₓ'. -/
@[simp, to_additive]
theorem MulHom.coe_comp [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align mul_hom.coe_comp MulHom.coe_comp
#align add_hom.coe_comp AddHom.coe_comp

/- warning: monoid_hom.coe_comp -> MonoidHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (M -> P) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u1, succ u2, succ u3} M N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (g : MonoidHom.{u2, u1} N P _inst_2 _inst_3) (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (M -> P) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u3, u1} M P _inst_1 _inst_3))) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u3, succ u2, succ u1} M N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} N P _inst_2 _inst_3))) g) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_comp MonoidHom.coe_compₓ'. -/
@[simp, to_additive]
theorem MonoidHom.coe_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (g : N →* P)
    (f : M →* N) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align monoid_hom.coe_comp MonoidHom.coe_comp
#align add_monoid_hom.coe_comp AddMonoidHom.coe_comp

/- warning: monoid_with_zero_hom.coe_comp -> MonoidWithZeroHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u3} P] (g : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (M -> P) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidWithZeroHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u1, succ u2, succ u3} M N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidWithZeroHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulZeroOneClass.{u3} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u1} P] (g : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) (f : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (M -> P) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u1} P (MulZeroOneClass.toMulOneClass.{u1} P _inst_3)) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P (MulZeroOneClass.toMulOneClass.{u3} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} P _inst_3) (MonoidWithZeroHomClass.toMonoidHomClass.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidWithZeroHom.monoidWithZeroHomClass.{u3, u1} M P _inst_1 _inst_3)))) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f)) (Function.comp.{succ u3, succ u2, succ u1} M N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toMul.{u1} P (MulZeroOneClass.toMulOneClass.{u1} P _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MulZeroOneClass.toMulOneClass.{u1} P _inst_3) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} N P _inst_2 _inst_3)))) g) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u3} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u3, u2} M N _inst_1 _inst_2)))) f))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.coe_comp MonoidWithZeroHom.coe_compₓ'. -/
@[simp]
theorem MonoidWithZeroHom.coe_comp [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (g : N →*₀ P) (f : M →*₀ N) : ⇑(g.comp f) = g ∘ f :=
  rfl
#align monoid_with_zero_hom.coe_comp MonoidWithZeroHom.coe_comp

/- warning: one_hom.comp_apply -> OneHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] (g : OneHom.{u2, u3} N P _inst_2 _inst_3) (f : OneHom.{u1, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u3} P (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : OneHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (OneHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) x) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (OneHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : OneHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (OneHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] (g : OneHom.{u2, u1} N P _inst_2 _inst_3) (f : OneHom.{u3, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => P) _x) (OneHomClass.toFunLike.{max u3 u1, u3, u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (OneHom.oneHomClass.{u3, u1} M P _inst_1 _inst_3)) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : N) => P) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (OneHom.oneHomClass.{u2, u1} N P _inst_2 _inst_3)) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u3 u2, u3, u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u3, u2} M N _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align one_hom.comp_apply OneHom.comp_applyₓ'. -/
@[to_additive]
theorem OneHom.comp_apply [One M] [One N] [One P] (g : OneHom N P) (f : OneHom M N) (x : M) :
    g.comp f x = g (f x) :=
  rfl
#align one_hom.comp_apply OneHom.comp_apply
#align zero_hom.comp_apply ZeroHom.comp_apply

/- warning: mul_hom.comp_apply -> MulHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (g : MulHom.{u2, u3} N P _inst_2 _inst_3) (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u3} P (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) x) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MulHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MulHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MulHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (g : MulHom.{u2, u1} N P _inst_2 _inst_3) (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MulHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulHom.mulHomClass.{u3, u1} M P _inst_1 _inst_3)) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MulHom.mulHomClass.{u2, u1} N P _inst_2 _inst_3)) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align mul_hom.comp_apply MulHom.comp_applyₓ'. -/
@[to_additive]
theorem MulHom.comp_apply [Mul M] [Mul N] [Mul P] (g : N →ₙ* P) (f : M →ₙ* N) (x : M) :
    g.comp f x = g (f x) :=
  rfl
#align mul_hom.comp_apply MulHom.comp_apply
#align add_hom.comp_apply AddHom.comp_apply

/- warning: monoid_hom.comp_apply -> MonoidHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u3} P (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) x) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] (g : MonoidHom.{u2, u1} N P _inst_2 _inst_3) (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u3, u1} M P _inst_1 _inst_3))) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} N P _inst_2 _inst_3))) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_apply MonoidHom.comp_applyₓ'. -/
@[to_additive]
theorem MonoidHom.comp_apply [MulOneClass M] [MulOneClass N] [MulOneClass P] (g : N →* P)
    (f : M →* N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align monoid_hom.comp_apply MonoidHom.comp_apply
#align add_monoid_hom.comp_apply AddMonoidHom.comp_apply

/- warning: monoid_with_zero_hom.comp_apply -> MonoidWithZeroHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u3} P] (g : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u3} P (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MonoidWithZeroHom.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f) x) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidWithZeroHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulZeroOneClass.{u3} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u1} P] (g : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) (f : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) x) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => P) _x) (MulHomClass.toFunLike.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P (MulOneClass.toMul.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u1} P (MulZeroOneClass.toMulOneClass.{u1} P _inst_3)) (MonoidHomClass.toMulHomClass.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P (MulZeroOneClass.toMulOneClass.{u3} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} P _inst_3) (MonoidWithZeroHomClass.toMonoidHomClass.{max u3 u1, u3, u1} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MonoidWithZeroHom.monoidWithZeroHomClass.{u3, u1} M P _inst_1 _inst_3)))) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toMul.{u1} P (MulZeroOneClass.toMulOneClass.{u1} P _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MulZeroOneClass.toMulOneClass.{u1} P _inst_3) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} N P _inst_2 _inst_3)))) g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u3} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u3, u2} M N _inst_1 _inst_2)))) f x))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.comp_apply MonoidWithZeroHom.comp_applyₓ'. -/
theorem MonoidWithZeroHom.comp_apply [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    (g : N →*₀ P) (f : M →*₀ N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align monoid_with_zero_hom.comp_apply MonoidWithZeroHom.comp_apply

/- warning: one_hom.comp_assoc -> OneHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] [_inst_4 : One.{u4} Q] (f : OneHom.{u1, u2} M N _inst_1 _inst_2) (g : OneHom.{u2, u3} N P _inst_2 _inst_3) (h : OneHom.{u3, u4} P Q _inst_3 _inst_4), Eq.{max (succ u4) (succ u1)} (OneHom.{u1, u4} M Q _inst_1 _inst_4) (OneHom.comp.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (OneHom.comp.{u2, u3, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (OneHom.comp.{u1, u3, u4} M P Q _inst_1 _inst_3 _inst_4 h (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} {Q : Type.{u4}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] [_inst_4 : One.{u4} Q] (f : OneHom.{u3, u2} M N _inst_1 _inst_2) (g : OneHom.{u2, u1} N P _inst_2 _inst_3) (h : OneHom.{u1, u4} P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u4)} (OneHom.{u3, u4} M Q _inst_1 _inst_4) (OneHom.comp.{u3, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (OneHom.comp.{u2, u1, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (OneHom.comp.{u3, u1, u4} M P Q _inst_1 _inst_3 _inst_4 h (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align one_hom.comp_assoc OneHom.comp_assocₓ'. -/
/-- Composition of monoid homomorphisms is associative. -/
@[to_additive "Composition of additive monoid homomorphisms is associative."]
theorem OneHom.comp_assoc {Q : Type _} [One M] [One N] [One P] [One Q] (f : OneHom M N)
    (g : OneHom N P) (h : OneHom P Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align one_hom.comp_assoc OneHom.comp_assoc
#align zero_hom.comp_assoc ZeroHom.comp_assoc

/- warning: mul_hom.comp_assoc -> MulHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] [_inst_4 : Mul.{u4} Q] (f : MulHom.{u1, u2} M N _inst_1 _inst_2) (g : MulHom.{u2, u3} N P _inst_2 _inst_3) (h : MulHom.{u3, u4} P Q _inst_3 _inst_4), Eq.{max (succ u4) (succ u1)} (MulHom.{u1, u4} M Q _inst_1 _inst_4) (MulHom.comp.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MulHom.comp.{u2, u3, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MulHom.comp.{u1, u3, u4} M P Q _inst_1 _inst_3 _inst_4 h (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} {Q : Type.{u4}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] [_inst_4 : Mul.{u4} Q] (f : MulHom.{u3, u2} M N _inst_1 _inst_2) (g : MulHom.{u2, u1} N P _inst_2 _inst_3) (h : MulHom.{u1, u4} P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u4)} (MulHom.{u3, u4} M Q _inst_1 _inst_4) (MulHom.comp.{u3, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MulHom.comp.{u2, u1, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MulHom.comp.{u3, u1, u4} M P Q _inst_1 _inst_3 _inst_4 h (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align mul_hom.comp_assoc MulHom.comp_assocₓ'. -/
@[to_additive]
theorem MulHom.comp_assoc {Q : Type _} [Mul M] [Mul N] [Mul P] [Mul Q] (f : M →ₙ* N) (g : N →ₙ* P)
    (h : P →ₙ* Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align mul_hom.comp_assoc MulHom.comp_assoc
#align add_hom.comp_assoc AddHom.comp_assoc

/- warning: monoid_hom.comp_assoc -> MonoidHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] [_inst_4 : MulOneClass.{u4} Q] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u2, u3} N P _inst_2 _inst_3) (h : MonoidHom.{u3, u4} P Q _inst_3 _inst_4), Eq.{max (succ u4) (succ u1)} (MonoidHom.{u1, u4} M Q _inst_1 _inst_4) (MonoidHom.comp.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidHom.comp.{u2, u3, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MonoidHom.comp.{u1, u3, u4} M P Q _inst_1 _inst_3 _inst_4 h (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} {Q : Type.{u4}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] [_inst_4 : MulOneClass.{u4} Q] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u2, u1} N P _inst_2 _inst_3) (h : MonoidHom.{u1, u4} P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u4)} (MonoidHom.{u3, u4} M Q _inst_1 _inst_4) (MonoidHom.comp.{u3, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidHom.comp.{u2, u1, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MonoidHom.comp.{u3, u1, u4} M P Q _inst_1 _inst_3 _inst_4 h (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_assoc MonoidHom.comp_assocₓ'. -/
@[to_additive]
theorem MonoidHom.comp_assoc {Q : Type _} [MulOneClass M] [MulOneClass N] [MulOneClass P]
    [MulOneClass Q] (f : M →* N) (g : N →* P) (h : P →* Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align monoid_hom.comp_assoc MonoidHom.comp_assoc
#align add_monoid_hom.comp_assoc AddMonoidHom.comp_assoc

/- warning: monoid_with_zero_hom.comp_assoc -> MonoidWithZeroHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u3} P] [_inst_4 : MulZeroOneClass.{u4} Q] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (h : MonoidWithZeroHom.{u3, u4} P Q _inst_3 _inst_4), Eq.{max (succ u4) (succ u1)} (MonoidWithZeroHom.{u1, u4} M Q _inst_1 _inst_4) (MonoidWithZeroHom.comp.{u1, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidWithZeroHom.comp.{u2, u3, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MonoidWithZeroHom.comp.{u1, u3, u4} M P Q _inst_1 _inst_3 _inst_4 h (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} {Q : Type.{u4}} [_inst_1 : MulZeroOneClass.{u3} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u1} P] [_inst_4 : MulZeroOneClass.{u4} Q] (f : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) (g : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) (h : MonoidWithZeroHom.{u1, u4} P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u4)} (MonoidWithZeroHom.{u3, u4} M Q _inst_1 _inst_4) (MonoidWithZeroHom.comp.{u3, u2, u4} M N Q _inst_1 _inst_2 _inst_4 (MonoidWithZeroHom.comp.{u2, u1, u4} N P Q _inst_2 _inst_3 _inst_4 h g) f) (MonoidWithZeroHom.comp.{u3, u1, u4} M P Q _inst_1 _inst_3 _inst_4 h (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.comp_assoc MonoidWithZeroHom.comp_assocₓ'. -/
theorem MonoidWithZeroHom.comp_assoc {Q : Type _} [MulZeroOneClass M] [MulZeroOneClass N]
    [MulZeroOneClass P] [MulZeroOneClass Q] (f : M →*₀ N) (g : N →*₀ P) (h : P →*₀ Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align monoid_with_zero_hom.comp_assoc MonoidWithZeroHom.comp_assoc

/- warning: one_hom.cancel_right -> OneHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] {g₁ : OneHom.{u2, u3} N P _inst_2 _inst_3} {g₂ : OneHom.{u2, u3} N P _inst_2 _inst_3} {f : OneHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₁ f) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (OneHom.{u2, u3} N P _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] {g₁ : OneHom.{u2, u1} N P _inst_2 _inst_3} {g₂ : OneHom.{u2, u1} N P _inst_2 _inst_3} {f : OneHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u3 u2, u3, u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u3, u2} M N _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (OneHom.{u3, u1} M P _inst_1 _inst_3) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₁ f) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} N P _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align one_hom.cancel_right OneHom.cancel_rightₓ'. -/
@[to_additive]
theorem OneHom.cancel_right [One M] [One N] [One P] {g₁ g₂ : OneHom N P} {f : OneHom M N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => OneHom.ext <| hf.forall.2 (OneHom.ext_iff.1 h), fun h => h ▸ rfl⟩
#align one_hom.cancel_right OneHom.cancel_right
#align zero_hom.cancel_right ZeroHom.cancel_right

/- warning: mul_hom.cancel_right -> MulHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] {g₁ : MulHom.{u2, u3} N P _inst_2 _inst_3} {g₂ : MulHom.{u2, u3} N P _inst_2 _inst_3} {f : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (MulHom.{u2, u3} N P _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] {g₁ : MulHom.{u2, u1} N P _inst_2 _inst_3} {g₂ : MulHom.{u2, u1} N P _inst_2 _inst_3} {f : MulHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MulHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u3, u2} M N _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MulHom.{u3, u1} M P _inst_1 _inst_3) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} N P _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align mul_hom.cancel_right MulHom.cancel_rightₓ'. -/
@[to_additive]
theorem MulHom.cancel_right [Mul M] [Mul N] [Mul P] {g₁ g₂ : N →ₙ* P} {f : M →ₙ* N}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MulHom.ext <| hf.forall.2 (MulHom.ext_iff.1 h), fun h => h ▸ rfl⟩
#align mul_hom.cancel_right MulHom.cancel_right
#align add_hom.cancel_right AddHom.cancel_right

/- warning: monoid_hom.cancel_right -> MonoidHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] {g₁ : MonoidHom.{u2, u3} N P _inst_2 _inst_3} {g₂ : MonoidHom.{u2, u3} N P _inst_2 _inst_3} {f : MonoidHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (MonoidHom.{u2, u3} N P _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] {g₁ : MonoidHom.{u2, u1} N P _inst_2 _inst_3} {g₂ : MonoidHom.{u2, u1} N P _inst_2 _inst_3} {f : MonoidHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align monoid_hom.cancel_right MonoidHom.cancel_rightₓ'. -/
@[to_additive]
theorem MonoidHom.cancel_right [MulOneClass M] [MulOneClass N] [MulOneClass P] {g₁ g₂ : N →* P}
    {f : M →* N} (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidHom.ext <| hf.forall.2 (MonoidHom.ext_iff.1 h), fun h => h ▸ rfl⟩
#align monoid_hom.cancel_right MonoidHom.cancel_right
#align add_monoid_hom.cancel_right AddMonoidHom.cancel_right

/- warning: monoid_with_zero_hom.cancel_right -> MonoidWithZeroHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u3} P] {g₁ : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3} {g₂ : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3} {f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidWithZeroHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulZeroOneClass.{u3} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u1} P] {g₁ : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3} {g₂ : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3} {f : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Surjective.{succ u3, succ u2} M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)) (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N (MulZeroOneClass.toMulOneClass.{u3} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MonoidWithZeroHomClass.toMonoidHomClass.{max u3 u2, u3, u2} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidWithZeroHom.monoidWithZeroHomClass.{u3, u2} M N _inst_1 _inst_2)))) f)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₁ f) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.cancel_right MonoidWithZeroHom.cancel_rightₓ'. -/
theorem MonoidWithZeroHom.cancel_right [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    {g₁ g₂ : N →*₀ P} {f : M →*₀ N} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => MonoidWithZeroHom.ext <| hf.forall.2 (MonoidWithZeroHom.ext_iff.1 h), fun h => h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_right MonoidWithZeroHom.cancel_right

/- warning: one_hom.cancel_left -> OneHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] {g : OneHom.{u2, u3} N P _inst_2 _inst_3} {f₁ : OneHom.{u1, u2} M N _inst_1 _inst_2} {f₂ : OneHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (OneHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : OneHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (OneHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₁) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] {g : OneHom.{u2, u1} N P _inst_2 _inst_3} {f₁ : OneHom.{u3, u2} M N _inst_1 _inst_2} {f₂ : OneHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : N) => P) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (OneHom.oneHomClass.{u2, u1} N P _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (OneHom.{u3, u1} M P _inst_1 _inst_3) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₁) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u3) (succ u2)} (OneHom.{u3, u2} M N _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align one_hom.cancel_left OneHom.cancel_leftₓ'. -/
@[to_additive]
theorem OneHom.cancel_left [One M] [One N] [One P] {g : OneHom N P} {f₁ f₂ : OneHom M N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => OneHom.ext fun x => hg <| by rw [← OneHom.comp_apply, h, OneHom.comp_apply], fun h =>
    h ▸ rfl⟩
#align one_hom.cancel_left OneHom.cancel_left
#align zero_hom.cancel_left ZeroHom.cancel_left

/- warning: mul_hom.cancel_left -> MulHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] {g : MulHom.{u2, u3} N P _inst_2 _inst_3} {f₁ : MulHom.{u1, u2} M N _inst_1 _inst_2} {f₂ : MulHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MulHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MulHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MulHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MulHom.{u1, u3} M P _inst_1 _inst_3) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₁) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] {g : MulHom.{u2, u1} N P _inst_2 _inst_3} {f₁ : MulHom.{u3, u2} M N _inst_1 _inst_2} {f₂ : MulHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MulHom.mulHomClass.{u2, u1} N P _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MulHom.{u3, u1} M P _inst_1 _inst_3) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₁) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u3) (succ u2)} (MulHom.{u3, u2} M N _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align mul_hom.cancel_left MulHom.cancel_leftₓ'. -/
@[to_additive]
theorem MulHom.cancel_left [Mul M] [Mul N] [Mul P] {g : N →ₙ* P} {f₁ f₂ : M →ₙ* N}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MulHom.ext fun x => hg <| by rw [← MulHom.comp_apply, h, MulHom.comp_apply], fun h =>
    h ▸ rfl⟩
#align mul_hom.cancel_left MulHom.cancel_left
#align add_hom.cancel_left AddHom.cancel_left

/- warning: monoid_hom.cancel_left -> MonoidHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u3} P] {g : MonoidHom.{u2, u3} N P _inst_2 _inst_3} {f₁ : MonoidHom.{u1, u2} M N _inst_1 _inst_2} {f₂ : MonoidHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_1 _inst_3) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₁) (MonoidHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulOneClass.{u1} P] {g : MonoidHom.{u2, u1} N P _inst_2 _inst_3} {f₁ : MonoidHom.{u3, u2} M N _inst_1 _inst_2} {f₂ : MonoidHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N _inst_2) (MulOneClass.toMul.{u1} P _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} N P _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_1 _inst_3) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₁) (MonoidHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u3) (succ u2)} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align monoid_hom.cancel_left MonoidHom.cancel_leftₓ'. -/
@[to_additive]
theorem MonoidHom.cancel_left [MulOneClass M] [MulOneClass N] [MulOneClass P] {g : N →* P}
    {f₁ f₂ : M →* N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => MonoidHom.ext fun x => hg <| by rw [← MonoidHom.comp_apply, h, MonoidHom.comp_apply],
    fun h => h ▸ rfl⟩
#align monoid_hom.cancel_left MonoidHom.cancel_left
#align add_monoid_hom.cancel_left AddMonoidHom.cancel_left

/- warning: monoid_with_zero_hom.cancel_left -> MonoidWithZeroHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u3} P] {g : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3} {f₁ : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2} {f₂ : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} N P (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MonoidWithZeroHom.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MonoidWithZeroHom.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidWithZeroHom.{u1, u3} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₁) (MonoidWithZeroHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : MulZeroOneClass.{u3} M] [_inst_2 : MulZeroOneClass.{u2} N] [_inst_3 : MulZeroOneClass.{u1} P] {g : MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3} {f₁ : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2} {f₂ : MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u1} N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulOneClass.toMul.{u2} N (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toMul.{u1} P (MulZeroOneClass.toMulOneClass.{u1} P _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P (MulZeroOneClass.toMulOneClass.{u2} N _inst_2) (MulZeroOneClass.toMulOneClass.{u1} P _inst_3) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (MonoidWithZeroHom.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MonoidWithZeroHom.monoidWithZeroHomClass.{u2, u1} N P _inst_2 _inst_3)))) g)) -> (Iff (Eq.{max (succ u3) (succ u1)} (MonoidWithZeroHom.{u3, u1} M P _inst_1 _inst_3) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₁) (MonoidWithZeroHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u3) (succ u2)} (MonoidWithZeroHom.{u3, u2} M N _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.cancel_left MonoidWithZeroHom.cancel_leftₓ'. -/
theorem MonoidWithZeroHom.cancel_left [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P]
    {g : N →*₀ P} {f₁ f₂ : M →*₀ N} (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    MonoidWithZeroHom.ext fun x =>
      hg <| by rw [← MonoidWithZeroHom.comp_apply, h, MonoidWithZeroHom.comp_apply],
    fun h => h ▸ rfl⟩
#align monoid_with_zero_hom.cancel_left MonoidWithZeroHom.cancel_left

/- warning: monoid_hom.to_one_hom_injective -> MonoidHom.toOneHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.{u1, u2} M N (MulOneClass.toHasOne.{u1} M _inst_1) (MulOneClass.toHasOne.{u2} N _inst_2)) (MonoidHom.toOneHom.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (OneHom.{u2, u1} M N (MulOneClass.toOne.{u2} M _inst_1) (MulOneClass.toOne.{u1} N _inst_2)) (MonoidHom.toOneHom.{u2, u1} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_one_hom_injective MonoidHom.toOneHom_injectiveₓ'. -/
@[to_additive]
theorem MonoidHom.toOneHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) := fun f g h =>
  MonoidHom.ext <| OneHom.ext_iff.mp h
#align monoid_hom.to_one_hom_injective MonoidHom.toOneHom_injective
#align add_monoid_hom.to_zero_hom_injective AddMonoidHom.toZeroHom_injective

/- warning: monoid_hom.to_mul_hom_injective -> MonoidHom.toMulHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2)) (MonoidHom.toMulHom.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2)) (MonoidHom.toMulHom.{u2, u1} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_mul_hom_injective MonoidHom.toMulHom_injectiveₓ'. -/
@[to_additive]
theorem MonoidHom.toMulHom_injective [MulOneClass M] [MulOneClass N] :
    Function.Injective (MonoidHom.toMulHom : (M →* N) → M →ₙ* N) := fun f g h =>
  MonoidHom.ext <| MulHom.ext_iff.mp h
#align monoid_hom.to_mul_hom_injective MonoidHom.toMulHom_injective
#align add_monoid_hom.to_add_hom_injective AddMonoidHom.toAddHom_injective

/- warning: monoid_with_zero_hom.to_monoid_hom_injective -> MonoidWithZeroHom.toMonoidHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.{u1, u2} M N (MulZeroOneClass.toMulOneClass.{u1} M _inst_1) (MulZeroOneClass.toMulOneClass.{u2} N _inst_2)) (MonoidWithZeroHom.toMonoidHom.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.{u2, u1} M N (MulZeroOneClass.toMulOneClass.{u2} M _inst_1) (MulZeroOneClass.toMulOneClass.{u1} N _inst_2)) (MonoidWithZeroHom.toMonoidHom.{u2, u1} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.to_monoid_hom_injective MonoidWithZeroHom.toMonoidHom_injectiveₓ'. -/
theorem MonoidWithZeroHom.toMonoidHom_injective [MulZeroOneClass M] [MulZeroOneClass N] :
    Function.Injective (MonoidWithZeroHom.toMonoidHom : (M →*₀ N) → M →* N) := fun f g h =>
  MonoidWithZeroHom.ext <| MonoidHom.ext_iff.mp h
#align monoid_with_zero_hom.to_monoid_hom_injective MonoidWithZeroHom.toMonoidHom_injective

/- warning: monoid_with_zero_hom.to_zero_hom_injective -> MonoidWithZeroHom.toZeroHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (ZeroHom.{u1, u2} M N (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)) (MulZeroClass.toHasZero.{u2} N (MulZeroOneClass.toMulZeroClass.{u2} N _inst_2))) (MonoidWithZeroHom.toZeroHom.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (ZeroHom.{u2, u1} M N (MulZeroOneClass.toZero.{u2} M _inst_1) (MulZeroOneClass.toZero.{u1} N _inst_2)) (MonoidWithZeroHom.toZeroHom.{u2, u1} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.to_zero_hom_injective MonoidWithZeroHom.toZeroHom_injectiveₓ'. -/
theorem MonoidWithZeroHom.toZeroHom_injective [MulZeroOneClass M] [MulZeroOneClass N] :
    Function.Injective (MonoidWithZeroHom.toZeroHom : (M →*₀ N) → ZeroHom M N) := fun f g h =>
  MonoidWithZeroHom.ext <| ZeroHom.ext_iff.mp h
#align monoid_with_zero_hom.to_zero_hom_injective MonoidWithZeroHom.toZeroHom_injective

/- warning: one_hom.comp_id -> OneHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.comp.{u1, u1, u2} M M N _inst_1 _inst_1 _inst_2 f (OneHom.id.{u1} M _inst_1)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) (OneHom.comp.{u2, u2, u1} M M N _inst_1 _inst_1 _inst_2 f (OneHom.id.{u2} M _inst_1)) f
Case conversion may be inaccurate. Consider using '#align one_hom.comp_id OneHom.comp_idₓ'. -/
@[simp, to_additive]
theorem OneHom.comp_id [One M] [One N] (f : OneHom M N) : f.comp (OneHom.id M) = f :=
  OneHom.ext fun x => rfl
#align one_hom.comp_id OneHom.comp_id
#align zero_hom.comp_id ZeroHom.comp_id

/- warning: mul_hom.comp_id -> MulHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.comp.{u1, u1, u2} M M N _inst_1 _inst_1 _inst_2 f (MulHom.id.{u1} M _inst_1)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) (MulHom.comp.{u2, u2, u1} M M N _inst_1 _inst_1 _inst_2 f (MulHom.id.{u2} M _inst_1)) f
Case conversion may be inaccurate. Consider using '#align mul_hom.comp_id MulHom.comp_idₓ'. -/
@[simp, to_additive]
theorem MulHom.comp_id [Mul M] [Mul N] (f : M →ₙ* N) : f.comp (MulHom.id M) = f :=
  MulHom.ext fun x => rfl
#align mul_hom.comp_id MulHom.comp_id
#align add_hom.comp_id AddHom.comp_id

/- warning: monoid_hom.comp_id -> MonoidHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.comp.{u1, u1, u2} M M N _inst_1 _inst_1 _inst_2 f (MonoidHom.id.{u1} M _inst_1)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.comp.{u2, u2, u1} M M N _inst_1 _inst_1 _inst_2 f (MonoidHom.id.{u2} M _inst_1)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_id MonoidHom.comp_idₓ'. -/
@[simp, to_additive]
theorem MonoidHom.comp_id [MulOneClass M] [MulOneClass N] (f : M →* N) :
    f.comp (MonoidHom.id M) = f :=
  MonoidHom.ext fun x => rfl
#align monoid_hom.comp_id MonoidHom.comp_id
#align add_monoid_hom.comp_id AddMonoidHom.comp_id

/- warning: monoid_with_zero_hom.comp_id -> MonoidWithZeroHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.comp.{u1, u1, u2} M M N _inst_1 _inst_1 _inst_2 f (MonoidWithZeroHom.id.{u1} M _inst_1)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MonoidWithZeroHom.comp.{u2, u2, u1} M M N _inst_1 _inst_1 _inst_2 f (MonoidWithZeroHom.id.{u2} M _inst_1)) f
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.comp_id MonoidWithZeroHom.comp_idₓ'. -/
@[simp]
theorem MonoidWithZeroHom.comp_id [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    f.comp (MonoidWithZeroHom.id M) = f :=
  MonoidWithZeroHom.ext fun x => rfl
#align monoid_with_zero_hom.comp_id MonoidWithZeroHom.comp_id

/- warning: one_hom.id_comp -> OneHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.comp.{u1, u2, u2} M N N _inst_1 _inst_2 _inst_2 (OneHom.id.{u2} N _inst_2) f) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (f : OneHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (OneHom.{u2, u1} M N _inst_1 _inst_2) (OneHom.comp.{u2, u1, u1} M N N _inst_1 _inst_2 _inst_2 (OneHom.id.{u1} N _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align one_hom.id_comp OneHom.id_compₓ'. -/
@[simp, to_additive]
theorem OneHom.id_comp [One M] [One N] (f : OneHom M N) : (OneHom.id N).comp f = f :=
  OneHom.ext fun x => rfl
#align one_hom.id_comp OneHom.id_comp
#align zero_hom.id_comp ZeroHom.id_comp

/- warning: mul_hom.id_comp -> MulHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (MulHom.comp.{u1, u2, u2} M N N _inst_1 _inst_2 _inst_2 (MulHom.id.{u2} N _inst_2) f) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MulHom.{u2, u1} M N _inst_1 _inst_2) (MulHom.comp.{u2, u1, u1} M N N _inst_1 _inst_2 _inst_2 (MulHom.id.{u1} N _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align mul_hom.id_comp MulHom.id_compₓ'. -/
@[simp, to_additive]
theorem MulHom.id_comp [Mul M] [Mul N] (f : M →ₙ* N) : (MulHom.id N).comp f = f :=
  MulHom.ext fun x => rfl
#align mul_hom.id_comp MulHom.id_comp
#align add_hom.id_comp AddHom.id_comp

/- warning: monoid_hom.id_comp -> MonoidHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.comp.{u1, u2, u2} M N N _inst_1 _inst_2 _inst_2 (MonoidHom.id.{u2} N _inst_2) f) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (MonoidHom.comp.{u2, u1, u1} M N N _inst_1 _inst_2 _inst_2 (MonoidHom.id.{u1} N _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.id_comp MonoidHom.id_compₓ'. -/
@[simp, to_additive]
theorem MonoidHom.id_comp [MulOneClass M] [MulOneClass N] (f : M →* N) :
    (MonoidHom.id N).comp f = f :=
  MonoidHom.ext fun x => rfl
#align monoid_hom.id_comp MonoidHom.id_comp
#align add_monoid_hom.id_comp AddMonoidHom.id_comp

/- warning: monoid_with_zero_hom.id_comp -> MonoidWithZeroHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : MulZeroOneClass.{u2} N] (f : MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u1, u2} M N _inst_1 _inst_2) (MonoidWithZeroHom.comp.{u1, u2, u2} M N N _inst_1 _inst_2 _inst_2 (MonoidWithZeroHom.id.{u2} N _inst_2) f) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : MulZeroOneClass.{u1} N] (f : MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidWithZeroHom.{u2, u1} M N _inst_1 _inst_2) (MonoidWithZeroHom.comp.{u2, u1, u1} M N N _inst_1 _inst_2 _inst_2 (MonoidWithZeroHom.id.{u1} N _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align monoid_with_zero_hom.id_comp MonoidWithZeroHom.id_compₓ'. -/
@[simp]
theorem MonoidWithZeroHom.id_comp [MulZeroOneClass M] [MulZeroOneClass N] (f : M →*₀ N) :
    (MonoidWithZeroHom.id N).comp f = f :=
  MonoidWithZeroHom.ext fun x => rfl
#align monoid_with_zero_hom.id_comp MonoidWithZeroHom.id_comp

/- warning: monoid_hom.map_pow -> MonoidHom.map_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (a : M) (n : Nat), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) f (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n)) (HPow.hPow.{u2, 0, u2} N Nat N (instHPow.{u2, 0} N Nat (Monoid.Pow.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) f a) n)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) (a : M) (n : Nat), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_1)) a n)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) f (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_1)) a n)) (HPow.hPow.{u1, 0, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHPow.{u1, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) Nat (Monoid.Pow.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) f a) n)
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_pow MonoidHom.map_powₓ'. -/
@[to_additive AddMonoidHom.map_nsmul]
protected theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = f a ^ n :=
  map_pow f a n
#align monoid_hom.map_pow MonoidHom.map_pow
#align add_monoid_hom.map_nsmul AddMonoidHom.map_nsmul

/- warning: monoid_hom.map_zpow' -> MonoidHom.map_zpow' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : DivInvMonoid.{u1} M] [_inst_2 : DivInvMonoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))), (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) f (Inv.inv.{u1} M (DivInvMonoid.toHasInv.{u1} M _inst_1) x)) (Inv.inv.{u2} N (DivInvMonoid.toHasInv.{u2} N _inst_2) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) f x))) -> (forall (a : M) (n : Int), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) f (HPow.hPow.{u1, 0, u1} M Int M (instHPow.{u1, 0} M Int (DivInvMonoid.Pow.{u1} M _inst_1)) a n)) (HPow.hPow.{u2, 0, u2} N Int N (instHPow.{u2, 0} N Int (DivInvMonoid.Pow.{u2} N _inst_2)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1)) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N _inst_2))) f a) n))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : DivInvMonoid.{u2} M] [_inst_2 : DivInvMonoid.{u1} N] (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))), (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (Inv.inv.{u2} M (DivInvMonoid.toInv.{u2} M _inst_1) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))))) f (Inv.inv.{u2} M (DivInvMonoid.toInv.{u2} M _inst_1) x)) (Inv.inv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (DivInvMonoid.toInv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))))) f x))) -> (forall (a : M) (n : Int), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (HPow.hPow.{u2, 0, u2} M Int M (instHPow.{u2, 0} M Int (DivInvMonoid.Pow.{u2} M _inst_1)) a n)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))))) f (HPow.hPow.{u2, 0, u2} M Int M (instHPow.{u2, 0} M Int (DivInvMonoid.Pow.{u2} M _inst_1)) a n)) (HPow.hPow.{u1, 0, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (instHPow.{u1, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) Int (DivInvMonoid.Pow.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) _inst_2)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1))) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))) M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M _inst_1)) (Monoid.toMulOneClass.{u1} N (DivInvMonoid.toMonoid.{u1} N _inst_2))))) f a) n))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_zpow' MonoidHom.map_zpow'ₓ'. -/
@[to_additive]
protected theorem MonoidHom.map_zpow' [DivInvMonoid M] [DivInvMonoid N] (f : M →* N)
    (hf : ∀ x, f x⁻¹ = (f x)⁻¹) (a : M) (n : ℤ) : f (a ^ n) = f a ^ n :=
  map_zpow' f hf a n
#align monoid_hom.map_zpow' MonoidHom.map_zpow'
#align add_monoid_hom.map_zsmul' AddMonoidHom.map_zsmul'

section End

namespace Monoid

variable (M) [MulOneClass M]

#print Monoid.End /-
/-- The monoid of endomorphisms. -/
protected def End :=
  M →* M
#align monoid.End Monoid.End
-/

namespace End

instance : Monoid (Monoid.End M) where
  mul := MonoidHom.comp
  one := MonoidHom.id M
  mul_assoc _ _ _ := MonoidHom.comp_assoc _ _ _
  mul_one := MonoidHom.comp_id
  one_mul := MonoidHom.id_comp

instance : Inhabited (Monoid.End M) :=
  ⟨1⟩

instance : MonoidHomClass (Monoid.End M) M M :=
  MonoidHom.monoidHomClass

end End

/- warning: monoid.coe_one -> Monoid.coe_one is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} ((fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (OfNat.ofNat.{u1} (Monoid.End.{u1} M _inst_1) 1 (OfNat.mk.{u1} (Monoid.End.{u1} M _inst_1) 1 (One.one.{u1} (Monoid.End.{u1} M _inst_1) (MulOneClass.toHasOne.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.monoid.{u1} M _inst_1))))))) (coeFn.{succ u1, succ u1} (Monoid.End.{u1} M _inst_1) (fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => M) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.monoidHomClass.{u1} M _inst_1)))) (OfNat.ofNat.{u1} (Monoid.End.{u1} M _inst_1) 1 (OfNat.mk.{u1} (Monoid.End.{u1} M _inst_1) 1 (One.one.{u1} (Monoid.End.{u1} M _inst_1) (MulOneClass.toHasOne.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.monoid.{u1} M _inst_1))))))) (id.{succ u1} M)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) _x) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.instMonoidHomClassEnd.{u1} M _inst_1))) (OfNat.ofNat.{u1} (Monoid.End.{u1} M _inst_1) 1 (One.toOfNat1.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toOne.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.instMonoidEnd.{u1} M _inst_1))))) (id.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align monoid.coe_one Monoid.coe_oneₓ'. -/
@[simp]
theorem coe_one : ((1 : Monoid.End M) : M → M) = id :=
  rfl
#align monoid.coe_one Monoid.coe_one

/- warning: monoid.coe_mul -> Monoid.coe_mul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M] (f : Monoid.End.{u1} M _inst_1) (g : Monoid.End.{u1} M _inst_1), Eq.{succ u1} ((fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (HMul.hMul.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (instHMul.{u1} (Monoid.End.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.monoid.{u1} M _inst_1)))) f g)) (coeFn.{succ u1, succ u1} (Monoid.End.{u1} M _inst_1) (fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => M) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.monoidHomClass.{u1} M _inst_1)))) (HMul.hMul.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (instHMul.{u1} (Monoid.End.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.monoid.{u1} M _inst_1)))) f g)) (Function.comp.{succ u1, succ u1, succ u1} M M M (coeFn.{succ u1, succ u1} (Monoid.End.{u1} M _inst_1) (fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => M) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.monoidHomClass.{u1} M _inst_1)))) f) (coeFn.{succ u1, succ u1} (Monoid.End.{u1} M _inst_1) (fun (_x : Monoid.End.{u1} M _inst_1) => M -> M) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => M) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.monoidHomClass.{u1} M _inst_1)))) g))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M] (f : Monoid.End.{u1} M _inst_1) (g : Monoid.End.{u1} M _inst_1), Eq.{succ u1} (forall (a : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) _x) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.instMonoidHomClassEnd.{u1} M _inst_1))) (HMul.hMul.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (Monoid.End.{u1} M _inst_1) (instHMul.{u1} (Monoid.End.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.toMulOneClass.{u1} (Monoid.End.{u1} M _inst_1) (Monoid.End.instMonoidEnd.{u1} M _inst_1)))) f g)) (Function.comp.{succ u1, succ u1, succ u1} M M M (FunLike.coe.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) _x) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.instMonoidHomClassEnd.{u1} M _inst_1))) f) (FunLike.coe.{succ u1, succ u1, succ u1} (Monoid.End.{u1} M _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => M) _x) (MulHomClass.toFunLike.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u1} M _inst_1) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (Monoid.End.{u1} M _inst_1) M M _inst_1 _inst_1 (Monoid.End.instMonoidHomClassEnd.{u1} M _inst_1))) g))
Case conversion may be inaccurate. Consider using '#align monoid.coe_mul Monoid.coe_mulₓ'. -/
@[simp]
theorem coe_mul (f g) : ((f * g : Monoid.End M) : M → M) = f ∘ g :=
  rfl
#align monoid.coe_mul Monoid.coe_mul

end Monoid

namespace AddMonoid

variable (A : Type _) [AddZeroClass A]

#print AddMonoid.End /-
/-- The monoid of endomorphisms. -/
protected def End :=
  A →+ A
#align add_monoid.End AddMonoid.End
-/

namespace End

instance : Monoid (AddMonoid.End A)
    where
  mul := AddMonoidHom.comp
  one := AddMonoidHom.id A
  mul_assoc _ _ _ := AddMonoidHom.comp_assoc _ _ _
  mul_one := AddMonoidHom.comp_id
  one_mul := AddMonoidHom.id_comp

instance : Inhabited (AddMonoid.End A) :=
  ⟨1⟩

instance : AddMonoidHomClass (AddMonoid.End A) A A :=
  AddMonoidHom.addMonoidHomClass

end End

/- warning: add_monoid.coe_one -> AddMonoid.coe_one is a dubious translation:
lean 3 declaration is
  forall (A : Type.{u1}) [_inst_1 : AddZeroClass.{u1} A], Eq.{succ u1} ((fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (OfNat.ofNat.{u1} (AddMonoid.End.{u1} A _inst_1) 1 (OfNat.mk.{u1} (AddMonoid.End.{u1} A _inst_1) 1 (One.one.{u1} (AddMonoid.End.{u1} A _inst_1) (MulOneClass.toHasOne.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toMulOneClass.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1))))))) (coeFn.{succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) (fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => A) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.addMonoidHomClass.{u1} A _inst_1)))) (OfNat.ofNat.{u1} (AddMonoid.End.{u1} A _inst_1) 1 (OfNat.mk.{u1} (AddMonoid.End.{u1} A _inst_1) 1 (One.one.{u1} (AddMonoid.End.{u1} A _inst_1) (MulOneClass.toHasOne.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toMulOneClass.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1))))))) (id.{succ u1} A)
but is expected to have type
  forall (A : Type.{u1}) [_inst_1 : AddZeroClass.{u1} A], Eq.{succ u1} (forall (a : A), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) a) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toAdd.{u1} A _inst_1) (AddZeroClass.toAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.instAddMonoidHomClassEnd.{u1} A _inst_1))) (OfNat.ofNat.{u1} (AddMonoid.End.{u1} A _inst_1) 1 (One.toOfNat1.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toOne.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1))))) (id.{succ u1} A)
Case conversion may be inaccurate. Consider using '#align add_monoid.coe_one AddMonoid.coe_oneₓ'. -/
@[simp]
theorem coe_one : ((1 : AddMonoid.End A) : A → A) = id :=
  rfl
#align add_monoid.coe_one AddMonoid.coe_one

/- warning: add_monoid.coe_mul -> AddMonoid.coe_mul is a dubious translation:
lean 3 declaration is
  forall (A : Type.{u1}) [_inst_1 : AddZeroClass.{u1} A] (f : AddMonoid.End.{u1} A _inst_1) (g : AddMonoid.End.{u1} A _inst_1), Eq.{succ u1} ((fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (HMul.hMul.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (instHMul.{u1} (AddMonoid.End.{u1} A _inst_1) (MulOneClass.toHasMul.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toMulOneClass.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1)))) f g)) (coeFn.{succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) (fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => A) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.addMonoidHomClass.{u1} A _inst_1)))) (HMul.hMul.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (instHMul.{u1} (AddMonoid.End.{u1} A _inst_1) (MulOneClass.toHasMul.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toMulOneClass.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1)))) f g)) (Function.comp.{succ u1, succ u1, succ u1} A A A (coeFn.{succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) (fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => A) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.addMonoidHomClass.{u1} A _inst_1)))) f) (coeFn.{succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) (fun (_x : AddMonoid.End.{u1} A _inst_1) => A -> A) (FunLike.hasCoeToFun.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => A) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddZeroClass.toHasAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.addMonoidHomClass.{u1} A _inst_1)))) g))
but is expected to have type
  forall (A : Type.{u1}) [_inst_1 : AddZeroClass.{u1} A] (f : AddMonoid.End.{u1} A _inst_1) (g : AddMonoid.End.{u1} A _inst_1), Eq.{succ u1} (forall (a : A), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) a) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toAdd.{u1} A _inst_1) (AddZeroClass.toAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.instAddMonoidHomClassEnd.{u1} A _inst_1))) (HMul.hMul.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.{u1} A _inst_1) (instHMul.{u1} (AddMonoid.End.{u1} A _inst_1) (MulOneClass.toMul.{u1} (AddMonoid.End.{u1} A _inst_1) (Monoid.toMulOneClass.{u1} (AddMonoid.End.{u1} A _inst_1) (AddMonoid.End.monoid.{u1} A _inst_1)))) f g)) (Function.comp.{succ u1, succ u1, succ u1} A A A (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toAdd.{u1} A _inst_1) (AddZeroClass.toAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.instAddMonoidHomClassEnd.{u1} A _inst_1))) f) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoid.End.{u1} A _inst_1) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : A) => A) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A (AddZeroClass.toAdd.{u1} A _inst_1) (AddZeroClass.toAdd.{u1} A _inst_1) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoid.End.{u1} A _inst_1) A A _inst_1 _inst_1 (AddMonoid.End.instAddMonoidHomClassEnd.{u1} A _inst_1))) g))
Case conversion may be inaccurate. Consider using '#align add_monoid.coe_mul AddMonoid.coe_mulₓ'. -/
@[simp]
theorem coe_mul (f g) : ((f * g : AddMonoid.End A) : A → A) = f ∘ g :=
  rfl
#align add_monoid.coe_mul AddMonoid.coe_mul

end AddMonoid

end End

/-- `1` is the homomorphism sending all elements to `1`. -/
@[to_additive]
instance [One M] [One N] : One (OneHom M N) :=
  ⟨⟨fun _ => 1, rfl⟩⟩

/-- `1` is the multiplicative homomorphism sending all elements to `1`. -/
@[to_additive]
instance [Mul M] [MulOneClass N] : One (M →ₙ* N) :=
  ⟨⟨fun _ => 1, fun _ _ => (one_mul 1).symm⟩⟩

/-- `1` is the monoid homomorphism sending all elements to `1`. -/
@[to_additive]
instance [MulOneClass M] [MulOneClass N] : One (M →* N) :=
  ⟨⟨fun _ => 1, rfl, fun _ _ => (one_mul 1).symm⟩⟩

/-- `0` is the homomorphism sending all elements to `0`. -/
add_decl_doc ZeroHom.hasZero

/-- `0` is the additive homomorphism sending all elements to `0`. -/
add_decl_doc AddHom.hasZero

/-- `0` is the additive monoid homomorphism sending all elements to `0`. -/
add_decl_doc AddMonoidHom.hasZero

/- warning: one_hom.one_apply -> OneHom.one_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (OneHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : OneHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (OneHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (OfNat.ofNat.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) 1 (OfNat.mk.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) 1 (One.one.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.hasOne.{u1, u2} M N _inst_1 _inst_2)))) x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : One.{u2} M] [_inst_2 : One.{u1} N] (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) _x) (OneHomClass.toFunLike.{max u2 u1, u2, u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (OneHom.oneHomClass.{u2, u1} M N _inst_1 _inst_2)) (OfNat.ofNat.{max u2 u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) 1 (One.toOfNat1.{max u2 u1} (OneHom.{u2, u1} M N _inst_1 _inst_2) (instOneOneHom.{u2, u1} M N _inst_1 _inst_2))) x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.1254 : M) => N) x) _inst_2))
Case conversion may be inaccurate. Consider using '#align one_hom.one_apply OneHom.one_applyₓ'. -/
@[simp, to_additive]
theorem OneHom.one_apply [One M] [One N] (x : M) : (1 : OneHom M N) x = 1 :=
  rfl
#align one_hom.one_apply OneHom.one_apply
#align zero_hom.zero_apply ZeroHom.zero_apply

/- warning: monoid_hom.one_apply -> MonoidHom.one_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (OfNat.mk.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) 1 (One.one.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_1 _inst_2) (MonoidHom.hasOne.{u1, u2} M N _inst_1 _inst_2)))) x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_2))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u1} N] (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_2) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_2))) (OfNat.ofNat.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) 1 (One.toOfNat1.{max u2 u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_2) (instOneMonoidHom.{u2, u1} M N _inst_1 _inst_2))) x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) _inst_2)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.one_apply MonoidHom.one_applyₓ'. -/
@[simp, to_additive]
theorem MonoidHom.one_apply [MulOneClass M] [MulOneClass N] (x : M) : (1 : M →* N) x = 1 :=
  rfl
#align monoid_hom.one_apply MonoidHom.one_apply
#align add_monoid_hom.zero_apply AddMonoidHom.zero_apply

/- warning: one_hom.one_comp -> OneHom.one_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] (f : OneHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u3 u2} (OneHom.{u2, u3} N P _inst_2 _inst_3) 1 (OfNat.mk.{max u3 u2} (OneHom.{u2, u3} N P _inst_2 _inst_3) 1 (One.one.{max u3 u2} (OneHom.{u2, u3} N P _inst_2 _inst_3) (OneHom.hasOne.{u2, u3} N P _inst_2 _inst_3)))) f) (OfNat.ofNat.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) 1 (OfNat.mk.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) 1 (One.one.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.hasOne.{u1, u3} M P _inst_1 _inst_3))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] (f : OneHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (OneHom.{u3, u1} M P _inst_1 _inst_3) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u2 u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) 1 (One.toOfNat1.{max u2 u1} (OneHom.{u2, u1} N P _inst_2 _inst_3) (instOneOneHom.{u2, u1} N P _inst_2 _inst_3))) f) (OfNat.ofNat.{max u3 u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) 1 (One.toOfNat1.{max u3 u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) (instOneOneHom.{u3, u1} M P _inst_1 _inst_3)))
Case conversion may be inaccurate. Consider using '#align one_hom.one_comp OneHom.one_compₓ'. -/
@[simp, to_additive]
theorem OneHom.one_comp [One M] [One N] [One P] (f : OneHom M N) : (1 : OneHom N P).comp f = 1 :=
  rfl
#align one_hom.one_comp OneHom.one_comp
#align zero_hom.zero_comp ZeroHom.zero_comp

/- warning: one_hom.comp_one -> OneHom.comp_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : One.{u1} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u3} P] (f : OneHom.{u2, u3} N P _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 f (OfNat.ofNat.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) 1 (OfNat.mk.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) 1 (One.one.{max u2 u1} (OneHom.{u1, u2} M N _inst_1 _inst_2) (OneHom.hasOne.{u1, u2} M N _inst_1 _inst_2))))) (OfNat.ofNat.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) 1 (OfNat.mk.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) 1 (One.one.{max u3 u1} (OneHom.{u1, u3} M P _inst_1 _inst_3) (OneHom.hasOne.{u1, u3} M P _inst_1 _inst_3))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : One.{u3} M] [_inst_2 : One.{u2} N] [_inst_3 : One.{u1} P] (f : OneHom.{u2, u1} N P _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} (OneHom.{u3, u1} M P _inst_1 _inst_3) (OneHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 f (OfNat.ofNat.{max u3 u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) 1 (One.toOfNat1.{max u3 u2} (OneHom.{u3, u2} M N _inst_1 _inst_2) (instOneOneHom.{u3, u2} M N _inst_1 _inst_2)))) (OfNat.ofNat.{max u3 u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) 1 (One.toOfNat1.{max u3 u1} (OneHom.{u3, u1} M P _inst_1 _inst_3) (instOneOneHom.{u3, u1} M P _inst_1 _inst_3)))
Case conversion may be inaccurate. Consider using '#align one_hom.comp_one OneHom.comp_oneₓ'. -/
@[simp, to_additive]
theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 :=
  by
  ext
  simp only [OneHom.map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]
#align one_hom.comp_one OneHom.comp_one
#align zero_hom.comp_zero ZeroHom.comp_zero

@[to_additive]
instance [One M] [One N] : Inhabited (OneHom M N) :=
  ⟨1⟩

@[to_additive]
instance [Mul M] [MulOneClass N] : Inhabited (M →ₙ* N) :=
  ⟨1⟩

@[to_additive]
instance [MulOneClass M] [MulOneClass N] : Inhabited (M →* N) :=
  ⟨1⟩

-- unlike the other homs, `monoid_with_zero_hom` does not have a `1` or `0`
instance [MulZeroOneClass M] : Inhabited (M →*₀ M) :=
  ⟨MonoidWithZeroHom.id M⟩

namespace MulHom

/-- Given two mul morphisms `f`, `g` to a commutative semigroup, `f * g` is the mul morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance [Mul M] [CommSemigroup N] : Mul (M →ₙ* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m
      map_mul' := by
        intros ; show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive morphisms `f`, `g` to an additive commutative semigroup, `f + g` is the
additive morphism sending `x` to `f x + g x`. -/
add_decl_doc AddHom.hasAdd

/- warning: mul_hom.mul_apply -> MulHom.mul_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : Mul.{u1} M} {mN : CommSemigroup.{u2} N} (f : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (g : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (instHMul.{max u2 u1} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (MulHom.hasMul.{u1, u2} M N mM mN)) f g) x) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {mM : Mul.{u2} M} {mN : CommSemigroup.{u1} N} (f : MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (g : MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (instHMul.{max u2 u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (MulHom.instMulMulHomToMulToSemigroup.{u2, u1} M N mM mN)) f g) x) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (Semigroup.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (CommSemigroup.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) g x))
Case conversion may be inaccurate. Consider using '#align mul_hom.mul_apply MulHom.mul_applyₓ'. -/
@[simp, to_additive]
theorem mul_apply {M N} {mM : Mul M} {mN : CommSemigroup N} (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x :=
  rfl
#align mul_hom.mul_apply MulHom.mul_apply
#align add_hom.add_apply AddHom.add_apply

/- warning: mul_hom.mul_comp -> MulHom.mul_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u3} P] (g₁ : MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (g₂ : MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (f : MulHom.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) (HMul.hMul.{max u3 u2, max u3 u2, max u3 u2} (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (instHMul.{max u3 u2} (MulHom.{u2, u3} N P _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.hasMul.{u2, u3} N P _inst_2 _inst_3)) g₁ g₂) f) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (instHMul.{max u3 u1} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.hasMul.{u1, u3} M P _inst_1 _inst_3)) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) g₁ f) (MulHom.comp.{u1, u2, u3} M N P _inst_1 _inst_2 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) g₂ f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : CommSemigroup.{u1} P] (g₁ : MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (g₂ : MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (f : MulHom.{u3, u2} M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u1)} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (instHMul.{max u2 u1} (MulHom.{u2, u1} N P _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.instMulMulHomToMulToSemigroup.{u2, u1} N P _inst_2 _inst_3)) g₁ g₂) f) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (instHMul.{max u3 u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.instMulMulHomToMulToSemigroup.{u3, u1} M P _inst_1 _inst_3)) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) g₁ f) (MulHom.comp.{u3, u2, u1} M N P _inst_1 _inst_2 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) g₂ f))
Case conversion may be inaccurate. Consider using '#align mul_hom.mul_comp MulHom.mul_compₓ'. -/
@[to_additive]
theorem mul_comp [Mul M] [Mul N] [CommSemigroup P] (g₁ g₂ : N →ₙ* P) (f : M →ₙ* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
#align mul_hom.mul_comp MulHom.mul_comp
#align add_hom.add_comp AddHom.add_comp

/- warning: mul_hom.comp_mul -> MulHom.comp_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : CommSemigroup.{u2} N] [_inst_3 : CommSemigroup.{u3} P] (g : MulHom.{u2, u3} N P (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (f₁ : MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (f₂ : MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))), Eq.{max (succ u3) (succ u1)} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.comp.{u1, u2, u3} M N P _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) g (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (instHMul.{max u2 u1} (MulHom.{u1, u2} M N _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.hasMul.{u1, u2} M N _inst_1 _inst_2)) f₁ f₂)) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (instHMul.{max u3 u1} (MulHom.{u1, u3} M P _inst_1 (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3))) (MulHom.hasMul.{u1, u3} M P _inst_1 _inst_3)) (MulHom.comp.{u1, u2, u3} M N P _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) g f₁) (MulHom.comp.{u1, u2, u3} M N P _inst_1 (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toHasMul.{u3} P (CommSemigroup.toSemigroup.{u3} P _inst_3)) g f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : CommSemigroup.{u2} N] [_inst_3 : CommSemigroup.{u1} P] (g : MulHom.{u2, u1} N P (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (f₁ : MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (f₂ : MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))), Eq.{max (succ u3) (succ u1)} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.comp.{u3, u2, u1} M N P _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) g (HMul.hMul.{max u3 u2, max u3 u2, max u3 u2} (MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (instHMul.{max u3 u2} (MulHom.{u3, u2} M N _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2))) (MulHom.instMulMulHomToMulToSemigroup.{u3, u2} M N _inst_1 _inst_2)) f₁ f₂)) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (instHMul.{max u3 u1} (MulHom.{u3, u1} M P _inst_1 (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3))) (MulHom.instMulMulHomToMulToSemigroup.{u3, u1} M P _inst_1 _inst_3)) (MulHom.comp.{u3, u2, u1} M N P _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) g f₁) (MulHom.comp.{u3, u2, u1} M N P _inst_1 (Semigroup.toMul.{u2} N (CommSemigroup.toSemigroup.{u2} N _inst_2)) (Semigroup.toMul.{u1} P (CommSemigroup.toSemigroup.{u1} P _inst_3)) g f₂))
Case conversion may be inaccurate. Consider using '#align mul_hom.comp_mul MulHom.comp_mulₓ'. -/
@[to_additive]
theorem comp_mul [Mul M] [CommSemigroup N] [CommSemigroup P] (g : N →ₙ* P) (f₁ f₂ : M →ₙ* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]
#align mul_hom.comp_mul MulHom.comp_mul
#align add_hom.comp_add AddHom.comp_add

end MulHom

namespace MonoidHom

variable [mM : MulOneClass M] [mN : MulOneClass N] [mP : MulOneClass P]

variable [Group G] [CommGroup H]

/-- Given two monoid morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid morphism
sending `x` to `f x * g x`. -/
@[to_additive]
instance {M N} {mM : MulOneClass M} [CommMonoid N] : Mul (M →* N) :=
  ⟨fun f g =>
    { toFun := fun m => f m * g m
      map_one' := show f 1 * g 1 = 1 by simp
      map_mul' := by
        intros ; show f (x * y) * g (x * y) = f x * g x * (f y * g y)
        rw [f.map_mul, g.map_mul, ← mul_assoc, ← mul_assoc, mul_right_comm (f x)] }⟩

/-- Given two additive monoid morphisms `f`, `g` to an additive commutative monoid, `f + g` is the
additive monoid morphism sending `x` to `f x + g x`. -/
add_decl_doc AddMonoidHom.hasAdd

/- warning: monoid_hom.mul_apply -> MonoidHom.mul_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : MulOneClass.{u1} M} {mN : CommMonoid.{u2} N} (f : MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (g : MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (x : M), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (fun (_x : MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (instHMul.{max u2 u1} (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (MonoidHom.hasMul.{u1, u2} M N mM mN)) f g) x) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN)))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (fun (_x : MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) (fun (_x : MonoidHom.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N mM (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N mN))) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {mM : MulOneClass.{u2} M} {mN : CommMonoid.{u1} N} (f : MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (g : MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN)) (MonoidHom.monoidHomClass.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (instHMul.{max u2 u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHom.mul.{u2, u1} M N mM mN)) f g) x) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) (CommMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) x) mN)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN)) (MonoidHom.monoidHomClass.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))) M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN)) (MonoidHom.monoidHomClass.{u2, u1} M N mM (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N mN))))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mul_apply MonoidHom.mul_applyₓ'. -/
@[simp, to_additive]
theorem mul_apply {M N} {mM : MulOneClass M} {mN : CommMonoid N} (f g : M →* N) (x : M) :
    (f * g) x = f x * g x :=
  rfl
#align monoid_hom.mul_apply MonoidHom.mul_apply
#align add_monoid_hom.add_apply AddMonoidHom.add_apply

/- warning: monoid_hom.one_comp -> MonoidHom.one_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_3 : MulOneClass.{u1} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : MulOneClass.{u3} P] (f : MonoidHom.{u1, u2} M N _inst_3 _inst_4), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 _inst_4 _inst_5 (OfNat.ofNat.{max u3 u2} (MonoidHom.{u2, u3} N P _inst_4 _inst_5) 1 (OfNat.mk.{max u3 u2} (MonoidHom.{u2, u3} N P _inst_4 _inst_5) 1 (One.one.{max u3 u2} (MonoidHom.{u2, u3} N P _inst_4 _inst_5) (MonoidHom.hasOne.{u2, u3} N P _inst_4 _inst_5)))) f) (OfNat.ofNat.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) 1 (OfNat.mk.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) 1 (One.one.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) (MonoidHom.hasOne.{u1, u3} M P _inst_3 _inst_5))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_3 : MulOneClass.{u3} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : MulOneClass.{u1} P] (f : MonoidHom.{u3, u2} M N _inst_3 _inst_4), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 _inst_4 _inst_5 (OfNat.ofNat.{max u2 u1} (MonoidHom.{u2, u1} N P _inst_4 _inst_5) 1 (One.toOfNat1.{max u2 u1} (MonoidHom.{u2, u1} N P _inst_4 _inst_5) (instOneMonoidHom.{u2, u1} N P _inst_4 _inst_5))) f) (OfNat.ofNat.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) 1 (One.toOfNat1.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) (instOneMonoidHom.{u3, u1} M P _inst_3 _inst_5)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.one_comp MonoidHom.one_compₓ'. -/
@[simp, to_additive]
theorem one_comp [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : M →* N) :
    (1 : N →* P).comp f = 1 :=
  rfl
#align monoid_hom.one_comp MonoidHom.one_comp
#align add_monoid_hom.zero_comp AddMonoidHom.zero_comp

/- warning: monoid_hom.comp_one -> MonoidHom.comp_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_3 : MulOneClass.{u1} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : MulOneClass.{u3} P] (f : MonoidHom.{u2, u3} N P _inst_4 _inst_5), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 _inst_4 _inst_5 f (OfNat.ofNat.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_3 _inst_4) 1 (OfNat.mk.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_3 _inst_4) 1 (One.one.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_3 _inst_4) (MonoidHom.hasOne.{u1, u2} M N _inst_3 _inst_4))))) (OfNat.ofNat.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) 1 (OfNat.mk.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) 1 (One.one.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 _inst_5) (MonoidHom.hasOne.{u1, u3} M P _inst_3 _inst_5))))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_3 : MulOneClass.{u3} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : MulOneClass.{u1} P] (f : MonoidHom.{u2, u1} N P _inst_4 _inst_5), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 _inst_4 _inst_5 f (OfNat.ofNat.{max u3 u2} (MonoidHom.{u3, u2} M N _inst_3 _inst_4) 1 (One.toOfNat1.{max u3 u2} (MonoidHom.{u3, u2} M N _inst_3 _inst_4) (instOneMonoidHom.{u3, u2} M N _inst_3 _inst_4)))) (OfNat.ofNat.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) 1 (One.toOfNat1.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 _inst_5) (instOneMonoidHom.{u3, u1} M P _inst_3 _inst_5)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_one MonoidHom.comp_oneₓ'. -/
@[simp, to_additive]
theorem comp_one [MulOneClass M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]
#align monoid_hom.comp_one MonoidHom.comp_one
#align add_monoid_hom.comp_zero AddMonoidHom.comp_zero

/- warning: monoid_hom.mul_comp -> MonoidHom.mul_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_3 : MulOneClass.{u1} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : CommMonoid.{u3} P] (g₁ : MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (g₂ : MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (f : MonoidHom.{u1, u2} M N _inst_3 _inst_4), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) (HMul.hMul.{max u3 u2, max u3 u2, max u3 u2} (MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (instHMul.{max u3 u2} (MonoidHom.{u2, u3} N P _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.hasMul.{u2, u3} N P _inst_4 _inst_5)) g₁ g₂) f) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (instHMul.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.hasMul.{u1, u3} M P _inst_3 _inst_5)) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) g₁ f) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) g₂ f))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_3 : MulOneClass.{u3} M] [_inst_4 : MulOneClass.{u2} N] [_inst_5 : CommMonoid.{u1} P] (g₁ : MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (g₂ : MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (f : MonoidHom.{u3, u2} M N _inst_3 _inst_4), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (instHMul.{max u2 u1} (MonoidHom.{u2, u1} N P _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.mul.{u2, u1} N P _inst_4 _inst_5)) g₁ g₂) f) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (instHMul.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.mul.{u3, u1} M P _inst_3 _inst_5)) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) g₁ f) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 _inst_4 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) g₂ f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mul_comp MonoidHom.mul_compₓ'. -/
@[to_additive]
theorem mul_comp [MulOneClass M] [MulOneClass N] [CommMonoid P] (g₁ g₂ : N →* P) (f : M →* N) :
    (g₁ * g₂).comp f = g₁.comp f * g₂.comp f :=
  rfl
#align monoid_hom.mul_comp MonoidHom.mul_comp
#align add_monoid_hom.add_comp AddMonoidHom.add_comp

/- warning: monoid_hom.comp_mul -> MonoidHom.comp_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_3 : MulOneClass.{u1} M] [_inst_4 : CommMonoid.{u2} N] [_inst_5 : CommMonoid.{u3} P] (g : MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (f₁ : MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (f₂ : MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) g (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (instHMul.{max u2 u1} (MonoidHom.{u1, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.hasMul.{u1, u2} M N _inst_3 _inst_4)) f₁ f₂)) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (instHMul.{max u3 u1} (MonoidHom.{u1, u3} M P _inst_3 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5))) (MonoidHom.hasMul.{u1, u3} M P _inst_3 _inst_5)) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) g f₁) (MonoidHom.comp.{u1, u2, u3} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_5)) g f₂))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_3 : MulOneClass.{u3} M] [_inst_4 : CommMonoid.{u2} N] [_inst_5 : CommMonoid.{u1} P] (g : MonoidHom.{u2, u1} N P (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (f₁ : MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (f₂ : MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) g (HMul.hMul.{max u3 u2, max u3 u2, max u3 u2} (MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (instHMul.{max u3 u2} (MonoidHom.{u3, u2} M N _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4))) (MonoidHom.mul.{u3, u2} M N _inst_3 _inst_4)) f₁ f₂)) (HMul.hMul.{max u3 u1, max u3 u1, max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (instHMul.{max u3 u1} (MonoidHom.{u3, u1} M P _inst_3 (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5))) (MonoidHom.mul.{u3, u1} M P _inst_3 _inst_5)) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) g f₁) (MonoidHom.comp.{u3, u2, u1} M N P _inst_3 (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N _inst_4)) (Monoid.toMulOneClass.{u1} P (CommMonoid.toMonoid.{u1} P _inst_5)) g f₂))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_mul MonoidHom.comp_mulₓ'. -/
@[to_additive]
theorem comp_mul [MulOneClass M] [CommMonoid N] [CommMonoid P] (g : N →* P) (f₁ f₂ : M →* N) :
    g.comp (f₁ * f₂) = g.comp f₁ * g.comp f₂ := by
  ext
  simp only [mul_apply, Function.comp_apply, map_mul, coe_comp]
#align monoid_hom.comp_mul MonoidHom.comp_mul
#align add_monoid_hom.comp_add AddMonoidHom.comp_add

/- warning: monoid_hom.map_inv -> MonoidHom.map_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : DivisionMonoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (a : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a)) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u1} β] (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_3)))) a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f (Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_3)))) a)) (Inv.inv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) a) (InvOneClass.toInv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) a) (DivInvOneMonoid.toInvOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) a) (DivisionMonoid.toDivInvOneMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) a) _inst_4))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f a))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_inv MonoidHom.map_invₓ'. -/
/-- Group homomorphisms preserve inverse. -/
@[to_additive "Additive group homomorphisms preserve negation."]
protected theorem map_inv [Group α] [DivisionMonoid β] (f : α →* β) (a : α) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f _
#align monoid_hom.map_inv MonoidHom.map_inv
#align add_monoid_hom.map_neg AddMonoidHom.map_neg

/- warning: monoid_hom.map_zpow -> MonoidHom.map_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : DivisionMonoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (g : α) (n : Int), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) g n)) (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f g) n)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u1} β] (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (g : α) (n : Int), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (HPow.hPow.{u2, 0, u2} α Int α (instHPow.{u2, 0} α Int (DivInvMonoid.Pow.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) g n)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f (HPow.hPow.{u2, 0, u2} α Int α (instHPow.{u2, 0} α Int (DivInvMonoid.Pow.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) g n)) (HPow.hPow.{u1, 0, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) Int ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (instHPow.{u1, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) Int (DivInvMonoid.Pow.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (DivisionMonoid.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) _inst_4))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f g) n)
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_zpow MonoidHom.map_zpowₓ'. -/
/-- Group homomorphisms preserve integer power. -/
@[to_additive "Additive group homomorphisms preserve integer scaling."]
protected theorem map_zpow [Group α] [DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ) :
    f (g ^ n) = f g ^ n :=
  map_zpow f g n
#align monoid_hom.map_zpow MonoidHom.map_zpow
#align add_monoid_hom.map_zsmul AddMonoidHom.map_zsmul

/- warning: monoid_hom.map_div -> MonoidHom.map_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : DivisionMonoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (g : α) (h : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) g h)) (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u1} β] (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (g : α) (h : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) g h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) g h)) (HDiv.hDiv.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (instHDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (DivInvMonoid.toDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (DivisionMonoid.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) _inst_4))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f g) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f h))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_div MonoidHom.map_divₓ'. -/
/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_div [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g / h) = f g / f h :=
  map_div f g h
#align monoid_hom.map_div MonoidHom.map_div
#align add_monoid_hom.map_sub AddMonoidHom.map_sub

/- warning: monoid_hom.map_mul_inv -> MonoidHom.map_mul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_3 : Group.{u1} α] [_inst_4 : DivisionMonoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (g : α) (h : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) g (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) h))) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f g) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))) (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (DivisionMonoid.toDivInvMonoid.{u2} β _inst_4)))) f h)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u1} β] (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (g : α) (h : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))))) g (Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_3)))) h))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))))) g (Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (Group.toDivisionMonoid.{u2} α _inst_3)))) h))) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (MulOneClass.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (DivInvMonoid.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) (DivisionMonoid.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) g) _inst_4))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f g) (Inv.inv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) (InvOneClass.toInv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) (DivInvOneMonoid.toInvOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) (DivisionMonoid.toDivInvOneMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) h) _inst_4))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))) α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u1} β (DivInvMonoid.toMonoid.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β _inst_4)))))) f h)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_mul_inv MonoidHom.map_mul_invₓ'. -/
/-- Group homomorphisms preserve division. -/
@[to_additive "Additive group homomorphisms preserve subtraction."]
protected theorem map_mul_inv [Group α] [DivisionMonoid β] (f : α →* β) (g h : α) :
    f (g * h⁻¹) = f g * (f h)⁻¹ :=
  map_mul_inv f g h
#align monoid_hom.map_mul_inv MonoidHom.map_mul_inv
#align add_monoid_hom.map_add_neg AddMonoidHom.map_add_neg

/- warning: injective_iff_map_eq_one -> injective_iff_map_eq_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {G : Type.{u2}} {H : Type.{u3}} [_inst_3 : Group.{u2} G] [_inst_4 : MulOneClass.{u3} H] [_inst_5 : MonoidHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4] (f : F), Iff (Function.Injective.{succ u2, succ u3} G H (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u1, u2, u3} F G H (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4 _inst_5))) f)) (forall (a : G), (Eq.{succ u3} H (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u1, u2, u3} F G H (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4 _inst_5))) f a) (OfNat.ofNat.{u3} H 1 (OfNat.mk.{u3} H 1 (One.one.{u3} H (MulOneClass.toHasOne.{u3} H _inst_4))))) -> (Eq.{succ u2} G a (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))))))))
but is expected to have type
  forall {F : Type.{u1}} {G : Type.{u3}} {H : Type.{u2}} [_inst_3 : Group.{u3} G] [_inst_4 : MulOneClass.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4] (f : F), Iff (Function.Injective.{succ u3, succ u2} G H (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4 _inst_5)) f)) (forall (a : G), (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4 _inst_5)) f a) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)))) -> (Eq.{succ u3} G a (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3))))))))
Case conversion may be inaccurate. Consider using '#align injective_iff_map_eq_one injective_iff_map_eq_oneₓ'. -/
/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial.
For the iff statement on the triviality of the kernel, see `injective_iff_map_eq_one'`.  -/
@[to_additive
      "A homomorphism from an additive group to an additive monoid is injective iff\nits kernel is trivial. For the iff statement on the triviality of the kernel,\nsee `injective_iff_map_eq_zero'`."]
theorem injective_iff_map_eq_one {G H} [Group G] [MulOneClass H] [MonoidHomClass F G H] (f : F) :
    Function.Injective f ↔ ∀ a, f a = 1 → a = 1 :=
  ⟨fun h x => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_self, map_one]⟩
#align injective_iff_map_eq_one injective_iff_map_eq_one
#align injective_iff_map_eq_zero injective_iff_map_eq_zero

/- warning: injective_iff_map_eq_one' -> injective_iff_map_eq_one' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {G : Type.{u2}} {H : Type.{u3}} [_inst_3 : Group.{u2} G] [_inst_4 : MulOneClass.{u3} H] [_inst_5 : MonoidHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4] (f : F), Iff (Function.Injective.{succ u2, succ u3} G H (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u1, u2, u3} F G H (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4 _inst_5))) f)) (forall (a : G), Iff (Eq.{succ u3} H (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => G -> H) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F G (fun (_x : G) => H) (MulHomClass.toFunLike.{u1, u2, u3} F G H (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) _inst_4 _inst_5))) f a) (OfNat.ofNat.{u3} H 1 (OfNat.mk.{u3} H 1 (One.one.{u3} H (MulOneClass.toHasOne.{u3} H _inst_4))))) (Eq.{succ u2} G a (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))))))))
but is expected to have type
  forall {F : Type.{u1}} {G : Type.{u3}} {H : Type.{u2}} [_inst_3 : Group.{u3} G] [_inst_4 : MulOneClass.{u2} H] [_inst_5 : MonoidHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4] (f : F), Iff (Function.Injective.{succ u3, succ u2} G H (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4 _inst_5)) f)) (forall (a : G), Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (FunLike.coe.{succ u1, succ u3, succ u2} F G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{u1, u3, u2} F G H (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} H _inst_4) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F G H (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) _inst_4 _inst_5)) f a) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) a) _inst_4)))) (Eq.{succ u3} G a (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3))))))))
Case conversion may be inaccurate. Consider using '#align injective_iff_map_eq_one' injective_iff_map_eq_one'ₓ'. -/
/-- A homomorphism from a group to a monoid is injective iff its kernel is trivial,
stated as an iff on the triviality of the kernel.
For the implication, see `injective_iff_map_eq_one`. -/
@[to_additive
      "A homomorphism from an additive group to an additive monoid is injective iff its\nkernel is trivial, stated as an iff on the triviality of the kernel. For the implication, see\n`injective_iff_map_eq_zero`."]
theorem injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H] [MonoidHomClass F G H] (f : F) :
    Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 :=
  (injective_iff_map_eq_one f).trans <|
    forall_congr' fun a => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩
#align injective_iff_map_eq_one' injective_iff_map_eq_one'
#align injective_iff_map_eq_zero' injective_iff_map_eq_zero'

include mM

/- warning: monoid_hom.mk' -> MonoidHom.mk' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {G : Type.{u2}} [mM : MulOneClass.{u1} M] [_inst_1 : Group.{u2} G] (f : M -> G), (forall (a : M) (b : M), Eq.{succ u2} G (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M mM)) a b)) (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))) (f a) (f b))) -> (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))
but is expected to have type
  forall {M : Type.{u1}} {G : Type.{u2}} [mM : Group.{u2} G] [_inst_1 : MulOneClass.{u1} M] (f : M -> G), (forall (a : M) (b : M), Eq.{succ u2} G (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b)) (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G mM))))) (f a) (f b))) -> (MonoidHom.{u1, u2} M G _inst_1 (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G mM))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.mk' MonoidHom.mk'ₓ'. -/
/-- Makes a group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive "Makes an additive group homomorphism from a proof that the map preserves addition.",
  simps (config := { fullyApplied := false })]
def mk' (f : M → G) (map_mul : ∀ a b : M, f (a * b) = f a * f b) : M →* G
    where
  toFun := f
  map_mul' := map_mul
  map_one' := mul_left_eq_self.1 <| by rw [← map_mul, mul_one]
#align monoid_hom.mk' MonoidHom.mk'
#align add_monoid_hom.mk' AddMonoidHom.mk'

omit mM

/- warning: monoid_hom.of_map_mul_inv -> MonoidHom.ofMapMulInv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H), (forall (a : G) (b : G), Eq.{succ u2} H (f (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b))) (HMul.hMul.{u2, u2, u2} H H H (instHMul.{u2} H (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))) (f a) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) (f b)))) -> (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H), (forall (a : G) (b : G), Eq.{succ u2} H (f (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b))) (HMul.hMul.{u2, u2, u2} H H H (instHMul.{u2} H (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))) (f a) (Inv.inv.{u2} H (InvOneClass.toInv.{u2} H (DivInvOneMonoid.toInvOneClass.{u2} H (DivisionMonoid.toDivInvOneMonoid.{u2} H (Group.toDivisionMonoid.{u2} H _inst_3)))) (f b)))) -> (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.of_map_mul_inv MonoidHom.ofMapMulInvₓ'. -/
/-- Makes a group homomorphism from a proof that the map preserves right division `λ x y, x * y⁻¹`.
See also `monoid_hom.of_map_div` for a version using `λ x y, x / y`.
-/
@[to_additive
      "Makes an additive group homomorphism from a proof that the map preserves\nthe operation `λ a b, a + -b`. See also `add_monoid_hom.of_map_sub` for a version using\n`λ a b, a - b`."]
def ofMapMulInv {H : Type _} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : G →* H :=
  mk' f fun x y =>
    calc
      f (x * y) = f x * (f <| 1 * 1⁻¹ * y⁻¹)⁻¹ := by
        simp only [one_mul, inv_one, ← map_div, inv_inv]
      _ = f x * f y := by
        simp only [map_div]
        simp only [mul_right_inv, one_mul, inv_inv]
      
#align monoid_hom.of_map_mul_inv MonoidHom.ofMapMulInv
#align add_monoid_hom.of_map_add_neg AddMonoidHom.ofMapAddNeg

/- warning: monoid_hom.coe_of_map_mul_inv -> MonoidHom.coe_of_map_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H) (map_div : forall (a : G) (b : G), Eq.{succ u2} H (f (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b))) (HMul.hMul.{u2, u2, u2} H H H (instHMul.{u2} H (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))) (f a) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)) (f b)))), Eq.{max (succ u1) (succ u2)} (G -> H) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (MonoidHom.ofMapMulInv.{u1, u2} G _inst_1 H _inst_3 f map_div)) f
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H) (map_div : forall (a : G) (b : G), Eq.{succ u2} H (f (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b))) (HMul.hMul.{u2, u2, u2} H H H (instHMul.{u2} H (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))) (f a) (Inv.inv.{u2} H (InvOneClass.toInv.{u2} H (DivInvOneMonoid.toInvOneClass.{u2} H (DivisionMonoid.toDivInvOneMonoid.{u2} H (Group.toDivisionMonoid.{u2} H _inst_3)))) (f b)))), Eq.{max (succ u1) (succ u2)} (G -> H) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))))) (MonoidHom.ofMapMulInv.{u1, u2} G _inst_1 H _inst_3 f map_div)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_of_map_mul_inv MonoidHom.coe_of_map_mul_invₓ'. -/
@[simp, to_additive]
theorem coe_of_map_mul_inv {H : Type _} [Group H] (f : G → H)
    (map_div : ∀ a b : G, f (a * b⁻¹) = f a * (f b)⁻¹) : ⇑(ofMapMulInv f map_div) = f :=
  rfl
#align monoid_hom.coe_of_map_mul_inv MonoidHom.coe_of_map_mul_inv
#align add_monoid_hom.coe_of_map_add_neg AddMonoidHom.coe_of_map_add_neg

/- warning: monoid_hom.of_map_div -> MonoidHom.ofMapDiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H), (forall (x : G) (y : G), Eq.{succ u2} H (f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x y)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toHasDiv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (f x) (f y))) -> (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H), (forall (x : G) (y : G), Eq.{succ u2} H (f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x y)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toDiv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (f x) (f y))) -> (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.of_map_div MonoidHom.ofMapDivₓ'. -/
/-- Define a morphism of additive groups given a map which respects ratios. -/
@[to_additive "Define a morphism of additive groups given a map which respects difference."]
def ofMapDiv {H : Type _} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) : G →* H :=
  ofMapMulInv f (by simpa only [div_eq_mul_inv] using hf)
#align monoid_hom.of_map_div MonoidHom.ofMapDiv
#align add_monoid_hom.of_map_sub AddMonoidHom.ofMapSub

/- warning: monoid_hom.coe_of_map_div -> MonoidHom.coe_of_map_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H) (hf : forall (x : G) (y : G), Eq.{succ u2} H (f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x y)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toHasDiv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (f x) (f y))), Eq.{max (succ u1) (succ u2)} (G -> H) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (MonoidHom.ofMapDiv.{u1, u2} G _inst_1 H _inst_3 f hf)) f
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] (f : G -> H) (hf : forall (x : G) (y : G), Eq.{succ u2} H (f (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x y)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toDiv.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (f x) (f y))), Eq.{max (succ u1) (succ u2)} (G -> H) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))))) (MonoidHom.ofMapDiv.{u1, u2} G _inst_1 H _inst_3 f hf)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_of_map_div MonoidHom.coe_of_map_divₓ'. -/
@[simp, to_additive]
theorem coe_of_map_div {H : Type _} [Group H] (f : G → H) (hf : ∀ x y, f (x / y) = f x / f y) :
    ⇑(ofMapDiv f hf) = f :=
  rfl
#align monoid_hom.coe_of_map_div MonoidHom.coe_of_map_div
#align add_monoid_hom.coe_of_map_sub AddMonoidHom.coe_of_map_sub

/-- If `f` is a monoid homomorphism to a commutative group, then `f⁻¹` is the homomorphism sending
`x` to `(f x)⁻¹`. -/
@[to_additive]
instance {M G} [MulOneClass M] [CommGroup G] : Inv (M →* G) :=
  ⟨fun f => mk' (fun g => (f g)⁻¹) fun a b => by rw [← mul_inv, f.map_mul]⟩

/-- If `f` is an additive monoid homomorphism to an additive commutative group, then `-f` is the
homomorphism sending `x` to `-(f x)`. -/
add_decl_doc AddMonoidHom.hasNeg

/- warning: monoid_hom.inv_apply -> MonoidHom.inv_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {G : Type.{u2}} {mM : MulOneClass.{u1} M} {gG : CommGroup.{u2} G} (f : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (x : M), Eq.{succ u2} G (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (fun (_x : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) => M -> G) (MonoidHom.hasCoeToFun.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (Inv.inv.{max u2 u1} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (MonoidHom.hasInv.{u1, u2} M G mM gG) f) x) (Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (fun (_x : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) => M -> G) (MonoidHom.hasCoeToFun.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) f x))
but is expected to have type
  forall {M : Type.{u2}} {G : Type.{u1}} {mM : MulOneClass.{u2} M} {gG : CommGroup.{u1} G} (f : MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG)))) (MonoidHom.monoidHomClass.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))))) (Inv.inv.{max u2 u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHom.instInvMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u2, u1} M G mM gG) f) x) (Inv.inv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (InvOneClass.toInv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (DivInvOneMonoid.toInvOneClass.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (DivisionMonoid.toDivInvOneMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (DivisionCommMonoid.toDivisionMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (CommGroup.toDivisionCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) gG))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG)))) (MonoidHom.monoidHomClass.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))))) f x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.inv_apply MonoidHom.inv_applyₓ'. -/
@[simp, to_additive]
theorem inv_apply {M G} {mM : MulOneClass M} {gG : CommGroup G} (f : M →* G) (x : M) :
    f⁻¹ x = (f x)⁻¹ :=
  rfl
#align monoid_hom.inv_apply MonoidHom.inv_apply
#align add_monoid_hom.neg_apply AddMonoidHom.neg_apply

/- warning: monoid_hom.inv_comp -> MonoidHom.inv_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {A : Type.{u3}} {mM : MulOneClass.{u1} M} {gN : MulOneClass.{u2} N} {gA : CommGroup.{u3} A} (φ : MonoidHom.{u2, u3} N A gN (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA))))) (ψ : MonoidHom.{u1, u2} M N mM gN), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M A mM (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA))))) (MonoidHom.comp.{u1, u2, u3} M N A mM gN (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA)))) (Inv.inv.{max u3 u2} (MonoidHom.{u2, u3} N A gN (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA))))) (MonoidHom.hasInv.{u2, u3} N A gN gA) φ) ψ) (Inv.inv.{max u3 u1} (MonoidHom.{u1, u3} M A mM (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA))))) (MonoidHom.hasInv.{u1, u3} M A mM gA) (MonoidHom.comp.{u1, u2, u3} M N A mM gN (Monoid.toMulOneClass.{u3} A (DivInvMonoid.toMonoid.{u3} A (Group.toDivInvMonoid.{u3} A (CommGroup.toGroup.{u3} A gA)))) φ ψ))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {A : Type.{u1}} {mM : MulOneClass.{u3} M} {gN : MulOneClass.{u2} N} {gA : CommGroup.{u1} A} (φ : MonoidHom.{u2, u1} N A gN (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA))))) (ψ : MonoidHom.{u3, u2} M N mM gN), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M A mM (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA))))) (MonoidHom.comp.{u3, u2, u1} M N A mM gN (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA)))) (Inv.inv.{max u2 u1} (MonoidHom.{u2, u1} N A gN (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA))))) (MonoidHom.instInvMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u2, u1} N A gN gA) φ) ψ) (Inv.inv.{max u1 u3} (MonoidHom.{u3, u1} M A mM (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA))))) (MonoidHom.instInvMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u3, u1} M A mM gA) (MonoidHom.comp.{u3, u2, u1} M N A mM gN (Monoid.toMulOneClass.{u1} A (DivInvMonoid.toMonoid.{u1} A (Group.toDivInvMonoid.{u1} A (CommGroup.toGroup.{u1} A gA)))) φ ψ))
Case conversion may be inaccurate. Consider using '#align monoid_hom.inv_comp MonoidHom.inv_compₓ'. -/
@[simp, to_additive]
theorem inv_comp {M N A} {mM : MulOneClass M} {gN : MulOneClass N} {gA : CommGroup A} (φ : N →* A)
    (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, coe_comp]
#align monoid_hom.inv_comp MonoidHom.inv_comp
#align add_monoid_hom.neg_comp AddMonoidHom.neg_comp

/- warning: monoid_hom.comp_inv -> MonoidHom.comp_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {mM : MulOneClass.{u1} M} {mA : CommGroup.{u2} A} {mB : CommGroup.{u3} B} (φ : MonoidHom.{u2, u3} A B (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u3} B (DivInvMonoid.toMonoid.{u3} B (Group.toDivInvMonoid.{u3} B (CommGroup.toGroup.{u3} B mB))))) (ψ : MonoidHom.{u1, u2} M A mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA))))), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M B mM (Monoid.toMulOneClass.{u3} B (DivInvMonoid.toMonoid.{u3} B (Group.toDivInvMonoid.{u3} B (CommGroup.toGroup.{u3} B mB))))) (MonoidHom.comp.{u1, u2, u3} M A B mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u3} B (DivInvMonoid.toMonoid.{u3} B (Group.toDivInvMonoid.{u3} B (CommGroup.toGroup.{u3} B mB)))) φ (Inv.inv.{max u2 u1} (MonoidHom.{u1, u2} M A mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA))))) (MonoidHom.hasInv.{u1, u2} M A mM mA) ψ)) (Inv.inv.{max u3 u1} (MonoidHom.{u1, u3} M B mM (Monoid.toMulOneClass.{u3} B (DivInvMonoid.toMonoid.{u3} B (Group.toDivInvMonoid.{u3} B (CommGroup.toGroup.{u3} B mB))))) (MonoidHom.hasInv.{u1, u3} M B mM mB) (MonoidHom.comp.{u1, u2, u3} M A B mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u3} B (DivInvMonoid.toMonoid.{u3} B (Group.toDivInvMonoid.{u3} B (CommGroup.toGroup.{u3} B mB)))) φ ψ))
but is expected to have type
  forall {M : Type.{u3}} {A : Type.{u2}} {B : Type.{u1}} {mM : MulOneClass.{u3} M} {mA : CommGroup.{u2} A} {mB : CommGroup.{u1} B} (φ : MonoidHom.{u2, u1} A B (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u1} B (DivInvMonoid.toMonoid.{u1} B (Group.toDivInvMonoid.{u1} B (CommGroup.toGroup.{u1} B mB))))) (ψ : MonoidHom.{u3, u2} M A mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA))))), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M B mM (Monoid.toMulOneClass.{u1} B (DivInvMonoid.toMonoid.{u1} B (Group.toDivInvMonoid.{u1} B (CommGroup.toGroup.{u1} B mB))))) (MonoidHom.comp.{u3, u2, u1} M A B mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u1} B (DivInvMonoid.toMonoid.{u1} B (Group.toDivInvMonoid.{u1} B (CommGroup.toGroup.{u1} B mB)))) φ (Inv.inv.{max u2 u3} (MonoidHom.{u3, u2} M A mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA))))) (MonoidHom.instInvMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u3, u2} M A mM mA) ψ)) (Inv.inv.{max u1 u3} (MonoidHom.{u3, u1} M B mM (Monoid.toMulOneClass.{u1} B (DivInvMonoid.toMonoid.{u1} B (Group.toDivInvMonoid.{u1} B (CommGroup.toGroup.{u1} B mB))))) (MonoidHom.instInvMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u3, u1} M B mM mB) (MonoidHom.comp.{u3, u2, u1} M A B mM (Monoid.toMulOneClass.{u2} A (DivInvMonoid.toMonoid.{u2} A (Group.toDivInvMonoid.{u2} A (CommGroup.toGroup.{u2} A mA)))) (Monoid.toMulOneClass.{u1} B (DivInvMonoid.toMonoid.{u1} B (Group.toDivInvMonoid.{u1} B (CommGroup.toGroup.{u1} B mB)))) φ ψ))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_inv MonoidHom.comp_invₓ'. -/
@[simp, to_additive]
theorem comp_inv {M A B} {mM : MulOneClass M} {mA : CommGroup A} {mB : CommGroup B} (φ : A →* B)
    (ψ : M →* A) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp only [Function.comp_apply, inv_apply, map_inv, coe_comp]
#align monoid_hom.comp_inv MonoidHom.comp_inv
#align add_monoid_hom.comp_neg AddMonoidHom.comp_neg

/-- If `f` and `g` are monoid homomorphisms to a commutative group, then `f / g` is the homomorphism
sending `x` to `(f x) / (g x)`. -/
@[to_additive]
instance {M G} [MulOneClass M] [CommGroup G] : Div (M →* G) :=
  ⟨fun f g =>
    mk' (fun x => f x / g x) fun a b => by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]⟩

/-- If `f` and `g` are monoid homomorphisms to an additive commutative group, then `f - g`
is the homomorphism sending `x` to `(f x) - (g x)`. -/
add_decl_doc AddMonoidHom.hasSub

/- warning: monoid_hom.div_apply -> MonoidHom.div_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {G : Type.{u2}} {mM : MulOneClass.{u1} M} {gG : CommGroup.{u2} G} (f : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (g : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (x : M), Eq.{succ u2} G (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (fun (_x : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) => M -> G) (MonoidHom.hasCoeToFun.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (instHDiv.{max u2 u1} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (MonoidHom.hasDiv.{u1, u2} M G mM gG)) f g) x) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG)))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (fun (_x : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) => M -> G) (MonoidHom.hasCoeToFun.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) (fun (_x : MonoidHom.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) => M -> G) (MonoidHom.hasCoeToFun.{u1, u2} M G mM (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G (CommGroup.toGroup.{u2} G gG))))) g x))
but is expected to have type
  forall {M : Type.{u2}} {G : Type.{u1}} {mM : MulOneClass.{u2} M} {gG : CommGroup.{u1} G} (f : MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (g : MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG)))) (MonoidHom.monoidHomClass.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))))) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (instHDiv.{max u2 u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHom.instDivMonoidHomToMulOneClassToMonoidToDivInvMonoidToGroup.{u2, u1} M G mM gG)) f g) x) (HDiv.hDiv.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (instHDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (DivInvMonoid.toDiv.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (Group.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) (CommGroup.toGroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) x) gG)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG)))) (MonoidHom.monoidHomClass.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => G) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G (MulOneClass.toMul.{u2} M mM) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))) M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG)))) (MonoidHom.monoidHomClass.{u2, u1} M G mM (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G gG))))))) g x))
Case conversion may be inaccurate. Consider using '#align monoid_hom.div_apply MonoidHom.div_applyₓ'. -/
@[simp, to_additive]
theorem div_apply {M G} {mM : MulOneClass M} {gG : CommGroup G} (f g : M →* G) (x : M) :
    (f / g) x = f x / g x :=
  rfl
#align monoid_hom.div_apply MonoidHom.div_apply
#align add_monoid_hom.sub_apply AddMonoidHom.sub_apply

end MonoidHom

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid, `f * g` is the monoid
with zero morphism sending `x` to `f x * g x`. -/
instance {M N} {hM : MulZeroOneClass M} [CommMonoidWithZero N] : Mul (M →*₀ N) :=
  ⟨fun f g =>
    { (f * g : M →* N) with
      toFun := fun a => f a * g a
      map_zero' := by rw [map_zero, zero_mul] }⟩

