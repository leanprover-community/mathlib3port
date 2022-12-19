/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson

! This file was ported from Lean 3 source module algebra.divisibility.basic
! leanprover-community/mathlib commit d4f69d96f3532729da8ebb763f4bc26fcf640f06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group

/-!
# Divisibility

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/833
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the basics of the divisibility relation in the context of `(comm_)` `monoid`s.

## Main definitions

 * `monoid.has_dvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/


variable {α : Type _}

section Semigroup

variable [Semigroup α] {a b c : α}

#print semigroupDvd /-
/-- There are two possible conventions for divisibility, which coincide in a `comm_monoid`.
    This matches the convention for ordinals. -/
instance (priority := 100) semigroupDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c
#align semigroup_has_dvd semigroupDvd
-/

/- warning: dvd.intro -> Dvd.intro is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α} (c : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a c) b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α} (c : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a c) b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align dvd.intro Dvd.introₓ'. -/
-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `exists.intro`
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.intro c h
#align dvd.intro Dvd.intro

alias Dvd.intro ← dvd_of_mul_right_eq

/- warning: exists_eq_mul_right_of_dvd -> exists_eq_mul_right_of_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a c)))
Case conversion may be inaccurate. Consider using '#align exists_eq_mul_right_of_dvd exists_eq_mul_right_of_dvdₓ'. -/
theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c :=
  h
#align exists_eq_mul_right_of_dvd exists_eq_mul_right_of_dvd

/- warning: dvd.elim -> Dvd.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {P : Prop} {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (forall (c : α), (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a c)) -> P) -> P
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {P : Prop} {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (forall (c : α), (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a c)) -> P) -> P
Case conversion may be inaccurate. Consider using '#align dvd.elim Dvd.elimₓ'. -/
theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂
#align dvd.elim Dvd.elim

attribute [local simp] mul_assoc mul_comm mul_left_comm

#print dvd_trans /-
@[trans]
theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩
#align dvd_trans dvd_trans
-/

alias dvd_trans ← Dvd.Dvd.trans

instance : IsTrans α (· ∣ ·) :=
  ⟨fun a b c => dvd_trans⟩

/- warning: dvd_mul_right -> dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (a : α) (b : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (a : α) (b : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align dvd_mul_right dvd_mul_rightₓ'. -/
@[simp]
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl
#align dvd_mul_right dvd_mul_right

/- warning: dvd_mul_of_dvd_left -> dvd_mul_of_dvd_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (forall (c : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b) -> (forall (c : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align dvd_mul_of_dvd_left dvd_mul_of_dvd_leftₓ'. -/
theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)
#align dvd_mul_of_dvd_left dvd_mul_of_dvd_left

alias dvd_mul_of_dvd_left ← Dvd.Dvd.mul_right

/- warning: dvd_of_mul_right_dvd -> dvd_of_mul_right_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) c) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) c) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align dvd_of_mul_right_dvd dvd_of_mul_right_dvdₓ'. -/
theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h
#align dvd_of_mul_right_dvd dvd_of_mul_right_dvd

section map_dvd

variable {M N : Type _} [Monoid M] [Monoid N]

/- warning: map_dvd -> map_dvd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_2 : Monoid.{u1} M] [_inst_3 : Monoid.{u2} N] {F : Type.{u3}} [_inst_4 : MulHomClass.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))] (f : F) {a : M} {b : M}, (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M _inst_2)) a b) -> (Dvd.Dvd.{u2} N (semigroupDvd.{u2} N (Monoid.toSemigroup.{u2} N _inst_3)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3)) _inst_4)) f a) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3)) _inst_4)) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_2 : Monoid.{u2} M] [_inst_3 : Monoid.{u1} N] {F : Type.{u3}} [_inst_4 : MulHomClass.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))] (f : F) {a : M} {b : M}, (Dvd.dvd.{u2} M (semigroupDvd.{u2} M (Monoid.toSemigroup.{u2} M _inst_2)) a b) -> (Dvd.dvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (semigroupDvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (Monoid.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) _inst_3)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) _inst_4) f a) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) _inst_4) f b))
Case conversion may be inaccurate. Consider using '#align map_dvd map_dvdₓ'. -/
theorem map_dvd {F : Type _} [MulHomClass F M N] (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩
#align map_dvd map_dvd

/- warning: mul_hom.map_dvd -> MulHom.map_dvd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_2 : Monoid.{u1} M] [_inst_3 : Monoid.{u2} N] (f : MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) {a : M} {b : M}, (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M _inst_2)) a b) -> (Dvd.Dvd.{u2} N (semigroupDvd.{u2} N (Monoid.toSemigroup.{u2} N _inst_3)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) (fun (_x : MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) (fun (_x : MulHom.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_3))) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_2 : Monoid.{u2} M] [_inst_3 : Monoid.{u1} N] (f : MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))) {a : M} {b : M}, (Dvd.dvd.{u2} M (semigroupDvd.{u2} M (Monoid.toSemigroup.{u2} M _inst_2)) a b) -> (Dvd.dvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (semigroupDvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (Monoid.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) _inst_3)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) (MulHom.mulHomClass.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) (MulHom.mulHomClass.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)))) f b))
Case conversion may be inaccurate. Consider using '#align mul_hom.map_dvd MulHom.map_dvdₓ'. -/
theorem MulHom.map_dvd (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b :=
  map_dvd f
#align mul_hom.map_dvd MulHom.map_dvd

/- warning: monoid_hom.map_dvd -> MonoidHom.map_dvd is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_2 : Monoid.{u1} M] [_inst_3 : Monoid.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) {a : M} {b : M}, (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M _inst_2)) a b) -> (Dvd.Dvd.{u2} N (semigroupDvd.{u2} N (Monoid.toSemigroup.{u2} N _inst_3)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) f b))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_2 : Monoid.{u2} M] [_inst_3 : Monoid.{u1} N] (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) {a : M} {b : M}, (Dvd.dvd.{u2} M (semigroupDvd.{u2} M (Monoid.toSemigroup.{u2} M _inst_2)) a b) -> (Dvd.dvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (semigroupDvd.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) (Monoid.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) a) _inst_3)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2475 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)))) f b))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_dvd MonoidHom.map_dvdₓ'. -/
theorem MonoidHom.map_dvd (f : M →* N) {a b} : a ∣ b → f a ∣ f b :=
  map_dvd f
#align monoid_hom.map_dvd MonoidHom.map_dvd

end map_dvd

end Semigroup

section Monoid

variable [Monoid α]

#print dvd_refl /-
@[refl, simp]
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_one a)
#align dvd_refl dvd_refl
-/

#print dvd_rfl /-
theorem dvd_rfl : ∀ {a : α}, a ∣ a :=
  dvd_refl
#align dvd_rfl dvd_rfl
-/

instance : IsRefl α (· ∣ ·) :=
  ⟨dvd_refl⟩

/- warning: one_dvd -> one_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) a
Case conversion may be inaccurate. Consider using '#align one_dvd one_dvdₓ'. -/
theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mul a)
#align one_dvd one_dvd

end Monoid

section CommSemigroup

variable [CommSemigroup α] {a b c : α}

/- warning: dvd.intro_left -> Dvd.intro_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} (c : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a) b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} (c : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a) b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align dvd.intro_left Dvd.intro_leftₓ'. -/
theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro _ (by rw [mul_comm] at h; apply h)
#align dvd.intro_left Dvd.intro_left

alias Dvd.intro_left ← dvd_of_mul_left_eq

/- warning: exists_eq_mul_left_of_dvd -> exists_eq_mul_left_of_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)))
Case conversion may be inaccurate. Consider using '#align exists_eq_mul_left_of_dvd exists_eq_mul_left_of_dvdₓ'. -/
theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))
#align exists_eq_mul_left_of_dvd exists_eq_mul_left_of_dvd

/- warning: dvd_iff_exists_eq_mul_left -> dvd_iff_exists_eq_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)))
Case conversion may be inaccurate. Consider using '#align dvd_iff_exists_eq_mul_left dvd_iff_exists_eq_mul_leftₓ'. -/
theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by 
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩
#align dvd_iff_exists_eq_mul_left dvd_iff_exists_eq_mul_left

/- warning: dvd.elim_left -> Dvd.elim_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {P : Prop}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (forall (c : α), (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)) -> P) -> P
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {P : Prop}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (forall (c : α), (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c a)) -> P) -> P
Case conversion may be inaccurate. Consider using '#align dvd.elim_left Dvd.elim_leftₓ'. -/
theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃
#align dvd.elim_left Dvd.elim_left

/- warning: dvd_mul_left -> dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] (a : α) (b : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] (a : α) (b : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align dvd_mul_left dvd_mul_leftₓ'. -/
@[simp]
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)
#align dvd_mul_left dvd_mul_left

/- warning: dvd_mul_of_dvd_right -> dvd_mul_of_dvd_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (forall (c : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (forall (c : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) c b))
Case conversion may be inaccurate. Consider using '#align dvd_mul_of_dvd_right dvd_mul_of_dvd_rightₓ'. -/
theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by rw [mul_comm];
  exact h.mul_right _
#align dvd_mul_of_dvd_right dvd_mul_of_dvd_right

alias dvd_mul_of_dvd_right ← Dvd.Dvd.mul_left

attribute [local simp] mul_assoc mul_comm mul_left_comm

/- warning: mul_dvd_mul -> mul_dvd_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) c d) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) a b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) c d) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b d))
Case conversion may be inaccurate. Consider using '#align mul_dvd_mul mul_dvd_mulₓ'. -/
theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ => ⟨e * f, by simp⟩
#align mul_dvd_mul mul_dvd_mul

/- warning: dvd_of_mul_left_dvd -> dvd_of_mul_left_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a b) c) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a b) c) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) b c)
Case conversion may be inaccurate. Consider using '#align dvd_of_mul_left_dvd dvd_of_mul_left_dvdₓ'. -/
theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])
#align dvd_of_mul_left_dvd dvd_of_mul_left_dvd

end CommSemigroup

section CommMonoid

variable [CommMonoid α] {a b : α}

/- warning: mul_dvd_mul_left -> mul_dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) b c) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) b c) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align mul_dvd_mul_left mul_dvd_mul_leftₓ'. -/
theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
  mul_dvd_mul (dvd_refl a) h
#align mul_dvd_mul_left mul_dvd_mul_left

/- warning: mul_dvd_mul_right -> mul_dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b) -> (forall (c : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b) -> (forall (c : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align mul_dvd_mul_right mul_dvd_mul_rightₓ'. -/
theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
  mul_dvd_mul h (dvd_refl c)
#align mul_dvd_mul_right mul_dvd_mul_right

#print pow_dvd_pow_of_dvd /-
theorem pow_dvd_pow_of_dvd {a b : α} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
  | 0 => by rw [pow_zero, pow_zero]
  | n + 1 => by 
    rw [pow_succ, pow_succ]
    exact mul_dvd_mul h (pow_dvd_pow_of_dvd n)
#align pow_dvd_pow_of_dvd pow_dvd_pow_of_dvd
-/

end CommMonoid

