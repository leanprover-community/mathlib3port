/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.commute
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Group.Commute

/-!
# Multiplicative homomorphisms respect semiconjugation and commutation.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/831
> Any changes to this file require a corresponding PR to mathlib4.
-/


section Commute

variable {F M N : Type _} [Mul M] [Mul N] {a x y : M}

/- warning: semiconj_by.map -> SemiconjBy.map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u3} N] {a : M} {x : M} {y : M} [_inst_3 : MulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2], (SemiconjBy.{u2} M _inst_1 a x y) -> (forall (f : F), SemiconjBy.{u3} N _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u1, u2, u3} F M N _inst_1 _inst_2 _inst_3)) f a) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u1, u2, u3} F M N _inst_1 _inst_2 _inst_3)) f x) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u1, u2, u3} F M N _inst_1 _inst_2 _inst_3)) f y))
but is expected to have type
  forall {F : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {a : M} {x : M} {y : M} [_inst_3 : MulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2], (SemiconjBy.{u2} M _inst_1 a x y) -> (forall (f : F), SemiconjBy.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) a) _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f a) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f x) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.map SemiconjBy.mapₓ'. -/
@[simp, to_additive]
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h
#align semiconj_by.map SemiconjBy.map

/- warning: commute.map -> Commute.map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u3} N] {x : M} {y : M} [_inst_3 : MulHomClass.{u1, u2, u3} F M N _inst_1 _inst_2], (Commute.{u2} M _inst_1 x y) -> (forall (f : F), Commute.{u3} N _inst_2 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u1, u2, u3} F M N _inst_1 _inst_2 _inst_3)) f x) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u1, u2, u3} F M N _inst_1 _inst_2 _inst_3)) f y))
but is expected to have type
  forall {F : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {x : M} {y : M} [_inst_3 : MulHomClass.{u3, u2, u1} F M N _inst_1 _inst_2], (Commute.{u2} M _inst_1 x y) -> (forall (f : F), Commute.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) x) _inst_2 (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f x) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2501 : M) => N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M N _inst_1 _inst_2 _inst_3) f y))
Case conversion may be inaccurate. Consider using '#align commute.map Commute.mapₓ'. -/
@[simp, to_additive]
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  h.map f
#align commute.map Commute.map

end Commute

