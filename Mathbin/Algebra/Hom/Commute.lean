/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.commute
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
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

@[simp, to_additive]
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h
#align semiconj_by.map SemiconjBy.map

@[simp, to_additive]
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  h.map f
#align commute.map Commute.map

end Commute

