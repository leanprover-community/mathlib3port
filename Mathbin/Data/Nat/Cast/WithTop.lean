/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.with_top
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Data.Nat.Basic

/-!
# Lemma about the coercion `ℕ → with_bot ℕ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An orphaned lemma about casting from `ℕ` to `with_bot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/


#print Nat.cast_withTop /-
theorem Nat.cast_withTop (n : ℕ) : @coe ℕ (WithTop ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_top Nat.cast_withTop
-/

#print Nat.cast_withBot /-
theorem Nat.cast_withBot (n : ℕ) : @coe ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_bot Nat.cast_withBot
-/

