/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.cast.with_top
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Data.Nat.Basic

/-!
# Lemma about the coercion `ℕ → with_bot ℕ`.

An orphaned lemma about casting from `ℕ` to `with_bot ℕ`,
exiled here to minimize imports to `data.rat.order` for porting purposes.
-/


theorem Nat.cast_with_top (n : ℕ) : @coe ℕ (WithTop ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_top Nat.cast_with_top

theorem Nat.cast_with_bot (n : ℕ) : @coe ℕ (WithBot ℕ) (@coeToLift _ _ Nat.castCoe) n = n :=
  rfl
#align nat.cast_with_bot Nat.cast_with_bot

