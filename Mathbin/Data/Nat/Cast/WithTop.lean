/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Algebra.Order.Monoid.WithTop
import Algebra.Group.Nat

#align_import data.nat.cast.with_top from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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

