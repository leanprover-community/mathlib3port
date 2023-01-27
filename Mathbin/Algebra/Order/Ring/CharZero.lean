/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module algebra.order.ring.char_zero
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Algebra.Order.Ring.Defs

/-!
# Strict ordered semiring have characteristic zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

#print StrictOrderedSemiring.to_charZero /-
-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.to_charZero [StrictOrderedSemiring α] :
    CharZero α :=
  ⟨StrictMono.injective <|
      strictMono_nat_of_lt_succ fun n => by
        rw [Nat.cast_succ]
        apply lt_add_one⟩
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.to_charZero
-/

