/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Algebra.CharZero.Defs
import Algebra.Order.Ring.Defs

#align_import algebra.order.ring.char_zero from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Strict ordered semiring have characteristic zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

#print StrictOrderedSemiring.toCharZero /-
-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.toCharZero [StrictOrderedSemiring α] :
    CharZero α :=
  ⟨StrictMono.injective <|
      strictMono_nat_of_lt_succ fun n => by rw [Nat.cast_succ]; apply lt_add_one⟩
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.toCharZero
-/

