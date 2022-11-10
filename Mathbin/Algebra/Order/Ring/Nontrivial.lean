/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Algebra.Order.Ring.Defs

/-!
# Nontrivial strict ordered semirings (and hence linear ordered semirings) are characteristic zero.
-/


variable {α : Type _}

section StrictOrderedSemiring

variable [StrictOrderedSemiring α] [Nontrivial α]

/-- Note this is not an instance as `char_zero` implies `nontrivial`, and this would risk forming a
loop. -/
theorem StrictOrderedSemiring.to_char_zero : CharZero α :=
  ⟨Nat.strict_mono_cast.Injective⟩

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring α]

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.to_char_zero : CharZero α :=
  StrictOrderedSemiring.to_char_zero

end LinearOrderedSemiring

