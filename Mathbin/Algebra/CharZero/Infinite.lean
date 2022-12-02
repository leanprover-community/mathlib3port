/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Data.Fintype.Lattice

/-! # A characteristic-zero semiring is infinite -/


open Set

variable (M : Type _) [AddMonoidWithOne M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective coe Nat.cast_injective
#align char_zero.infinite CharZero.infinite

