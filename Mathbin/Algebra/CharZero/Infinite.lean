/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Algebra.CharZero.Defs
import Data.Fintype.Card

#align_import algebra.char_zero.infinite from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-! # A characteristic-zero semiring is infinite 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


open Set

variable (M : Type _) [AddMonoidWithOne M] [CharZero M]

#print CharZero.infinite /-
-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective coe Nat.cast_injective
#align char_zero.infinite CharZero.infinite
-/

