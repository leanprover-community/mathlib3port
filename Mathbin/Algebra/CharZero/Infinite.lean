/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.char_zero.infinite
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Data.Fintype.Card

/-! # A characteristic-zero semiring is infinite -/


open Set

variable (M : Type _) [AddMonoidWithOne M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective coe Nat.cast_injective
#align char_zero.infinite CharZero.infinite

