/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.char_zero.infinite
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Data.Fintype.Card

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

