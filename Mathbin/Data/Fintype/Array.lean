/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fintype.Pi
import Mathbin.Logic.Equiv.Array

#align_import data.fintype.array from "leanprover-community/mathlib"@"2fe465deb81bcd7ccafa065bb686888a82f15372"

/-!
# `array n α` is a fintype when `α` is.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

instance DArray.fintype {n : ℕ} {α : Fin n → Type _} [∀ n, Fintype (α n)] : Fintype (DArray n α) :=
  Fintype.ofEquiv _ (Equiv.dArrayEquivFin _).symm
#align d_array.fintype DArray.fintype

instance Vector.fintype {n : ℕ} {α : Type _} [Fintype α] : Fintype (Array' n α) :=
  DArray.fintype
#align array.fintype Vector.fintypeₓ

