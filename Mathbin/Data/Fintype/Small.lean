/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Data.Fintype.Card
import Logic.Small.Defs

#align_import data.fintype.small from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# All finite types are small.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

That is, any `α` with `[fintype α]` is equivalent to a type in any universe.

-/


universe w v

instance (priority := 100) Countable.toSmall (α : Type v) [Fintype α] : Small.{w} α :=
  by
  rw [small_congr (Fintype.equivFin α)]
  infer_instance
#align small_of_fintype Countable.toSmallₓ

