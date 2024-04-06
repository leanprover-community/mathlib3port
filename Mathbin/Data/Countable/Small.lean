/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Logic.Small.Defs
import Data.Countable.Defs

#align_import data.countable.small from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# All countable types are small.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

That is, any countable type is equivalent to a type in any universe.
-/


universe w v

#print Countable.toSmall /-
instance (priority := 100) Countable.toSmall (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨f, hf⟩ := exists_injective_nat α
  small_of_injective hf
#align small_of_countable Countable.toSmall
-/

