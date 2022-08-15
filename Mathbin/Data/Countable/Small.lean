/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Countable.Basic
import Mathbin.Logic.Small

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/


universe w v

instance (priority := 100) small_of_countable (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨f, hf⟩ := exists_injective_nat α
  small_of_injective hf

