/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.countable.small
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Small.Basic
import Mathbin.Data.Countable.Defs

/-!
# All countable types are small.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

That is, any countable type is equivalent to a type in any universe.
-/


universe w v

#print small_of_countable /-
instance (priority := 100) small_of_countable (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨f, hf⟩ := exists_injective_nat α
  small_of_injective hf
#align small_of_countable small_of_countable
-/

