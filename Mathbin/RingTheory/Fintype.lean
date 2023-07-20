/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Units

#align_import ring_theory.fintype from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Some facts about finite rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open scoped Classical

#print card_units_lt /-
theorem card_units_lt (M₀ : Type _) [MonoidWithZero M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem (coe : M₀ˣ → M₀) Units.ext not_isUnit_zero
#align card_units_lt card_units_lt
-/

