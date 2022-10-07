/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Fintype.Basic

/-!
# Some facts about finite rings
-/


open Classical

theorem card_units_lt (M₀ : Type _) [MonoidWithZeroₓ M₀] [Nontrivial M₀] [Fintypeₓ M₀] :
    Fintypeₓ.card M₀ˣ < Fintypeₓ.card M₀ :=
  Fintypeₓ.card_lt_of_injective_of_not_mem (coe : M₀ˣ → M₀) Units.ext not_is_unit_zero

