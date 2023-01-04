/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module ring_theory.fintype
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Units

/-!
# Some facts about finite rings
-/


open Classical

theorem card_units_lt (M₀ : Type _) [MonoidWithZero M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem (coe : M₀ˣ → M₀) Units.ext not_isUnit_zero
#align card_units_lt card_units_lt

