import Mathbin.Data.Fintype.Basic

/-!
# Some facts about finite rings
-/


open_locale Classical

theorem card_units_lt (M₀ : Type _) [MonoidWithZeroₓ M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card (M₀)ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem (coeₓ : (M₀)ˣ → M₀) Units.ext not_is_unit_zero

