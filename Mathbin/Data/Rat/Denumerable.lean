import Mathbin.SetTheory.Cardinal

/-!
# Denumerability of ℚ

This file proves that ℚ is infinite, denumerable, and deduces that it has cardinality `omega`.
-/


namespace Rat

open Denumerable

instance : Infinite ℚ :=
  Infinite.of_injective (coeₓ : ℕ → ℚ) Nat.cast_injective

private def denumerable_aux : ℚ ≃ { x : ℤ × ℕ // 0 < x.2 ∧ x.1.natAbs.Coprime x.2 } :=
  { toFun := fun x => ⟨⟨x.1, x.2⟩, x.3, x.4⟩, invFun := fun x => ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩,
    left_inv := fun ⟨_, _, _, _⟩ => rfl, right_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl }

-- error in Data.Rat.Denumerable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Denumerability of the Rational Numbers** -/ instance : denumerable exprℚ() :=
begin
  let [ident T] [] [":=", expr {x : «expr × »(exprℤ(), exprℕ()) // «expr ∧ »(«expr < »(0, x.2), x.1.nat_abs.coprime x.2)}],
  letI [] [":", expr infinite T] [":=", expr infinite.of_injective _ denumerable_aux.injective],
  letI [] [":", expr encodable T] [":=", expr encodable.subtype],
  letI [] [":", expr denumerable T] [":=", expr of_encodable_of_infinite T],
  exact [expr denumerable.of_equiv T denumerable_aux]
end

end Rat

namespace Cardinal

open_locale Cardinal

theorem mk_rat : # ℚ = ω :=
  mk_denumerable ℚ

end Cardinal

