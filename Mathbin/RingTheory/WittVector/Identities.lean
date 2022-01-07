import Mathbin.RingTheory.WittVector.Frobenius
import Mathbin.RingTheory.WittVector.Verschiebung
import Mathbin.RingTheory.WittVector.MulP

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type _} [Fact p.prime] [CommRingₓ R]

local notation "𝕎" => WittVector p

noncomputable section

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  ghost_calc x
  ghost_simp [mul_commₓ]

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `zmod p`. -/
theorem verschiebung_zmod (x : 𝕎 (Zmod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]

theorem coeff_p_pow [CharP R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 := by
  induction' i with i h
  · simp only [one_coeff_zero, Ne.def, pow_zeroₓ]
    
  · rw [pow_succ'ₓ, ← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_succ, h, one_pow]
    

/-- The “projection formula” for Frobenius and Verschiebung. -/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) : verschiebung (x * frobenius y) = verschiebung x * y := by
  ghost_calc x y
  rintro ⟨⟩ <;> ghost_simp [mul_assocₓ]

end WittVector

