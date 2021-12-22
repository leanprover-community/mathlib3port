import Mathbin.Data.MvPolynomial.Cardinal
import Mathbin.Data.MvPolynomial.Equiv

/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ω`.
-/


universe u

open_locale Cardinal

open Cardinal

namespace Polynomial

theorem cardinal_mk_le_max {R : Type u} [CommSemiringₓ R] : # (Polynomial R) ≤ max (# R) ω :=
  calc # (Polynomial R) = # (MvPolynomial PUnit.{u + 1} R) :=
    Cardinal.eq.2 ⟨(MvPolynomial.punitAlgEquiv.{u, u} R).toEquiv.symm⟩
    _ ≤ _ := MvPolynomial.cardinal_mk_le_max
    _ ≤ _ := by
    have : # PUnit.{u + 1} ≤ ω
    exact le_of_ltₓ (lt_omega_iff_fintype.2 ⟨inferInstance⟩)
    rw [max_assocₓ, max_eq_rightₓ this]
    

end Polynomial

