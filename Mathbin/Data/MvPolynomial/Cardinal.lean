/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathbin.Data.MvPolynomial.Equiv
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/


universe u v

open Cardinal

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiringₓ R]

@[simp]
theorem cardinal_mk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    # (MvPolynomial σ R) = max (max (Cardinal.lift.{u} <| # R) <| Cardinal.lift.{v} <| # σ) ℵ₀ := by
  haveI : Infinite (σ →₀ ℕ) := infinite_iff.2 ((le_max_rightₓ _ _).trans (mk_finsupp_nat σ).Ge)
  refine' (mk_finsupp_lift_of_infinite _ R).trans _
  rw [mk_finsupp_nat, max_assocₓ, lift_max, lift_aleph_0, max_commₓ]

@[simp]
theorem cardinal_mk_eq_lift [IsEmpty σ] : # (MvPolynomial σ R) = Cardinal.lift.{u} (# R) :=
  ((isEmptyRingEquiv R σ).toEquiv.trans Equivₓ.ulift.{u}.symm).cardinal_eq

theorem cardinal_lift_mk_le_max {σ : Type u} {R : Type v} [CommSemiringₓ R] :
    # (MvPolynomial σ R) ≤ max (max (Cardinal.lift.{u} <| # R) <| Cardinal.lift.{v} <| # σ) ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0)
    
  cases is_empty_or_nonempty σ
  · exact cardinal_mk_eq_lift.trans_le (le_max_of_le_left <| le_max_leftₓ _ _)
    
  · exact cardinal_mk_eq_max_lift.le
    

end TwoUniverses

variable {σ R : Type u} [CommSemiringₓ R]

theorem cardinal_mk_eq_max [Nonempty σ] [Nontrivial R] : # (MvPolynomial σ R) = max (max (# R) (# σ)) ℵ₀ := by
  simp

/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
theorem cardinal_mk_le_max : # (MvPolynomial σ R) ≤ max (max (# R) (# σ)) ℵ₀ :=
  cardinal_lift_mk_le_max.trans <| by
    rw [lift_id, lift_id]

end MvPolynomial

