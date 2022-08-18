/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathbin.Data.Polynomial.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ℵ₀`.
-/


universe u

open Cardinal Polynomial

open Cardinal

namespace Polynomial

@[simp]
theorem cardinal_mk_eq_max {R : Type u} [Semiringₓ R] [Nontrivial R] : # R[X] = max (# R) ℵ₀ :=
  (toFinsuppIso R).toEquiv.cardinal_eq.trans <| by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_commₓ]
    rfl

theorem cardinal_mk_le_max {R : Type u} [Semiringₓ R] : # R[X] ≤ max (# R) ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0)
    
  · exact cardinal_mk_eq_max.le
    

end Polynomial

