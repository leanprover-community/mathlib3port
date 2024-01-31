/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.MonoidAlgebra.Division
import Data.MvPolynomial.Basic

#align_import data.mv_polynomial.division from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# Division of `mv_polynomial` by monomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `mv_polynomial.div_monomial x s`: divides `x` by the monomial `mv_polynomial.monomial 1 s`
* `mv_polynomial.mod_monomial x s`: the remainder upon dividing `x` by the monomial
  `mv_polynomial.monomial 1 s`.

## Main results

* `mv_polynomial.div_monomial_add_mod_monomial`, `mv_polynomial.mod_monomial_add_div_monomial`:
  `div_monomial` and `mod_monomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Where possible, the results in this file should be first proved in the generality of
`add_monoid_algebra`, and then the versions specialized to `mv_polynomial` proved in terms of these.

-/


variable {σ R : Type _} [CommSemiring R]

namespace MvPolynomial

section CopiedDeclarations

/-! Please ensure the declarations in this section are direct translations of `add_monoid_algebra`
results. -/


#print MvPolynomial.divMonomial /-
/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
noncomputable def divMonomial (p : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  AddMonoidAlgebra.divOf p s
#align mv_polynomial.div_monomial MvPolynomial.divMonomial
-/

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

#print MvPolynomial.coeff_divMonomial /-
@[simp]
theorem coeff_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) (s' : σ →₀ ℕ) :
    coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x :=
  rfl
#align mv_polynomial.coeff_div_monomial MvPolynomial.coeff_divMonomial
-/

#print MvPolynomial.support_divMonomial /-
@[simp]
theorem support_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.Preimage _ ((add_right_injective s).InjOn _) :=
  rfl
#align mv_polynomial.support_div_monomial MvPolynomial.support_divMonomial
-/

#print MvPolynomial.zero_divMonomial /-
@[simp]
theorem zero_divMonomial (s : σ →₀ ℕ) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.zero_divOf _
#align mv_polynomial.zero_div_monomial MvPolynomial.zero_divMonomial
-/

#print MvPolynomial.divMonomial_zero /-
theorem divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x :=
  x.divOf_zero
#align mv_polynomial.div_monomial_zero MvPolynomial.divMonomial_zero
-/

#print MvPolynomial.add_divMonomial /-
theorem add_divMonomial (x y : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (x + y) /ᵐᵒⁿᵒᵐⁱᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s :=
  map_add _ _ _
#align mv_polynomial.add_div_monomial MvPolynomial.add_divMonomial
-/

#print MvPolynomial.divMonomial_add /-
theorem divMonomial_add (a b : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b :=
  x.divOf_add _ _
#align mv_polynomial.div_monomial_add MvPolynomial.divMonomial_add
-/

#print MvPolynomial.divMonomial_monomial_mul /-
@[simp]
theorem divMonomial_monomial_mul (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.of'_mul_divOf _
#align mv_polynomial.div_monomial_monomial_mul MvPolynomial.divMonomial_monomial_mul
-/

#print MvPolynomial.divMonomial_mul_monomial /-
@[simp]
theorem divMonomial_mul_monomial (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.mul_of'_divOf _
#align mv_polynomial.div_monomial_mul_monomial MvPolynomial.divMonomial_mul_monomial
-/

#print MvPolynomial.divMonomial_monomial /-
@[simp]
theorem divMonomial_monomial (a : σ →₀ ℕ) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R) :=
  AddMonoidAlgebra.of'_divOf _
#align mv_polynomial.div_monomial_monomial MvPolynomial.divMonomial_monomial
-/

#print MvPolynomial.modMonomial /-
/-- The remainder upon division by `monomial 1 s`. -/
noncomputable def modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  x.modOf s
#align mv_polynomial.mod_monomial MvPolynomial.modMonomial
-/

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

#print MvPolynomial.coeff_modMonomial_of_not_le /-
@[simp]
theorem coeff_modMonomial_of_not_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : ¬s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x :=
  x.modOf_apply_of_not_exists_add s s'
    (by
      rintro ⟨d, rfl⟩
      exact h le_self_add)
#align mv_polynomial.coeff_mod_monomial_of_not_le MvPolynomial.coeff_modMonomial_of_not_le
-/

#print MvPolynomial.coeff_modMonomial_of_le /-
@[simp]
theorem coeff_modMonomial_of_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 :=
  x.modOf_apply_of_exists_add _ _ <| exists_add_of_le h
#align mv_polynomial.coeff_mod_monomial_of_le MvPolynomial.coeff_modMonomial_of_le
-/

#print MvPolynomial.monomial_mul_modMonomial /-
@[simp]
theorem monomial_mul_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.of'_mul_modOf _
#align mv_polynomial.monomial_mul_mod_monomial MvPolynomial.monomial_mul_modMonomial
-/

#print MvPolynomial.mul_monomial_modMonomial /-
@[simp]
theorem mul_monomial_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.mul_of'_modOf _
#align mv_polynomial.mul_monomial_mod_monomial MvPolynomial.mul_monomial_modMonomial
-/

#print MvPolynomial.monomial_modMonomial /-
@[simp]
theorem monomial_modMonomial (s : σ →₀ ℕ) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.of'_modOf _
#align mv_polynomial.monomial_mod_monomial MvPolynomial.monomial_modMonomial
-/

#print MvPolynomial.divMonomial_add_modMonomial /-
theorem divMonomial_add_modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x :=
  AddMonoidAlgebra.divOf_add_modOf x s
#align mv_polynomial.div_monomial_add_mod_monomial MvPolynomial.divMonomial_add_modMonomial
-/

#print MvPolynomial.modMonomial_add_divMonomial /-
theorem modMonomial_add_divMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x :=
  AddMonoidAlgebra.modOf_add_divOf x s
#align mv_polynomial.mod_monomial_add_div_monomial MvPolynomial.modMonomial_add_divMonomial
-/

#print MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero /-
theorem monomial_one_dvd_iff_modMonomial_eq_zero {i : σ →₀ ℕ} {x : MvPolynomial σ R} :
    monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0 :=
  AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero
#align mv_polynomial.monomial_one_dvd_iff_mod_monomial_eq_zero MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero
-/

end CopiedDeclarations

section XLemmas

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

#print MvPolynomial.X_mul_divMonomial /-
@[simp]
theorem X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_monomial_mul _ _
#align mv_polynomial.X_mul_div_monomial MvPolynomial.X_mul_divMonomial
-/

#print MvPolynomial.X_divMonomial /-
@[simp]
theorem X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1 :=
  divMonomial_monomial (Finsupp.single i 1)
#align mv_polynomial.X_div_monomial MvPolynomial.X_divMonomial
-/

#print MvPolynomial.mul_X_divMonomial /-
@[simp]
theorem mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_mul_monomial _ _
#align mv_polynomial.mul_X_div_monomial MvPolynomial.mul_X_divMonomial
-/

#print MvPolynomial.X_mul_modMonomial /-
@[simp]
theorem X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_mul_modMonomial _ _
#align mv_polynomial.X_mul_mod_monomial MvPolynomial.X_mul_modMonomial
-/

#print MvPolynomial.mul_X_modMonomial /-
@[simp]
theorem mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  mul_monomial_modMonomial _ _
#align mv_polynomial.mul_X_mod_monomial MvPolynomial.mul_X_modMonomial
-/

#print MvPolynomial.modMonomial_X /-
@[simp]
theorem modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_modMonomial _
#align mv_polynomial.mod_monomial_X MvPolynomial.modMonomial_X
-/

#print MvPolynomial.divMonomial_add_modMonomial_single /-
theorem divMonomial_add_modMonomial_single (x : MvPolynomial σ R) (i : σ) :
    X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_add_modMonomial _ _
#align mv_polynomial.div_monomial_add_mod_monomial_single MvPolynomial.divMonomial_add_modMonomial_single
-/

#print MvPolynomial.modMonomial_add_divMonomial_single /-
theorem modMonomial_add_divMonomial_single (x : MvPolynomial σ R) (i : σ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) = x :=
  modMonomial_add_divMonomial _ _
#align mv_polynomial.mod_monomial_add_div_monomial_single MvPolynomial.modMonomial_add_divMonomial_single
-/

#print MvPolynomial.X_dvd_iff_modMonomial_eq_zero /-
theorem X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} :
    X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_one_dvd_iff_modMonomial_eq_zero
#align mv_polynomial.X_dvd_iff_mod_monomial_eq_zero MvPolynomial.X_dvd_iff_modMonomial_eq_zero
-/

end XLemmas

/-! ### Some results about dvd (`∣`) on `monomial` and `X` -/


#print MvPolynomial.monomial_dvd_monomial /-
theorem monomial_dvd_monomial {r s : R} {i j : σ →₀ ℕ} :
    monomial i r ∣ monomial j s ↔ (s = 0 ∨ i ≤ j) ∧ r ∣ s :=
  by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx 
    have hj := hx j
    have hi := hx i
    classical
  · rintro ⟨h | hij, d, rfl⟩
    · simp_rw [h, monomial_zero, dvd_zero]
    · refine' ⟨monomial (j - i) d, _⟩
      rw [monomial_mul, add_tsub_cancel_of_le hij]
#align mv_polynomial.monomial_dvd_monomial MvPolynomial.monomial_dvd_monomial
-/

#print MvPolynomial.monomial_one_dvd_monomial_one /-
@[simp]
theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ →₀ ℕ} :
    monomial i (1 : R) ∣ monomial j 1 ↔ i ≤ j :=
  by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or_iff, dvd_rfl, and_true_iff]
#align mv_polynomial.monomial_one_dvd_monomial_one MvPolynomial.monomial_one_dvd_monomial_one
-/

#print MvPolynomial.X_dvd_X /-
@[simp]
theorem X_dvd_X [Nontrivial R] {i j : σ} :
    (X i : MvPolynomial σ R) ∣ (X j : MvPolynomial σ R) ↔ i = j :=
  by
  refine' monomial_one_dvd_monomial_one.trans _
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero, Ne.def,
    one_ne_zero, not_false_iff, and_true_iff]
#align mv_polynomial.X_dvd_X MvPolynomial.X_dvd_X
-/

#print MvPolynomial.X_dvd_monomial /-
@[simp]
theorem X_dvd_monomial {i : σ} {j : σ →₀ ℕ} {r : R} :
    (X i : MvPolynomial σ R) ∣ monomial j r ↔ r = 0 ∨ j i ≠ 0 :=
  by
  refine' monomial_dvd_monomial.trans _
  simp_rw [one_dvd, and_true_iff, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
#align mv_polynomial.X_dvd_monomial MvPolynomial.X_dvd_monomial
-/

end MvPolynomial

