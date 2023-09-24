/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Algebra.MonoidAlgebra.Ideal
import Data.MvPolynomial.Division

#align_import ring_theory.mv_polynomial.ideal from "leanprover-community/mathlib"@"4f81bc21e32048db7344b7867946e992cf5f68cc"

/-!
# Lemmas about ideals of `mv_polynomial`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Notably this contains results about monomial ideals.

## Main results

* `mv_polynomial.mem_ideal_span_monomial_image`
* `mv_polynomial.mem_ideal_span_X_image`
-/


variable {σ R : Type _}

namespace MvPolynomial

variable [CommSemiring R]

#print MvPolynomial.mem_ideal_span_monomial_image /-
/-- `x` is in a monomial ideal generated by `s` iff every element of of its support dominates one of
the generators. Note that `si ≤ xi` is analogous to saying that the monomial corresponding to `si`
divides the monomial corresponding to `xi`. -/
theorem mem_ideal_span_monomial_image {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi :=
  by
  refine' add_monoid_algebra.mem_ideal_span_of'_image.trans _
  simp_rw [le_iff_exists_add, add_comm]
  rfl
#align mv_polynomial.mem_ideal_span_monomial_image MvPolynomial.mem_ideal_span_monomial_image
-/

#print MvPolynomial.mem_ideal_span_monomial_image_iff_dvd /-
theorem mem_ideal_span_monomial_image_iff_dvd {x : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    x ∈ Ideal.span ((fun s => monomial s (1 : R)) '' s) ↔
      ∀ xi ∈ x.support, ∃ si ∈ s, monomial si 1 ∣ monomial xi (x.coeff xi) :=
  by
  refine' mem_ideal_span_monomial_image.trans (forall₂_congr fun xi hxi => _)
  simp_rw [monomial_dvd_monomial, one_dvd, and_true_iff, mem_support_iff.mp hxi, false_or_iff]
#align mv_polynomial.mem_ideal_span_monomial_image_iff_dvd MvPolynomial.mem_ideal_span_monomial_image_iff_dvd
-/

#print MvPolynomial.mem_ideal_span_X_image /-
/-- `x` is in a monomial ideal generated by variables `X` iff every element of of its support
has a component in `s`. -/
theorem mem_ideal_span_X_image {x : MvPolynomial σ R} {s : Set σ} :
    x ∈ Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial σ R)) ↔
      ∀ m ∈ x.support, ∃ i ∈ s, (m : σ →₀ ℕ) i ≠ 0 :=
  by
  have := @mem_ideal_span_monomial_image σ R _ _ ((fun i => Finsupp.single i 1) '' s)
  rw [Set.image_image] at this 
  refine' this.trans _
  simp [Nat.one_le_iff_ne_zero]
#align mv_polynomial.mem_ideal_span_X_image MvPolynomial.mem_ideal_span_X_image
-/

end MvPolynomial

