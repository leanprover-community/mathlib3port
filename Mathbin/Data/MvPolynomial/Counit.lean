/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.mv_polynomial.counit
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Basic

/-!
## Counit morphisms for multivariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

One may consider the ring of multivariate polynomials `mv_polynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism
  `mv_polynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `mv_polynomial.counit` is an “absolute” variant with `R = ℤ`
* `mv_polynomial.counit_nat` is an “absolute” variant with `R = ℕ`

-/


namespace MvPolynomial

open Function

variable (A B R : Type _) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

#print MvPolynomial.ACounit /-
/-- `mv_polynomial.acounit A B` is the natural surjective algebra homomorphism
`mv_polynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`,
and `mv_polynomial.counit_nat` for the “absolute” variant with `A = ℕ`. -/
noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id
#align mv_polynomial.acounit MvPolynomial.ACounit
-/

variable {B}

#print MvPolynomial.ACounit_X /-
@[simp]
theorem ACounit_X (b : B) : ACounit A B (X b) = b :=
  aeval_X _ b
#align mv_polynomial.acounit_X MvPolynomial.ACounit_X
-/

variable {A} (B)

#print MvPolynomial.ACounit_C /-
@[simp]
theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a :=
  aeval_C _ a
#align mv_polynomial.acounit_C MvPolynomial.ACounit_C
-/

variable (A)

#print MvPolynomial.ACounit_surjective /-
theorem ACounit_surjective : Surjective (ACounit A B) := fun b => ⟨X b, ACounit_X A b⟩
#align mv_polynomial.acounit_surjective MvPolynomial.ACounit_surjective
-/

#print MvPolynomial.counit /-
/-- `mv_polynomial.counit R` is the natural surjective ring homomorphism
`mv_polynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring,
and `mv_polynomial.counit_nat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def counit : MvPolynomial R ℤ →+* R :=
  ACounit ℤ R
#align mv_polynomial.counit MvPolynomial.counit
-/

#print MvPolynomial.counitNat /-
/-- `mv_polynomial.counit_nat A` is the natural surjective ring homomorphism
`mv_polynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring
and `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`. -/
noncomputable def counitNat : MvPolynomial A ℕ →+* A :=
  ACounit ℕ A
#align mv_polynomial.counit_nat MvPolynomial.counitNat
-/

#print MvPolynomial.counit_surjective /-
theorem counit_surjective : Surjective (counit R) :=
  ACounit_surjective ℤ R
#align mv_polynomial.counit_surjective MvPolynomial.counit_surjective
-/

#print MvPolynomial.counitNat_surjective /-
theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective ℕ A
#align mv_polynomial.counit_nat_surjective MvPolynomial.counitNat_surjective
-/

#print MvPolynomial.counit_C /-
theorem counit_C (n : ℤ) : counit R (C n) = n :=
  ACounit_C _ _
#align mv_polynomial.counit_C MvPolynomial.counit_C
-/

#print MvPolynomial.counitNat_C /-
theorem counitNat_C (n : ℕ) : counitNat A (C n) = n :=
  ACounit_C _ _
#align mv_polynomial.counit_nat_C MvPolynomial.counitNat_C
-/

variable {R A}

#print MvPolynomial.counit_X /-
@[simp]
theorem counit_X (r : R) : counit R (X r) = r :=
  ACounit_X _ _
#align mv_polynomial.counit_X MvPolynomial.counit_X
-/

#print MvPolynomial.counitNat_X /-
@[simp]
theorem counitNat_X (a : A) : counitNat A (X a) = a :=
  ACounit_X _ _
#align mv_polynomial.counit_nat_X MvPolynomial.counitNat_X
-/

end MvPolynomial

