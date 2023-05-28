/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.charpoly.basic
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.FieldTheory.Minpoly.Field

/-!

# Characteristic polynomial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `linear_algebra/charpoly/to_matrix`.

## Main definition

* `linear_map.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [Nontrivial R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Classical Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

#print LinearMap.charpoly /-
/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
#align linear_map.charpoly LinearMap.charpoly
-/

/- warning: linear_map.charpoly_def -> LinearMap.charpoly_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.charpoly_def LinearMap.charpoly_defₓ'. -/
theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl
#align linear_map.charpoly_def LinearMap.charpoly_def

end Basic

section Coeff

#print LinearMap.charpoly_monic /-
theorem charpoly_monic : f.charpoly.Monic :=
  charpoly_monic _
#align linear_map.charpoly_monic LinearMap.charpoly_monic
-/

end Coeff

section CayleyHamilton

#print LinearMap.aeval_self_charpoly /-
/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a linear map, applied
to the linear map itself, is zero.

See `matrix.aeval_self_charpoly` for the equivalent statement about matrices. -/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 :=
  by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (choose_basis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.coe_algHom, ← Polynomial.aeval_algHom_apply _ _ _,
    charpoly_def]
  exact aeval_self_charpoly _
#align linear_map.aeval_self_charpoly LinearMap.aeval_self_charpoly
-/

/- warning: linear_map.is_integral -> LinearMap.isIntegral is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Nontrivial.{u1} R] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] [_inst_6 : Module.Finite.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (f : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4 _inst_4), IsIntegral.{u1, u2} R (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4 _inst_4) _inst_1 (Module.End.ring.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_3 _inst_4) (Module.End.algebra.{u1, u2} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4) f
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Nontrivial.{u1} R] [_inst_3 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] [_inst_5 : Module.Free.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] [_inst_6 : Module.Finite.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4] (f : LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4 _inst_4), IsIntegral.{u1, u2} R (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4 _inst_4) _inst_1 (Module.End.ring.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_3 _inst_4) (Module.instAlgebraEndToSemiringSemiring.{u1, u2} R M (CommRing.toCommSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_4) f
Case conversion may be inaccurate. Consider using '#align linear_map.is_integral LinearMap.isIntegralₓ'. -/
theorem isIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩
#align linear_map.is_integral LinearMap.isIntegral

/- warning: linear_map.minpoly_dvd_charpoly -> LinearMap.minpoly_dvd_charpoly is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {M : Type.{u2}} [_inst_7 : Field.{u1} K] [_inst_8 : AddCommGroup.{u2} M] [_inst_9 : Module.{u1, u2} K M (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8)] [_inst_10 : FiniteDimensional.{u1, u2} K M (Field.toDivisionRing.{u1} K _inst_7) _inst_8 _inst_9] (f : LinearMap.{u1, u1, u2, u2} K K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (RingHom.id.{u1} K (Semiring.toNonAssocSemiring.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9 _inst_9), Dvd.Dvd.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (semigroupDvd.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (SemigroupWithZero.toSemigroup.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalSemiring.toSemigroupWithZero.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalRing.toNonUnitalSemiring.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalCommRing.toNonUnitalRing.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (CommRing.toNonUnitalCommRing.{u1} (Polynomial.{u1} K (Ring.toSemiring.{u1} K (CommRing.toRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (Polynomial.commRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))))))) (minpoly.{u1, u2} K (LinearMap.{u1, u1, u2, u2} K K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (RingHom.id.{u1} K (Semiring.toNonAssocSemiring.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9 _inst_9) (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (Module.End.ring.{u1, u2} K M (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) _inst_8 _inst_9) (Module.End.algebra.{u1, u2} K M (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9) f) (LinearMap.charpoly.{u1, u2} K M (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (LocalRing.to_nontrivial.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_7))) (Field.localRing.{u1} K _inst_7)) _inst_8 _inst_9 (Module.Free.of_divisionRing.{u1, u2} K M (Field.toDivisionRing.{u1} K _inst_7) _inst_8 _inst_9) _inst_10 f)
but is expected to have type
  forall {K : Type.{u1}} {M : Type.{u2}} [_inst_7 : Field.{u1} K] [_inst_8 : AddCommGroup.{u2} M] [_inst_9 : Module.{u1, u2} K M (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8)] [_inst_10 : FiniteDimensional.{u1, u2} K M (Field.toDivisionRing.{u1} K _inst_7) _inst_8 _inst_9] (f : LinearMap.{u1, u1, u2, u2} K K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (RingHom.id.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9 _inst_9), Dvd.dvd.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (semigroupDvd.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (SemigroupWithZero.toSemigroup.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalSemiring.toSemigroupWithZero.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (CommRing.toNonUnitalCommRing.{u1} (Polynomial.{u1} K (CommSemiring.toSemiring.{u1} K (CommRing.toCommSemiring.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))) (Polynomial.commRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7))))))))) (minpoly.{u1, u2} K (LinearMap.{u1, u1, u2, u2} K K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (RingHom.id.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))))) M M (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9 _inst_9) (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (Module.End.ring.{u1, u2} K M (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) _inst_8 _inst_9) (Module.instAlgebraEndToSemiringSemiring.{u1, u2} K M (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_8) _inst_9) f) (LinearMap.charpoly.{u1, u2} K M (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (LocalRing.toNontrivial.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) (Field.instLocalRingToSemiringToDivisionSemiringToSemifield.{u1} K _inst_7)) _inst_8 _inst_9 (Module.Free.of_divisionRing.{u1, u2} K M (Field.toDivisionRing.{u1} K _inst_7) _inst_8 _inst_9) _inst_10 f)
Case conversion may be inaccurate. Consider using '#align linear_map.minpoly_dvd_charpoly LinearMap.minpoly_dvd_charpolyₓ'. -/
theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)
#align linear_map.minpoly_dvd_charpoly LinearMap.minpoly_dvd_charpoly

#print LinearMap.aeval_eq_aeval_mod_charpoly /-
/-- Any endomorphism polynomial `p` is equivalent under evaluation to `p %ₘ f.charpoly`; that is,
`p` is equivalent to a polynomial with degree less than the dimension of the module. -/
theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_modByMonic_eq_self_of_root f.charpoly_monic f.aeval_self_charpoly).symm
#align linear_map.aeval_eq_aeval_mod_charpoly LinearMap.aeval_eq_aeval_mod_charpoly
-/

#print LinearMap.pow_eq_aeval_mod_charpoly /-
/-- Any endomorphism power can be computed as the sum of endomorphism powers less than the
dimension of the module. -/
theorem pow_eq_aeval_mod_charpoly (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]
#align linear_map.pow_eq_aeval_mod_charpoly LinearMap.pow_eq_aeval_mod_charpoly
-/

variable {f}

/- warning: linear_map.minpoly_coeff_zero_of_injective -> LinearMap.minpoly_coeff_zero_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.minpoly_coeff_zero_of_injective LinearMap.minpoly_coeff_zero_of_injectiveₓ'. -/
theorem minpoly_coeff_zero_of_injective (hf : Function.Injective f) : (minpoly R f).coeff 0 ≠ 0 :=
  by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree :=
    by
    rw [hP, mul_comm]
    refine' degree_lt_degree_mul_X fun h => _
    rw [h, MulZeroClass.mul_zero] at hP
    exact minpoly.ne_zero (IsIntegral f) hP
  have hPmonic : P.monic :=
    by
    suffices (minpoly R f).Monic by
      rwa [monic.def, hP, mul_comm, leading_coeff_mul_X, ← monic.def] at this
    exact minpoly.monic (IsIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, mul_eq_comp, ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp, AlgHom.map_mul,
    zero_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (ext hzero))
#align linear_map.minpoly_coeff_zero_of_injective LinearMap.minpoly_coeff_zero_of_injective

end CayleyHamilton

end LinearMap

