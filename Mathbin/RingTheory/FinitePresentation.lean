/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.finite_presentation
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.FiniteType
import Mathbin.RingTheory.MvPolynomial.Tower
import Mathbin.RingTheory.Ideal.QuotientOperations

/-!
# Finiteness conditions in commutative algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `algebra.finite_presentation`, `ring_hom.finite_presentation`, `alg_hom.finite_presentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/


open Function (Surjective)

open BigOperators Polynomial

section ModuleAndAlgebra

variable (R A B M N : Type _)

#print Algebra.FinitePresentation /-
/-- An algebra over a commutative semiring is `finite_presentation` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop :=
  ∃ (n : ℕ)(f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ f.toRingHom.ker.FG
#align algebra.finite_presentation Algebra.FinitePresentation
-/

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

namespace FiniteType

variable {R A B}

/- warning: algebra.finite_type.of_finite_presentation -> Algebra.FiniteType.of_finitePresentation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))], (Algebra.FinitePresentation.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) -> (Algebra.FiniteType.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))], (Algebra.FinitePresentation.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) -> (Algebra.FiniteType.{u2, u1} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3)
Case conversion may be inaccurate. Consider using '#align algebra.finite_type.of_finite_presentation Algebra.FiniteType.of_finitePresentationₓ'. -/
/-- A finitely presented algebra is of finite type. -/
theorem of_finitePresentation : FinitePresentation R A → FiniteType R A :=
  by
  rintro ⟨n, f, hf⟩
  apply finite_type.iff_quotient_mv_polynomial''.2
  exact ⟨n, f, hf.1⟩
#align algebra.finite_type.of_finite_presentation Algebra.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable {R A B}

/- warning: algebra.finite_presentation.of_finite_type -> Algebra.FinitePresentation.of_finiteType is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_10 : IsNoetherianRing.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))], Iff (Algebra.FiniteType.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3) (Algebra.FinitePresentation.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] [_inst_10 : IsNoetherianRing.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))], Iff (Algebra.FiniteType.{u2, u1} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) (Algebra.FinitePresentation.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3)
Case conversion may be inaccurate. Consider using '#align algebra.finite_presentation.of_finite_type Algebra.FinitePresentation.of_finiteTypeₓ'. -/
/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
theorem of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A :=
  by
  refine' ⟨fun h => _, Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine' ⟨n, f, hf, _⟩
  have hnoet : IsNoetherianRing (MvPolynomial (Fin n) R) := by infer_instance
  replace hnoet := (isNoetherianRing_iff.1 hnoet).noetherian
  exact hnoet f.to_ring_hom.ker
#align algebra.finite_presentation.of_finite_type Algebra.FinitePresentation.of_finiteType

#print Algebra.FinitePresentation.equiv /-
/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem equiv (hfp : FinitePresentation R A) (e : A ≃ₐ[R] B) : FinitePresentation R B :=
  by
  obtain ⟨n, f, hf⟩ := hfp
  use n, AlgHom.comp (↑e) f
  constructor
  · exact Function.Surjective.comp e.surjective hf.1
  suffices hker : (AlgHom.comp (↑e) f).toRingHom.ker = f.to_ring_hom.ker
  · rw [hker]
    exact hf.2
  · have hco : (AlgHom.comp (↑e) f).toRingHom = RingHom.comp (↑e.to_ring_equiv) f.to_ring_hom :=
      by
      have h : (AlgHom.comp (↑e) f).toRingHom = e.to_alg_hom.to_ring_hom.comp f.to_ring_hom := rfl
      have h1 : ↑e.to_ring_equiv = e.to_alg_hom.toRingHom := rfl
      rw [h, h1]
    rw [RingHom.ker_eq_comap_bot, hco, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
      RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e), RingHom.ker_eq_comap_bot]
#align algebra.finite_presentation.equiv Algebra.FinitePresentation.equiv
-/

variable (R)

#print Algebra.FinitePresentation.mvPolynomial /-
/-- The ring of polynomials in finitely many variables is finitely presented. -/
protected theorem mvPolynomial (ι : Type u_2) [Finite ι] :
    FinitePresentation R (MvPolynomial ι R) := by
  cases nonempty_fintype ι <;>
    exact
      let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
      ⟨Fintype.card ι, eqv, eqv.Surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.Injective).symm ▸ Submodule.fg_bot⟩
#align algebra.finite_presentation.mv_polynomial Algebra.FinitePresentation.mvPolynomial
-/

#print Algebra.FinitePresentation.self /-
/-- `R` is finitely presented as `R`-algebra. -/
theorem self : FinitePresentation R R :=
  equiv (FinitePresentation.mvPolynomial R PEmpty) (MvPolynomial.isEmptyAlgEquiv R PEmpty)
#align algebra.finite_presentation.self Algebra.FinitePresentation.self
-/

#print Algebra.FinitePresentation.polynomial /-
/-- `R[X]` is finitely presented as `R`-algebra. -/
theorem polynomial : FinitePresentation R R[X] :=
  equiv (FinitePresentation.mvPolynomial R PUnit) (MvPolynomial.pUnitAlgEquiv R)
#align algebra.finite_presentation.polynomial Algebra.FinitePresentation.polynomial
-/

variable {R}

#print Algebra.FinitePresentation.quotient /-
/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
protected theorem quotient {I : Ideal A} (h : I.FG) (hfp : FinitePresentation R A) :
    FinitePresentation R (A ⧸ I) := by
  obtain ⟨n, f, hf⟩ := hfp
  refine' ⟨n, (Ideal.Quotient.mkₐ R I).comp f, _, _⟩
  · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
  · refine' Ideal.fg_ker_comp _ _ hf.2 _ hf.1
    simp [h]
#align algebra.finite_presentation.quotient Algebra.FinitePresentation.quotient
-/

#print Algebra.FinitePresentation.of_surjective /-
/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f) (hker : f.toRingHom.ker.FG)
    (hfp : FinitePresentation R A) : FinitePresentation R B :=
  equiv (hfp.Quotient hker) (Ideal.quotientKerAlgEquivOfSurjective hf)
#align algebra.finite_presentation.of_surjective Algebra.FinitePresentation.of_surjective
-/

#print Algebra.FinitePresentation.iff /-
theorem iff :
    FinitePresentation R A ↔
      ∃ (n : _)(I : Ideal (MvPolynomial (Fin n) R))(e : (_ ⧸ I) ≃ₐ[R] A), I.FG :=
  by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, f.to_ring_hom.ker, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    exact Equiv ((finite_presentation.mv_polynomial R _).Quotient hfg) e
#align algebra.finite_presentation.iff Algebra.FinitePresentation.iff
-/

/- warning: algebra.finite_presentation.iff_quotient_mv_polynomial' -> Algebra.FinitePresentation.iff_quotient_mvPolynomial' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} {A : Type.{u_2}} [_inst_1 : CommRing.{u_1} R] [_inst_2 : CommRing.{u_2} A] [_inst_3 : Algebra.{u_1, u_2} R A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2))], Iff (Algebra.FinitePresentation.{u_1, u_2} R A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) _inst_3) (Exists.{succ (succ u_2)} Type.{u_2} (fun (ι : Type.{u_2}) => Exists.{succ u_2} (Fintype.{u_2} ι) (fun (_x : Fintype.{u_2} ι) => Exists.{max (succ (max u_2 u_1)) (succ u_2)} (AlgHom.{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3) (fun (f : AlgHom.{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3) => And (Function.Surjective.{max (succ u_2) (succ u_1), succ u_2} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (coeFn.{max (succ (max u_2 u_1)) (succ u_2), max (succ (max u_2 u_1)) (succ u_2)} (AlgHom.{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3) (fun (_x : AlgHom.{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3) => (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) -> A) ([anonymous].{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3) f)) (Ideal.FG.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (RingHom.ker.{max u_2 u_1, u_2, max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (RingHom.{max u_2 u_1, u_2} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (Semiring.toNonAssocSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1)))) (Semiring.toNonAssocSemiring.{u_2} A (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)))) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (RingHom.ringHomClass.{max u_2 u_1, u_2} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (Semiring.toNonAssocSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1)))) (Semiring.toNonAssocSemiring.{u_2} A (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)))) (AlgHom.toRingHom.{u_1, max u_2 u_1, u_2} R (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) A (CommRing.toCommSemiring.{u_1} R _inst_1) (Ring.toSemiring.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (CommRing.toRing.{max u_2 u_1} (MvPolynomial.{u_2, u_1} ι R (CommRing.toCommSemiring.{u_1} R _inst_1)) (MvPolynomial.commRing.{u_1, u_2} R ι _inst_1))) (Ring.toSemiring.{u_2} A (CommRing.toRing.{u_2} A _inst_2)) (MvPolynomial.algebra.{u_1, u_1, u_2} R R ι (CommRing.toCommSemiring.{u_1} R _inst_1) (CommRing.toCommSemiring.{u_1} R _inst_1) (Algebra.id.{u_1} R (CommRing.toCommSemiring.{u_1} R _inst_1))) _inst_3 f)))))))
but is expected to have type
  forall {R : Type.{w₁}} {A : Type.{w₂}} [_inst_1 : CommRing.{w₁} R] [_inst_2 : CommRing.{w₂} A] [_inst_3 : Algebra.{w₁, w₂} R A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))], Iff (Algebra.FinitePresentation.{w₁, w₂} R A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) _inst_3) (Exists.{succ (succ u_1)} Type.{u_1} (fun (ι : Type.{u_1}) => Exists.{succ u_1} (Fintype.{u_1} ι) (fun (_x : Fintype.{u_1} ι) => Exists.{max (max (succ w₁) (succ w₂)) (succ u_1)} (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) (fun (f : AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) => And (Function.Surjective.{max (succ w₁) (succ u_1), succ w₂} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (FunLike.coe.{max (max (succ w₁) (succ w₂)) (succ u_1), max (succ w₁) (succ u_1), succ w₂} (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (fun (_x : MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2186 : MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) => A) _x) (SMulHomClass.toFunLike.{max (max w₁ w₂) u_1, w₁, max w₁ u_1, w₂} (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (SMulZeroClass.toSMul.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (AddMonoid.toZero.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (AddCommMonoid.toAddMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))))))) (DistribSMul.toSMulZeroClass.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (AddMonoid.toAddZeroClass.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (AddCommMonoid.toAddMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))))))) (DistribMulAction.toDistribSMul.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MonoidWithZero.toMonoid.{w₁} R (Semiring.toMonoidWithZero.{w₁} R (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)))) (AddCommMonoid.toAddMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))))))) (Module.toDistribMulAction.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))))) (Algebra.toModule.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)))))))) (SMulZeroClass.toSMul.{w₁, w₂} R A (AddMonoid.toZero.{w₂} A (AddCommMonoid.toAddMonoid.{w₂} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))))))) (DistribSMul.toSMulZeroClass.{w₁, w₂} R A (AddMonoid.toAddZeroClass.{w₂} A (AddCommMonoid.toAddMonoid.{w₂} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))))))) (DistribMulAction.toDistribSMul.{w₁, w₂} R A (MonoidWithZero.toMonoid.{w₁} R (Semiring.toMonoidWithZero.{w₁} R (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)))) (AddCommMonoid.toAddMonoid.{w₂} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)))))) (Module.toDistribMulAction.{w₁, w₂} R A (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))))) (Algebra.toModule.{w₁, w₂} R A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) _inst_3))))) (DistribMulActionHomClass.toSMulHomClass.{max (max w₁ w₂) u_1, w₁, max w₁ u_1, w₂} (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (MonoidWithZero.toMonoid.{w₁} R (Semiring.toMonoidWithZero.{w₁} R (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)))) (AddCommMonoid.toAddMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))))))) (AddCommMonoid.toAddMonoid.{w₂} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)))))) (Module.toDistribMulAction.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))))) (Algebra.toModule.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))))) (Module.toDistribMulAction.{w₁, w₂} R A (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))))) (Algebra.toModule.{w₁, w₂} R A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) _inst_3)) (NonUnitalAlgHomClass.toDistribMulActionHomClass.{max (max w₁ w₂) u_1, w₁, max w₁ u_1, w₂} (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (MonoidWithZero.toMonoid.{w₁} R (Semiring.toMonoidWithZero.{w₁} R (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)))) (Module.toDistribMulAction.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))))) (Algebra.toModule.{w₁, max w₁ u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))))) (Module.toDistribMulAction.{w₁, w₂} R A (CommSemiring.toSemiring.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{w₂} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{w₂} A (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2))))) (Algebra.toModule.{w₁, w₂} R A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) _inst_3)) (AlgHom.instNonUnitalAlgHomClassToMonoidToMonoidWithZeroToSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToDistribMulActionToAddCommMonoidToModuleToDistribMulActionToAddCommMonoidToModule.{w₁, max w₁ u_1, w₂, max (max w₁ w₂) u_1} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3 (AlgHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3) (AlgHom.algHomClass.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3))))) f)) (Ideal.FG.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (RingHom.ker.{max w₁ u_1, w₂, max (max w₁ w₂) u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (RingHom.{max w₁ u_1, w₂} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))) (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)))) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (RingHom.instRingHomClassRingHom.{max w₁ u_1, w₂} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (Semiring.toNonAssocSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1)))) (Semiring.toNonAssocSemiring.{w₂} A (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)))) (AlgHom.toRingHom.{w₁, max w₁ u_1, w₂} R (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) A (CommRing.toCommSemiring.{w₁} R _inst_1) (CommSemiring.toSemiring.{max w₁ u_1} (MvPolynomial.{u_1, w₁} ι R (CommRing.toCommSemiring.{w₁} R _inst_1)) (MvPolynomial.commSemiring.{w₁, u_1} R ι (CommRing.toCommSemiring.{w₁} R _inst_1))) (CommSemiring.toSemiring.{w₂} A (CommRing.toCommSemiring.{w₂} A _inst_2)) (MvPolynomial.algebra.{w₁, w₁, u_1} R R ι (CommRing.toCommSemiring.{w₁} R _inst_1) (CommRing.toCommSemiring.{w₁} R _inst_1) (Algebra.id.{w₁} R (CommRing.toCommSemiring.{w₁} R _inst_1))) _inst_3 f)))))))
Case conversion may be inaccurate. Consider using '#align algebra.finite_presentation.iff_quotient_mv_polynomial' Algebra.FinitePresentation.iff_quotient_mvPolynomial'ₓ'. -/
/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
theorem iff_quotient_mvPolynomial' :
    FinitePresentation R A ↔
      ∃ (ι : Type u_2)(_ : Fintype ι)(f : MvPolynomial ι R →ₐ[R] A),
        Surjective f ∧ f.toRingHom.ker.FG :=
  by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine'
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.to_alg_hom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ _ hfk ulift_var.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv ulift_var.to_ring_equiv
  · rintro ⟨ι, hfintype, f, hf⟩
    skip
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    refine'
      ⟨Fintype.card ι, f.comp Equiv.symm, hf.1.comp (AlgEquiv.symm Equiv).Surjective,
        Ideal.fg_ker_comp _ f _ hf.2 equiv.symm.surjective⟩
    convert Submodule.fg_bot
    exact RingHom.ker_coe_equiv equiv.symm.to_ring_equiv
#align algebra.finite_presentation.iff_quotient_mv_polynomial' Algebra.FinitePresentation.iff_quotient_mvPolynomial'

#print Algebra.FinitePresentation.mvPolynomial_of_finitePresentation /-
/-- If `A` is a finitely presented `R`-algebra, then `mv_polynomial (fin n) A` is finitely presented
as `R`-algebra. -/
theorem mvPolynomial_of_finitePresentation (hfp : FinitePresentation R A) (ι : Type _) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) :=
  by
  rw [iff_quotient_mv_polynomial'] at hfp⊢
  classical
    obtain ⟨ι', _, f, hf_surj, hf_ker⟩ := hfp
    skip
    let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
    cases nonempty_fintype (Sum ι ι')
    refine'
      ⟨Sum ι ι', by infer_instance, g,
        (MvPolynomial.map_surjective f.to_ring_hom hf_surj).comp (AlgEquiv.surjective _),
        Ideal.fg_ker_comp _ _ _ _ (AlgEquiv.surjective _)⟩
    · convert Submodule.fg_bot
      exact RingHom.ker_coe_equiv (MvPolynomial.sumAlgEquiv R ι ι').toRingEquiv
    · rw [AlgHom.toRingHom_eq_coe, MvPolynomial.mapAlgHom_coe_ringHom, MvPolynomial.ker_map]
      exact hf_ker.map MvPolynomial.C
#align algebra.finite_presentation.mv_polynomial_of_finite_presentation Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
-/

#print Algebra.FinitePresentation.trans /-
/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
theorem trans [Algebra A B] [IsScalarTower R A B] (hfpA : FinitePresentation R A)
    (hfpB : FinitePresentation A B) : FinitePresentation R B :=
  by
  obtain ⟨n, I, e, hfg⟩ := Iff.1 hfpB
  exact Equiv ((mv_polynomial_of_finite_presentation hfpA _).Quotient hfg) (e.restrict_scalars R)
#align algebra.finite_presentation.trans Algebra.FinitePresentation.trans
-/

open MvPolynomial

/- warning: algebra.finite_presentation.of_restrict_scalars_finite_presentation -> Algebra.FinitePresentation.of_restrict_scalars_finitePresentation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_4 : CommRing.{u3} B] [_inst_5 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4))] [_inst_10 : Algebra.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4))] [_inst_11 : IsScalarTower.{u1, u2, u3} R A B (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} A B (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} A B (MulZeroClass.toHasZero.{u2} A (MulZeroOneClass.toMulZeroClass.{u2} A (MonoidWithZero.toMulZeroOneClass.{u2} A (Semiring.toMonoidWithZero.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))))) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} A B (Semiring.toMonoidWithZero.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (Module.toMulActionWithZero.{u2, u3} A B (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4))))) (Algebra.toModule.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)) _inst_10))))) (SMulZeroClass.toHasSmul.{u1, u3} R B (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} R B (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} R B (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u3} B (AddMonoid.toAddZeroClass.{u3} B (AddCommMonoid.toAddMonoid.{u3} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)))))))) (Module.toMulActionWithZero.{u1, u3} R B (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} B (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4))))) (Algebra.toModule.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)) _inst_5)))))], (Algebra.FinitePresentation.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)) _inst_5) -> (forall [hRA : Algebra.FiniteType.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_3], Algebra.FinitePresentation.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_4)) _inst_10)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] [_inst_4 : CommRing.{u3} B] [_inst_5 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4))] [_inst_10 : Algebra.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4))] [_inst_11 : IsScalarTower.{u1, u2, u3} R A B (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3) (Algebra.toSMul.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4)) _inst_10) (Algebra.toSMul.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4)) _inst_5)], (Algebra.FinitePresentation.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4)) _inst_5) -> (forall [hRA : Algebra.FiniteType.{u2, u1} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3], Algebra.FinitePresentation.{u2, u3} A B (CommRing.toCommSemiring.{u2} A _inst_2) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_4)) _inst_10)
Case conversion may be inaccurate. Consider using '#align algebra.finite_presentation.of_restrict_scalars_finite_presentation Algebra.FinitePresentation.of_restrict_scalars_finitePresentationₓ'. -/
-- We follow the proof of https://stacks.math.columbia.edu/tag/0561
-- TODO: extract out helper lemmas and tidy proof.
theorem of_restrict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B]
    (hRB : FinitePresentation R B) [hRA : FiniteType R A] : FinitePresentation A B := by
  classical
    obtain ⟨n, f, hf, s, hs⟩ := hRB
    let RX := MvPolynomial (Fin n) R
    let AX := MvPolynomial (Fin n) A
    refine' ⟨n, MvPolynomial.aeval (f ∘ X), _, _⟩
    · rw [← Algebra.range_top_iff_surjective, ← Algebra.adjoin_range_eq_range_aeval, Set.range_comp,
        _root_.eq_top_iff, ← @adjoin_adjoin_of_tower R A B, adjoin_image, adjoin_range_X,
        Algebra.map_top, (Algebra.range_top_iff_surjective _).mpr hf]
      exact subset_adjoin
    · obtain ⟨t, ht⟩ := hRA.out
      have := fun i : t => hf (algebraMap A B i)
      choose t' ht'
      have ht'' : Algebra.adjoin R (algebraMap A AX '' t ∪ Set.range (X : _ → AX)) = ⊤ :=
        by
        rw [adjoin_union_eq_adjoin_adjoin, ← Subalgebra.restrictScalars_top R]
        congr 1
        swap
        · exact Subalgebra.isScalarTower_mid _
        rw [adjoin_algebra_map, ht]
        apply Subalgebra.restrictScalars_injective R
        rw [← adjoin_restrict_scalars, adjoin_range_X, Subalgebra.restrictScalars_top,
          Subalgebra.restrictScalars_top]
      let g : t → AX := fun x => C (x : A) - map (algebraMap R A) (t' x)
      refine' ⟨s.image (map (algebraMap R A)) ∪ t.attach.image g, _⟩
      rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.attach_eq_univ,
        Finset.coe_univ, Set.image_univ]
      let s₀ := _
      let I := _
      change Ideal.span s₀ = I
      have leI : Ideal.span s₀ ≤ I := by
        rw [Ideal.span_le]
        rintro _ (⟨x, hx, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
        all_goals dsimp [g]; rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        · rw [MvPolynomial.aeval_map_algebraMap, ← aeval_unique]
          have := Ideal.subset_span hx
          rwa [hs] at this
        ·
          rw [map_sub, MvPolynomial.aeval_map_algebraMap, ← aeval_unique, aeval_C, ht',
            Subtype.coe_mk, sub_self]
      apply leI.antisymm
      intro x hx
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx
      let s₀ := _
      change x ∈ Ideal.span s₀
      have :
        x ∈
          (map (algebraMap R A) : _ →+* AX).srange.toAddSubmonoid ⊔
            (Ideal.span s₀).toAddSubmonoid :=
        by
        have : x ∈ (⊤ : Subalgebra R AX) := trivial
        rw [← ht''] at this
        apply adjoin_induction this
        · rintro _ (⟨x, hx, rfl⟩ | ⟨i, rfl⟩)
          · rw [algebra_map_eq, ← sub_add_cancel (C x) (map (algebraMap R A) (t' ⟨x, hx⟩)),
              add_comm]
            apply AddSubmonoid.add_mem_sup
            · exact Set.mem_range_self _
            · apply Ideal.subset_span
              apply Set.mem_union_right
              exact Set.mem_range_self ⟨x, hx⟩
          · apply AddSubmonoid.mem_sup_left
            exact ⟨X i, map_X _ _⟩
        · intro r
          apply AddSubmonoid.mem_sup_left
          exact ⟨C r, map_C _ _⟩
        · intro _ _ h₁ h₂
          exact add_mem h₁ h₂
        · intro x₁ x₂ h₁ h₂
          obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := add_submonoid.mem_sup.mp h₁
          obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := add_submonoid.mem_sup.mp h₂
          rw [add_mul, mul_add, add_assoc, ← map_mul]
          apply AddSubmonoid.add_mem_sup
          · exact Set.mem_range_self _
          · refine' add_mem (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)
      obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := add_submonoid.mem_sup.mp this
      rw [map_add, aeval_map_algebra_map, ← aeval_unique, show aeval (f ∘ X) q = 0 from leI hq,
        add_zero] at hx
      suffices Ideal.span (s : Set RX) ≤ (Ideal.span s₀).comap (map <| algebraMap R A)
        by
        refine' add_mem _ hq
        rw [hs] at this
        exact this hx
      rw [Ideal.span_le]
      intro x hx
      apply Ideal.subset_span
      apply Set.mem_union_left
      exact Set.mem_image_of_mem _ hx
#align algebra.finite_presentation.of_restrict_scalars_finite_presentation Algebra.FinitePresentation.of_restrict_scalars_finitePresentation

#print Algebra.FinitePresentation.ker_fg_of_mvPolynomial /-
-- TODO: extract out helper lemmas and tidy proof.
/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
theorem ker_fg_of_mvPolynomial {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A)
    (hf : Function.Surjective f) (hfp : FinitePresentation R A) : f.toRingHom.ker.FG := by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := hfp
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh
    let aeval_h : RXm →ₐ[R] RXn := aeval h
    let g' : Fin n → RXn := fun i => X i - aeval_h (g i)
    refine' ⟨finset.univ.image g' ∪ s.image aeval_h, _⟩
    simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
    have hh' : ∀ x, f (aeval_h x) = f' x := by
      intro x
      rw [← f.coe_to_ring_hom, map_aeval]
      simp_rw [AlgHom.coe_toRingHom, hh]
      rw [AlgHom.comp_algebraMap, ← aeval_eq_eval₂_hom, ← aeval_unique]
    let s' := Set.range g' ∪ aeval_h '' s
    have leI : Ideal.span s' ≤ f.to_ring_hom.ker :=
      by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨x, hx, rfl⟩)
      · change f (g' i) = 0
        rw [map_sub, ← hg, hh', sub_self]
      · change f (aeval_h x) = 0
        rw [hh']
        change x ∈ f'.to_ring_hom.ker
        rw [← hs]
        exact Ideal.subset_span hx
    apply leI.antisymm
    intro x hx
    have : x ∈ aeval_h.range.to_add_submonoid ⊔ (Ideal.span s').toAddSubmonoid :=
      by
      have : x ∈ adjoin R (Set.range X : Set RXn) :=
        by
        rw [adjoin_range_X]
        trivial
      apply adjoin_induction this
      · rintro _ ⟨i, rfl⟩
        rw [← sub_add_cancel (X i) (aeval h (g i)), add_comm]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · apply Submodule.subset_span
          apply Set.mem_union_left
          exact Set.mem_range_self _
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, aeval_C _ _⟩
      · intro _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro p₁ p₂ h₁ h₂
        obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := add_submonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := add_submonoid.mem_sup.mp h₂
        rw [mul_add, add_mul, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · exact add_mem (Ideal.mul_mem_right _ _ hy₁) (Ideal.mul_mem_left _ _ hy₂)
    obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := add_submonoid.mem_sup.mp this
    refine' add_mem _ hy
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
      show f y = 0 from leI hy, add_zero, hh'] at hx
    suffices Ideal.span (s : Set RXm) ≤ (Ideal.span s').comap aeval_h
      by
      apply this
      rwa [hs]
    rw [Ideal.span_le]
    intro x hx
    apply Submodule.subset_span
    apply Set.mem_union_right
    exact Set.mem_image_of_mem _ hx
#align algebra.finite_presentation.ker_fg_of_mv_polynomial Algebra.FinitePresentation.ker_fg_of_mvPolynomial
-/

#print Algebra.FinitePresentation.ker_fG_of_surjective /-
/-- If `f : A →ₐ[R] B` is a sujection between finitely-presented `R`-algebras, then the kernel of
`f` is finitely generated. -/
theorem ker_fG_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (hRA : FinitePresentation R A) (hRB : FinitePresentation R B) : f.toRingHom.ker.FG :=
  by
  obtain ⟨n, g, hg, hg'⟩ := hRA
  convert(ker_fg_of_mv_polynomial (f.comp g) (hf.comp hg) hRB).map g.to_ring_hom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap, Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R →+* A) hg]
#align algebra.finite_presentation.ker_fg_of_surjective Algebra.FinitePresentation.ker_fG_of_surjective
-/

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRing A] [CommRing B] [CommRing C]

#print RingHom.FinitePresentation /-
/-- A ring morphism `A →+* B` is of `finite_presentation` if `B` is finitely presented as
`A`-algebra. -/
def FinitePresentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra
#align ring_hom.finite_presentation RingHom.FinitePresentation
-/

namespace FiniteType

/- warning: ring_hom.finite_type.of_finite_presentation -> RingHom.FiniteType.of_finitePresentation is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] {f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))}, (RingHom.FinitePresentation.{u1, u2} A B _inst_1 _inst_2 f) -> (RingHom.FiniteType.{u1, u2} A B _inst_1 _inst_2 f)
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : CommRing.{u2} A] [_inst_2 : CommRing.{u1} B] {f : RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))}, (RingHom.FinitePresentation.{u2, u1} A B _inst_1 _inst_2 f) -> (RingHom.FiniteType.{u2, u1} A B _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_type.of_finite_presentation RingHom.FiniteType.of_finitePresentationₓ'. -/
theorem of_finitePresentation {f : A →+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf
#align ring_hom.finite_type.of_finite_presentation RingHom.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable (A)

#print RingHom.FinitePresentation.id /-
theorem id : FinitePresentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A
#align ring_hom.finite_presentation.id RingHom.FinitePresentation.id
-/

variable {A}

/- warning: ring_hom.finite_presentation.comp_surjective -> RingHom.FinitePresentation.comp_surjective is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} {C : Type.{u3}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] [_inst_3 : CommRing.{u3} C] {f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))} {g : RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))}, (RingHom.FinitePresentation.{u1, u2} A B _inst_1 _inst_2 f) -> (Function.Surjective.{succ u2, succ u3} B C (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))) (fun (_x : RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))) => B -> C) (RingHom.hasCoeToFun.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))) g)) -> (Ideal.FG.{u2} B (Ring.toSemiring.{u2} B (CommRing.toRing.{u2} B _inst_2)) (RingHom.ker.{u2, u3, max u2 u3} B C (RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))) (Ring.toSemiring.{u2} B (CommRing.toRing.{u2} B _inst_2)) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_3)) (RingHom.ringHomClass.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))) g)) -> (RingHom.FinitePresentation.{u1, u3} A C _inst_1 _inst_3 (RingHom.comp.{u1, u2, u3} A B C (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3))) g f))
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommRing.{u3} A] [_inst_2 : CommRing.{u2} B] [_inst_3 : CommRing.{u1} C] {f : RingHom.{u3, u2} A B (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_1))) (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2)))} {g : RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))}, (RingHom.FinitePresentation.{u3, u2} A B _inst_1 _inst_2 f) -> (Function.Surjective.{succ u2, succ u1} B C (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : B) => C) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) B C (NonUnitalNonAssocSemiring.toMul.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))))) (NonUnitalNonAssocSemiring.toMul.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) B C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3))) (RingHom.instRingHomClassRingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3))))))) g)) -> (Ideal.FG.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2)) (RingHom.ker.{u2, u1, max u2 u1} B C (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)) (RingHom.instRingHomClassRingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))) g)) -> (RingHom.FinitePresentation.{u3, u1} A C _inst_1 _inst_3 (RingHom.comp.{u3, u2, u1} A B C (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_1))) (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3))) g f))
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_presentation.comp_surjective RingHom.FinitePresentation.comp_surjectiveₓ'. -/
theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FinitePresentation) (hg : Surjective g)
    (hker : g.ker.FG) : (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.of_surjective A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra
    { g with
      toFun := g
      commutes' := fun a => rfl }
    hg hker hf
#align ring_hom.finite_presentation.comp_surjective RingHom.FinitePresentation.comp_surjective

/- warning: ring_hom.finite_presentation.of_surjective -> RingHom.FinitePresentation.of_surjective is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] (f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))), (Function.Surjective.{succ u1, succ u2} A B (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) (fun (_x : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) => A -> B) (RingHom.hasCoeToFun.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) f)) -> (Ideal.FG.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_1)) (RingHom.ker.{u1, u2, max u1 u2} A B (RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_1)) (Ring.toSemiring.{u2} B (CommRing.toRing.{u2} B _inst_2)) (RingHom.ringHomClass.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) f)) -> (RingHom.FinitePresentation.{u1, u2} A B _inst_1 _inst_2 f)
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : CommRing.{u2} A] [_inst_2 : CommRing.{u1} B] (f : RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))), (Function.Surjective.{succ u2, succ u1} A B (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : A) => B) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) A B (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) A B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2))) (RingHom.instRingHomClassRingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2))))))) f)) -> (Ideal.FG.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1)) (RingHom.ker.{u2, u1, max u2 u1} A B (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))) f)) -> (RingHom.FinitePresentation.{u2, u1} A B _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_presentation.of_surjective RingHom.FinitePresentation.of_surjectiveₓ'. -/
theorem of_surjective (f : A →+* B) (hf : Surjective f) (hker : f.ker.FG) : f.FinitePresentation :=
  by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker
#align ring_hom.finite_presentation.of_surjective RingHom.FinitePresentation.of_surjective

/- warning: ring_hom.finite_presentation.of_finite_type -> RingHom.FinitePresentation.of_finiteType is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] [_inst_4 : IsNoetherianRing.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_1))] {f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))}, Iff (RingHom.FiniteType.{u1, u2} A B _inst_1 _inst_2 f) (RingHom.FinitePresentation.{u1, u2} A B _inst_1 _inst_2 f)
but is expected to have type
  forall {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : CommRing.{u2} A] [_inst_2 : CommRing.{u1} B] [_inst_4 : IsNoetherianRing.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))] {f : RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_1))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_2)))}, Iff (RingHom.FiniteType.{u2, u1} A B _inst_1 _inst_2 f) (RingHom.FinitePresentation.{u2, u1} A B _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_presentation.of_finite_type RingHom.FinitePresentation.of_finiteTypeₓ'. -/
theorem of_finiteType [IsNoetherianRing A] {f : A →+* B} : f.FiniteType ↔ f.FinitePresentation :=
  @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _
#align ring_hom.finite_presentation.of_finite_type RingHom.FinitePresentation.of_finiteType

/- warning: ring_hom.finite_presentation.comp -> RingHom.FinitePresentation.comp is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} {C : Type.{u3}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] [_inst_3 : CommRing.{u3} C] {g : RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))} {f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))}, (RingHom.FinitePresentation.{u2, u3} B C _inst_2 _inst_3 g) -> (RingHom.FinitePresentation.{u1, u2} A B _inst_1 _inst_2 f) -> (RingHom.FinitePresentation.{u1, u3} A C _inst_1 _inst_3 (RingHom.comp.{u1, u2, u3} A B C (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3))) g f))
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u3}} {C : Type.{u2}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u3} B] [_inst_3 : CommRing.{u2} C] {g : RingHom.{u3, u2} B C (Semiring.toNonAssocSemiring.{u3} B (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_2))) (Semiring.toNonAssocSemiring.{u2} C (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_3)))} {f : RingHom.{u1, u3} A B (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1))) (Semiring.toNonAssocSemiring.{u3} B (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_2)))}, (RingHom.FinitePresentation.{u3, u2} B C _inst_2 _inst_3 g) -> (RingHom.FinitePresentation.{u1, u3} A B _inst_1 _inst_2 f) -> (RingHom.FinitePresentation.{u1, u2} A C _inst_1 _inst_3 (RingHom.comp.{u1, u3, u2} A B C (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1))) (Semiring.toNonAssocSemiring.{u3} B (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_2))) (Semiring.toNonAssocSemiring.{u2} C (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_3))) g f))
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_presentation.comp RingHom.FinitePresentation.compₓ'. -/
theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation :=
  @Algebra.FinitePresentation.trans A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    {
      smul_assoc := fun a b c =>
        by
        simp only [Algebra.smul_def, RingHom.map_mul, mul_assoc]
        rfl }
    hf hg
#align ring_hom.finite_presentation.comp RingHom.FinitePresentation.comp

/- warning: ring_hom.finite_presentation.of_comp_finite_type -> RingHom.FinitePresentation.of_comp_finiteType is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} {C : Type.{u3}} [_inst_1 : CommRing.{u1} A] [_inst_2 : CommRing.{u2} B] [_inst_3 : CommRing.{u3} C] (f : RingHom.{u1, u2} A B (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2)))) {g : RingHom.{u2, u3} B C (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3)))}, (RingHom.FinitePresentation.{u1, u3} A C _inst_1 _inst_3 (RingHom.comp.{u1, u2, u3} A B C (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} B (Ring.toNonAssocRing.{u2} B (CommRing.toRing.{u2} B _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} C (Ring.toNonAssocRing.{u3} C (CommRing.toRing.{u3} C _inst_3))) g f)) -> (RingHom.FiniteType.{u1, u2} A B _inst_1 _inst_2 f) -> (RingHom.FinitePresentation.{u2, u3} B C _inst_2 _inst_3 g)
but is expected to have type
  forall {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommRing.{u3} A] [_inst_2 : CommRing.{u2} B] [_inst_3 : CommRing.{u1} C] (f : RingHom.{u3, u2} A B (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_1))) (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2)))) {g : RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3)))}, (RingHom.FinitePresentation.{u3, u1} A C _inst_1 _inst_3 (RingHom.comp.{u3, u2, u1} A B C (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_1))) (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_2))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_3))) g f)) -> (RingHom.FiniteType.{u3, u2} A B _inst_1 _inst_2 f) -> (RingHom.FinitePresentation.{u2, u1} B C _inst_2 _inst_3 g)
Case conversion may be inaccurate. Consider using '#align ring_hom.finite_presentation.of_comp_finite_type RingHom.FinitePresentation.of_comp_finiteTypeₓ'. -/
theorem of_comp_finiteType (f : A →+* B) {g : B →+* C} (hg : (g.comp f).FinitePresentation)
    (hf : f.FiniteType) : g.FinitePresentation :=
  @Algebra.FinitePresentation.of_restrict_scalars_finitePresentation _ _ f.toAlgebra _
    (g.comp f).toAlgebra g.toAlgebra
    (@IsScalarTower.of_algebraMap_eq' _ _ _ f.toAlgebra g.toAlgebra (g.comp f).toAlgebra rfl) hg hf
#align ring_hom.finite_presentation.of_comp_finite_type RingHom.FinitePresentation.of_comp_finiteType

end FinitePresentation

end RingHom

namespace AlgHom

variable {R A B C : Type _} [CommRing R]

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

#print AlgHom.FinitePresentation /-
/-- An algebra morphism `A →ₐ[R] B` is of `finite_presentation` if it is of finite presentation as
ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
def FinitePresentation (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation
#align alg_hom.finite_presentation AlgHom.FinitePresentation
-/

namespace FiniteType

variable {R A}

/- warning: alg_hom.finite_type.of_finite_presentation -> AlgHom.FiniteType.of_finitePresentation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] {f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6}, (AlgHom.FinitePresentation.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FiniteType.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
but is expected to have type
  forall {R : Type.{u3}} {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : CommRing.{u3} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u1} B] [_inst_5 : Algebra.{u3, u2} R A (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] [_inst_6 : Algebra.{u3, u1} R B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))] {f : AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6}, (AlgHom.FinitePresentation.{u3, u2, u1} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FiniteType.{u3, u2, u1} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_type.of_finite_presentation AlgHom.FiniteType.of_finitePresentationₓ'. -/
theorem of_finitePresentation {f : A →ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.of_finitePresentation hf
#align alg_hom.finite_type.of_finite_presentation AlgHom.FiniteType.of_finitePresentation

end FiniteType

namespace FinitePresentation

variable (R A)

/- warning: alg_hom.finite_presentation.id -> AlgHom.FinitePresentation.id is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (A : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))], AlgHom.FinitePresentation.{u1, u2, u2} R A A _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgHom.id.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) _inst_5)
but is expected to have type
  forall (R : Type.{u2}) (A : Type.{u1}) [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_5 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))], AlgHom.FinitePresentation.{u2, u1, u1} R A A _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (AlgHom.id.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_5)
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.id AlgHom.FinitePresentation.idₓ'. -/
theorem id : FinitePresentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A
#align alg_hom.finite_presentation.id AlgHom.FinitePresentation.id

variable {R A}

/- warning: alg_hom.finite_presentation.comp -> AlgHom.FinitePresentation.comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_4 : CommRing.{u4} C] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] [_inst_7 : Algebra.{u1, u4} R C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4))] {g : AlgHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7} {f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6}, (AlgHom.FinitePresentation.{u1, u3, u4} R B C _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g) -> (AlgHom.FinitePresentation.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FinitePresentation.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u1, u2, u3, u4} R A B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_5 _inst_6 _inst_7 g f))
but is expected to have type
  forall {R : Type.{u4}} {A : Type.{u1}} {B : Type.{u3}} {C : Type.{u2}} [_inst_1 : CommRing.{u4} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : CommRing.{u3} B] [_inst_4 : CommRing.{u2} C] [_inst_5 : Algebra.{u4, u1} R A (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] [_inst_6 : Algebra.{u4, u3} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_3))] [_inst_7 : Algebra.{u4, u2} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_4))] {g : AlgHom.{u4, u3, u2} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_3)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_4)) _inst_6 _inst_7} {f : AlgHom.{u4, u1, u3} R A B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_3)) _inst_5 _inst_6}, (AlgHom.FinitePresentation.{u4, u3, u2} R B C _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g) -> (AlgHom.FinitePresentation.{u4, u1, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FinitePresentation.{u4, u1, u2} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u4, u1, u3, u2} R A B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_3)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_4)) _inst_5 _inst_6 _inst_7 g f))
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.comp AlgHom.FinitePresentation.compₓ'. -/
theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation)
    (hf : f.FinitePresentation) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf
#align alg_hom.finite_presentation.comp AlgHom.FinitePresentation.comp

/- warning: alg_hom.finite_presentation.comp_surjective -> AlgHom.FinitePresentation.comp_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_4 : CommRing.{u4} C] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] [_inst_7 : Algebra.{u1, u4} R C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4))] {f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6} {g : AlgHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7}, (AlgHom.FinitePresentation.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (Function.Surjective.{succ u3, succ u4} B C (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (AlgHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7) (fun (_x : AlgHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7) => B -> C) ([anonymous].{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7) g)) -> (Ideal.FG.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (RingHom.ker.{u3, u4, max u3 u4} B C (RingHom.{u3, u4} B C (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))) (Semiring.toNonAssocSemiring.{u4} C (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)))) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) (RingHom.ringHomClass.{u3, u4} B C (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))) (Semiring.toNonAssocSemiring.{u4} C (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)))) (AlgHom.toRingHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7 g))) -> (AlgHom.FinitePresentation.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u1, u2, u3, u4} R A B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_5 _inst_6 _inst_7 g f))
but is expected to have type
  forall {R : Type.{u4}} {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommRing.{u4} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : CommRing.{u2} B] [_inst_4 : CommRing.{u1} C] [_inst_5 : Algebra.{u4, u3} R A (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] [_inst_6 : Algebra.{u4, u2} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))] [_inst_7 : Algebra.{u4, u1} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))] {f : AlgHom.{u4, u3, u2} R A B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) _inst_5 _inst_6} {g : AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7}, (AlgHom.FinitePresentation.{u4, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (Function.Surjective.{succ u2, succ u1} B C (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7) B (fun (_x : B) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2186 : B) => C) _x) (SMulHomClass.toFunLike.{max u2 u1, u4, u2, u1} (AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7) R B C (SMulZeroClass.toSMul.{u4, u2} R B (AddMonoid.toZero.{u2} B (AddCommMonoid.toAddMonoid.{u2} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))))))) (DistribSMul.toSMulZeroClass.{u4, u2} R B (AddMonoid.toAddZeroClass.{u2} B (AddCommMonoid.toAddMonoid.{u2} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))))))) (DistribMulAction.toDistribSMul.{u4, u2} R B (MonoidWithZero.toMonoid.{u4} R (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u2} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)))))) (Module.toDistribMulAction.{u4, u2} R B (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))))) (Algebra.toModule.{u4, u2} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) _inst_6))))) (SMulZeroClass.toSMul.{u4, u1} R C (AddMonoid.toZero.{u1} C (AddCommMonoid.toAddMonoid.{u1} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))))))) (DistribSMul.toSMulZeroClass.{u4, u1} R C (AddMonoid.toAddZeroClass.{u1} C (AddCommMonoid.toAddMonoid.{u1} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))))))) (DistribMulAction.toDistribSMul.{u4, u1} R C (MonoidWithZero.toMonoid.{u4} R (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u1} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)))))) (Module.toDistribMulAction.{u4, u1} R C (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))))) (Algebra.toModule.{u4, u1} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_7))))) (DistribMulActionHomClass.toSMulHomClass.{max u2 u1, u4, u2, u1} (AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7) R B C (MonoidWithZero.toMonoid.{u4} R (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u2} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)))))) (AddCommMonoid.toAddMonoid.{u1} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)))))) (Module.toDistribMulAction.{u4, u2} R B (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))))) (Algebra.toModule.{u4, u2} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) _inst_6)) (Module.toDistribMulAction.{u4, u1} R C (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))))) (Algebra.toModule.{u4, u1} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_7)) (NonUnitalAlgHomClass.toDistribMulActionHomClass.{max u2 u1, u4, u2, u1} (AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7) R B C (MonoidWithZero.toMonoid.{u4} R (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)))) (Module.toDistribMulAction.{u4, u2} R B (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} B (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))))) (Algebra.toModule.{u4, u2} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) _inst_6)) (Module.toDistribMulAction.{u4, u1} R C (CommSemiring.toSemiring.{u4} R (CommRing.toCommSemiring.{u4} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} C (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))))) (Algebra.toModule.{u4, u1} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_7)) (AlgHom.instNonUnitalAlgHomClassToMonoidToMonoidWithZeroToSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToDistribMulActionToAddCommMonoidToModuleToDistribMulActionToAddCommMonoidToModule.{u4, u2, u1, max u2 u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7 (AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7) (AlgHom.algHomClass.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7))))) g)) -> (Ideal.FG.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (RingHom.ker.{u2, u1, max u2 u1} B C (RingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)))) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) (RingHom.instRingHomClassRingHom.{u2, u1} B C (Semiring.toNonAssocSemiring.{u2} B (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))) (Semiring.toNonAssocSemiring.{u1} C (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)))) (AlgHom.toRingHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7 g))) -> (AlgHom.FinitePresentation.{u4, u3, u1} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u4, u3, u2, u1} R A B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_5 _inst_6 _inst_7 g f))
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.comp_surjective AlgHom.FinitePresentation.comp_surjectiveₓ'. -/
theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FinitePresentation)
    (hg : Surjective g) (hker : g.toRingHom.ker.FG) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp_surjective hf hg hker
#align alg_hom.finite_presentation.comp_surjective AlgHom.FinitePresentation.comp_surjective

/- warning: alg_hom.finite_presentation.of_surjective -> AlgHom.FinitePresentation.of_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] (f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6), (Function.Surjective.{succ u2, succ u3} A B (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6) (fun (_x : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6) => A -> B) ([anonymous].{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6) f)) -> (Ideal.FG.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (RingHom.ker.{u2, u3, max u2 u3} A B (RingHom.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)))) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (RingHom.ringHomClass.{u2, u3} A B (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Semiring.toNonAssocSemiring.{u3} B (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)))) (AlgHom.toRingHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6 f))) -> (AlgHom.FinitePresentation.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
but is expected to have type
  forall {R : Type.{u3}} {A : Type.{u2}} {B : Type.{u1}} [_inst_1 : CommRing.{u3} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u1} B] [_inst_5 : Algebra.{u3, u2} R A (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] [_inst_6 : Algebra.{u3, u1} R B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))] (f : AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6), (Function.Surjective.{succ u2, succ u1} A B (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.GroupAction._hyg.2186 : A) => B) _x) (SMulHomClass.toFunLike.{max u2 u1, u3, u2, u1} (AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6) R A B (SMulZeroClass.toSMul.{u3, u2} R A (AddMonoid.toZero.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (DistribSMul.toSMulZeroClass.{u3, u2} R A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))))) (DistribMulAction.toDistribSMul.{u3, u2} R A (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))))) (Module.toDistribMulAction.{u3, u2} R A (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (Algebra.toModule.{u3, u2} R A (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_5))))) (SMulZeroClass.toSMul.{u3, u1} R B (AddMonoid.toZero.{u1} B (AddCommMonoid.toAddMonoid.{u1} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))))))) (DistribSMul.toSMulZeroClass.{u3, u1} R B (AddMonoid.toAddZeroClass.{u1} B (AddCommMonoid.toAddMonoid.{u1} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))))))) (DistribMulAction.toDistribSMul.{u3, u1} R B (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u1} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)))))) (Module.toDistribMulAction.{u3, u1} R B (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))))) (Algebra.toModule.{u3, u1} R B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_6))))) (DistribMulActionHomClass.toSMulHomClass.{max u2 u1, u3, u2, u1} (AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6) R A B (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))))) (AddCommMonoid.toAddMonoid.{u1} B (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)))))) (Module.toDistribMulAction.{u3, u2} R A (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (Algebra.toModule.{u3, u2} R A (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_5)) (Module.toDistribMulAction.{u3, u1} R B (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))))) (Algebra.toModule.{u3, u1} R B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_6)) (NonUnitalAlgHomClass.toDistribMulActionHomClass.{max u2 u1, u3, u2, u1} (AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6) R A B (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)))) (Module.toDistribMulAction.{u3, u2} R A (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) (Algebra.toModule.{u3, u2} R A (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_5)) (Module.toDistribMulAction.{u3, u1} R B (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} B (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} B (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))))) (Algebra.toModule.{u3, u1} R B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_6)) (AlgHom.instNonUnitalAlgHomClassToMonoidToMonoidWithZeroToSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToNonUnitalNonAssocSemiringToNonAssocSemiringToDistribMulActionToAddCommMonoidToModuleToDistribMulActionToAddCommMonoidToModule.{u3, u2, u1, max u2 u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6 (AlgHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6) (AlgHom.algHomClass.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6))))) f)) -> (Ideal.FG.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (RingHom.ker.{u2, u1, max u2 u1} A B (RingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)))) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) (RingHom.instRingHomClassRingHom.{u2, u1} A B (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Semiring.toNonAssocSemiring.{u1} B (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)))) (AlgHom.toRingHom.{u3, u2, u1} R A B (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6 f))) -> (AlgHom.FinitePresentation.{u3, u2, u1} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.of_surjective AlgHom.FinitePresentation.of_surjectiveₓ'. -/
theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) (hker : f.toRingHom.ker.FG) :
    f.FinitePresentation :=
  RingHom.FinitePresentation.of_surjective f hf hker
#align alg_hom.finite_presentation.of_surjective AlgHom.FinitePresentation.of_surjective

/- warning: alg_hom.finite_presentation.of_finite_type -> AlgHom.FinitePresentation.of_finiteType is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] [_inst_8 : IsNoetherianRing.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] {f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6}, Iff (AlgHom.FiniteType.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) (AlgHom.FinitePresentation.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u3}} {B : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : CommRing.{u1} B] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] [_inst_6 : Algebra.{u2, u1} R B (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3))] [_inst_8 : IsNoetherianRing.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] {f : AlgHom.{u2, u3, u1} R A B (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) (CommSemiring.toSemiring.{u1} B (CommRing.toCommSemiring.{u1} B _inst_3)) _inst_5 _inst_6}, Iff (AlgHom.FiniteType.{u2, u3, u1} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) (AlgHom.FinitePresentation.{u2, u3, u1} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f)
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.of_finite_type AlgHom.FinitePresentation.of_finiteTypeₓ'. -/
theorem of_finiteType [IsNoetherianRing A] {f : A →ₐ[R] B} : f.FiniteType ↔ f.FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType
#align alg_hom.finite_presentation.of_finite_type AlgHom.FinitePresentation.of_finiteType

/- warning: alg_hom.finite_presentation.of_comp_finite_type -> AlgHom.FinitePresentation.of_comp_finiteType is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} {B : Type.{u3}} {C : Type.{u4}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : CommRing.{u3} B] [_inst_4 : CommRing.{u4} C] [_inst_5 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] [_inst_6 : Algebra.{u1, u3} R B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] [_inst_7 : Algebra.{u1, u4} R C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4))] (f : AlgHom.{u1, u2, u3} R A B (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) _inst_5 _inst_6) {g : AlgHom.{u1, u3, u4} R B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_6 _inst_7}, (AlgHom.FinitePresentation.{u1, u2, u4} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u1, u2, u3, u4} R A B C (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3)) (Ring.toSemiring.{u4} C (CommRing.toRing.{u4} C _inst_4)) _inst_5 _inst_6 _inst_7 g f)) -> (AlgHom.FiniteType.{u1, u2, u3} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FinitePresentation.{u1, u3, u4} R B C _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g)
but is expected to have type
  forall {R : Type.{u4}} {A : Type.{u3}} {B : Type.{u2}} {C : Type.{u1}} [_inst_1 : CommRing.{u4} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : CommRing.{u2} B] [_inst_4 : CommRing.{u1} C] [_inst_5 : Algebra.{u4, u3} R A (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] [_inst_6 : Algebra.{u4, u2} R B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3))] [_inst_7 : Algebra.{u4, u1} R C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4))] (f : AlgHom.{u4, u3, u2} R A B (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) _inst_5 _inst_6) {g : AlgHom.{u4, u2, u1} R B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_6 _inst_7}, (AlgHom.FinitePresentation.{u4, u3, u1} R A C _inst_1 _inst_2 _inst_4 _inst_5 _inst_7 (AlgHom.comp.{u4, u3, u2, u1} R A B C (CommRing.toCommSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) (CommSemiring.toSemiring.{u2} B (CommRing.toCommSemiring.{u2} B _inst_3)) (CommSemiring.toSemiring.{u1} C (CommRing.toCommSemiring.{u1} C _inst_4)) _inst_5 _inst_6 _inst_7 g f)) -> (AlgHom.FiniteType.{u4, u3, u2} R A B _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 f) -> (AlgHom.FinitePresentation.{u4, u2, u1} R B C _inst_1 _inst_3 _inst_4 _inst_6 _inst_7 g)
Case conversion may be inaccurate. Consider using '#align alg_hom.finite_presentation.of_comp_finite_type AlgHom.FinitePresentation.of_comp_finiteTypeₓ'. -/
theorem of_comp_finiteType (f : A →ₐ[R] B) {g : B →ₐ[R] C} (h : (g.comp f).FinitePresentation)
    (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'
#align alg_hom.finite_presentation.of_comp_finite_type AlgHom.FinitePresentation.of_comp_finiteType

end FinitePresentation

end AlgHom

