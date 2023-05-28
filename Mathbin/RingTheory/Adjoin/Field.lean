/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module ring_theory.adjoin.field
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Splits
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.RingTheory.AdjoinRoot

/-!
# Adjoining elements to a field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some lemmas on the ring generating by adjoining an element to a field.

## Main statements

* `lift_of_splits`: If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`.

-/


noncomputable section

open BigOperators Polynomial

section Embeddings

variable (F : Type _) [Field F]

/- warning: alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly -> AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) [_inst_1 : Field.{u1} F] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] [_inst_3 : Algebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2))] (x : R), AlgEquiv.{u1, u2, u1} F (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3) R (Subalgebra.setLike.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3)) (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.hasSingleton.{u2} R) x))) (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Subalgebra.toSemiring.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3 (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.hasSingleton.{u2} R) x))) (Ring.toSemiring.{u1} (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (CommRing.toRing.{u1} (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (AdjoinRoot.instCommRing.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)))) (Subalgebra.algebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3 (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.hasSingleton.{u2} R) x))) (AdjoinRoot.algebra.{u1, u1} F F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x) (CommRing.toCommSemiring.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1))) (Algebra.id.{u1} F (CommRing.toCommSemiring.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)))))
but is expected to have type
  forall (F : Type.{u1}) [_inst_1 : Field.{u1} F] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] [_inst_3 : Algebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2))] (x : R), AlgEquiv.{u1, u2, u1} F (Subtype.{succ u2} R (fun (x_1 : R) => Membership.mem.{u2, u2} R (Subalgebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3) R (Subalgebra.instSetLikeSubalgebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3)) x_1 (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.instSingletonSet.{u2} R) x)))) (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Subalgebra.toSemiring.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3 (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.instSingletonSet.{u2} R) x))) (CommSemiring.toSemiring.{u1} (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (CommRing.toCommSemiring.{u1} (AdjoinRoot.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)) (AdjoinRoot.instCommRing.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x)))) (Subalgebra.algebra.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3 (Algebra.adjoin.{u1, u2} F R (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_2)) _inst_3 (Singleton.singleton.{u2, u2} R (Set.{u2} R) (Set.instSingletonSet.{u2} R) x))) (AdjoinRoot.instAlgebraAdjoinRootToSemiringToCommSemiringInstCommRing.{u1, u1} F F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (minpoly.{u1, u2} F R (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1)) (CommRing.toRing.{u2} R _inst_2) _inst_3 x) (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)) (Algebra.id.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))))
Case conversion may be inaccurate. Consider using '#align alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly AlgEquiv.adjoinSingletonEquivAdjoinRootMinpolyₓ'. -/
/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type _} [CommRing R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective
      (AlgHom.codRestrict (AdjoinRoot.liftHom _ x <| minpoly.aeval F x) _ fun p =>
        AdjoinRoot.induction_on _ p fun p =>
          (Algebra.adjoin_singleton_eq_range_aeval F x).symm ▸
            (Polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩)
      ⟨(AlgHom.injective_codRestrict _ _ _).2 <|
          (injective_iff_map_eq_zero _).2 fun p =>
            AdjoinRoot.induction_on _ p fun p hp =>
              Ideal.Quotient.eq_zero_iff_mem.2 <| Ideal.mem_span_singleton.2 <| minpoly.dvd F x hp,
        fun y =>
        let ⟨p, hp⟩ :=
          (SetLike.ext_iff.1 (Algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2
        ⟨AdjoinRoot.mk _ p, Subtype.eq hp⟩⟩
#align alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly

open Finset

/- warning: lift_of_splits -> lift_of_splits is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lift_of_splits lift_of_splitsₓ'. -/
/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type _} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    (s : Finset K) :
    (∀ x ∈ s, IsIntegral F x ∧ Polynomial.Splits (algebraMap F L) (minpoly F x)) →
      Nonempty (Algebra.adjoin F (↑s : Set K) →ₐ[F] L) :=
  by
  classical
    refine' Finset.induction_on s (fun H => _) fun a s has ih H => _
    · rw [coe_empty, Algebra.adjoin_empty]
      exact ⟨(Algebra.ofId F L).comp (Algebra.botEquiv F K)⟩
    rw [forall_mem_insert] at H
    rcases H with ⟨⟨H1, H2⟩, H3⟩
    cases' ih H3 with f
    choose H3 H4 using H3
    rw [coe_insert, Set.insert_eq, Set.union_comm, Algebra.adjoin_union_eq_adjoin_adjoin]
    letI := (f : Algebra.adjoin F (↑s : Set K) →+* L).toAlgebra
    haveI : FiniteDimensional F (Algebra.adjoin F (↑s : Set K)) :=
      ((Submodule.fg_iff_finiteDimensional _).1
          (FG_adjoin_of_finite s.finite_to_set H3)).of_subalgebra_toSubmodule
    letI := fieldOfFiniteDimensional F (Algebra.adjoin F (↑s : Set K))
    have H5 : IsIntegral (Algebra.adjoin F (↑s : Set K)) a := isIntegral_of_isScalarTower H1
    have H6 :
      (minpoly (Algebra.adjoin F (↑s : Set K)) a).Splits
        (algebraMap (Algebra.adjoin F (↑s : Set K)) L) :=
      by
      refine'
        Polynomial.splits_of_splits_of_dvd _
          (Polynomial.map_ne_zero <| minpoly.ne_zero H1 : Polynomial.map (algebraMap _ _) _ ≠ 0)
          ((Polynomial.splits_map_iff _ _).2 _) (minpoly.dvd _ _ _)
      · rw [← IsScalarTower.algebraMap_eq]; exact H2
      · rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨y, hy⟩ := Polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm
    refine' ⟨Subalgebra.ofRestrictScalars _ _ _⟩
    refine' (AdjoinRoot.liftHom (minpoly (Algebra.adjoin F (↑s : Set K)) a) y hy).comp _
    exact AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly (Algebra.adjoin F (↑s : Set K)) a
#align lift_of_splits lift_of_splits

end Embeddings

