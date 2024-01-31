/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Data.Polynomial.Splits
import RingTheory.Adjoin.Basic
import RingTheory.AdjoinRoot

#align_import ring_theory.adjoin.field from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

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

open scoped BigOperators Polynomial

section Embeddings

variable (F : Type _) [Field F]

#print AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly /-
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
-/

open Finset

#print Polynomial.lift_of_splits /-
/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem Polynomial.lift_of_splits {F K L : Type _} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] (s : Finset K) :
    (∀ x ∈ s, IsIntegral F x ∧ Polynomial.Splits (algebraMap F L) (minpoly F x)) →
      Nonempty (Algebra.adjoin F (↑s : Set K) →ₐ[F] L) :=
  by classical
#align lift_of_splits Polynomial.lift_of_splits
-/

end Embeddings

