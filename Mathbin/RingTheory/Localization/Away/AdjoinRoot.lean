/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.RingTheory.Localization.Away.Basic

#align_import ring_theory.localization.away.adjoin_root from "leanprover-community/mathlib"@"c20927220ef87bb4962ba08bf6da2ce3cf50a6dd"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The `R`-`alg_equiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/


open Polynomial AdjoinRoot Localization

variable {R : Type _} [CommRing R]

attribute [local instance] IsLocalization.algHom_subsingleton AdjoinRoot.algHom_subsingleton

#print Localization.awayEquivAdjoin /-
/-- The `R`-`alg_equiv` between the localization of `R` away from `r` and
    `R` with an inverse of `r` adjoined. -/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.AwayMap.lift_eq r (isUnit_of_mul_eq_one _ _ <| root_isInv r) }
    (liftHom _ (IsLocalization.Away.invSelf r) <| by
      simp only [map_sub, map_mul, aeval_C, aeval_X, IsLocalization.Away.mul_invSelf, aeval_one,
        sub_self])
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
#align localization.away_equiv_adjoin Localization.awayEquivAdjoin
-/

#print IsLocalization.adjoin_inv /-
theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)
#align is_localization.adjoin_inv IsLocalization.adjoin_inv
-/

#print IsLocalization.Away.finitePresentation /-
theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
  (AdjoinRoot.finitePresentation _).Equiv <|
    (Localization.awayEquivAdjoin r).symm.trans <| IsLocalization.algEquiv (Submonoid.powers r) _ _
#align is_localization.away.finite_presentation IsLocalization.Away.finitePresentation
-/

