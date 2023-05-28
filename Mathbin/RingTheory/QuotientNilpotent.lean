/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module ring_theory.quotient_nilpotent
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Nilpotent
import Mathbin.RingTheory.Ideal.QuotientOperations

/-!
# Nilpotent elements in quotient rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


/- warning: ideal.is_radical_iff_quotient_reduced -> Ideal.isRadical_iff_quotient_reduced is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))), Iff (Ideal.IsRadical.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) I) (IsReduced.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Submodule.Quotient.HasQuotient.Quotient.hasZero.{u1, u1} R R (CommRing.toRing.{u1} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) I) (Monoid.Pow.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toMonoid.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))), Iff (Ideal.IsRadical.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) I) (IsReduced.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Submodule.Quotient.instZeroQuotientSubmoduleToSemiringToAddCommMonoidHasQuotient.{u1, u1} R R (CommRing.toRing.{u1} R _inst_1) (Ring.toAddCommGroup.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) I) (Monoid.Pow.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (MonoidWithZero.toMonoid.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Semiring.toMonoidWithZero.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))))))
Case conversion may be inaccurate. Consider using '#align ideal.is_radical_iff_quotient_reduced Ideal.isRadical_iff_quotient_reducedₓ'. -/
theorem Ideal.isRadical_iff_quotient_reduced {R : Type _} [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) :=
  by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective (@Ideal.Quotient.mk_surjective R _ I)
#align ideal.is_radical_iff_quotient_reduced Ideal.isRadical_iff_quotient_reduced

variable {R S : Type _} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)

/- warning: ideal.is_nilpotent.induction_on -> Ideal.IsNilpotent.induction_on is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.is_nilpotent.induction_on Ideal.IsNilpotent.induction_onₓ'. -/
/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, Prop}
    (h₁ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, I ^ 2 = ⊥ → P I)
    (h₂ :
      ∀ ⦃S : Type _⦄ [CommRing S],
        ∀ I J : Ideal S, I ≤ J → P I → P (J.map (Ideal.Quotient.mk I)) → P J) :
    P I := by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  revert S
  apply Nat.strong_induction_on n
  clear n
  intro n H S _ I hI
  by_cases hI' : I = ⊥
  · subst hI'; apply h₁; rw [← Ideal.zero_eq_bot, zero_pow]; exact zero_lt_two
  cases n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    haveI := subsingleton_of_bot_eq_top hI.symm
    exact (hI' (Subsingleton.elim _ _)).elim
  cases n
  · rw [pow_one] at hI
    exact (hI' hI).elim
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  · apply H n.succ _ (I ^ 2)
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      exact Ideal.pow_le_pow (by linarith)
    · exact le_refl n.succ.succ
  · apply h₁; rw [← Ideal.map_pow, Ideal.map_quotient_self]
#align ideal.is_nilpotent.induction_on Ideal.IsNilpotent.induction_on

/- warning: is_nilpotent.is_unit_quotient_mk_iff -> IsNilpotent.isUnit_quotient_mk_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_nilpotent.is_unit_quotient_mk_iff IsNilpotent.isUnit_quotient_mk_iffₓ'. -/
theorem IsNilpotent.isUnit_quotient_mk_iff {R : Type _} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x :=
  by
  refine' ⟨_, fun h => h.map I.Quotient.mk⟩
  revert x
  apply Ideal.IsNilpotent.induction_on I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    skip
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one, _root_.map_mul, hy, IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    have : (x * y - 1) ^ 2 = 0 := by rw [← Ideal.mem_bot, ← e]; exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 := by rw [eq_comm, ← sub_eq_zero, ← this]; ring
    exact isUnit_of_mul_eq_one _ _ this
#align is_nilpotent.is_unit_quotient_mk_iff IsNilpotent.isUnit_quotient_mk_iff

