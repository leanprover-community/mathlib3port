/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module ring_theory.valuation.extend_to_localization
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.Valuation.Basic

/-!

# Extending valuations to a localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that, given a valuation `v` taking values in a linearly ordered commutative *group*
with zero `Γ`, and a submonoid `S` of `v.supp.prime_compl`, the valuation `v` can be naturally
extended to the localization `S⁻¹A`.

-/


variable {A : Type _} [CommRing A] {Γ : Type _} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation A Γ) {S : Submonoid A} (hS : S ≤ v.supp.primeCompl) (B : Type _) [CommRing B]
  [Algebra A B] [IsLocalization S B]

/- warning: valuation.extend_to_localization -> Valuation.extendToLocalization is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : CommRing.{u1} A] {Γ : Type.{u2}} [_inst_2 : LinearOrderedCommGroupWithZero.{u2} Γ] (v : Valuation.{u1, u2} A Γ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) (CommRing.toRing.{u1} A _inst_1)) {S : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))}, (LE.le.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))) (Submonoid.completeLattice.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_1)))))))))) S (Ideal.primeCompl.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1) (Valuation.supp.{u1, u2} A Γ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) v) (Valuation.extendToLocalization._proof_1.{u1, u2} A _inst_1 Γ _inst_2 v))) -> (forall (B : Type.{u3}) [_inst_3 : CommRing.{u3} B] [_inst_4 : Algebra.{u1, u3} A B (CommRing.toCommSemiring.{u1} A _inst_1) (Ring.toSemiring.{u3} B (CommRing.toRing.{u3} B _inst_3))] [_inst_5 : IsLocalization.{u1, u3} A (CommRing.toCommSemiring.{u1} A _inst_1) S B (CommRing.toCommSemiring.{u3} B _inst_3) _inst_4], Valuation.{u3, u2} B Γ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) (CommRing.toRing.{u3} B _inst_3))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : CommRing.{u1} A] {Γ : Type.{u2}} [_inst_2 : LinearOrderedCommGroupWithZero.{u2} Γ] (v : Valuation.{u1, u2} A Γ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) (CommRing.toRing.{u1} A _inst_1)) {S : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))}, (LE.le.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))) (Preorder.toLE.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))) (Submonoid.instCompleteLatticeSubmonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1)))))))))) S (Ideal.primeCompl.{u1} A (CommRing.toCommSemiring.{u1} A _inst_1) (Valuation.supp.{u1, u2} A Γ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) v) (Valuation.instIsPrimeToSemiringToCommSemiringSupp.{u1, u2} A Γ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) v (LinearOrderedCommGroupWithZero.toNontrivial.{u2} Γ _inst_2) (GroupWithZero.noZeroDivisors.{u2} Γ (CommGroupWithZero.toGroupWithZero.{u2} Γ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u2} Γ _inst_2)))))) -> (forall (B : Type.{u3}) [_inst_3 : CommRing.{u3} B] [_inst_4 : Algebra.{u1, u3} A B (CommRing.toCommSemiring.{u1} A _inst_1) (CommSemiring.toSemiring.{u3} B (CommRing.toCommSemiring.{u3} B _inst_3))] [_inst_5 : IsLocalization.{u1, u3} A (CommRing.toCommSemiring.{u1} A _inst_1) S B (CommRing.toCommSemiring.{u3} B _inst_3) _inst_4], Valuation.{u3, u2} B Γ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u2} Γ _inst_2) (CommRing.toRing.{u3} B _inst_3))
Case conversion may be inaccurate. Consider using '#align valuation.extend_to_localization Valuation.extendToLocalizationₓ'. -/
/-- We can extend a valuation `v` on a ring to a localization at a submonoid of
the complement of `v.supp`. -/
noncomputable def Valuation.extendToLocalization : Valuation B Γ :=
  let f := IsLocalization.toLocalizationMap S B
  let h : ∀ s : S, IsUnit (v.1.toMonoidHom s) := fun s => isUnit_iff_ne_zero.2 (hS s.2)
  { f.lift h with
    map_zero' := by convert f.lift_eq _ 0 <;> simp
    map_add_le_max' := fun x y =>
      by
      obtain ⟨a, b, s, rfl, rfl⟩ : ∃ (a b : A)(s : S), f.mk' a s = x ∧ f.mk' b s = y :=
        by
        obtain ⟨a, s, rfl⟩ := f.mk'_surjective x
        obtain ⟨b, t, rfl⟩ := f.mk'_surjective y
        use a * t, b * s, s * t; constructor <;> · rw [f.mk'_eq_iff_eq, Submonoid.coe_mul]; ring_nf
      convert_to f.lift h (f.mk' (a + b) s) ≤ max (f.lift h _) (f.lift h _)
      · refine' congr_arg (f.lift h) (IsLocalization.eq_mk'_iff_mul_eq.2 _)
        rw [add_mul, map_add]; iterate 2 erw [IsLocalization.mk'_spec]
      iterate 3 rw [f.lift_mk']; rw [max_mul_mul_right]
      apply mul_le_mul_right' (v.map_add a b) }
#align valuation.extend_to_localization Valuation.extendToLocalization

/- warning: valuation.extend_to_localization_apply_map_apply -> Valuation.extendToLocalization_apply_map_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align valuation.extend_to_localization_apply_map_apply Valuation.extendToLocalization_apply_map_applyₓ'. -/
@[simp]
theorem Valuation.extendToLocalization_apply_map_apply (a : A) :
    v.extendToLocalization hS B (algebraMap A B a) = v a :=
  Submonoid.LocalizationMap.lift_eq _ _ a
#align valuation.extend_to_localization_apply_map_apply Valuation.extendToLocalization_apply_map_apply

