/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.ideal.quotient_operations
! leanprover-community/mathlib commit b88d81c84530450a8989e918608e5960f015e6c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Ideal.Quotient

/-!
# More operations on modules and ideals related to quotients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/- warning: ring_hom.ker_lift -> RingHom.kerLift is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))), RingHom.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f)) S (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f)) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f)) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f)) (Ideal.Quotient.commRing.{u1} R _inst_1 (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f))))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))), RingHom.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f)) S (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f)) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f)) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f)) (Ideal.Quotient.commRing.{u1} R _inst_1 (RingHom.ker.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f))))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))
Case conversion may be inaccurate. Consider using '#align ring_hom.ker_lift RingHom.kerLiftₓ'. -/
/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def kerLift (f : R →+* S) : R ⧸ f.ker →+* S :=
  Ideal.Quotient.lift _ f fun r => f.mem_ker.mp
#align ring_hom.ker_lift RingHom.kerLift

/- warning: ring_hom.ker_lift_mk -> RingHom.kerLift_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.ker_lift_mk RingHom.kerLift_mkₓ'. -/
@[simp]
theorem kerLift_mk (f : R →+* S) (r : R) : kerLift f (Ideal.Quotient.mk f.ker r) = f r :=
  Ideal.Quotient.lift_mk _ _ _
#align ring_hom.ker_lift_mk RingHom.kerLift_mk

/- warning: ring_hom.ker_lift_injective -> RingHom.kerLift_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.ker_lift_injective RingHom.kerLift_injectiveₓ'. -/
/-- The induced map from the quotient by the kernel is injective. -/
theorem kerLift_injective (f : R →+* S) : Function.Injective (kerLift f) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : f a = f b) =>
    Ideal.Quotient.eq.2 <| show a - b ∈ ker f by rw [mem_ker, map_sub, h, sub_self]
#align ring_hom.ker_lift_injective RingHom.kerLift_injective

/- warning: ring_hom.lift_injective_of_ker_le_ideal -> RingHom.lift_injective_of_ker_le_ideal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.lift_injective_of_ker_le_ideal RingHom.lift_injective_of_ker_le_idealₓ'. -/
theorem lift_injective_of_ker_le_ideal (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hI : f.ker ≤ I) : Function.Injective (Ideal.Quotient.lift I f H) :=
  by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI ((RingHom.mem_ker f).mpr hu)
#align ring_hom.lift_injective_of_ker_le_ideal RingHom.lift_injective_of_ker_le_ideal

variable {f}

/- warning: ring_hom.quotient_ker_equiv_of_right_inverse -> RingHom.quotientKerEquivOfRightInverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverseₓ'. -/
/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) : R ⧸ f.ker ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk f.ker ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply ker_lift_injective
      simp [hf (f x)]
    right_inv := hf }
#align ring_hom.quotient_ker_equiv_of_right_inverse RingHom.quotientKerEquivOfRightInverse

/- warning: ring_hom.quotient_ker_equiv_of_right_inverse.apply -> RingHom.quotientKerEquivOfRightInverse.apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.quotient_ker_equiv_of_right_inverse.apply RingHom.quotientKerEquivOfRightInverse.applyₓ'. -/
@[simp]
theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : R ⧸ f.ker) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.apply RingHom.quotientKerEquivOfRightInverse.apply

/- warning: ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply -> RingHom.quotientKerEquivOfRightInverse.Symm.apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply RingHom.quotientKerEquivOfRightInverse.Symm.applyₓ'. -/
@[simp]
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk f.ker (g x) :=
  rfl
#align ring_hom.quotient_ker_equiv_of_right_inverse.symm.apply RingHom.quotientKerEquivOfRightInverse.Symm.apply

/- warning: ring_hom.quotient_ker_equiv_of_surjective -> RingHom.quotientKerEquivOfSurjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjectiveₓ'. -/
/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ f.ker ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ring_hom.quotient_ker_equiv_of_surjective RingHom.quotientKerEquivOfSurjective

end RingHom

namespace Ideal

variable {R : Type u} {S : Type v} {F : Type w} [CommRing R] [CommRing S]

/- warning: ideal.map_quotient_self -> Ideal.map_quotient_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.map_quotient_self Ideal.map_quotient_selfₓ'. -/
@[simp]
theorem map_quotient_self (I : Ideal R) : map (Quotient.mk I) I = ⊥ :=
  eq_bot_iff.2 <|
    Ideal.map_le_iff_le_comap.2 fun x hx =>
      (Submodule.mem_bot (R ⧸ I)).2 <| Ideal.Quotient.eq_zero_iff_mem.2 hx
#align ideal.map_quotient_self Ideal.map_quotient_self

/- warning: ideal.mk_ker -> Ideal.mk_ker is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))}, Eq.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (RingHom.ker.{u1, u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (RingHom.{u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (RingHom.ringHomClass.{u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))) (Ideal.Quotient.mk.{u1} R _inst_1 I)) I
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))}, Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (RingHom.ker.{u1, u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (RingHom.{u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (RingHom.instRingHomClassRingHom.{u1, u1} R (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))) (Ideal.Quotient.mk.{u1} R _inst_1 I)) I
Case conversion may be inaccurate. Consider using '#align ideal.mk_ker Ideal.mk_kerₓ'. -/
@[simp]
theorem mk_ker {I : Ideal R} : (Quotient.mk I).ker = I := by
  ext <;> rw [RingHom.ker, mem_comap, Submodule.mem_bot, quotient.eq_zero_iff_mem]
#align ideal.mk_ker Ideal.mk_ker

/- warning: ideal.map_mk_eq_bot_of_le -> Ideal.map_mk_eq_bot_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.map_mk_eq_bot_of_le Ideal.map_mk_eq_bot_of_leₓ'. -/
theorem map_mk_eq_bot_of_le {I J : Ideal R} (h : I ≤ J) : I.map J.Quotient.mk = ⊥ := by
  rw [map_eq_bot_iff_le_ker, mk_ker]; exact h
#align ideal.map_mk_eq_bot_of_le Ideal.map_mk_eq_bot_of_le

/- warning: ideal.ker_quotient_lift -> Ideal.ker_quotient_lift is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_quotient_lift Ideal.ker_quotient_liftₓ'. -/
theorem ker_quotient_lift {S : Type v} [CommRing S] {I : Ideal R} (f : R →+* S) (H : I ≤ f.ker) :
    (Ideal.Quotient.lift I f H).ker = f.ker.map I.Quotient.mk :=
  by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := quotient.mk_surjective x
    rw [RingHom.mem_ker, ← hy, Ideal.Quotient.lift_mk, ← RingHom.mem_ker] at hx
    rw [← hy, mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective I.Quotient.mk quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [RingHom.mem_ker, ← hy.right, Ideal.Quotient.lift_mk, ← RingHom.mem_ker f]
    exact hy.left
#align ideal.ker_quotient_lift Ideal.ker_quotient_lift

/- warning: ideal.bot_quotient_is_maximal_iff -> Ideal.bot_quotient_isMaximal_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))), Iff (Ideal.IsMaximal.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (Bot.bot.{u1} (Ideal.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (Submodule.hasBot.{u1, u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))))) (Semiring.toModule.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))))) (Ideal.IsMaximal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) I)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))), Iff (Ideal.IsMaximal.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (Bot.bot.{u1} (Ideal.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (Submodule.instBotSubmodule.{u1, u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))))) (Semiring.toModule.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I))))))) (Ideal.IsMaximal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) I)
Case conversion may be inaccurate. Consider using '#align ideal.bot_quotient_is_maximal_iff Ideal.bot_quotient_isMaximal_iffₓ'. -/
@[simp]
theorem bot_quotient_isMaximal_iff (I : Ideal R) : (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    @mk_ker _ _ I ▸
      @comap_isMaximal_of_surjective _ _ _ _ _ _ (Quotient.mk I) Quotient.mk_surjective ⊥ hI,
    fun hI => by skip; letI := quotient.field I; exact bot_is_maximal⟩
#align ideal.bot_quotient_is_maximal_iff Ideal.bot_quotient_isMaximal_iff

/- warning: ideal.mem_quotient_iff_mem_sup -> Ideal.mem_quotient_iff_mem_sup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.mem_quotient_iff_mem_sup Ideal.mem_quotient_iff_mem_supₓ'. -/
/-- See also `ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
theorem mem_quotient_iff_mem_sup {I J : Ideal R} {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J ⊔ I := by
  rw [← mem_comap, comap_map_of_surjective (Quotient.mk' I) quotient.mk_surjective, ←
    RingHom.ker_eq_comap_bot, mk_ker]
#align ideal.mem_quotient_iff_mem_sup Ideal.mem_quotient_iff_mem_sup

/- warning: ideal.mem_quotient_iff_mem -> Ideal.mem_quotient_iff_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.mem_quotient_iff_mem Ideal.mem_quotient_iff_memₓ'. -/
/-- See also `ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
theorem mem_quotient_iff_mem {I J : Ideal R} (hIJ : I ≤ J) {x : R} :
    Quotient.mk I x ∈ J.map (Quotient.mk I) ↔ x ∈ J := by
  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]
#align ideal.mem_quotient_iff_mem Ideal.mem_quotient_iff_mem

/- warning: ideal.comap_map_mk -> Ideal.comap_map_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.comap_map_mk Ideal.comap_map_mkₓ'. -/
theorem comap_map_mk {I J : Ideal R} (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by ext;
  rw [← Ideal.mem_quotient_iff_mem h, Ideal.mem_comap]
#align ideal.comap_map_mk Ideal.comap_map_mk

section QuotientAlgebra

variable (R₁ R₂ : Type _) {A B : Type _}

variable [CommSemiring R₁] [CommSemiring R₂] [CommRing A] [CommRing B]

variable [Algebra R₁ A] [Algebra R₂ A] [Algebra R₁ B]

#print Ideal.Quotient.algebra /-
/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance Quotient.algebra {I : Ideal A} : Algebra R₁ (A ⧸ I) :=
  {
    RingHom.comp (Ideal.Quotient.mk I)
      (algebraMap R₁
        A) with
    toFun := fun x => Ideal.Quotient.mk I (algebraMap R₁ A x)
    smul := (· • ·)
    smul_def' := fun r x =>
      Quotient.inductionOn' x fun x =>
        ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (RingHom.map_mul _ _ _)
    commutes' := fun _ _ => mul_comm _ _ }
#align ideal.quotient.algebra Ideal.Quotient.algebra
-/

#print Ideal.Quotient.isScalarTower /-
-- Lean can struggle to find this instance later if we don't provide this shortcut
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := by infer_instance
#align ideal.quotient.is_scalar_tower Ideal.Quotient.isScalarTower
-/

#print Ideal.Quotient.mkₐ /-
/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def Quotient.mkₐ (I : Ideal A) : A →ₐ[R₁] A ⧸ I :=
  ⟨fun a => Submodule.Quotient.mk a, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
#align ideal.quotient.mkₐ Ideal.Quotient.mkₐ
-/

/- warning: ideal.quotient.alg_hom_ext -> Ideal.Quotient.algHom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient.alg_hom_ext Ideal.Quotient.algHom_extₓ'. -/
theorem Quotient.algHom_ext {I : Ideal A} {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I →ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
  AlgHom.ext fun x => Quotient.inductionOn' x <| AlgHom.congr_fun h
#align ideal.quotient.alg_hom_ext Ideal.Quotient.algHom_ext

#print Ideal.Quotient.alg_map_eq /-
theorem Quotient.alg_map_eq (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl
#align ideal.quotient.alg_map_eq Ideal.Quotient.alg_map_eq
-/

#print Ideal.Quotient.mkₐ_toRingHom /-
theorem Quotient.mkₐ_toRingHom (I : Ideal A) :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_to_ring_hom Ideal.Quotient.mkₐ_toRingHom
-/

#print Ideal.Quotient.mkₐ_eq_mk /-
@[simp]
theorem Quotient.mkₐ_eq_mk (I : Ideal A) : ⇑(Quotient.mkₐ R₁ I) = Ideal.Quotient.mk I :=
  rfl
#align ideal.quotient.mkₐ_eq_mk Ideal.Quotient.mkₐ_eq_mk
-/

#print Ideal.Quotient.algebraMap_eq /-
@[simp]
theorem Quotient.algebraMap_eq (I : Ideal R) : algebraMap R (R ⧸ I) = I.Quotient.mk :=
  rfl
#align ideal.quotient.algebra_map_eq Ideal.Quotient.algebraMap_eq
-/

#print Ideal.Quotient.mk_comp_algebraMap /-
@[simp]
theorem Quotient.mk_comp_algebraMap (I : Ideal A) :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl
#align ideal.quotient.mk_comp_algebra_map Ideal.Quotient.mk_comp_algebraMap
-/

/- warning: ideal.quotient.mk_algebra_map -> Ideal.Quotient.mk_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient.mk_algebra_map Ideal.Quotient.mk_algebraMapₓ'. -/
@[simp]
theorem Quotient.mk_algebraMap (I : Ideal A) (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl
#align ideal.quotient.mk_algebra_map Ideal.Quotient.mk_algebraMap

#print Ideal.Quotient.mkₐ_surjective /-
/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
theorem Quotient.mkₐ_surjective (I : Ideal A) : Function.Surjective (Quotient.mkₐ R₁ I) :=
  surjective_quot_mk _
#align ideal.quotient.mkₐ_surjective Ideal.Quotient.mkₐ_surjective
-/

/- warning: ideal.quotient.mkₐ_ker -> Ideal.Quotient.mkₐ_ker is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient.mkₐ_ker Ideal.Quotient.mkₐ_kerₓ'. -/
/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
theorem Quotient.mkₐ_ker (I : Ideal A) : (Quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
  Ideal.mk_ker
#align ideal.quotient.mkₐ_ker Ideal.Quotient.mkₐ_ker

variable {R₁}

#print Ideal.Quotient.liftₐ /-
/-- `ideal.quotient.lift` as an `alg_hom`. -/
def Quotient.liftₐ (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    A ⧸ I →ₐ[R₁] B :=
  {-- this is is_scalar_tower.algebra_map_apply R₁ A (A ⧸ I) but the file `algebra.algebra.tower`
      -- imports this file.
      Ideal.Quotient.lift
      I (f : A →+* B) hI with
    commutes' := fun r =>
      by
      have : algebraMap R₁ (A ⧸ I) r = algebraMap A (A ⧸ I) (algebraMap R₁ A r) := by
        simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
      rw [this, Ideal.Quotient.algebraMap_eq, RingHom.toFun_eq_coe, Ideal.Quotient.lift_mk,
        AlgHom.coe_toRingHom, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] }
#align ideal.quotient.liftₐ Ideal.Quotient.liftₐ
-/

/- warning: ideal.quotient.liftₐ_apply -> Ideal.Quotient.liftₐ_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient.liftₐ_apply Ideal.Quotient.liftₐ_applyₓ'. -/
@[simp]
theorem Quotient.liftₐ_apply (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A →+* B) hI x :=
  rfl
#align ideal.quotient.liftₐ_apply Ideal.Quotient.liftₐ_apply

/- warning: ideal.quotient.liftₐ_comp -> Ideal.Quotient.liftₐ_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient.liftₐ_comp Ideal.Quotient.liftₐ_compₓ'. -/
theorem Quotient.liftₐ_comp (I : Ideal A) (f : A →ₐ[R₁] B) (hI : ∀ a : A, a ∈ I → f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun x => (Ideal.Quotient.lift_mk I (f : A →+* B) hI : _)
#align ideal.quotient.liftₐ_comp Ideal.Quotient.liftₐ_comp

/- warning: ideal.ker_lift.map_smul -> Ideal.KerLift.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_lift.map_smul Ideal.KerLift.map_smulₓ'. -/
theorem KerLift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.toRingHom.ker) :
    f.toRingHom.kerLift (r • x) = r • f.toRingHom.kerLift x :=
  by
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x
  rw [← AlgHom.map_smul, quotient.mkₐ_eq_mk, RingHom.kerLift_mk]
  exact f.map_smul _ _
#align ideal.ker_lift.map_smul Ideal.KerLift.map_smul

/- warning: ideal.ker_lift_alg -> Ideal.kerLiftAlg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_lift_alg Ideal.kerLiftAlgₓ'. -/
/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def kerLiftAlg (f : A →ₐ[R₁] B) : A ⧸ f.toRingHom.ker →ₐ[R₁] B :=
  AlgHom.mk' f.toRingHom.kerLift fun _ _ => KerLift.map_smul f _ _
#align ideal.ker_lift_alg Ideal.kerLiftAlg

/- warning: ideal.ker_lift_alg_mk -> Ideal.kerLiftAlg_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_lift_alg_mk Ideal.kerLiftAlg_mkₓ'. -/
@[simp]
theorem kerLiftAlg_mk (f : A →ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk f.toRingHom.ker a) = f a :=
  rfl
#align ideal.ker_lift_alg_mk Ideal.kerLiftAlg_mk

/- warning: ideal.ker_lift_alg_to_ring_hom -> Ideal.kerLiftAlg_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_lift_alg_to_ring_hom Ideal.kerLiftAlg_toRingHomₓ'. -/
@[simp]
theorem kerLiftAlg_toRingHom (f : A →ₐ[R₁] B) : (kerLiftAlg f).toRingHom = RingHom.kerLift f :=
  rfl
#align ideal.ker_lift_alg_to_ring_hom Ideal.kerLiftAlg_toRingHom

/- warning: ideal.ker_lift_alg_injective -> Ideal.kerLiftAlg_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.ker_lift_alg_injective Ideal.kerLiftAlg_injectiveₓ'. -/
/-- The induced algebra morphism from the quotient by the kernel is injective. -/
theorem kerLiftAlg_injective (f : A →ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective f
#align ideal.ker_lift_alg_injective Ideal.kerLiftAlg_injective

#print Ideal.quotientKerAlgEquivOfRightInverse /-
/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) : (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse fun x => show f.toRingHom (g x) = x from hf x,
    kerLiftAlg f with }
#align ideal.quotient_ker_alg_equiv_of_right_inverse Ideal.quotientKerAlgEquivOfRightInverse
-/

/- warning: ideal.quotient_ker_alg_equiv_of_right_inverse.apply -> Ideal.quotientKerAlgEquivOfRightInverse.apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_ker_alg_equiv_of_right_inverse.apply Ideal.quotientKerAlgEquivOfRightInverse.applyₓ'. -/
@[simp]
theorem quotientKerAlgEquivOfRightInverse.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : A ⧸ f.toRingHom.ker) :
    quotientKerAlgEquivOfRightInverse hf x = kerLiftAlg f x :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse.apply Ideal.quotientKerAlgEquivOfRightInverse.apply

/- warning: ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply -> Ideal.QuotientKerAlgEquivOfRightInverseSymm.apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply Ideal.QuotientKerAlgEquivOfRightInverseSymm.applyₓ'. -/
@[simp]
theorem QuotientKerAlgEquivOfRightInverseSymm.apply {f : A →ₐ[R₁] B} {g : B → A}
    (hf : Function.RightInverse g f) (x : B) :
    (quotientKerAlgEquivOfRightInverse hf).symm x = Quotient.mkₐ R₁ f.toRingHom.ker (g x) :=
  rfl
#align ideal.quotient_ker_alg_equiv_of_right_inverse_symm.apply Ideal.QuotientKerAlgEquivOfRightInverseSymm.apply

#print Ideal.quotientKerAlgEquivOfSurjective /-
/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ f.toRingHom.ker) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.HasRightInverse)
#align ideal.quotient_ker_alg_equiv_of_surjective Ideal.quotientKerAlgEquivOfSurjective
-/

/- warning: ideal.quotient_map -> Ideal.quotientMap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} S] {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (J : Ideal.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))), (LE.le.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Preorder.toHasLe.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.completeLattice.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) I (Ideal.comap.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f J)) -> (RingHom.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (Ideal.hasQuotient.{u2} S _inst_2) J) (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (NonAssocRing.toNonAssocSemiring.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (Ideal.hasQuotient.{u2} S _inst_2) J) (Ring.toNonAssocRing.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (Ideal.hasQuotient.{u2} S _inst_2) J) (CommRing.toRing.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (Ideal.hasQuotient.{u2} S _inst_2) J) (Ideal.Quotient.commRing.{u2} S _inst_2 J)))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} S] {I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} (J : Ideal.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))), (LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))))) I (Ideal.comap.{u1, u2, max u1 u2} R S (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))) f J)) -> (RingHom.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} S _inst_2) J) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (Semiring.toNonAssocSemiring.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} S _inst_2) J) (CommSemiring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} S _inst_2) J) (CommRing.toCommSemiring.{u2} (HasQuotient.Quotient.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} S _inst_2) J) (Ideal.Quotient.commRing.{u2} S _inst_2 J)))))
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map Ideal.quotientMapₓ'. -/
/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotientMap {I : Ideal R} (J : Ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) : R ⧸ I →+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha
#align ideal.quotient_map Ideal.quotientMap

/- warning: ideal.quotient_map_mk -> Ideal.quotientMap_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_mk Ideal.quotientMap_mkₓ'. -/
@[simp]
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_mk Ideal.quotientMap_mk

/- warning: ideal.quotient_map_algebra_map -> Ideal.quotientMap_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_algebra_map Ideal.quotientMap_algebraMapₓ'. -/
@[simp]
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} {f : A →+* S} {H : J ≤ I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _
#align ideal.quotient_map_algebra_map Ideal.quotientMap_algebraMap

/- warning: ideal.quotient_map_comp_mk -> Ideal.quotientMap_comp_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_comp_mk Ideal.quotientMap_comp_mkₓ'. -/
theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]
#align ideal.quotient_map_comp_mk Ideal.quotientMap_comp_mk

/- warning: ideal.quotient_equiv -> Ideal.quotientEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_equiv Ideal.quotientEquivₓ'. -/
/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
    R ⧸ I ≃+* S ⧸ J :=
  {
    quotientMap J (↑f)
      (by rw [hIJ];
        exact
          @le_comap_map _ S _ _ _ _ _
            _) with
    invFun := quotientMap I (↑f.symm) (by rw [hIJ]; exact le_of_eq (map_comap_of_equiv I f))
    left_inv := by rintro ⟨r⟩; simp
    right_inv := by rintro ⟨s⟩; simp }
#align ideal.quotient_equiv Ideal.quotientEquiv

/- warning: ideal.quotient_equiv_mk -> Ideal.quotientEquiv_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_equiv_mk Ideal.quotientEquiv_mkₓ'. -/
@[simp]
theorem quotientEquiv_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S))
    (x : R) : quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl
#align ideal.quotient_equiv_mk Ideal.quotientEquiv_mk

/- warning: ideal.quotient_equiv_symm_mk -> Ideal.quotientEquiv_symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_equiv_symm_mk Ideal.quotientEquiv_symm_mkₓ'. -/
@[simp]
theorem quotientEquiv_symm_mk (I : Ideal R) (J : Ideal S) (f : R ≃+* S)
    (hIJ : J = I.map (f : R →+* S)) (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl
#align ideal.quotient_equiv_symm_mk Ideal.quotientEquiv_symm_mk

/- warning: ideal.quotient_map_injective' -> Ideal.quotientMap_injective' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_injective' Ideal.quotientMap_injective'ₓ'. -/
/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (h : I.comap f ≤ J) : Function.Injective (quotientMap I f H) :=
  by
  refine' (injective_iff_map_eq_zero (QuotientMap I f H)).2 fun a ha => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha
  exact quotient.eq_zero_iff_mem.mpr (h ha)
#align ideal.quotient_map_injective' Ideal.quotientMap_injective'

/- warning: ideal.quotient_map_injective -> Ideal.quotientMap_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_injective Ideal.quotientMap_injectiveₓ'. -/
/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
theorem quotientMap_injective {I : Ideal S} {f : R →+* S} :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl
#align ideal.quotient_map_injective Ideal.quotientMap_injective

/- warning: ideal.quotient_map_surjective -> Ideal.quotientMap_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_surjective Ideal.quotientMap_surjectiveₓ'. -/
theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} {f : R →+* S} {H : J ≤ I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩
#align ideal.quotient_map_surjective Ideal.quotientMap_surjective

/- warning: ideal.comp_quotient_map_eq_of_comp_eq -> Ideal.comp_quotientMap_eq_of_comp_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.comp_quotient_map_eq_of_comp_eq Ideal.comp_quotientMap_eq_of_comp_eqₓ'. -/
/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type _} [CommRing R'] [CommRing S'] {f : R →+* S}
    {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f) (I : Ideal S') :
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
      (quotientMap I f' le_rfl).comp
        (quotientMap (I.comap f') g
          (le_of_eq (trans (comap_comap f g') (hfg ▸ comap_comap g f')))) :=
  by
  refine' RingHom.ext fun a => _
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotient_map_mk]
  exact congr_arg (Quotient.mk' I) (trans (g'.comp_apply f r).symm (hfg ▸ f'.comp_apply g r))
#align ideal.comp_quotient_map_eq_of_comp_eq Ideal.comp_quotientMap_eq_of_comp_eq

/- warning: ideal.quotient_mapₐ -> Ideal.quotientMapₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_mapₐ Ideal.quotientMapₐₓ'. -/
/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotientMapₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A →+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_mapₐ Ideal.quotientMapₐ

/- warning: ideal.quotient_map_mkₐ -> Ideal.quotient_map_mkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_mkₐ Ideal.quotient_map_mkₐₓ'. -/
@[simp]
theorem quotient_map_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl
#align ideal.quotient_map_mkₐ Ideal.quotient_map_mkₐ

/- warning: ideal.quotient_map_comp_mkₐ -> Ideal.quotient_map_comp_mkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_map_comp_mkₐ Ideal.quotient_map_comp_mkₐₓ'. -/
theorem quotient_map_comp_mkₐ {I : Ideal A} (J : Ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, AlgHom.comp_apply]
#align ideal.quotient_map_comp_mkₐ Ideal.quotient_map_comp_mkₐ

/- warning: ideal.quotient_equiv_alg -> Ideal.quotientEquivAlg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_equiv_alg Ideal.quotientEquivAlgₓ'. -/
/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotientEquivAlg (I : Ideal A) (J : Ideal B) (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with commutes' := fun r => by simp }
#align ideal.quotient_equiv_alg Ideal.quotientEquivAlg

/- warning: ideal.quotient_algebra -> Ideal.quotientAlgebra is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {A : Type.{u2}} [_inst_5 : CommRing.{u2} A] {I : Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5))} [_inst_10 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5))], Algebra.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) (RingHom.ringHomClass.{u1, u2} R A (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) _inst_10) I)) (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5))) (Ideal.hasQuotient.{u2} A _inst_5) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) (RingHom.ringHomClass.{u1, u2} R A (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) _inst_10) I)) (Ideal.Quotient.commRing.{u1} R _inst_1 (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) (RingHom.ringHomClass.{u1, u2} R A (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5)) _inst_10) I))) (CommSemiring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5))) (Ideal.hasQuotient.{u2} A _inst_5) I) (CommRing.toCommSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_5))) (Ideal.hasQuotient.{u2} A _inst_5) I) (Ideal.Quotient.commRing.{u2} A _inst_5 I)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {A : Type.{u2}} [_inst_5 : CommRing.{u2} A] {I : Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))} [_inst_10 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))], Algebra.{u1, u2} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) _inst_10) I)) (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_5) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) _inst_10) I)) (Ideal.Quotient.commRing.{u1} R _inst_1 (Ideal.comap.{u1, u2, max u1 u2} R A (RingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) (RingHom.instRingHomClassRingHom.{u1, u2} R A (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)))) (algebraMap.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5)) _inst_10) I))) (CommSemiring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_5) I) (CommRing.toCommSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_5) I) (Ideal.Quotient.commRing.{u2} A _inst_5 I)))
Case conversion may be inaccurate. Consider using '#align ideal.quotient_algebra Ideal.quotientAlgebraₓ'. -/
instance (priority := 100) quotientAlgebra {I : Ideal A} [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  (quotientMap I (algebraMap R A) (le_of_eq rfl)).toAlgebra
#align ideal.quotient_algebra Ideal.quotientAlgebra

/- warning: ideal.algebra_map_quotient_injective -> Ideal.algebraMap_quotient_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.algebra_map_quotient_injective Ideal.algebraMap_quotient_injectiveₓ'. -/
theorem algebraMap_quotient_injective {I : Ideal A} [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) :=
  by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := quotient.eq.mp hab
  rw [← RingHom.map_sub] at hab
  exact quotient.eq.mpr hab
#align ideal.algebra_map_quotient_injective Ideal.algebraMap_quotient_injective

variable (R₁)

#print Ideal.quotientEquivAlgOfEq /-
/-- Quotienting by equal ideals gives equivalent algebras. -/
def quotientEquivAlgOfEq {I J : Ideal A} (h : I = J) : (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
#align ideal.quotient_equiv_alg_of_eq Ideal.quotientEquivAlgOfEq
-/

/- warning: ideal.quotient_equiv_alg_of_eq_mk -> Ideal.quotientEquivAlgOfEq_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.quotient_equiv_alg_of_eq_mk Ideal.quotientEquivAlgOfEq_mkₓ'. -/
@[simp]
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl
#align ideal.quotient_equiv_alg_of_eq_mk Ideal.quotientEquivAlgOfEq_mk

#print Ideal.quotientEquivAlgOfEq_symm /-
@[simp]
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by ext <;> rfl
#align ideal.quotient_equiv_alg_of_eq_symm Ideal.quotientEquivAlgOfEq_symm
-/

end QuotientAlgebra

end Ideal

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/- warning: double_quot.quot_left_to_quot_sup -> DoubleQuot.quotLeftToQuotSup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (J : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))), RingHom.{u1, u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) I J)) (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (NonAssocRing.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) I J)) (Ring.toNonAssocRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) I J)) (CommRing.toRing.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ideal.hasQuotient.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) I J)) (Ideal.Quotient.commRing.{u1} R _inst_1 (Sup.sup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (IdemSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.idemSemiring.{u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) I J)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))), RingHom.{u1, u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) I J)) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) I) (Ideal.Quotient.commRing.{u1} R _inst_1 I)))) (Semiring.toNonAssocSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) I J)) (CommSemiring.toSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) I J)) (CommRing.toCommSemiring.{u1} (HasQuotient.Quotient.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u1} R _inst_1) (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) I J)) (Ideal.Quotient.commRing.{u1} R _inst_1 (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) I J)))))
Case conversion may be inaccurate. Consider using '#align double_quot.quot_left_to_quot_sup DoubleQuot.quotLeftToQuotSupₓ'. -/
/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quotLeftToQuotSup : R ⧸ I →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor I (I ⊔ J) le_sup_left
#align double_quot.quot_left_to_quot_sup DoubleQuot.quotLeftToQuotSup

/- warning: double_quot.ker_quot_left_to_quot_sup -> DoubleQuot.ker_quotLeftToQuotSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.ker_quot_left_to_quot_sup DoubleQuot.ker_quotLeftToQuotSupₓ'. -/
/-- The kernel of `quot_left_to_quot_sup` -/
theorem ker_quotLeftToQuotSup : (quotLeftToQuotSup I J).ker = J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quot_left_to_quot_sup, quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective I.Quotient.mk quotient.mk_surjective, ← sup_assoc]
#align double_quot.ker_quot_left_to_quot_sup DoubleQuot.ker_quotLeftToQuotSup

#print DoubleQuot.quotQuotToQuotSup /-
/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) →+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quot_left_to_quot_sup I J)
    (ker_quot_left_to_quot_sup I J).symm.le
#align double_quot.quot_quot_to_quot_sup DoubleQuot.quotQuotToQuotSup
-/

#print DoubleQuot.quotQuotMk /-
/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quotQuotMk : R →+* (R ⧸ I) ⧸ J.map I.Quotient.mk :=
  (J.map I.Quotient.mk).Quotient.mk.comp I.Quotient.mk
#align double_quot.quot_quot_mk DoubleQuot.quotQuotMk
-/

#print DoubleQuot.ker_quotQuotMk /-
/-- The kernel of `quot_quot_mk` -/
theorem ker_quotQuotMk : (quotQuotMk I J).ker = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← RingHom.ker, mk_ker,
    comap_map_of_surjective (Ideal.Quotient.mk I) quotient.mk_surjective, ← RingHom.ker, mk_ker,
    sup_comm]
#align double_quot.ker_quot_quot_mk DoubleQuot.ker_quotQuotMk
-/

/- warning: double_quot.lift_sup_quot_quot_mk -> DoubleQuot.liftSupQuotQuotMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMkₓ'. -/
/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J →+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le
#align double_quot.lift_sup_quot_quot_mk DoubleQuot.liftSupQuotQuotMk

#print DoubleQuot.quotQuotEquivQuotSup /-
/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`)-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofHomInv (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J) (by ext z; rfl) (by ext z; rfl)
#align double_quot.quot_quot_equiv_quot_sup DoubleQuot.quotQuotEquivQuotSup
-/

/- warning: double_quot.quot_quot_equiv_quot_sup_quot_quot_mk -> DoubleQuot.quotQuotEquivQuotSup_quotQuotMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_sup_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_quotQuotMkₓ'. -/
@[simp]
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_quotQuotMk

#print DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk /-
@[simp]
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_symm_quot_quot_mk DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm /-
/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* (R ⧸ J) ⧸ I.map J.Quotient.mk :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq sup_comm)).trans (quotQuotEquivQuotSup J I).symm
#align double_quot.quot_quot_equiv_comm DoubleQuot.quotQuotEquivComm
-/

#print DoubleQuot.quotQuotEquivComm_quotQuotMk /-
@[simp]
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl
#align double_quot.quot_quot_equiv_comm_quot_quot_mk DoubleQuot.quotQuotEquivComm_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm_comp_quotQuotMk /-
@[simp]
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
  RingHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mk DoubleQuot.quotQuotEquivComm_comp_quotQuotMk
-/

#print DoubleQuot.quotQuotEquivComm_symm /-
@[simp]
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I :=
  rfl
#align double_quot.quot_quot_equiv_comm_symm DoubleQuot.quotQuotEquivComm_symm
-/

variable {I J}

/- warning: double_quot.quot_quot_equiv_quot_of_le -> DoubleQuot.quotQuotEquivQuotOfLE is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLEₓ'. -/
/-- **The Third Isomorphism theorem** for rings. See `quot_quot_equiv_quot_sup` for a version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLE (h : I ≤ J) : (R ⧸ I) ⧸ J.map I.Quotient.mk ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)
#align double_quot.quot_quot_equiv_quot_of_le DoubleQuot.quotQuotEquivQuotOfLE

/- warning: double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk -> DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMkₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I ≤ J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = J.Quotient.mk x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk

/- warning: double_quot.quot_quot_equiv_quot_of_le_symm_mk -> DoubleQuot.quotQuotEquivQuotOfLE_symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_symm_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_mkₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I ≤ J) :
    (quotQuotEquivQuotOfLE h).symm (J.Quotient.mk x) = quotQuotMk I J x :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_mk

/- warning: double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk -> DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₓ'. -/
theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = J.Quotient.mk := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mk DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMk

/- warning: double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk -> DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₓ'. -/
theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I ≤ J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) J.Quotient.mk = quotQuotMk I J := by ext <;> rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mk DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk

end

section Algebra

#print DoubleQuot.quotQuotEquivComm_mk_mk /-
@[simp]
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_mk_mk DoubleQuot.quotQuotEquivComm_mk_mk
-/

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

/- warning: double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map -> DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMapₓ'. -/
@[simp]
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_quot_sup_quot_quot_algebra_map DoubleQuot.quotQuotEquivQuotSup_quot_quot_algebraMap

#print DoubleQuot.quotQuotEquivComm_algebraMap /-
@[simp]
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl
#align double_quot.quot_quot_equiv_comm_algebra_map DoubleQuot.quotQuotEquivComm_algebraMap
-/

end Algebra

section AlgebraQuotient

variable (R) {A : Type _} [CommSemiring R] [CommRing A] [Algebra R A]

variable (I J : Ideal A)

/- warning: double_quot.quot_left_to_quot_supₐ -> DoubleQuot.quotLeftToQuotSupₐ is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))] (I : Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (J : Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))), AlgHom.{u1, u2, u2} R (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) I) (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Submodule.idemSemiring.{u2, u2} A (CommRing.toCommSemiring.{u2} A _inst_2) A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Algebra.id.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) I J)) _inst_1 (Ring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) I) (CommRing.toRing.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) I) (Ideal.Quotient.commRing.{u2} A _inst_2 I))) (Ring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Submodule.idemSemiring.{u2, u2} A (CommRing.toCommSemiring.{u2} A _inst_2) A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Algebra.id.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) I J)) (CommRing.toRing.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Ideal.hasQuotient.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Submodule.idemSemiring.{u2, u2} A (CommRing.toCommSemiring.{u2} A _inst_2) A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Algebra.id.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) I J)) (Ideal.Quotient.commRing.{u2} A _inst_2 (Sup.sup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Submodule.idemSemiring.{u2, u2} A (CommRing.toCommSemiring.{u2} A _inst_2) A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Algebra.id.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) I J)))) (Ideal.Quotient.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_3 I) (Ideal.Quotient.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_3 (Sup.sup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2))) (Submodule.idemSemiring.{u2, u2} A (CommRing.toCommSemiring.{u2} A _inst_2) A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_2)) (Algebra.id.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))))) I J))
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] (I : Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (J : Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))), AlgHom.{u1, u2, u2} R (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) I) (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (SemilatticeSup.toSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (IdemCommSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instIdemCommSemiringIdealToSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) I J)) _inst_1 (CommSemiring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) I) (CommRing.toCommSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) I) (Ideal.Quotient.commRing.{u2} A _inst_2 I))) (CommSemiring.toSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (SemilatticeSup.toSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (IdemCommSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instIdemCommSemiringIdealToSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) I J)) (CommRing.toCommSemiring.{u2} (HasQuotient.Quotient.{u2, u2} A (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instHasQuotientIdealToSemiringToCommSemiring.{u2} A _inst_2) (Sup.sup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (SemilatticeSup.toSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (IdemCommSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instIdemCommSemiringIdealToSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) I J)) (Ideal.Quotient.commRing.{u2} A _inst_2 (Sup.sup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (SemilatticeSup.toSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (IdemCommSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instIdemCommSemiringIdealToSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) I J)))) (Ideal.Quotient.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_3 I) (Ideal.Quotient.algebra.{u1, u2} R A _inst_1 _inst_2 _inst_3 (Sup.sup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (SemilatticeSup.toSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (IdemCommSemiring.toSemilatticeSup.{u2} (Ideal.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))) (Ideal.instIdemCommSemiringIdealToSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))) I J))
Case conversion may be inaccurate. Consider using '#align double_quot.quot_left_to_quot_supₐ DoubleQuot.quotLeftToQuotSupₐₓ'. -/
/-- The natural algebra homomorphism `A / I → A / (I ⊔ J)`. -/
def quotLeftToQuotSupₐ : A ⧸ I →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_left_to_quot_supₐ DoubleQuot.quotLeftToQuotSupₐ

/- warning: double_quot.quot_left_to_quot_supₐ_to_ring_hom -> DoubleQuot.quotLeftToQuotSupₐ_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_left_to_quot_supₐ_to_ring_hom DoubleQuot.quotLeftToQuotSupₐ_toRingHomₓ'. -/
@[simp]
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J).toRingHom = quotLeftToQuotSup I J :=
  rfl
#align double_quot.quot_left_to_quot_supₐ_to_ring_hom DoubleQuot.quotLeftToQuotSupₐ_toRingHom

/- warning: double_quot.coe_quot_left_to_quot_supₐ -> DoubleQuot.coe_quotLeftToQuotSupₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_left_to_quot_supₐ DoubleQuot.coe_quotLeftToQuotSupₐₓ'. -/
@[simp]
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl
#align double_quot.coe_quot_left_to_quot_supₐ DoubleQuot.coe_quotLeftToQuotSupₐ

/- warning: double_quot.quot_quot_to_quot_supₐ -> DoubleQuot.quotQuotToQuotSupₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_to_quot_supₐ DoubleQuot.quotQuotToQuotSupₐₓ'. -/
/-- The algebra homomorphism `(A / I) / J' -> A / (I ⊔ J) induced by `quot_left_to_quot_sup`,
  where `J'` is the projection of `J` in `A / I`. -/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) →ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_quot_to_quot_supₐ DoubleQuot.quotQuotToQuotSupₐ

/- warning: double_quot.quot_quot_to_quot_supₐ_to_ring_hom -> DoubleQuot.quotQuotToQuotSupₐ_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_to_quot_supₐ_to_ring_hom DoubleQuot.quotQuotToQuotSupₐ_toRingHomₓ'. -/
@[simp]
theorem quotQuotToQuotSupₐ_toRingHom :
    (quotQuotToQuotSupₐ R I J).toRingHom = quotQuotToQuotSup I J :=
  rfl
#align double_quot.quot_quot_to_quot_supₐ_to_ring_hom DoubleQuot.quotQuotToQuotSupₐ_toRingHom

/- warning: double_quot.coe_quot_quot_to_quot_supₐ -> DoubleQuot.coe_quotQuotToQuotSupₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_to_quot_supₐ DoubleQuot.coe_quotQuotToQuotSupₐₓ'. -/
@[simp]
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl
#align double_quot.coe_quot_quot_to_quot_supₐ DoubleQuot.coe_quotQuotToQuotSupₐ

#print DoubleQuot.quotQuotMkₐ /-
/-- The composition of the algebra homomorphisms `A → (A / I)` and `(A / I) → (A / I) / J'`,
  where `J'` is the projection `J` in `A / I`. -/
def quotQuotMkₐ : A →ₐ[R] (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) :=
  AlgHom.mk (quotQuotMk I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.quot_quot_mkₐ DoubleQuot.quotQuotMkₐ
-/

/- warning: double_quot.quot_quot_mkₐ_to_ring_hom -> DoubleQuot.quotQuotMkₐ_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_mkₐ_to_ring_hom DoubleQuot.quotQuotMkₐ_toRingHomₓ'. -/
@[simp]
theorem quotQuotMkₐ_toRingHom : (quotQuotMkₐ R I J).toRingHom = quotQuotMk I J :=
  rfl
#align double_quot.quot_quot_mkₐ_to_ring_hom DoubleQuot.quotQuotMkₐ_toRingHom

/- warning: double_quot.coe_quot_quot_mkₐ -> DoubleQuot.coe_quotQuotMkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_mkₐ DoubleQuot.coe_quotQuotMkₐₓ'. -/
@[simp]
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl
#align double_quot.coe_quot_quot_mkₐ DoubleQuot.coe_quotQuotMkₐ

/- warning: double_quot.lift_sup_quot_quot_mkₐ -> DoubleQuot.liftSupQuotQuotMkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.lift_sup_quot_quot_mkₐ DoubleQuot.liftSupQuotQuotMkₐₓ'. -/
/-- The injective algebra homomorphism `A / (I ⊔ J) → (A / I) / J'`induced by `quot_quot_mk`,
  where `J'` is the projection `J` in `A / I`. -/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J →ₐ[R] (A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R) :=
  AlgHom.mk (liftSupQuotQuotMk I J) rfl (map_mul _) rfl (map_add _) fun _ => rfl
#align double_quot.lift_sup_quot_quot_mkₐ DoubleQuot.liftSupQuotQuotMkₐ

/- warning: double_quot.lift_sup_quot_quot_mkₐ_to_ring_hom -> DoubleQuot.liftSupQuotQuotMkₐ_toRingHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.lift_sup_quot_quot_mkₐ_to_ring_hom DoubleQuot.liftSupQuotQuotMkₐ_toRingHomₓ'. -/
@[simp]
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J).toRingHom = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.lift_sup_quot_quot_mkₐ_to_ring_hom DoubleQuot.liftSupQuotQuotMkₐ_toRingHom

/- warning: double_quot.coe_lift_sup_quot_quot_mkₐ -> DoubleQuot.coe_liftSupQuotQuotMkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_lift_sup_quot_quot_mkₐ DoubleQuot.coe_liftSupQuotQuotMkₐₓ'. -/
@[simp]
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl
#align double_quot.coe_lift_sup_quot_quot_mkₐ DoubleQuot.coe_liftSupQuotQuotMkₐ

/- warning: double_quot.quot_quot_equiv_quot_supₐ -> DoubleQuot.quotQuotEquivQuotSupₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_supₐ DoubleQuot.quotQuotEquivQuotSupₐₓ'. -/
/-- `quot_quot_to_quot_add` and `lift_sup_quot_quot_mk` are inverse isomorphisms. In the case where
    `I ≤ J`, this is the Third Isomorphism Theorem (see `quot_quot_equiv_quot_of_le`). -/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] A ⧸ I ⊔ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotSup I J) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_supₐ DoubleQuot.quotQuotEquivQuotSupₐ

/- warning: double_quot.quot_quot_equiv_quot_supₐ_to_ring_equiv -> DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_supₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquivₓ'. -/
@[simp]
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J).toRingEquiv = quotQuotEquivQuotSup I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_toRingEquiv

/- warning: double_quot.coe_quot_quot_equiv_quot_supₐ -> DoubleQuot.coe_quotQuotEquivQuotSupₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_equiv_quot_supₐ DoubleQuot.coe_quotQuotEquivQuotSupₐₓ'. -/
@[simp]
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ DoubleQuot.coe_quotQuotEquivQuotSupₐ

/- warning: double_quot.quot_quot_equiv_quot_supₐ_symm_to_ring_equiv -> DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_supₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquivₓ'. -/
@[simp]
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J).symm.toRingEquiv = (quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_supₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotSupₐ_symm_toRingEquiv

/- warning: double_quot.coe_quot_quot_equiv_quot_supₐ_symm -> DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_equiv_quot_supₐ_symm DoubleQuot.coe_quotQuotEquivQuotSupₐ_symmₓ'. -/
@[simp]
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = (quotQuotEquivQuotSup I J).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_supₐ_symm DoubleQuot.coe_quotQuotEquivQuotSupₐ_symm

#print DoubleQuot.quotQuotEquivCommₐ /-
/-- The natural algebra isomorphism `(A / I) / J' → (A / J) / I'`,
  where `J'` (resp. `I'`) is the projection of `J` in `A / I` (resp. `I` in `A / J`). -/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (J.Quotient.mkₐ R) :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivComm I J) fun _ => rfl
#align double_quot.quot_quot_equiv_commₐ DoubleQuot.quotQuotEquivCommₐ
-/

/- warning: double_quot.quot_quot_equiv_commₐ_to_ring_equiv -> DoubleQuot.quotQuotEquivCommₐ_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_commₐ_to_ring_equiv DoubleQuot.quotQuotEquivCommₐ_toRingEquivₓ'. -/
@[simp]
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J).toRingEquiv = quotQuotEquivComm I J :=
  rfl
#align double_quot.quot_quot_equiv_commₐ_to_ring_equiv DoubleQuot.quotQuotEquivCommₐ_toRingEquiv

/- warning: double_quot.coe_quot_quot_equiv_commₐ -> DoubleQuot.coe_quotQuotEquivCommₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_equiv_commₐ DoubleQuot.coe_quotQuotEquivCommₐₓ'. -/
@[simp]
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = quotQuotEquivComm I J :=
  rfl
#align double_quot.coe_quot_quot_equiv_commₐ DoubleQuot.coe_quotQuotEquivCommₐ

/- warning: double_quot.quot_quot_equiv_comm_symmₐ -> DoubleQuot.quotQuotEquivComm_symmₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_comm_symmₐ DoubleQuot.quotQuotEquivComm_symmₐₓ'. -/
@[simp]
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I :=
  -- TODO: should be `rfl` but times out
    AlgEquiv.ext
    fun x => (FunLike.congr_fun (quotQuotEquivComm_symm I J) x : _)
#align double_quot.quot_quot_equiv_comm_symmₐ DoubleQuot.quotQuotEquivComm_symmₐ

/- warning: double_quot.quot_quot_equiv_comm_comp_quot_quot_mkₐ -> DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐₓ'. -/
@[simp]
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
  AlgHom.ext <| quotQuotEquivComm_quotQuotMk I J
#align double_quot.quot_quot_equiv_comm_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivComm_comp_quotQuotMkₐ

variable {I J}

/- warning: double_quot.quot_quot_equiv_quot_of_leₐ -> DoubleQuot.quotQuotEquivQuotOfLEₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_leₐ DoubleQuot.quotQuotEquivQuotOfLEₐₓ'. -/
/-- The **third isomoprhism theorem** for rings. See `quot_quot_equiv_quot_sup` for version
    that does not assume an inclusion of ideals. -/
def quotQuotEquivQuotOfLEₐ (h : I ≤ J) : ((A ⧸ I) ⧸ J.map (I.Quotient.mkₐ R)) ≃ₐ[R] A ⧸ J :=
  @AlgEquiv.ofRingEquiv R _ _ _ _ _ _ _ (quotQuotEquivQuotOfLE h) fun _ => rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ DoubleQuot.quotQuotEquivQuotOfLEₐ

/- warning: double_quot.quot_quot_equiv_quot_of_leₐ_to_ring_equiv -> DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_leₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquivₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h).toRingEquiv = quotQuotEquivQuotOfLE h :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_toRingEquiv

/- warning: double_quot.coe_quot_quot_equiv_quot_of_leₐ -> DoubleQuot.coe_quotQuotEquivQuotOfLEₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_equiv_quot_of_leₐ DoubleQuot.coe_quotQuotEquivQuotOfLEₐₓ'. -/
@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = quotQuotEquivQuotOfLE h :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ DoubleQuot.coe_quotQuotEquivQuotOfLEₐ

/- warning: double_quot.quot_quot_equiv_quot_of_leₐ_symm_to_ring_equiv -> DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_leₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquivₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I ≤ J) :
    (quotQuotEquivQuotOfLEₐ R h).symm.toRingEquiv = (quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_leₐ_symm_to_ring_equiv DoubleQuot.quotQuotEquivQuotOfLEₐ_symm_toRingEquiv

/- warning: double_quot.coe_quot_quot_equiv_quot_of_leₐ_symm -> DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.coe_quot_quot_equiv_quot_of_leₐ_symm DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symmₓ'. -/
@[simp]
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I ≤ J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = (quotQuotEquivQuotOfLE h).symm :=
  rfl
#align double_quot.coe_quot_quot_equiv_quot_of_leₐ_symm DoubleQuot.coe_quotQuotEquivQuotOfLEₐ_symm

/- warning: double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mkₐ -> DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = J.Quotient.mkₐ R :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_comp_quot_quot_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_comp_quotQuotMkₐ

/- warning: double_quot.quot_quot_equiv_quot_of_le_symm_comp_mkₐ -> DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐₓ'. -/
@[simp]
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I ≤ J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (J.Quotient.mkₐ R) = quotQuotMkₐ R I J :=
  rfl
#align double_quot.quot_quot_equiv_quot_of_le_symm_comp_mkₐ DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mkₐ

end AlgebraQuotient

end DoubleQuot

