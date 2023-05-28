/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module ring_theory.graded_algebra.homogeneous_localization
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous Localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Notation
- `ι` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ι → submodule R A` is the grading of `A`;
- `x : submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `homogeneous_localization.num_denom_same_deg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `num_denom_same_deg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `num_denom_same_deg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `num_denom_same_deg 𝒜 x` by the kernel of `c ↦ c.num / c.denom`.

* `homogeneous_localization.num_denom_same_deg.embedding` : for `x : submonoid A` and any
  `c : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.denom` of `Aₓ`.
* `homogeneous_localization`: `num_denom_same_deg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `homogeneous_localization.val`: if `f : homogeneous_localization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `homogeneous_localization 𝒜 x` as a subring of `Aₓ`
  through `homogeneous_localization.val`.
* `homogeneous_localization.num`: if `f : homogeneous_localization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `homogeneous_localization.denom`: if `f : homogeneous_localization 𝒜 x`, then `f.denom : A` is the
  denominator of `f`.
* `homogeneous_localization.deg`: if `f : homogeneous_localization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.denom ∈ 𝒜 f.deg`
  (see `homogeneous_localization.num_mem_deg` and `homogeneous_localization.denom_mem_deg`).
* `homogeneous_localization.num_mem_deg`: if `f : homogeneous_localization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `homogeneous_localization.denom_mem_deg`: if `f : homogeneous_localization 𝒜 x`, then
  `f.denom_mem_deg` is a proof that `f.denom ∈ 𝒜 f.deg`.
* `homogeneous_localization.eq_num_div_denom`: if `f : homogeneous_localization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.denom`.

* `homogeneous_localization.local_ring`: `homogeneous_localization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike

variable {ι R A : Type _}

variable [AddCommMonoid ι] [DecidableEq ι]

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

variable (x : Submonoid A)

-- mathport name: «exprat »
local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/- warning: homogeneous_localization.num_denom_same_deg -> HomogeneousLocalization.NumDenSameDeg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] (𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜], (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))) -> Sort.{max (succ u1) (succ u3)}
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))], (ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))) -> (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))) -> Sort.{max (succ u1) (succ u3)}
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg HomogeneousLocalization.NumDenSameDegₓ'. -/
/--
Let `x` be a submonoid of `A`, then `num_denom_same_deg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
@[nolint has_nonempty_instance]
structure NumDenSameDeg where
  deg : ι
  (num den : 𝒜 deg)
  denom_mem : (denom : A) ∈ x
#align homogeneous_localization.num_denom_same_deg HomogeneousLocalization.NumDenSameDeg

end

namespace NumDenomSameDeg

open SetLike.GradedMonoid Submodule

variable {𝒜}

/- warning: homogeneous_localization.num_denom_same_deg.ext -> HomogeneousLocalization.NumDenSameDeg.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.ext HomogeneousLocalization.NumDenSameDeg.extₓ'. -/
@[ext]
theorem ext {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hdenom : (c1.den : A) = c2.den) : c1 = c2 :=
  by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  simp only; exact ⟨hdeg, by subst hdeg <;> subst hnum, by subst hdeg <;> subst hdenom⟩
#align homogeneous_localization.num_denom_same_deg.ext HomogeneousLocalization.NumDenSameDeg.ext

instance : One (NumDenSameDeg 𝒜 x)
    where one :=
    { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      denom_mem := Submonoid.one_mem _ }

/- warning: homogeneous_localization.num_denom_same_deg.deg_one -> HomogeneousLocalization.NumDenSameDeg.deg_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))), Eq.{succ u1} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (OfNat.ofNat.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 1 (OfNat.mk.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 1 (One.one.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.NumDenSameDeg.hasOne.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x))))) (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι (AddCommMonoid.toAddMonoid.{u1} ι _inst_1))))))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} ι] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u1} A] [_inst_5 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_4))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u3, u2, u1} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u3} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)))))), Eq.{succ u3} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x (OfNat.ofNat.{max u3 u1} (HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) 1 (One.toOfNat1.{max u3 u1} (HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) (HomogeneousLocalization.NumDenSameDeg.instOneNumDenSameDeg.{u3, u2, u1} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x)))) (OfNat.ofNat.{u3} ι 0 (Zero.toOfNat0.{u3} ι (AddMonoid.toZero.{u3} ι (AddCommMonoid.toAddMonoid.{u3} ι _inst_1))))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_one HomogeneousLocalization.NumDenSameDeg.deg_oneₓ'. -/
@[simp]
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_one HomogeneousLocalization.NumDenSameDeg.deg_one

#print HomogeneousLocalization.NumDenSameDeg.num_one /-
@[simp]
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_one HomogeneousLocalization.NumDenSameDeg.num_one
-/

#print HomogeneousLocalization.NumDenSameDeg.den_one /-
@[simp]
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_one HomogeneousLocalization.NumDenSameDeg.den_one
-/

instance : Zero (NumDenSameDeg 𝒜 x) where zero := ⟨0, 0, ⟨1, one_mem⟩, Submonoid.one_mem _⟩

/- warning: homogeneous_localization.num_denom_same_deg.deg_zero -> HomogeneousLocalization.NumDenSameDeg.deg_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))), Eq.{succ u1} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (OfNat.ofNat.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 0 (OfNat.mk.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 0 (Zero.zero.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.NumDenSameDeg.hasZero.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x))))) (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι (AddCommMonoid.toAddMonoid.{u1} ι _inst_1))))))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : AddCommMonoid.{u3} ι] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u1} A] [_inst_5 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_4))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u3, u2, u1} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u3} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_4)))))), Eq.{succ u3} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x (OfNat.ofNat.{max u3 u1} (HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) 0 (Zero.toOfNat0.{max u3 u1} (HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) (HomogeneousLocalization.NumDenSameDeg.instZeroNumDenSameDeg.{u3, u2, u1} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x)))) (OfNat.ofNat.{u3} ι 0 (Zero.toOfNat0.{u3} ι (AddMonoid.toZero.{u3} ι (AddCommMonoid.toAddMonoid.{u3} ι _inst_1))))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_zero HomogeneousLocalization.NumDenSameDeg.deg_zeroₓ'. -/
@[simp]
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_zero HomogeneousLocalization.NumDenSameDeg.deg_zero

#print HomogeneousLocalization.NumDenSameDeg.num_zero /-
@[simp]
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_zero HomogeneousLocalization.NumDenSameDeg.num_zero
-/

#print HomogeneousLocalization.NumDenSameDeg.den_zero /-
@[simp]
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_zero HomogeneousLocalization.NumDenSameDeg.den_zero
-/

instance : Mul (NumDenSameDeg 𝒜 x)
    where mul p q :=
    { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.Prop q.num.Prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.Prop q.den.Prop⟩
      denom_mem := Submonoid.mul_mem _ p.denom_mem q.denom_mem }

/- warning: homogeneous_localization.num_denom_same_deg.deg_mul -> HomogeneousLocalization.NumDenSameDeg.deg_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_mul HomogeneousLocalization.NumDenSameDeg.deg_mulₓ'. -/
@[simp]
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_mul HomogeneousLocalization.NumDenSameDeg.deg_mul

/- warning: homogeneous_localization.num_denom_same_deg.num_mul -> HomogeneousLocalization.NumDenSameDeg.num_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.num_mul HomogeneousLocalization.NumDenSameDeg.num_mulₓ'. -/
@[simp]
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_mul HomogeneousLocalization.NumDenSameDeg.num_mul

/- warning: homogeneous_localization.num_denom_same_deg.denom_mul -> HomogeneousLocalization.NumDenSameDeg.den_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.denom_mul HomogeneousLocalization.NumDenSameDeg.den_mulₓ'. -/
@[simp]
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_mul HomogeneousLocalization.NumDenSameDeg.den_mul

instance : Add (NumDenSameDeg 𝒜 x)
    where add c1 c2 :=
    { deg := c1.deg + c2.deg
      num :=
        ⟨c1.den * c2.num + c2.den * c1.num,
          add_mem (mul_mem c1.den.2 c2.num.2) (add_comm c2.deg c1.deg ▸ mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, mul_mem c1.den.2 c2.den.2⟩
      denom_mem := Submonoid.mul_mem _ c1.denom_mem c2.denom_mem }

/- warning: homogeneous_localization.num_denom_same_deg.deg_add -> HomogeneousLocalization.NumDenSameDeg.deg_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_add HomogeneousLocalization.NumDenSameDeg.deg_addₓ'. -/
@[simp]
theorem deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_add HomogeneousLocalization.NumDenSameDeg.deg_add

/- warning: homogeneous_localization.num_denom_same_deg.num_add -> HomogeneousLocalization.NumDenSameDeg.num_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.num_add HomogeneousLocalization.NumDenSameDeg.num_addₓ'. -/
@[simp]
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_add HomogeneousLocalization.NumDenSameDeg.num_add

/- warning: homogeneous_localization.num_denom_same_deg.denom_add -> HomogeneousLocalization.NumDenSameDeg.den_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.denom_add HomogeneousLocalization.NumDenSameDeg.den_addₓ'. -/
@[simp]
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_add HomogeneousLocalization.NumDenSameDeg.den_add

instance : Neg (NumDenSameDeg 𝒜 x)
    where neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.denom_mem⟩

/- warning: homogeneous_localization.num_denom_same_deg.deg_neg -> HomogeneousLocalization.NumDenSameDeg.deg_neg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))) (c : HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Eq.{succ u1} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (Neg.neg.{max u1 u3} (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.NumDenSameDeg.hasNeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) c)) (HomogeneousLocalization.NumDenSameDeg.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x c)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} (_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))) (𝒜 : HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{succ u3} ι (HomogeneousLocalization.NumDenSameDeg.deg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (Neg.neg.{max u3 u1} (HomogeneousLocalization.NumDenSameDeg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (HomogeneousLocalization.NumDenSameDeg.instNegNumDenSameDeg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 𝒜)) (HomogeneousLocalization.NumDenSameDeg.deg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜)
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_neg HomogeneousLocalization.NumDenSameDeg.deg_negₓ'. -/
@[simp]
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_neg HomogeneousLocalization.NumDenSameDeg.deg_neg

/- warning: homogeneous_localization.num_denom_same_deg.num_neg -> HomogeneousLocalization.NumDenSameDeg.num_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.num_neg HomogeneousLocalization.NumDenSameDeg.num_negₓ'. -/
@[simp]
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_neg HomogeneousLocalization.NumDenSameDeg.num_neg

/- warning: homogeneous_localization.num_denom_same_deg.denom_neg -> HomogeneousLocalization.NumDenSameDeg.den_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.denom_neg HomogeneousLocalization.NumDenSameDeg.den_negₓ'. -/
@[simp]
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_neg HomogeneousLocalization.NumDenSameDeg.den_neg

instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  one := 1
  mul := (· * ·)
  mul_assoc c1 c2 c3 := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul c := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one c := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm c1 c2 := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

instance : Pow (NumDenSameDeg 𝒜 x) ℕ
    where pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den,
      by
      induction' n with n ih
      · simpa only [coe_gnpow, pow_zero] using Submonoid.one_mem _
      · simpa only [pow_succ', coe_gnpow] using x.mul_mem ih c.denom_mem⟩

/- warning: homogeneous_localization.num_denom_same_deg.deg_pow -> HomogeneousLocalization.NumDenSameDeg.deg_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_pow HomogeneousLocalization.NumDenSameDeg.deg_powₓ'. -/
@[simp]
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_pow HomogeneousLocalization.NumDenSameDeg.deg_pow

/- warning: homogeneous_localization.num_denom_same_deg.num_pow -> HomogeneousLocalization.NumDenSameDeg.num_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.num_pow HomogeneousLocalization.NumDenSameDeg.num_powₓ'. -/
@[simp]
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = c.num ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_pow HomogeneousLocalization.NumDenSameDeg.num_pow

/- warning: homogeneous_localization.num_denom_same_deg.denom_pow -> HomogeneousLocalization.NumDenSameDeg.den_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.denom_pow HomogeneousLocalization.NumDenSameDeg.den_powₓ'. -/
@[simp]
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).den : A) = c.den ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_pow HomogeneousLocalization.NumDenSameDeg.den_pow

section SMul

variable {α : Type _} [SMul α R] [SMul α A] [IsScalarTower α R A]

instance : SMul α (NumDenSameDeg 𝒜 x) where smul m c := ⟨c.deg, m • c.num, c.den, c.denom_mem⟩

/- warning: homogeneous_localization.num_denom_same_deg.deg_smul -> HomogeneousLocalization.NumDenSameDeg.deg_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.deg_smul HomogeneousLocalization.NumDenSameDeg.deg_smulₓ'. -/
@[simp]
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_smul HomogeneousLocalization.NumDenSameDeg.deg_smul

/- warning: homogeneous_localization.num_denom_same_deg.num_smul -> HomogeneousLocalization.NumDenSameDeg.num_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.num_smul HomogeneousLocalization.NumDenSameDeg.num_smulₓ'. -/
@[simp]
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_smul HomogeneousLocalization.NumDenSameDeg.num_smul

/- warning: homogeneous_localization.num_denom_same_deg.denom_smul -> HomogeneousLocalization.NumDenSameDeg.den_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.denom_smul HomogeneousLocalization.NumDenSameDeg.den_smulₓ'. -/
@[simp]
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_smul HomogeneousLocalization.NumDenSameDeg.den_smul

end SMul

variable (𝒜)

/- warning: homogeneous_localization.num_denom_same_deg.embedding -> HomogeneousLocalization.NumDenSameDeg.embedding is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] (𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))), (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) -> (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] (_inst_4 : ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))) (_inst_5 : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))), (HomogeneousLocalization.NumDenSameDeg.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_2) _inst_5)
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_denom_same_deg.embedding HomogeneousLocalization.NumDenSameDeg.embeddingₓ'. -/
/-- For `x : prime ideal of A` and any `p : num_denom_same_deg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.denom` of `Aₓ`.
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.denom_mem⟩
#align homogeneous_localization.num_denom_same_deg.embedding HomogeneousLocalization.NumDenSameDeg.embedding

end NumDenomSameDeg

end HomogeneousLocalization

/- warning: homogeneous_localization -> HomogeneousLocalization is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] (𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜], (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))) -> Type.{max u1 u3}
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))], (ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))) -> (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))) -> Type.{max u1 u3}
Case conversion may be inaccurate. Consider using '#align homogeneous_localization HomogeneousLocalizationₓ'. -/
/--
For `x : prime ideal of A`, `homogeneous_localization 𝒜 x` is `num_denom_same_deg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
@[nolint has_nonempty_instance]
def HomogeneousLocalization : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)
#align homogeneous_localization HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/- warning: homogeneous_localization.val -> HomogeneousLocalization.val is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) -> (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_2) _inst_5)
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.val HomogeneousLocalization.valₓ'. -/
/-- View an element of `homogeneous_localization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id
#align homogeneous_localization.val HomogeneousLocalization.val

/- warning: homogeneous_localization.val_mk' -> HomogeneousLocalization.val_mk'' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.val_mk' HomogeneousLocalization.val_mk''ₓ'. -/
@[simp]
theorem val_mk'' (i : NumDenSameDeg 𝒜 x) :
    val (Quotient.mk'' i) = Localization.mk i.num ⟨i.den, i.denom_mem⟩ :=
  rfl
#align homogeneous_localization.val_mk' HomogeneousLocalization.val_mk''

variable (x)

/- warning: homogeneous_localization.val_injective -> HomogeneousLocalization.val_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))), Function.Injective.{succ (max u1 u3), succ u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} A] [_inst_3 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2))] {_inst_4 : ι -> (Submodule.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_2))))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)) _inst_3))} (_inst_5 : Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_2)))))), Function.Injective.{max (succ u3) (succ u2), succ u2} (HomogeneousLocalization.{u3, u1, u2} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (Localization.{u2} A (CommRing.toCommMonoid.{u2} A _inst_2) _inst_5) (HomogeneousLocalization.val.{u3, u1, u2} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.val_injective HomogeneousLocalization.val_injectiveₓ'. -/
theorem val_injective : Function.Injective (@HomogeneousLocalization.val _ _ _ _ _ _ _ _ 𝒜 _ x) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun a b h => Quotient.sound' h
#align homogeneous_localization.val_injective HomogeneousLocalization.val_injective

#print HomogeneousLocalization.hasPow /-
instance hasPow : Pow (HomogeneousLocalization 𝒜 x) ℕ
    where pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) =>
          by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, denom_pow]
          convert congr_arg (fun z => z ^ n) h <;> erw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z
#align homogeneous_localization.has_pow HomogeneousLocalization.hasPow
-/

section SMul

variable {α : Type _} [SMul α R] [SMul α A] [IsScalarTower α R A]

variable [IsScalarTower α A A]

instance : SMul α (HomogeneousLocalization 𝒜 x)
    where smul m :=
    Quotient.map' ((· • ·) m) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_smul, denom_smul]
      convert congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk] <;> rfl

/- warning: homogeneous_localization.smul_val -> HomogeneousLocalization.smul_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.smul_val HomogeneousLocalization.smul_valₓ'. -/
@[simp]
theorem smul_val (y : HomogeneousLocalization 𝒜 x) (n : α) : (n • y).val = n • y.val :=
  by
  induction y using Quotient.inductionOn
  unfold HomogeneousLocalization.val SMul.smul
  simp only [Quotient.liftOn₂'_mk, Quotient.liftOn'_mk]
  change Localization.mk _ _ = n • Localization.mk _ _
  dsimp only
  rw [Localization.smul_mk]
  congr 1
#align homogeneous_localization.smul_val HomogeneousLocalization.smul_val

end SMul

instance : Neg (HomogeneousLocalization 𝒜 x)
    where neg :=
    Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_neg, denom_neg, ← Localization.neg_mk]
      exact congr_arg (fun c => -c) h

instance : Add (HomogeneousLocalization 𝒜 x)
    where add :=
    Quotient.map₂' (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, denom_add, ← Localization.add_mk]
      convert congr_arg₂ (· + ·) h h' <;> erw [Localization.add_mk] <;> rfl

instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

instance : Mul (HomogeneousLocalization 𝒜 x)
    where mul :=
    Quotient.map₂' (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) =>
      by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, denom_mul]
      convert congr_arg₂ (· * ·) h h' <;> erw [Localization.mk_mul] <;> rfl

instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1

instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0

/- warning: homogeneous_localization.zero_eq -> HomogeneousLocalization.zero_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.zero_eq HomogeneousLocalization.zero_eqₓ'. -/
theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl
#align homogeneous_localization.zero_eq HomogeneousLocalization.zero_eq

/- warning: homogeneous_localization.one_eq -> HomogeneousLocalization.one_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.one_eq HomogeneousLocalization.one_eqₓ'. -/
theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl
#align homogeneous_localization.one_eq HomogeneousLocalization.one_eq

variable {x}

/- warning: homogeneous_localization.zero_val -> HomogeneousLocalization.zero_val is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (OfNat.ofNat.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 0 (OfNat.mk.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 0 (Zero.zero.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.hasZero.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x))))) (OfNat.ofNat.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 0 (OfNat.mk.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 0 (Zero.zero.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (Localization.hasZero.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) x))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} ι] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : CommRing.{u1} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u1, u3} R A (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u1, u3} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u1, u3} R A (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u2, u1, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u2} ι _inst_1) (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)))))}, Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x (OfNat.ofNat.{max u2 u3} (HomogeneousLocalization.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) 0 (Zero.toOfNat0.{max u2 u3} (HomogeneousLocalization.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) (HomogeneousLocalization.instZeroHomogeneousLocalization.{u2, u1, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x)))) (OfNat.ofNat.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 0 (Zero.toOfNat0.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (Localization.instZeroLocalizationToCommMonoid.{u3} A (CommSemiring.toCommMonoidWithZero.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) x)))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.zero_val HomogeneousLocalization.zero_valₓ'. -/
theorem zero_val : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _
#align homogeneous_localization.zero_val HomogeneousLocalization.zero_val

/- warning: homogeneous_localization.one_val -> HomogeneousLocalization.one_val is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (OfNat.ofNat.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 1 (OfNat.mk.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) 1 (One.one.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.hasOne.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x))))) (OfNat.ofNat.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 1 (OfNat.mk.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 1 (One.one.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (Localization.hasOne.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u2} ι] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : CommRing.{u1} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u1, u3} R A (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u1, u3} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u1, u3} R A (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u2, u1, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u2} ι _inst_1) (CommRing.toCommSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_4)))))}, Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x (OfNat.ofNat.{max u2 u3} (HomogeneousLocalization.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) 1 (One.toOfNat1.{max u2 u3} (HomogeneousLocalization.{u2, u1, u3} ι R A _inst_3 _inst_4 _inst_5 𝒜 x) (HomogeneousLocalization.instOneHomogeneousLocalization.{u2, u1, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x)))) (OfNat.ofNat.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) 1 (One.toOfNat1.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (Localization.instOneLocalization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x)))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.one_val HomogeneousLocalization.one_valₓ'. -/
theorem one_val : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one
#align homogeneous_localization.one_val HomogeneousLocalization.one_val

/- warning: homogeneous_localization.add_val -> HomogeneousLocalization.add_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.add_val HomogeneousLocalization.add_valₓ'. -/
@[simp]
theorem add_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 + y2).val = y1.val + y2.val :=
  by
  induction y1 using Quotient.inductionOn
  induction y2 using Quotient.inductionOn
  unfold HomogeneousLocalization.val Add.add
  simp only [Quotient.liftOn₂'_mk, Quotient.liftOn'_mk]
  change Localization.mk _ _ = Localization.mk _ _ + Localization.mk _ _
  dsimp only
  rw [Localization.add_mk]
  rfl
#align homogeneous_localization.add_val HomogeneousLocalization.add_val

/- warning: homogeneous_localization.mul_val -> HomogeneousLocalization.mul_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.mul_val HomogeneousLocalization.mul_valₓ'. -/
@[simp]
theorem mul_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 * y2).val = y1.val * y2.val :=
  by
  induction y1 using Quotient.inductionOn
  induction y2 using Quotient.inductionOn
  unfold HomogeneousLocalization.val Mul.mul
  simp only [Quotient.liftOn₂'_mk, Quotient.liftOn'_mk]
  change Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  dsimp only
  rw [Localization.mk_mul]
  rfl
#align homogeneous_localization.mul_val HomogeneousLocalization.mul_val

/- warning: homogeneous_localization.neg_val -> HomogeneousLocalization.neg_val is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (y : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x (Neg.neg.{max u1 u3} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (HomogeneousLocalization.hasNeg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) y)) (Neg.neg.{u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (Localization.hasNeg.{u3} A _inst_4 x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x y))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{succ u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2) _inst_5) (HomogeneousLocalization.val.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 (Neg.neg.{max u3 u1} (HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (HomogeneousLocalization.instNegHomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 𝒜)) (Neg.neg.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2) _inst_5) (Localization.instNegLocalizationToCommMonoid.{u1} A _inst_2 _inst_5) (HomogeneousLocalization.val.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.neg_val HomogeneousLocalization.neg_valₓ'. -/
@[simp]
theorem neg_val (y : HomogeneousLocalization 𝒜 x) : (-y).val = -y.val :=
  by
  induction y using Quotient.inductionOn
  unfold HomogeneousLocalization.val Neg.neg
  simp only [Quotient.liftOn₂'_mk, Quotient.liftOn'_mk]
  change Localization.mk _ _ = -Localization.mk _ _
  dsimp only
  rw [Localization.neg_mk]
  rfl
#align homogeneous_localization.neg_val HomogeneousLocalization.neg_val

/- warning: homogeneous_localization.sub_val -> HomogeneousLocalization.sub_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.sub_val HomogeneousLocalization.sub_valₓ'. -/
@[simp]
theorem sub_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [show y1 - y2 = y1 + -y2 from rfl, add_val, neg_val] <;> rfl
#align homogeneous_localization.sub_val HomogeneousLocalization.sub_val

/- warning: homogeneous_localization.pow_val -> HomogeneousLocalization.pow_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.pow_val HomogeneousLocalization.pow_valₓ'. -/
@[simp]
theorem pow_val (y : HomogeneousLocalization 𝒜 x) (n : ℕ) : (y ^ n).val = y.val ^ n :=
  by
  induction y using Quotient.inductionOn
  unfold HomogeneousLocalization.val Pow.pow
  simp only [Quotient.liftOn₂'_mk, Quotient.liftOn'_mk]
  change Localization.mk _ _ = Localization.mk _ _ ^ n
  rw [Localization.mk_pow]
  dsimp only
  congr 1
#align homogeneous_localization.pow_val HomogeneousLocalization.pow_val

instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

/- warning: homogeneous_localization.nat_cast_val -> HomogeneousLocalization.natCast_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.nat_cast_val HomogeneousLocalization.natCast_valₓ'. -/
@[simp]
theorem natCast_val (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, zero_val, one_val, *]
#align homogeneous_localization.nat_cast_val HomogeneousLocalization.natCast_val

/- warning: homogeneous_localization.int_cast_val -> HomogeneousLocalization.intCast_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.int_cast_val HomogeneousLocalization.intCast_valₓ'. -/
@[simp]
theorem intCast_val (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, zero_val, one_val, *]
#align homogeneous_localization.int_cast_val HomogeneousLocalization.intCast_val

#print HomogeneousLocalization.homogenousLocalizationCommRing /-
instance homogenousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).CommRing _ zero_val one_val add_val mul_val neg_val
    sub_val (fun z n => smul_val x z n) (fun z n => smul_val x z n) pow_val natCast_val intCast_val
#align homogeneous_localization.homogenous_localization_comm_ring HomogeneousLocalization.homogenousLocalizationCommRing
-/

#print HomogeneousLocalization.homogeneousLocalizationAlgebra /-
instance homogeneousLocalizationAlgebra : Algebra (HomogeneousLocalization 𝒜 x) (Localization x)
    where
  smul p q := p.val * q
  toFun := val
  map_one' := one_val
  map_mul' := mul_val
  map_zero' := zero_val
  map_add' := add_val
  commutes' p q := mul_comm _ _
  smul_def' p q := rfl
#align homogeneous_localization.homogeneous_localization_algebra HomogeneousLocalization.homogeneousLocalizationAlgebra
-/

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/- warning: homogeneous_localization.num -> HomogeneousLocalization.num is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) -> A
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> A
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num HomogeneousLocalization.numₓ'. -/
/-- numerator of an element in `homogeneous_localization x`-/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).num
#align homogeneous_localization.num HomogeneousLocalization.num

/- warning: homogeneous_localization.denom -> HomogeneousLocalization.den is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) -> A
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> A
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.denom HomogeneousLocalization.denₓ'. -/
/-- denominator of an element in `homogeneous_localization x`-/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).den
#align homogeneous_localization.denom HomogeneousLocalization.den

/- warning: homogeneous_localization.deg -> HomogeneousLocalization.deg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) -> ι
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)))))}, (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> ι
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.deg HomogeneousLocalization.degₓ'. -/
/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out' f).deg
#align homogeneous_localization.deg HomogeneousLocalization.deg

/- warning: homogeneous_localization.denom_mem -> HomogeneousLocalization.den_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (f : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Membership.Mem.{u3, u3} A (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))) (SetLike.hasMem.{u3, u3} (Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))) A (Submonoid.setLike.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))))) (HomogeneousLocalization.den.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) x
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Membership.mem.{u1, u1} A (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))) A (Submonoid.instSetLikeSubmonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))))))) (HomogeneousLocalization.den.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) _inst_5
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.denom_mem HomogeneousLocalization.den_memₓ'. -/
theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den ∈ x :=
  (Quotient.out' f).denom_mem
#align homogeneous_localization.denom_mem HomogeneousLocalization.den_mem

/- warning: homogeneous_localization.num_mem_deg -> HomogeneousLocalization.num_mem_deg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (f : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Membership.Mem.{u3, u3} A (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5)) (SetLike.hasMem.{u3, u3} (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5)) A (Submodule.setLike.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) (HomogeneousLocalization.num.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (𝒜 (HomogeneousLocalization.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Membership.mem.{u1, u1} A (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) A (Submodule.setLike.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))) (HomogeneousLocalization.num.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (_inst_4 (HomogeneousLocalization.deg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.num_mem_deg HomogeneousLocalization.num_mem_degₓ'. -/
theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out' f).num.2
#align homogeneous_localization.num_mem_deg HomogeneousLocalization.num_mem_deg

/- warning: homogeneous_localization.denom_mem_deg -> HomogeneousLocalization.den_mem_deg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (f : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Membership.Mem.{u3, u3} A (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5)) (SetLike.hasMem.{u3, u3} (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5)) A (Submodule.setLike.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) (HomogeneousLocalization.den.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (𝒜 (HomogeneousLocalization.deg.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Membership.mem.{u1, u1} A (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) A (Submodule.setLike.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))) (HomogeneousLocalization.den.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (_inst_4 (HomogeneousLocalization.deg.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.denom_mem_deg HomogeneousLocalization.den_mem_degₓ'. -/
theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den ∈ 𝒜 f.deg :=
  (Quotient.out' f).den.2
#align homogeneous_localization.denom_mem_deg HomogeneousLocalization.den_mem_deg

/- warning: homogeneous_localization.eq_num_div_denom -> HomogeneousLocalization.eq_num_div_den is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (f : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (Localization.mk.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x (HomogeneousLocalization.num.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (Subtype.mk.{succ u3} A (fun (x_1 : A) => Membership.Mem.{u3, u3} A (Submonoid.{u3} A (Monoid.toMulOneClass.{u3} A (CommMonoid.toMonoid.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4)))) (SetLike.hasMem.{u3, u3} (Submonoid.{u3} A (Monoid.toMulOneClass.{u3} A (CommMonoid.toMonoid.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4)))) A (Submonoid.setLike.{u3} A (Monoid.toMulOneClass.{u3} A (CommMonoid.toMonoid.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4))))) x_1 x) (HomogeneousLocalization.den.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (HomogeneousLocalization.den_mem.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{succ u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2) _inst_5) (HomogeneousLocalization.val.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (Localization.mk.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2) _inst_5 (HomogeneousLocalization.num.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (Subtype.mk.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2)))) A (Submonoid.instSetLikeSubmonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2))))) x _inst_5) (HomogeneousLocalization.den.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (HomogeneousLocalization.den_mem.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜)))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.eq_num_div_denom HomogeneousLocalization.eq_num_div_denₓ'. -/
theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.denom_mem⟩ :=
  by
  have := Quotient.out_eq' f
  apply_fun HomogeneousLocalization.val  at this
  rw [← this]
  unfold HomogeneousLocalization.val
  simp only [Quotient.liftOn'_mk'']
  rfl
#align homogeneous_localization.eq_num_div_denom HomogeneousLocalization.eq_num_div_den

/- warning: homogeneous_localization.ext_iff_val -> HomogeneousLocalization.ext_iff_val is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] {𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))} [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] {x : Submonoid.{u3} A (MulZeroOneClass.toMulOneClass.{u3} A (NonAssocSemiring.toMulZeroOneClass.{u3} A (NonAssocRing.toNonAssocSemiring.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4)))))} (f : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) (g : HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x), Iff (Eq.{succ (max u1 u3)} (HomogeneousLocalization.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x) f g) (Eq.{succ u3} (Localization.{u3} A (CommRing.toCommMonoid.{u3} A _inst_4) x) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x f) (HomogeneousLocalization.val.{u1, u2, u3} ι R A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 x g))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {_inst_4 : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))} {_inst_5 : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)))))} (𝒜 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (_inst_6 : HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Iff (Eq.{max (succ u3) (succ u1)} (HomogeneousLocalization.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 𝒜 _inst_6) (Eq.{succ u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_2) _inst_5) (HomogeneousLocalization.val.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 𝒜) (HomogeneousLocalization.val.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6))
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.ext_iff_val HomogeneousLocalization.ext_iff_valₓ'. -/
theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  { mp := fun h => h ▸ rfl
    mpr := fun h => by
      induction f using Quotient.inductionOn
      induction g using Quotient.inductionOn
      rw [Quotient.eq']
      unfold HomogeneousLocalization.val at h
      simpa only [Quotient.liftOn'_mk] using h }
#align homogeneous_localization.ext_iff_val HomogeneousLocalization.ext_iff_val

section

variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/- warning: homogeneous_localization.at_prime -> HomogeneousLocalization.AtPrime is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] (𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜] (𝔭 : Ideal.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))) [_inst_7 : Ideal.IsPrime.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) 𝔭], Type.{max u1 u3}
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))], (ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))) -> (forall (_inst_5 : Ideal.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))) [𝒜 : Ideal.IsPrime.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_5], Type.{max u1 u3})
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.at_prime HomogeneousLocalization.AtPrimeₓ'. -/
/-- Localizing a ring homogeneously at a prime ideal-/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl
#align homogeneous_localization.at_prime HomogeneousLocalization.AtPrime

/- warning: homogeneous_localization.is_unit_iff_is_unit_val -> HomogeneousLocalization.isUnit_iff_isUnit_val is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.is_unit_iff_is_unit_val HomogeneousLocalization.isUnit_iff_isUnit_valₓ'. -/
theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) : IsUnit f.val ↔ IsUnit f :=
  ⟨fun h1 => by
    rcases h1 with ⟨⟨a, b, eq0, eq1⟩, eq2 : a = f.val⟩
    rw [eq2] at eq0 eq1
    clear a eq2
    induction' b using Localization.induction_on with data
    rcases data with ⟨a, ⟨b, hb⟩⟩
    dsimp only at eq0 eq1
    have b_f_denom_not_mem : b * f.denom ∈ 𝔭.prime_compl := fun r =>
      Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (fun r2 => hb r2) fun r2 => f.denom_mem r2
    rw [f.eq_num_div_denom, Localization.mk_mul,
      show (⟨b, hb⟩ : 𝔭.prime_compl) * ⟨f.denom, _⟩ = ⟨b * f.denom, _⟩ from rfl,
      show (1 : Localization.AtPrime 𝔭) = Localization.mk 1 1 by erw [Localization.mk_self 1],
      Localization.mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨c, hc⟩, eq1⟩
    simp only [← Subtype.val_eq_coe] at eq1
    change c * (1 * (a * f.num)) = _ at eq1
    simp only [one_mul, mul_one] at eq1
    have mem1 : c * (a * f.num) ∈ 𝔭.prime_compl :=
      eq1.symm ▸ fun r => Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (by tauto) (by tauto)
    have mem2 : f.num ∉ 𝔭 := by
      contrapose! mem1
      erw [Classical.not_not]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ mem1)
    refine'
            ⟨⟨f, Quotient.mk'' ⟨f.deg, ⟨f.denom, f.denom_mem_deg⟩, ⟨f.num, f.num_mem_deg⟩, mem2⟩, _,
                _⟩,
              rfl⟩ <;>
          simp only [ext_iff_val, mul_val, val_mk', ← Subtype.val_eq_coe, f.eq_num_div_denom,
            Localization.mk_mul, one_val] <;>
        convert Localization.mk_self _ <;>
      simpa only [mul_comm] ,
    fun ⟨⟨_, b, eq1, eq2⟩, rfl⟩ =>
    by
    simp only [ext_iff_val, mul_val, one_val] at eq1 eq2
    exact ⟨⟨f.val, b.val, eq1, eq2⟩, rfl⟩⟩
#align homogeneous_localization.is_unit_iff_is_unit_val HomogeneousLocalization.isUnit_iff_isUnit_val

instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simpa [ext_iff_val, zero_val, one_val, zero_ne_one] using r⟩⟩

instance : LocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    by
    simp only [← is_unit_iff_is_unit_val, sub_val, one_val]
    induction a using Quotient.inductionOn'
    simp only [HomogeneousLocalization.val_mk'', ← Subtype.val_eq_coe]
    by_cases mem1 : a.num.1 ∈ 𝔭
    · right
      have : a.denom.1 - a.num.1 ∈ 𝔭.prime_compl := fun h =>
        a.denom_mem (sub_add_cancel a.denom.val a.num.val ▸ Ideal.add_mem _ h mem1 : a.denom.1 ∈ 𝔭)
      apply isUnit_of_mul_eq_one _ (Localization.mk a.denom.1 ⟨a.denom.1 - a.num.1, this⟩)
      simp only [sub_mul, Localization.mk_mul, one_mul, Localization.sub_mk, ← Subtype.val_eq_coe,
        Submonoid.coe_mul]
      convert Localization.mk_self _
      simp only [← Subtype.val_eq_coe, Submonoid.coe_mul]
      ring
    · left
      change _ ∈ 𝔭.prime_compl at mem1
      apply isUnit_of_mul_eq_one _ (Localization.mk a.denom.1 ⟨a.num.1, mem1⟩)
      rw [Localization.mk_mul]
      convert Localization.mk_self _
      simpa only [mul_comm]

end

section

variable (𝒜) (f : A)

/- warning: homogeneous_localization.away -> HomogeneousLocalization.Away is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CommRing.{u2} R] [_inst_4 : CommRing.{u3} A] [_inst_5 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4))] (𝒜 : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_3)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_4))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5))) [_inst_6 : GradedAlgebra.{u1, u2, u3} ι R A (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) (CommRing.toCommSemiring.{u2} R _inst_3) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_4)) _inst_5 𝒜], A -> Type.{max u1 u3}
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2))], (ι -> (Submodule.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_2)) _inst_3))) -> A -> Type.{max u1 u3}
Case conversion may be inaccurate. Consider using '#align homogeneous_localization.away HomogeneousLocalization.Awayₓ'. -/
/-- Localising away from powers of `f` homogeneously.-/
abbrev Away :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)
#align homogeneous_localization.away HomogeneousLocalization.Away

end

end HomogeneousLocalization

