/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module ring_theory.graded_algebra.homogeneous_ideal
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous ideals of a graded algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines homogeneous ideals of `graded_ring 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_ring.proj`.
* `homogeneous_ideal 𝒜`: The structure extending ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open BigOperators Pointwise DirectSum

variable {ι σ R A : Type _}

section HomogeneousDef

variable [Semiring A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

variable (I : Ideal A)

include A

#print Ideal.IsHomogeneous /-
/-- An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def Ideal.IsHomogeneous : Prop :=
  ∀ (i : ι) ⦃r : A⦄, r ∈ I → (DirectSum.decompose 𝒜 r i : A) ∈ I
#align ideal.is_homogeneous Ideal.IsHomogeneous
-/

#print HomogeneousIdeal /-
/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
structure HomogeneousIdeal extends Submodule A A where
  is_homogeneous' : Ideal.IsHomogeneous 𝒜 to_submodule
#align homogeneous_ideal HomogeneousIdeal
-/

variable {𝒜}

#print HomogeneousIdeal.toIdeal /-
/-- Converting a homogeneous ideal to an ideal-/
def HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule
#align homogeneous_ideal.to_ideal HomogeneousIdeal.toIdeal
-/

/- warning: homogeneous_ideal.is_homogeneous -> HomogeneousIdeal.isHomogeneous is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6), Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6), Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.is_homogeneous HomogeneousIdeal.isHomogeneousₓ'. -/
theorem HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) : I.toIdeal.Homogeneous 𝒜 :=
  I.is_homogeneous'
#align homogeneous_ideal.is_homogeneous HomogeneousIdeal.isHomogeneous

/- warning: homogeneous_ideal.to_ideal_injective -> HomogeneousIdeal.toIdeal_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜], Function.Injective.{succ u3, succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] [_inst_3 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : AddMonoid.{u2} ι] [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜], Function.Injective.{succ u3, succ u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_injective HomogeneousIdeal.toIdeal_injectiveₓ'. -/
theorem HomogeneousIdeal.toIdeal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 → Ideal A) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y) => by simp [h]
#align homogeneous_ideal.to_ideal_injective HomogeneousIdeal.toIdeal_injective

#print HomogeneousIdeal.setLike /-
instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A
    where
  coe I := I.toIdeal
  coe_injective' I J h := HomogeneousIdeal.toIdeal_injective <| SetLike.coe_injective h
#align homogeneous_ideal.set_like HomogeneousIdeal.setLike
-/

/- warning: homogeneous_ideal.ext -> HomogeneousIdeal.ext is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6} {J : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6}, (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 J)) -> (Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) I J)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6} {J : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6}, (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 J)) -> (Eq.{succ u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) I J)
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.ext HomogeneousIdeal.extₓ'. -/
@[ext]
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.toIdeal_injective h
#align homogeneous_ideal.ext HomogeneousIdeal.ext

/- warning: homogeneous_ideal.mem_iff -> HomogeneousIdeal.mem_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6} {x : A}, Iff (Membership.Mem.{u3, u3} A (Ideal.{u3} A _inst_1) (SetLike.hasMem.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))) x (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) (Membership.Mem.{u3, u3} A (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.hasMem.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)) x I)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6} {x : A}, Iff (Membership.mem.{u1, u1} A (Ideal.{u1} A _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} A _inst_1) A (Submodule.setLike.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1))) x (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) (Membership.mem.{u1, u1} A (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.instMembership.{u1, u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)) x I)
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.mem_iff HomogeneousIdeal.mem_iffₓ'. -/
@[simp]
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl
#align homogeneous_ideal.mem_iff HomogeneousIdeal.mem_iff

end HomogeneousDef

section HomogeneousCore

variable [Semiring A]

variable [SetLike σ A] (𝒜 : ι → σ)

variable (I : Ideal A)

include A

#print Ideal.homogeneousCore' /-
/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span (coe '' ((coe : Subtype (Homogeneous 𝒜) → A) ⁻¹' I))
#align ideal.homogeneous_core' Ideal.homogeneousCore'
-/

/- warning: ideal.homogeneous_core'_mono -> Ideal.homogeneousCore'_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] (𝒜 : ι -> σ), Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (Ideal.homogeneousCore'.{u1, u2, u3} ι σ A _inst_1 _inst_2 𝒜)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] (𝒜 : ι -> σ), Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (Ideal.homogeneousCore'.{u2, u1, u3} ι σ A _inst_1 _inst_2 𝒜)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core'_mono Ideal.homogeneousCore'_monoₓ'. -/
theorem Ideal.homogeneousCore'_mono : Monotone (Ideal.homogeneousCore' 𝒜) := fun I J I_le_J =>
  Ideal.span_mono <| Set.image_subset _ fun x => @I_le_J _
#align ideal.homogeneous_core'_mono Ideal.homogeneousCore'_mono

/- warning: ideal.homogeneous_core'_le -> Ideal.homogeneousCore'_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] (𝒜 : ι -> σ) (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (Ideal.homogeneousCore'.{u1, u2, u3} ι σ A _inst_1 _inst_2 𝒜 I) I
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] (𝒜 : ι -> σ) (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) (Ideal.homogeneousCore'.{u2, u1, u3} ι σ A _inst_1 _inst_2 𝒜 I) I
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core'_le Ideal.homogeneousCore'_leₓ'. -/
theorem Ideal.homogeneousCore'_le : I.homogeneousCore' 𝒜 ≤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _
#align ideal.homogeneous_core'_le Ideal.homogeneousCore'_le

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiring A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

variable (I : Ideal A)

include A

/- warning: ideal.is_homogeneous_iff_forall_subset -> Ideal.isHomogeneous_iff_forall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous_iff_forall_subset Ideal.isHomogeneous_iff_forall_subsetₓ'. -/
theorem Ideal.isHomogeneous_iff_forall_subset :
    I.Homogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' I :=
  Iff.rfl
#align ideal.is_homogeneous_iff_forall_subset Ideal.isHomogeneous_iff_forall_subset

/- warning: ideal.is_homogeneous_iff_subset_Inter -> Ideal.isHomogeneous_iff_subset_iInter is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous_iff_subset_Inter Ideal.isHomogeneous_iff_subset_iInterₓ'. -/
theorem Ideal.isHomogeneous_iff_subset_iInter :
    I.Homogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_iInter_iff.symm
#align ideal.is_homogeneous_iff_subset_Inter Ideal.isHomogeneous_iff_subset_iInter

/- warning: ideal.mul_homogeneous_element_mem_of_mem -> Ideal.mul_homogeneous_element_mem_of_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.mul_homogeneous_element_mem_of_mem Ideal.mul_homogeneous_element_mem_of_memₓ'. -/
theorem Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A) (hx₁ : Homogeneous 𝒜 x)
    (hx₂ : x ∈ I) (j : ι) : GradedRing.proj 𝒜 j (r * x) ∈ I := by
  classical
    rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_mul, map_sum]
    apply Ideal.sum_mem
    intro k hk
    obtain ⟨i, hi⟩ := hx₁
    have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) :=
      graded_monoid.mul_mem (SetLike.coe_mem _) hi
    erw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 mem₁, coe_of_apply, [anonymous]]
    split_ifs
    · exact I.mul_mem_left _ hx₂
    · exact I.zero_mem
#align ideal.mul_homogeneous_element_mem_of_mem Ideal.mul_homogeneous_element_mem_of_mem

/- warning: ideal.is_homogeneous_span -> Ideal.homogeneous_span is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (s : Set.{u3} A), (forall (x : A), (Membership.Mem.{u3, u3} A (Set.{u3} A) (Set.hasMem.{u3} A) x s) -> (SetLike.Homogeneous.{u1, u3, u2} ι A σ _inst_2 𝒜 x)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.span.{u3} A _inst_1 s))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] [_inst_3 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : AddMonoid.{u2} ι] [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (s : Set.{u3} A), (forall (x : A), (Membership.mem.{u3, u3} A (Set.{u3} A) (Set.instMembershipSet.{u3} A) x s) -> (SetLike.Homogeneous.{u2, u3, u1} ι A σ _inst_2 𝒜 x)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.span.{u3} A _inst_1 s))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous_span Ideal.homogeneous_spanₓ'. -/
theorem Ideal.homogeneous_span (s : Set A) (h : ∀ x ∈ s, Homogeneous 𝒜 x) :
    (Ideal.span s).Homogeneous 𝒜 := by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_total] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.total_apply, Finsupp.sum, decompose_sum, Dfinsupp.finset_sum_apply,
    AddSubmonoidClass.coe_finset_sum]
  refine' Ideal.sum_mem _ _
  rintro z hz1
  rw [smul_eq_mul]
  refine' Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
  · exact Ideal.subset_span z.2
#align ideal.is_homogeneous_span Ideal.homogeneous_span

#print Ideal.homogeneousCore /-
/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun x h => by rw [Subtype.image_preimage_coe] at h; exact h.2⟩
#align ideal.homogeneous_core Ideal.homogeneousCore
-/

/- warning: ideal.homogeneous_core_mono -> Ideal.homogeneousCore_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜], Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.partialOrder.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6))) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] [_inst_3 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : AddMonoid.{u2} ι] [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜], Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.instPartialOrder.{u3, u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6))) (Ideal.homogeneousCore.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core_mono Ideal.homogeneousCore_monoₓ'. -/
theorem Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneousCore'_mono 𝒜
#align ideal.homogeneous_core_mono Ideal.homogeneousCore_mono

/- warning: ideal.to_ideal_homogeneous_core_le -> Ideal.toIdeal_homogeneousCore_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u1, u3} σ A] [_inst_3 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u2} ι] [_inst_5 : AddMonoid.{u2} ι] [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u2, u1, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I
Case conversion may be inaccurate. Consider using '#align ideal.to_ideal_homogeneous_core_le Ideal.toIdeal_homogeneousCore_leₓ'. -/
theorem Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal ≤ I :=
  Ideal.homogeneousCore'_le 𝒜 I
#align ideal.to_ideal_homogeneous_core_le Ideal.toIdeal_homogeneousCore_le

variable {𝒜 I}

/- warning: ideal.mem_homogeneous_core_of_is_homogeneous_of_mem -> Ideal.mem_homogeneousCore_of_homogeneous_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : Ideal.{u3} A _inst_1} {x : A}, (SetLike.Homogeneous.{u1, u3, u2} ι A σ _inst_2 𝒜 x) -> (Membership.Mem.{u3, u3} A (Ideal.{u3} A _inst_1) (SetLike.hasMem.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))) x I) -> (Membership.Mem.{u3, u3} A (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.hasMem.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)) x (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u2} A] [_inst_2 : SetLike.{u1, u2} σ A] [_inst_3 : AddSubmonoidClass.{u1, u2} σ A (AddMonoid.toAddZeroClass.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u2, u1} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : Ideal.{u2} A _inst_1} {x : A}, (SetLike.Homogeneous.{u3, u2, u1} ι A σ _inst_2 𝒜 x) -> (Membership.mem.{u2, u2} A (Ideal.{u2} A _inst_1) (SetLike.instMembership.{u2, u2} (Ideal.{u2} A _inst_1) A (Submodule.setLike.{u2, u2} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_1))) (Semiring.toModule.{u2} A _inst_1))) x I) -> (Membership.mem.{u2, u2} A (HomogeneousIdeal.{u3, u1, u2} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (SetLike.instMembership.{u2, u2} (HomogeneousIdeal.{u3, u1, u2} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) A (HomogeneousIdeal.setLike.{u3, u1, u2} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6)) x (Ideal.homogeneousCore.{u3, u1, u2} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I))
Case conversion may be inaccurate. Consider using '#align ideal.mem_homogeneous_core_of_is_homogeneous_of_mem Ideal.mem_homogeneousCore_of_homogeneous_of_memₓ'. -/
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x : A} (h : SetLike.Homogeneous 𝒜 x)
    (hmem : x ∈ I) : x ∈ I.homogeneousCore 𝒜 :=
  Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩
#align ideal.mem_homogeneous_core_of_is_homogeneous_of_mem Ideal.mem_homogeneousCore_of_homogeneous_of_mem

/- warning: ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self -> Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) -> (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] {I : Ideal.{u1} A _inst_1}, (Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) -> (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I)
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_selfₓ'. -/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.Homogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I :=
  by
  apply le_antisymm (I.homogeneous_core'_le 𝒜) _
  intro x hx
  classical
    rw [← DirectSum.sum_support_decompose 𝒜 x]
    exact Ideal.sum_mem _ fun j hj => Ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩
#align ideal.is_homogeneous.to_ideal_homogeneous_core_eq_self Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self

/- warning: homogeneous_ideal.to_ideal_homogeneous_core_eq_self -> HomogeneousIdeal.toIdeal_homogeneousCore_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6), Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] {𝒜 : ι -> σ} [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6), Eq.{succ u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6) (Ideal.homogeneousCore.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_homogeneous_core_eq_self HomogeneousIdeal.toIdeal_homogeneousCore_eq_selfₓ'. -/
@[simp]
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousCore 𝒜 = I := by
  ext1 <;> convert Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.is_homogeneous
#align homogeneous_ideal.to_ideal_homogeneous_core_eq_self HomogeneousIdeal.toIdeal_homogeneousCore_eq_self

variable (𝒜 I)

/- warning: ideal.is_homogeneous.iff_eq -> Ideal.IsHomogeneous.iff_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : SetLike.{u2, u3} σ A] [_inst_3 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u1} ι] [_inst_5 : AddMonoid.{u1} ι] [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : Ideal.{u3} A _inst_1), Iff (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : SetLike.{u2, u1} σ A] [_inst_3 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_2] (𝒜 : ι -> σ) [_inst_4 : DecidableEq.{succ u3} ι] [_inst_5 : AddMonoid.{u3} ι] [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_1 _inst_2 _inst_3 𝒜] (I : Ideal.{u1} A _inst_1), Iff (Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I) (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 (Ideal.homogeneousCore.{u3, u2, u1} ι σ A _inst_1 _inst_2 _inst_3 𝒜 (fun (a : ι) (b : ι) => _inst_4 a b) _inst_5 _inst_6 I)) I)
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.iff_eq Ideal.IsHomogeneous.iff_eqₓ'. -/
theorem Ideal.IsHomogeneous.iff_eq : I.Homogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩
#align ideal.is_homogeneous.iff_eq Ideal.IsHomogeneous.iff_eq

/- warning: ideal.is_homogeneous.iff_exists -> Ideal.IsHomogeneous.iff_exists is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.iff_exists Ideal.IsHomogeneous.iff_existsₓ'. -/
theorem Ideal.IsHomogeneous.iff_exists :
    I.Homogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span (coe '' S) :=
  by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm
#align ideal.is_homogeneous.iff_exists Ideal.IsHomogeneous.iff_exists

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/


section Operations

section Semiring

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

namespace Ideal.IsHomogeneous

/- warning: ideal.is_homogeneous.bot -> Ideal.IsHomogeneous.bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Bot.bot.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasBot.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Bot.bot.{u1} (Ideal.{u1} A _inst_1) (Submodule.instBotSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.bot Ideal.IsHomogeneous.botₓ'. -/
theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr =>
  by
  simp only [Ideal.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Ideal.zero_mem
#align ideal.is_homogeneous.bot Ideal.IsHomogeneous.bot

/- warning: ideal.is_homogeneous.top -> Ideal.IsHomogeneous.top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Top.top.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasTop.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Top.top.{u1} (Ideal.{u1} A _inst_1) (Submodule.instTopSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.top Ideal.IsHomogeneous.topₓ'. -/
theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r hr => by simp only [Submodule.mem_top]
#align ideal.is_homogeneous.top Ideal.IsHomogeneous.top

variable {𝒜}

/- warning: ideal.is_homogeneous.inf -> Ideal.IsHomogeneous.inf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A _inst_1} {J : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Inf.inf.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) I J))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A _inst_1} {J : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Inf.inf.{u3} (Ideal.{u3} A _inst_1) (Submodule.instInfSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) I J))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.inf Ideal.IsHomogeneous.infₓ'. -/
theorem inf {I J : Ideal A} (HI : I.Homogeneous 𝒜) (HJ : J.Homogeneous 𝒜) : (I ⊓ J).Homogeneous 𝒜 :=
  fun i r hr => ⟨HI _ hr.1, HJ _ hr.2⟩
#align ideal.is_homogeneous.inf Ideal.IsHomogeneous.inf

/- warning: ideal.is_homogeneous.sup -> Ideal.IsHomogeneous.sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A _inst_1} {J : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Sup.sup.{u3} (Ideal.{u3} A _inst_1) (SemilatticeSup.toHasSup.{u3} (Ideal.{u3} A _inst_1) (Lattice.toSemilatticeSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toLattice.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) I J))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A _inst_1} {J : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Sup.sup.{u3} (Ideal.{u3} A _inst_1) (SemilatticeSup.toSup.{u3} (Ideal.{u3} A _inst_1) (Lattice.toSemilatticeSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toLattice.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) I J))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.sup Ideal.IsHomogeneous.supₓ'. -/
theorem sup {I J : Ideal A} (HI : I.Homogeneous 𝒜) (HJ : J.Homogeneous 𝒜) : (I ⊔ J).Homogeneous 𝒜 :=
  by
  rw [iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm
#align ideal.is_homogeneous.sup Ideal.IsHomogeneous.sup

/- warning: ideal.is_homogeneous.supr -> Ideal.IsHomogeneous.iSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {f : κ -> (Ideal.{u3} A _inst_1)}, (forall (i : κ), Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u3, u4} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) κ (fun (i : κ) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {f : κ -> (Ideal.{u3} A _inst_1)}, (forall (i : κ), Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u3, u4} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) κ (fun (i : κ) => f i)))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.supr Ideal.IsHomogeneous.iSupₓ'. -/
protected theorem iSup {κ : Sort _} {f : κ → Ideal A} (h : ∀ i, (f i).Homogeneous 𝒜) :
    (⨆ i, f i).Homogeneous 𝒜 := by
  simp_rw [iff_exists] at h⊢
  choose s hs using h
  refine' ⟨⋃ i, s i, _⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs
#align ideal.is_homogeneous.supr Ideal.IsHomogeneous.iSup

/- warning: ideal.is_homogeneous.infi -> Ideal.IsHomogeneous.iInf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {f : κ -> (Ideal.{u3} A _inst_1)}, (forall (i : κ), Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u3, u4} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) κ (fun (i : κ) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {f : κ -> (Ideal.{u3} A _inst_1)}, (forall (i : κ), Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u3, u4} (Ideal.{u3} A _inst_1) (Submodule.instInfSetSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) κ (fun (i : κ) => f i)))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.infi Ideal.IsHomogeneous.iInfₓ'. -/
protected theorem iInf {κ : Sort _} {f : κ → Ideal A} (h : ∀ i, (f i).Homogeneous 𝒜) :
    (⨅ i, f i).Homogeneous 𝒜 := by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx⊢
  exact fun j => h _ _ (hx j)
#align ideal.is_homogeneous.infi Ideal.IsHomogeneous.iInf

/- warning: ideal.is_homogeneous.supr₂ -> Ideal.IsHomogeneous.iSup₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {κ' : κ -> Sort.{u5}} {f : forall (i : κ), (κ' i) -> (Ideal.{u3} A _inst_1)}, (forall (i : κ) (j : κ' i), Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i j)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u3, u4} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) κ (fun (i : κ) => iSup.{u3, u5} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (κ' i) (fun (j : κ' i) => f i j))))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u5}} {κ' : κ -> Sort.{u4}} {f : forall (i : κ), (κ' i) -> (Ideal.{u3} A _inst_1)}, (forall (i : κ) (j : κ' i), Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i j)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u3, u5} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) κ (fun (i : κ) => iSup.{u3, u4} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (κ' i) (fun (j : κ' i) => f i j))))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.supr₂ Ideal.IsHomogeneous.iSup₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).Homogeneous 𝒜) : (⨆ (i) (j), f i j).Homogeneous 𝒜 :=
  IsHomogeneous.iSup fun i => IsHomogeneous.iSup <| h i
#align ideal.is_homogeneous.supr₂ Ideal.IsHomogeneous.iSup₂

/- warning: ideal.is_homogeneous.infi₂ -> Ideal.IsHomogeneous.iInf₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} {κ' : κ -> Sort.{u5}} {f : forall (i : κ), (κ' i) -> (Ideal.{u3} A _inst_1)}, (forall (i : κ) (j : κ' i), Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i j)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u3, u4} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) κ (fun (i : κ) => iInf.{u3, u5} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) (κ' i) (fun (j : κ' i) => f i j))))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u5}} {κ' : κ -> Sort.{u4}} {f : forall (i : κ), (κ' i) -> (Ideal.{u3} A _inst_1)}, (forall (i : κ) (j : κ' i), Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (f i j)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u3, u5} (Ideal.{u3} A _inst_1) (Submodule.instInfSetSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) κ (fun (i : κ) => iInf.{u3, u4} (Ideal.{u3} A _inst_1) (Submodule.instInfSetSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) (κ' i) (fun (j : κ' i) => f i j))))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.infi₂ Ideal.IsHomogeneous.iInf₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).Homogeneous 𝒜) : (⨅ (i) (j), f i j).Homogeneous 𝒜 :=
  IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i
#align ideal.is_homogeneous.infi₂ Ideal.IsHomogeneous.iInf₂

/- warning: ideal.is_homogeneous.Sup -> Ideal.IsHomogeneous.sSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {ℐ : Set.{u3} (Ideal.{u3} A _inst_1)}, (forall (I : Ideal.{u3} A _inst_1), (Membership.Mem.{u3, u3} (Ideal.{u3} A _inst_1) (Set.{u3} (Ideal.{u3} A _inst_1)) (Set.hasMem.{u3} (Ideal.{u3} A _inst_1)) I ℐ) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (SupSet.sSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) ℐ))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {ℐ : Set.{u3} (Ideal.{u3} A _inst_1)}, (forall (I : Ideal.{u3} A _inst_1), (Membership.mem.{u3, u3} (Ideal.{u3} A _inst_1) (Set.{u3} (Ideal.{u3} A _inst_1)) (Set.instMembershipSet.{u3} (Ideal.{u3} A _inst_1)) I ℐ) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (SupSet.sSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) ℐ))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.Sup Ideal.IsHomogeneous.sSupₓ'. -/
theorem sSup {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) : (sSup ℐ).Homogeneous 𝒜 :=
  by rw [sSup_eq_iSup]; exact supr₂ h
#align ideal.is_homogeneous.Sup Ideal.IsHomogeneous.sSup

/- warning: ideal.is_homogeneous.Inf -> Ideal.IsHomogeneous.sInf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {ℐ : Set.{u3} (Ideal.{u3} A _inst_1)}, (forall (I : Ideal.{u3} A _inst_1), (Membership.Mem.{u3, u3} (Ideal.{u3} A _inst_1) (Set.{u3} (Ideal.{u3} A _inst_1)) (Set.hasMem.{u3} (Ideal.{u3} A _inst_1)) I ℐ) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (InfSet.sInf.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) ℐ))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {ℐ : Set.{u3} (Ideal.{u3} A _inst_1)}, (forall (I : Ideal.{u3} A _inst_1), (Membership.mem.{u3, u3} (Ideal.{u3} A _inst_1) (Set.{u3} (Ideal.{u3} A _inst_1)) (Set.instMembershipSet.{u3} (Ideal.{u3} A _inst_1)) I ℐ) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (InfSet.sInf.{u3} (Ideal.{u3} A _inst_1) (Submodule.instInfSetSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) ℐ))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.Inf Ideal.IsHomogeneous.sInfₓ'. -/
theorem sInf {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) : (sInf ℐ).Homogeneous 𝒜 :=
  by rw [sInf_eq_iInf]; exact infi₂ h
#align ideal.is_homogeneous.Inf Ideal.IsHomogeneous.sInf

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

instance : PartialOrder (HomogeneousIdeal 𝒜) :=
  SetLike.partialOrder

instance : Top (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

instance : Bot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

instance : Sup (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.Homogeneous.sup J.Homogeneous⟩⟩

instance : Inf (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.Homogeneous.inf J.Homogeneous⟩⟩

instance : SupSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨆ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.Homogeneous⟩⟩

instance : InfSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨅ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.Homogeneous⟩⟩

/- warning: homogeneous_ideal.coe_top -> HomogeneousIdeal.coe_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Set.{u3} A) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (HasLiftT.mk.{succ u3, succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (CoeTCₓ.coe.{succ u3, succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (SetLike.Set.hasCoeT.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) A (HomogeneousIdeal.setLike.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)))) (Top.top.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasTop.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Set.univ.{u3} A)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Set.{u3} A) (SetLike.coe.{u3, u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) A (HomogeneousIdeal.setLike.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Top.top.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instTopHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Set.univ.{u3} A)
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.coe_top HomogeneousIdeal.coe_topₓ'. -/
@[simp]
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ :=
  rfl
#align homogeneous_ideal.coe_top HomogeneousIdeal.coe_top

/- warning: homogeneous_ideal.coe_bot -> HomogeneousIdeal.coe_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Set.{u3} A) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (HasLiftT.mk.{succ u3, succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (CoeTCₓ.coe.{succ u3, succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Set.{u3} A) (SetLike.Set.hasCoeT.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) A (HomogeneousIdeal.setLike.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)))) (Bot.bot.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasBot.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (OfNat.ofNat.{u3} (Set.{u3} A) 0 (OfNat.mk.{u3} (Set.{u3} A) 0 (Zero.zero.{u3} (Set.{u3} A) (Set.zero.{u3} A (MulZeroClass.toHasZero.{u3} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))))))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Set.{u3} A) (SetLike.coe.{u3, u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) A (HomogeneousIdeal.setLike.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Bot.bot.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instBotHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (OfNat.ofNat.{u3} (Set.{u3} A) 0 (Zero.toOfNat0.{u3} (Set.{u3} A) (Set.zero.{u3} A (MonoidWithZero.toZero.{u3} A (Semiring.toMonoidWithZero.{u3} A _inst_1)))))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.coe_bot HomogeneousIdeal.coe_botₓ'. -/
@[simp]
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 :=
  rfl
#align homogeneous_ideal.coe_bot HomogeneousIdeal.coe_bot

/- warning: homogeneous_ideal.coe_sup -> HomogeneousIdeal.coe_sup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.coe_sup HomogeneousIdeal.coe_supₓ'. -/
@[simp]
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A) :=
  Submodule.coe_sup _ _
#align homogeneous_ideal.coe_sup HomogeneousIdeal.coe_sup

/- warning: homogeneous_ideal.coe_inf -> HomogeneousIdeal.coe_inf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.coe_inf HomogeneousIdeal.coe_infₓ'. -/
@[simp]
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = I ∩ J :=
  rfl
#align homogeneous_ideal.coe_inf HomogeneousIdeal.coe_inf

/- warning: homogeneous_ideal.to_ideal_top -> HomogeneousIdeal.toIdeal_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Top.top.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasTop.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Top.top.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasTop.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Top.top.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instTopHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Top.top.{u3} (Ideal.{u3} A _inst_1) (Submodule.instTopSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_top HomogeneousIdeal.toIdeal_topₓ'. -/
@[simp]
theorem toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) :=
  rfl
#align homogeneous_ideal.to_ideal_top HomogeneousIdeal.toIdeal_top

/- warning: homogeneous_ideal.to_ideal_bot -> HomogeneousIdeal.toIdeal_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Bot.bot.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasBot.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Bot.bot.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasBot.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Bot.bot.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instBotHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Bot.bot.{u3} (Ideal.{u3} A _inst_1) (Submodule.instBotSubmodule.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_bot HomogeneousIdeal.toIdeal_botₓ'. -/
@[simp]
theorem toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) :=
  rfl
#align homogeneous_ideal.to_ideal_bot HomogeneousIdeal.toIdeal_bot

/- warning: homogeneous_ideal.to_ideal_sup -> HomogeneousIdeal.toIdeal_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (J : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Sup.sup.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasSup.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) I J)) (Sup.sup.{u3} (Ideal.{u3} A _inst_1) (SemilatticeSup.toHasSup.{u3} (Ideal.{u3} A _inst_1) (Lattice.toSemilatticeSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toLattice.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (J : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Sup.sup.{u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instSupHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) I J)) (Sup.sup.{u1} (Ideal.{u1} A _inst_1) (SemilatticeSup.toSup.{u1} (Ideal.{u1} A _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} A _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} A _inst_1) (Submodule.completeLattice.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)))))) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_sup HomogeneousIdeal.toIdeal_supₓ'. -/
@[simp]
theorem toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl
#align homogeneous_ideal.to_ideal_sup HomogeneousIdeal.toIdeal_sup

/- warning: homogeneous_ideal.to_ideal_inf -> HomogeneousIdeal.toIdeal_inf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (J : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Inf.inf.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasInf.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) I J)) (Inf.inf.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (J : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Inf.inf.{u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instInfHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) I J)) (Inf.inf.{u1} (Ideal.{u1} A _inst_1) (Submodule.instInfSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_inf HomogeneousIdeal.toIdeal_infₓ'. -/
@[simp]
theorem toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal :=
  rfl
#align homogeneous_ideal.to_ideal_inf HomogeneousIdeal.toIdeal_inf

/- warning: homogeneous_ideal.to_ideal_Sup -> HomogeneousIdeal.toIdeal_sSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_Sup HomogeneousIdeal.toIdeal_sSupₓ'. -/
@[simp]
theorem toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s ∈ ℐ, toIdeal s :=
  rfl
#align homogeneous_ideal.to_ideal_Sup HomogeneousIdeal.toIdeal_sSup

/- warning: homogeneous_ideal.to_ideal_Inf -> HomogeneousIdeal.toIdeal_sInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_Inf HomogeneousIdeal.toIdeal_sInfₓ'. -/
@[simp]
theorem toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s ∈ ℐ, toIdeal s :=
  rfl
#align homogeneous_ideal.to_ideal_Inf HomogeneousIdeal.toIdeal_sInf

/- warning: homogeneous_ideal.to_ideal_supr -> HomogeneousIdeal.toIdeal_iSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} (s : κ -> (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)), Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u3, u4} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasSup.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) κ (fun (i : κ) => s i))) (iSup.{u3, u4} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) κ (fun (i : κ) => HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (s i)))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} (s : κ -> (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)), Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iSup.{u1, u4} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instSupSetHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) κ (fun (i : κ) => s i))) (iSup.{u1, u4} (Ideal.{u1} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u1} (Ideal.{u1} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} A _inst_1) (Submodule.completeLattice.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)))) κ (fun (i : κ) => HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (s i)))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_supr HomogeneousIdeal.toIdeal_iSupₓ'. -/
@[simp]
theorem toIdeal_iSup {κ : Sort _} (s : κ → HomogeneousIdeal 𝒜) :
    (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal := by rw [iSup, to_ideal_Sup, iSup_range]
#align homogeneous_ideal.to_ideal_supr HomogeneousIdeal.toIdeal_iSup

/- warning: homogeneous_ideal.to_ideal_infi -> HomogeneousIdeal.toIdeal_iInf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} (s : κ -> (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)), Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u3, u4} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasInf.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) κ (fun (i : κ) => s i))) (iInf.{u3, u4} (Ideal.{u3} A _inst_1) (Submodule.hasInf.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)) κ (fun (i : κ) => HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (s i)))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {κ : Sort.{u4}} (s : κ -> (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)), Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (iInf.{u1, u4} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instInfSetHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) κ (fun (i : κ) => s i))) (iInf.{u1, u4} (Ideal.{u1} A _inst_1) (Submodule.instInfSetSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1)) κ (fun (i : κ) => HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (s i)))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_infi HomogeneousIdeal.toIdeal_iInfₓ'. -/
@[simp]
theorem toIdeal_iInf {κ : Sort _} (s : κ → HomogeneousIdeal 𝒜) :
    (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal := by rw [iInf, to_ideal_Inf, iInf_range]
#align homogeneous_ideal.to_ideal_infi HomogeneousIdeal.toIdeal_iInf

/- warning: homogeneous_ideal.to_ideal_supr₂ -> HomogeneousIdeal.toIdeal_iSup₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_supr₂ HomogeneousIdeal.toIdeal_iSup₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem toIdeal_iSup₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal := by simp_rw [to_ideal_supr]
#align homogeneous_ideal.to_ideal_supr₂ HomogeneousIdeal.toIdeal_iSup₂

/- warning: homogeneous_ideal.to_ideal_infi₂ -> HomogeneousIdeal.toIdeal_iInf₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_infi₂ HomogeneousIdeal.toIdeal_iInf₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem toIdeal_iInf₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal := by simp_rw [to_ideal_infi]
#align homogeneous_ideal.to_ideal_infi₂ HomogeneousIdeal.toIdeal_iInf₂

/- warning: homogeneous_ideal.eq_top_iff -> HomogeneousIdeal.eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Iff (Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) I (Top.top.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasTop.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (Top.top.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasTop.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Iff (Eq.{succ u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) I (Top.top.{u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instTopHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (Top.top.{u1} (Ideal.{u1} A _inst_1) (Submodule.instTopSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1))))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.eq_top_iff HomogeneousIdeal.eq_top_iffₓ'. -/
@[simp]
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  toIdeal_injective.eq_iff.symm
#align homogeneous_ideal.eq_top_iff HomogeneousIdeal.eq_top_iff

/- warning: homogeneous_ideal.eq_bot_iff -> HomogeneousIdeal.eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Iff (Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) I (Bot.bot.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasBot.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (Bot.bot.{u3} (Ideal.{u3} A _inst_1) (Submodule.hasBot.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Iff (Eq.{succ u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) I (Bot.bot.{u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instBotHomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))) (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (Bot.bot.{u1} (Ideal.{u1} A _inst_1) (Submodule.instBotSubmodule.{u1, u1} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))) (Semiring.toModule.{u1} A _inst_1))))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.eq_bot_iff HomogeneousIdeal.eq_bot_iffₓ'. -/
@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  toIdeal_injective.eq_iff.symm
#align homogeneous_ideal.eq_bot_iff HomogeneousIdeal.eq_bot_iff

instance : CompleteLattice (HomogeneousIdeal 𝒜) :=
  toIdeal_injective.CompleteLattice _ toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf toIdeal_top
    toIdeal_bot

instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(· ⊔ ·)⟩

/- warning: homogeneous_ideal.to_ideal_add -> HomogeneousIdeal.toIdeal_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_add HomogeneousIdeal.toIdeal_addₓ'. -/
@[simp]
theorem toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl
#align homogeneous_ideal.to_ideal_add HomogeneousIdeal.toIdeal_add

instance : Inhabited (HomogeneousIdeal 𝒜) where default := ⊥

end HomogeneousIdeal

end Semiring

section CommSemiring

variable [CommSemiring A]

variable [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

variable (I : Ideal A)

include A

/- warning: ideal.is_homogeneous.mul -> Ideal.IsHomogeneous.mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommSemiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)} {J : Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)}, (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (HMul.hMul.{u3, u3, u3} (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (instHMul.{u3} (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.hasMul.{u3} A _inst_1)) I J))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : CommSemiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)} {J : Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)}, (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) -> (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A (CommSemiring.toSemiring.{u3} A _inst_1) _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (HMul.hMul.{u3, u3, u3} (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (instHMul.{u3} (Ideal.{u3} A (CommSemiring.toSemiring.{u3} A _inst_1)) (Ideal.instMulIdealToSemiring.{u3} A _inst_1)) I J))
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.mul Ideal.IsHomogeneous.mulₓ'. -/
theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.Homogeneous 𝒜) (HJ : J.Homogeneous 𝒜) :
    (I * J).Homogeneous 𝒜 :=
  by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneous_submonoid 𝒜).Subtype).symm⟩
#align ideal.is_homogeneous.mul Ideal.IsHomogeneous.mul

variable {𝒜}

instance : Mul (HomogeneousIdeal 𝒜)
    where mul I J := ⟨I.toIdeal * J.toIdeal, I.Homogeneous.mul J.Homogeneous⟩

/- warning: homogeneous_ideal.to_ideal_mul -> HomogeneousIdeal.toIdeal_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_mul HomogeneousIdeal.toIdeal_mulₓ'. -/
@[simp]
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl
#align homogeneous_ideal.to_ideal_mul HomogeneousIdeal.toIdeal_mul

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section HomogeneousCore

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

include A

/- warning: ideal.homogeneous_core.gc -> Ideal.homogeneousCore.gc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisConnection.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.partialOrder.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisConnection.{u3, u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instPartialOrderHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core.gc Ideal.homogeneousCore.gcₓ'. -/
theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) := fun I J =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H, fun H =>
    le_trans H (Ideal.homogeneousCore'_le _ _)⟩
#align ideal.homogeneous_core.gc Ideal.homogeneousCore.gc

/- warning: ideal.homogeneous_core.gi -> Ideal.homogeneousCore.gi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisCoinsertion.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.partialOrder.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisCoinsertion.{u3, u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instPartialOrderHomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core.gi Ideal.homogeneousCore.giₓ'. -/
/-- `to_ideal : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜)
    where
  choice I HI :=
    ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le I := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)
#align ideal.homogeneous_core.gi Ideal.homogeneousCore.gi

/- warning: ideal.homogeneous_core_eq_Sup -> Ideal.homogeneousCore_eq_sSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (SupSet.sSup.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasSup.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (setOf.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (fun (J : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) => LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) I)))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousCore.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) (SupSet.sSup.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instSupSetHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (setOf.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (fun (J : HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) => LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) I)))
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core_eq_Sup Ideal.homogeneousCore_eq_sSupₓ'. -/
theorem Ideal.homogeneousCore_eq_sSup :
    I.homogeneousCore 𝒜 = sSup { J : HomogeneousIdeal 𝒜 | J.toIdeal ≤ I } :=
  Eq.symm <| IsLUB.sSup_eq <| (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.IsLUB
#align ideal.homogeneous_core_eq_Sup Ideal.homogeneousCore_eq_sSup

/- warning: ideal.homogeneous_core'_eq_Sup -> Ideal.homogeneousCore'_eq_sSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (Ideal.{u3} A _inst_1) (Ideal.homogeneousCore'.{u1, u2, u3} ι σ A _inst_1 _inst_4 𝒜 I) (SupSet.sSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toHasSup.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (setOf.{u3} (Ideal.{u3} A _inst_1) (fun (J : Ideal.{u3} A _inst_1) => And (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) (LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) J I))))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (Ideal.{u3} A _inst_1) (Ideal.homogeneousCore'.{u2, u1, u3} ι σ A _inst_1 _inst_4 𝒜 I) (SupSet.sSup.{u3} (Ideal.{u3} A _inst_1) (ConditionallyCompleteLattice.toSupSet.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (setOf.{u3} (Ideal.{u3} A _inst_1) (fun (J : Ideal.{u3} A _inst_1) => And (Ideal.IsHomogeneous.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J) (LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) J I))))
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_core'_eq_Sup Ideal.homogeneousCore'_eq_sSupₓ'. -/
theorem Ideal.homogeneousCore'_eq_sSup :
    I.homogeneousCore' 𝒜 = sSup { J : Ideal A | J.Homogeneous 𝒜 ∧ J ≤ I } :=
  by
  refine' (IsLUB.sSup_eq _).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (to_ideal : HomogeneousIdeal 𝒜 → Ideal A) := fun x y => id
  convert coe_mono.map_is_greatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext
  rw [mem_image, mem_set_of_eq]
  refine'
    ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, by rintro ⟨x, ⟨hx, rfl⟩⟩ <;> exact ⟨x.is_homogeneous, hx⟩⟩
#align ideal.homogeneous_core'_eq_Sup Ideal.homogeneousCore'_eq_sSup

end HomogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

include A

#print Ideal.homogeneousHull /-
/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | ∃ (i : ι)(x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r },
    by
    refine' Ideal.homogeneous_span _ _ fun x hx => _
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.homogeneous_coe⟩
#align ideal.homogeneous_hull Ideal.homogeneousHull
-/

/- warning: ideal.le_to_ideal_homogeneous_hull -> Ideal.le_toIdeal_homogeneousHull is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) I (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) I (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Ideal.homogeneousHull.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I))
Case conversion may be inaccurate. Consider using '#align ideal.le_to_ideal_homogeneous_hull Ideal.le_toIdeal_homogeneousHullₓ'. -/
theorem Ideal.le_toIdeal_homogeneousHull : I ≤ (Ideal.homogeneousHull 𝒜 I).toIdeal :=
  by
  intro r hr
  classical
    rw [← DirectSum.sum_support_decompose 𝒜 r]
    refine' Ideal.sum_mem _ _
    intro j hj
    apply Ideal.subset_span
    use j
    use ⟨r, hr⟩
    rfl
#align ideal.le_to_ideal_homogeneous_hull Ideal.le_toIdeal_homogeneousHull

/- warning: ideal.homogeneous_hull_mono -> Ideal.homogeneousHull_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.partialOrder.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], Monotone.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instPartialOrderHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_hull_mono Ideal.homogeneousHull_monoₓ'. -/
theorem Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J =>
  by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  refine' ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩
#align ideal.homogeneous_hull_mono Ideal.homogeneousHull_mono

variable {I 𝒜}

/- warning: ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self -> Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u3} A _inst_1}, (Ideal.IsHomogeneous.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I)) I)
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] {I : Ideal.{u1} A _inst_1}, (Ideal.IsHomogeneous.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I) -> (Eq.{succ u1} (Ideal.{u1} A _inst_1) (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 (Ideal.homogeneousHull.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I)) I)
Case conversion may be inaccurate. Consider using '#align ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_selfₓ'. -/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.Homogeneous 𝒜) :
    (Ideal.homogeneousHull 𝒜 I).toIdeal = I :=
  by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop
#align ideal.is_homogeneous.to_ideal_homogeneous_hull_eq_self Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self

/- warning: homogeneous_ideal.homogeneous_hull_to_ideal_eq_self -> HomogeneousIdeal.homogeneousHull_toIdeal_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) I
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u1} A] [_inst_2 : DecidableEq.{succ u3} ι] [_inst_3 : AddMonoid.{u3} ι] [_inst_4 : SetLike.{u2, u1} σ A] [_inst_5 : AddSubmonoidClass.{u2, u1} σ A (AddMonoid.toAddZeroClass.{u1} A (AddMonoidWithOne.toAddMonoid.{u1} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} A (NonAssocSemiring.toAddCommMonoidWithOne.{u1} A (Semiring.toNonAssocSemiring.{u1} A _inst_1))))) _inst_4] {𝒜 : ι -> σ} [_inst_6 : GradedRing.{u3, u1, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6), Eq.{succ u1} (HomogeneousIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousHull.{u3, u2, u1} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 (HomogeneousIdeal.toIdeal.{u3, u2, u1} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 I)) I
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.homogeneous_hull_to_ideal_eq_self HomogeneousIdeal.homogeneousHull_toIdeal_eq_selfₓ'. -/
@[simp]
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousHull 𝒜 = I :=
  HomogeneousIdeal.toIdeal_injective <| I.Homogeneous.toIdeal_homogeneousHull_eq_self
#align homogeneous_ideal.homogeneous_hull_to_ideal_eq_self HomogeneousIdeal.homogeneousHull_toIdeal_eq_self

variable (I 𝒜)

/- warning: ideal.to_ideal_homogeneous_hull_eq_supr -> Ideal.toIdeal_homogeneousHull_eq_iSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.to_ideal_homogeneous_hull_eq_supr Ideal.toIdeal_homogeneousHull_eq_iSupₓ'. -/
theorem Ideal.toIdeal_homogeneousHull_eq_iSup :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) :=
  by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_set_of_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, Subtype.coe_mk, SetLike.mem_coe]
#align ideal.to_ideal_homogeneous_hull_eq_supr Ideal.toIdeal_homogeneousHull_eq_iSup

/- warning: ideal.homogeneous_hull_eq_supr -> Ideal.homogeneousHull_eq_iSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_hull_eq_supr Ideal.homogeneousHull_eq_iSupₓ'. -/
theorem Ideal.homogeneousHull_eq_iSup :
    I.homogeneousHull 𝒜 =
      ⨆ i,
        ⟨Ideal.span (GradedRing.proj 𝒜 i '' I),
          Ideal.homogeneous_span 𝒜 _ (by rintro _ ⟨x, -, rfl⟩; apply SetLike.homogeneous_coe)⟩ :=
  by ext1; rw [Ideal.toIdeal_homogeneousHull_eq_iSup, to_ideal_supr]; rfl
#align ideal.homogeneous_hull_eq_supr Ideal.homogeneousHull_eq_iSup

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

/- warning: ideal.homogeneous_hull.gc -> Ideal.homogeneousHull.gc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisConnection.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.partialOrder.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisConnection.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instPartialOrderHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_hull.gc Ideal.homogeneousHull.gcₓ'. -/
theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal := fun I J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _), fun H =>
    J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩
#align ideal.homogeneous_hull.gc Ideal.homogeneousHull.gc

/- warning: ideal.homogeneous_hull.gi -> Ideal.homogeneousHull.gi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisInsertion.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.partialOrder.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜], GaloisInsertion.{u3, u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) (PartialOrder.toPreorder.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instPartialOrderHomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_hull.gi Ideal.homogeneousHull.giₓ'. -/
/-- `ideal.homogeneous_hull 𝒜` and `to_ideal : homogeneous_ideal 𝒜 → ideal A` form a galois
insertion-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal
    where
  choice I H := ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u I := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H
#align ideal.homogeneous_hull.gi Ideal.homogeneousHull.gi

/- warning: ideal.homogeneous_hull_eq_Inf -> Ideal.homogeneousHull_eq_sInf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousHull.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I) (InfSet.sInf.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.hasInf.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (setOf.{u3} (HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (fun (J : HomogeneousIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) => LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toHasLe.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (SetLike.partialOrder.{u3, u3} (Ideal.{u3} A _inst_1) A (Submodule.setLike.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1))))) I (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_1 _inst_4 _inst_5 𝒜] (I : Ideal.{u3} A _inst_1), Eq.{succ u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (Ideal.homogeneousHull.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6 I) (InfSet.sInf.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (HomogeneousIdeal.instInfSetHomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6) (setOf.{u3} (HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) (fun (J : HomogeneousIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6) => LE.le.{u3} (Ideal.{u3} A _inst_1) (Preorder.toLE.{u3} (Ideal.{u3} A _inst_1) (PartialOrder.toPreorder.{u3} (Ideal.{u3} A _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Ideal.{u3} A _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Ideal.{u3} A _inst_1) (Submodule.completeLattice.{u3, u3} A A _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))) (Semiring.toModule.{u3} A _inst_1)))))) I (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_6 J))))
Case conversion may be inaccurate. Consider using '#align ideal.homogeneous_hull_eq_Inf Ideal.homogeneousHull_eq_sInfₓ'. -/
theorem Ideal.homogeneousHull_eq_sInf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = sInf { J : HomogeneousIdeal 𝒜 | I ≤ J.toIdeal } :=
  Eq.symm <| IsGLB.sInf_eq <| (Ideal.homogeneousHull.gc 𝒜).isLeast_l.IsGLB
#align ideal.homogeneous_hull_eq_Inf Ideal.homogeneousHull_eq_sInf

end GaloisConnection

section IrrelevantIdeal

variable [Semiring A]

variable [DecidableEq ι]

variable [CanonicallyOrderedAddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

open GradedRing SetLike.GradedMonoid DirectSum

#print HomogeneousIdeal.irrelevant /-
/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `canonically_ordered_add_monoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `ι` is assumed to be `canonically_ordered_add_monoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i ≤ 0`, i.e. `{a | ∀ (i : ι), i ≤ 0 → aᵢ = 0}`.
-/
def HomogeneousIdeal.irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨(GradedRing.projZeroRingHom 𝒜).ker, fun i r (hr : (decompose 𝒜 r 0 : A) = 0) =>
    by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩
#align homogeneous_ideal.irrelevant HomogeneousIdeal.irrelevant
-/

/- warning: homogeneous_ideal.mem_irrelevant_iff -> HomogeneousIdeal.mem_irrelevant_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.mem_irrelevant_iff HomogeneousIdeal.mem_irrelevant_iffₓ'. -/
@[simp]
theorem HomogeneousIdeal.mem_irrelevant_iff (a : A) :
    a ∈ HomogeneousIdeal.irrelevant 𝒜 ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl
#align homogeneous_ideal.mem_irrelevant_iff HomogeneousIdeal.mem_irrelevant_iff

/- warning: homogeneous_ideal.to_ideal_irrelevant -> HomogeneousIdeal.toIdeal_irrelevant is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : CanonicallyOrderedAddMonoid.{u1} ι] [_inst_4 : SetLike.{u2, u3} σ A] [_inst_5 : AddSubmonoidClass.{u2, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u1, u3, u2} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} ι (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ι _inst_3))) _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u1, u2, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u1} ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} ι (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ι _inst_3))) _inst_6 (HomogeneousIdeal.irrelevant.{u1, u2, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (RingHom.ker.{u3, u3, u3} A A (RingHom.{u3, u3} A A (Semiring.toNonAssocSemiring.{u3} A _inst_1) (Semiring.toNonAssocSemiring.{u3} A _inst_1)) _inst_1 _inst_1 (RingHom.ringHomClass.{u3, u3} A A (Semiring.toNonAssocSemiring.{u3} A _inst_1) (Semiring.toNonAssocSemiring.{u3} A _inst_1)) (GradedRing.projZeroRingHom.{u1, u3, u2} ι A σ _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))
but is expected to have type
  forall {ι : Type.{u2}} {σ : Type.{u1}} {A : Type.{u3}} [_inst_1 : Semiring.{u3} A] [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : CanonicallyOrderedAddMonoid.{u2} ι] [_inst_4 : SetLike.{u1, u3} σ A] [_inst_5 : AddSubmonoidClass.{u1, u3} σ A (AddMonoid.toAddZeroClass.{u3} A (AddMonoidWithOne.toAddMonoid.{u3} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} A (NonAssocSemiring.toAddCommMonoidWithOne.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_1))))) _inst_4] (𝒜 : ι -> σ) [_inst_6 : GradedRing.{u2, u3, u1} ι A σ (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u2} ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} ι (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} ι _inst_3))) _inst_1 _inst_4 _inst_5 𝒜], Eq.{succ u3} (Ideal.{u3} A _inst_1) (HomogeneousIdeal.toIdeal.{u2, u1, u3} ι σ A _inst_1 _inst_4 _inst_5 𝒜 (fun (a : ι) (b : ι) => _inst_2 a b) (AddCommMonoid.toAddMonoid.{u2} ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} ι (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} ι _inst_3))) _inst_6 (HomogeneousIdeal.irrelevant.{u2, u1, u3} ι σ A _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6)) (RingHom.ker.{u3, u3, u3} A A (RingHom.{u3, u3} A A (Semiring.toNonAssocSemiring.{u3} A _inst_1) (Semiring.toNonAssocSemiring.{u3} A _inst_1)) _inst_1 _inst_1 (RingHom.instRingHomClassRingHom.{u3, u3} A A (Semiring.toNonAssocSemiring.{u3} A _inst_1) (Semiring.toNonAssocSemiring.{u3} A _inst_1)) (GradedRing.projZeroRingHom.{u2, u3, u1} ι A σ _inst_1 (fun (a : ι) (b : ι) => _inst_2 a b) _inst_3 _inst_4 _inst_5 𝒜 _inst_6))
Case conversion may be inaccurate. Consider using '#align homogeneous_ideal.to_ideal_irrelevant HomogeneousIdeal.toIdeal_irrelevantₓ'. -/
@[simp]
theorem HomogeneousIdeal.toIdeal_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal = (GradedRing.projZeroRingHom 𝒜).ker :=
  rfl
#align homogeneous_ideal.to_ideal_irrelevant HomogeneousIdeal.toIdeal_irrelevant

end IrrelevantIdeal

