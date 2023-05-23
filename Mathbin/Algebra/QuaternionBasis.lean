/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.quaternion_basis
! leanprover-community/mathlib commit 3aa5b8a9ed7a7cabd36e6e1d022c9858ab8a8c2d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Quaternion
import Mathbin.Tactic.Ring

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `quaternion_algebra.basis A c₁ c₂`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂]`.
* `quaternion_algebra.basis.self R`: the canonical basis for `ℍ[R,c₁,c₂]`.
* `quaternion_algebra.basis.comp_hom b f`: transform a basis `b` by an alg_hom `f`.
* `quaternion_algebra.lift`: Define an `alg_hom` out of `ℍ[R,c₁,c₂]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `complex.lift`,
  but takes a bundled `quaternion_algebra.basis` instead of just a `subtype` as the amount of
  data / proves is non-negligeable.
-/


open Quaternion

namespace QuaternionAlgebra

#print QuaternionAlgebra.Basis /-
/-- A quaternion basis contains the information both sufficient and necessary to construct an
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to `A`; or equivalently, a surjective
`R`-algebra homomorphism from `ℍ[R,c₁,c₂]` to an `R`-subalgebra of `A`.

Note that for definitional convenience, `k` is provided as a field even though `i_mul_j` fully
determines it. -/
structure Basis {R : Type _} (A : Type _) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ : R) where
  (i j k : A)
  i_mul_i : i * i = c₁ • 1
  j_mul_j : j * j = c₂ • 1
  i_mul_j : i * j = k
  j_mul_i : j * i = -k
#align quaternion_algebra.basis QuaternionAlgebra.Basis
-/

variable {R : Type _} {A B : Type _} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ : R}

namespace Basis

/- warning: quaternion_algebra.basis.ext -> QuaternionAlgebra.Basis.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} {{q₁ : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂}} {{q₂ : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂}}, (Eq.{succ u2} A (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₁) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₂)) -> (Eq.{succ u2} A (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₁) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₂)) -> (Eq.{succ u2} (QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) q₁ q₂)
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Ring.{u1} A] [_inst_4 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u1} A _inst_2)] {c₁ : R} {c₂ : R} {{q₁ : QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂}} {{q₂ : QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂}}, (Eq.{succ u1} A (QuaternionAlgebra.Basis.i.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₁) (QuaternionAlgebra.Basis.i.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₂)) -> (Eq.{succ u1} A (QuaternionAlgebra.Basis.j.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₁) (QuaternionAlgebra.Basis.j.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q₂)) -> (Eq.{succ u1} (QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂) q₁ q₂)
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.ext QuaternionAlgebra.Basis.extₓ'. -/
/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂⦄ (hi : q₁.i = q₂.i) (hj : q₁.j = q₂.j) : q₁ = q₂ :=
  by
  cases q₁
  cases q₂
  congr
  rw [← q₁_i_mul_j, ← q₂_i_mul_j]
  congr
#align quaternion_algebra.basis.ext QuaternionAlgebra.Basis.ext

variable (R)

/- warning: quaternion_algebra.basis.self -> QuaternionAlgebra.Basis.self is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] {c₁ : R} {c₂ : R}, QuaternionAlgebra.Basis.{u1, u1} R (QuaternionAlgebra.{u1} R c₁ c₂) _inst_1 (QuaternionAlgebra.ring.{u1} R _inst_1 c₁ c₂) (QuaternionAlgebra.algebra.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) c₁ c₂
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] {c₁ : R} {c₂ : R}, QuaternionAlgebra.Basis.{u1, u1} R (QuaternionAlgebra.{u1} R c₁ c₂) _inst_1 (QuaternionAlgebra.instRing.{u1} R _inst_1 c₁ c₂) (QuaternionAlgebra.instAlgebraQuaternionAlgebraToSemiringInstRing.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) c₁ c₂
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.self QuaternionAlgebra.Basis.selfₓ'. -/
/-- There is a natural quaternionic basis for the `quaternion_algebra`. -/
@[simps i j k]
protected def self : Basis ℍ[R,c₁,c₂] c₁ c₂
    where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp
#align quaternion_algebra.basis.self QuaternionAlgebra.Basis.self

variable {R}

instance : Inhabited (Basis ℍ[R,c₁,c₂] c₁ c₂) :=
  ⟨Basis.self R⟩

variable (q : Basis A c₁ c₂)

include q

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

/- warning: quaternion_algebra.basis.i_mul_k -> QuaternionAlgebra.Basis.i_mul_k is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) c₁ (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4)) c₁ (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.i_mul_k QuaternionAlgebra.Basis.i_mul_kₓ'. -/
@[simp]
theorem i_mul_k : q.i * q.k = c₁ • q.j := by
  rw [← i_mul_j, ← mul_assoc, i_mul_i, smul_mul_assoc, one_mul]
#align quaternion_algebra.basis.i_mul_k QuaternionAlgebra.Basis.i_mul_k

/- warning: quaternion_algebra.basis.k_mul_i -> QuaternionAlgebra.Basis.k_mul_i is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) c₁) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4)) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) c₁) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.k_mul_i QuaternionAlgebra.Basis.k_mul_iₓ'. -/
@[simp]
theorem k_mul_i : q.k * q.i = -c₁ • q.j := by
  rw [← i_mul_j, mul_assoc, j_mul_i, mul_neg, i_mul_k, neg_smul]
#align quaternion_algebra.basis.k_mul_i QuaternionAlgebra.Basis.k_mul_i

/- warning: quaternion_algebra.basis.k_mul_j -> QuaternionAlgebra.Basis.k_mul_j is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) c₂ (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4)) c₂ (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.k_mul_j QuaternionAlgebra.Basis.k_mul_jₓ'. -/
@[simp]
theorem k_mul_j : q.k * q.j = c₂ • q.i := by
  rw [← i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]
#align quaternion_algebra.basis.k_mul_j QuaternionAlgebra.Basis.k_mul_j

/- warning: quaternion_algebra.basis.j_mul_k -> QuaternionAlgebra.Basis.j_mul_k is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) c₂) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) (QuaternionAlgebra.Basis.j.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4)) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) c₂) (QuaternionAlgebra.Basis.i.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.j_mul_k QuaternionAlgebra.Basis.j_mul_kₓ'. -/
@[simp]
theorem j_mul_k : q.j * q.k = -c₂ • q.i := by
  rw [← i_mul_j, ← mul_assoc, j_mul_i, neg_mul, k_mul_j, neg_smul]
#align quaternion_algebra.basis.j_mul_k QuaternionAlgebra.Basis.j_mul_k

/- warning: quaternion_algebra.basis.k_mul_k -> QuaternionAlgebra.Basis.k_mul_k is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (Neg.neg.{u2} A (SubNegMonoid.toHasNeg.{u2} A (AddGroup.toSubNegMonoid.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (AddCommGroupWithOne.toAddGroupWithOne.{u2} A (Ring.toAddCommGroupWithOne.{u2} A _inst_2))))) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) c₁ c₂) (OfNat.ofNat.{u2} A 1 (OfNat.mk.{u2} A 1 (One.one.{u2} A (AddMonoidWithOne.toOne.{u2} A (AddGroupWithOne.toAddMonoidWithOne.{u2} A (AddCommGroupWithOne.toAddGroupWithOne.{u2} A (Ring.toAddCommGroupWithOne.{u2} A _inst_2)))))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2)))) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q) (QuaternionAlgebra.Basis.k.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q)) (Neg.neg.{u2} A (Ring.toNeg.{u2} A _inst_2) (HSMul.hSMul.{u1, u2, u2} R A A (instHSMul.{u1, u2} R A (Algebra.toSMul.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) c₁ c₂) (OfNat.ofNat.{u2} A 1 (One.toOfNat1.{u2} A (Semiring.toOne.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.k_mul_k QuaternionAlgebra.Basis.k_mul_kₓ'. -/
@[simp]
theorem k_mul_k : q.k * q.k = -((c₁ * c₂) • 1) := by
  rw [← i_mul_j, mul_assoc, ← mul_assoc q.j _ _, j_mul_i, ← i_mul_j, ← mul_assoc, mul_neg, ←
    mul_assoc, i_mul_i, smul_mul_assoc, one_mul, neg_mul, smul_mul_assoc, j_mul_j, smul_smul]
#align quaternion_algebra.basis.k_mul_k QuaternionAlgebra.Basis.k_mul_k

#print QuaternionAlgebra.Basis.lift /-
/-- Intermediate result used to define `quaternion_algebra.basis.lift_hom`. -/
def lift (x : ℍ[R,c₁,c₂]) : A :=
  algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k
#align quaternion_algebra.basis.lift QuaternionAlgebra.Basis.lift
-/

/- warning: quaternion_algebra.basis.lift_zero -> QuaternionAlgebra.Basis.lift_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (OfNat.ofNat.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 0 (OfNat.mk.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 0 (Zero.zero.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.hasZero.{u1} R _inst_1 c₁ c₂))))) (OfNat.ofNat.{u2} A 0 (OfNat.mk.{u2} A 0 (Zero.zero.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A _inst_2))))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (OfNat.ofNat.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 0 (Zero.toOfNat0.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.instZeroQuaternionAlgebra.{u1} R _inst_1 c₁ c₂)))) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A (Ring.toSemiring.{u2} A _inst_2)))))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_zero QuaternionAlgebra.Basis.lift_zeroₓ'. -/
theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂]) = 0 := by simp [lift]
#align quaternion_algebra.basis.lift_zero QuaternionAlgebra.Basis.lift_zero

/- warning: quaternion_algebra.basis.lift_one -> QuaternionAlgebra.Basis.lift_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (OfNat.ofNat.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 1 (OfNat.mk.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 1 (One.one.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.hasOne.{u1} R _inst_1 c₁ c₂))))) (OfNat.ofNat.{u2} A 1 (OfNat.mk.{u2} A 1 (One.one.{u2} A (AddMonoidWithOne.toOne.{u2} A (AddGroupWithOne.toAddMonoidWithOne.{u2} A (AddCommGroupWithOne.toAddGroupWithOne.{u2} A (Ring.toAddCommGroupWithOne.{u2} A _inst_2)))))))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (OfNat.ofNat.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) 1 (One.toOfNat1.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.instOneQuaternionAlgebra.{u1} R _inst_1 c₁ c₂)))) (OfNat.ofNat.{u2} A 1 (One.toOfNat1.{u2} A (Semiring.toOne.{u2} A (Ring.toSemiring.{u2} A _inst_2))))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_one QuaternionAlgebra.Basis.lift_oneₓ'. -/
theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂]) = 1 := by simp [lift]
#align quaternion_algebra.basis.lift_one QuaternionAlgebra.Basis.lift_one

/- warning: quaternion_algebra.basis.lift_add -> QuaternionAlgebra.Basis.lift_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (x : QuaternionAlgebra.{u1} R c₁ c₂) (y : QuaternionAlgebra.{u1} R c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (HAdd.hAdd.{u1, u1, u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.{u1} R c₁ c₂) (instHAdd.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.hasAdd.{u1} R _inst_1 c₁ c₂)) x y)) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (Distrib.toHasAdd.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x) (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q y))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Ring.{u1} A] [_inst_4 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u1} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (x : QuaternionAlgebra.{u2} R c₁ c₂) (y : QuaternionAlgebra.{u2} R c₁ c₂), Eq.{succ u1} A (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (HAdd.hAdd.{u2, u2, u2} (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.{u2} R c₁ c₂) (instHAdd.{u2} (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.instAddQuaternionAlgebra.{u2} R _inst_1 c₁ c₂)) x y)) (HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A (Distrib.toAdd.{u1} A (NonUnitalNonAssocSemiring.toDistrib.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A _inst_2)))))) (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x) (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q y))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_add QuaternionAlgebra.Basis.lift_addₓ'. -/
theorem lift_add (x y : ℍ[R,c₁,c₂]) : q.lift (x + y) = q.lift x + q.lift y :=
  by
  simp [lift, add_smul]
  abel
#align quaternion_algebra.basis.lift_add QuaternionAlgebra.Basis.lift_add

/- warning: quaternion_algebra.basis.lift_mul -> QuaternionAlgebra.Basis.lift_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (x : QuaternionAlgebra.{u1} R c₁ c₂) (y : QuaternionAlgebra.{u1} R c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (HMul.hMul.{u1, u1, u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.{u1} R c₁ c₂) (instHMul.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.hasMul.{u1} R _inst_1 c₁ c₂)) x y)) (HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (Distrib.toHasMul.{u2} A (Ring.toDistrib.{u2} A _inst_2))) (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x) (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q y))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Ring.{u1} A] [_inst_4 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u1} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (x : QuaternionAlgebra.{u2} R c₁ c₂) (y : QuaternionAlgebra.{u2} R c₁ c₂), Eq.{succ u1} A (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (HMul.hMul.{u2, u2, u2} (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.{u2} R c₁ c₂) (instHMul.{u2} (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.instMulQuaternionAlgebra.{u2} R _inst_1 c₁ c₂)) x y)) (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (NonUnitalNonAssocRing.toMul.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A _inst_2)))) (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x) (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q y))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_mul QuaternionAlgebra.Basis.lift_mulₓ'. -/
theorem lift_mul (x y : ℍ[R,c₁,c₂]) : q.lift (x * y) = q.lift x * q.lift y :=
  by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp only [add_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, ← Algebra.smul_def,
    smul_add, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, add_smul, ← add_assoc, mul_neg, neg_smul]
  simp only [mul_right_comm _ _ (c₁ * c₂), mul_comm _ (c₁ * c₂)]
  simp only [mul_comm _ c₁, mul_right_comm _ _ c₁]
  simp only [mul_comm _ c₂, mul_right_comm _ _ c₂]
  simp only [← mul_comm c₁ c₂, ← mul_assoc]
  simp [sub_eq_add_neg, add_smul, ← add_assoc]
  abel
#align quaternion_algebra.basis.lift_mul QuaternionAlgebra.Basis.lift_mul

/- warning: quaternion_algebra.basis.lift_smul -> QuaternionAlgebra.Basis.lift_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (r : R) (x : QuaternionAlgebra.{u1} R c₁ c₂), Eq.{succ u2} A (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (SMul.smul.{u1, u1} R (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.hasSmul.{u1, u1} R R _inst_1 c₁ c₂ (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))))) r x)) (SMul.smul.{u1, u2} R A (SMulZeroClass.toHasSmul.{u1, u2} R A (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} A (AddMonoid.toAddZeroClass.{u2} A (AddCommMonoid.toAddMonoid.{u2} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R A (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A (Ring.toSemiring.{u2} A _inst_2)))) (Algebra.toModule.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2) _inst_4))))) r (QuaternionAlgebra.Basis.lift.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : Ring.{u1} A] [_inst_4 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u1} A _inst_2)] {c₁ : R} {c₂ : R} (q : QuaternionAlgebra.Basis.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (r : R) (x : QuaternionAlgebra.{u2} R c₁ c₂), Eq.{succ u1} A (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q (HSMul.hSMul.{u2, u2, u2} R (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.{u2} R c₁ c₂) (instHSMul.{u2, u2} R (QuaternionAlgebra.{u2} R c₁ c₂) (QuaternionAlgebra.instSMulQuaternionAlgebra.{u2, u2} R R c₁ c₂ (Algebra.toSMul.{u2, u2} R R (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (Algebra.id.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) r x)) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (Algebra.toSMul.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u1} A _inst_2) _inst_4)) r (QuaternionAlgebra.Basis.lift.{u2, u1} R A _inst_1 _inst_2 _inst_4 c₁ c₂ q x))
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_smul QuaternionAlgebra.Basis.lift_smulₓ'. -/
theorem lift_smul (r : R) (x : ℍ[R,c₁,c₂]) : q.lift (r • x) = r • q.lift x := by
  simp [lift, mul_smul, ← Algebra.smul_def]
#align quaternion_algebra.basis.lift_smul QuaternionAlgebra.Basis.lift_smul

/- warning: quaternion_algebra.basis.lift_hom -> QuaternionAlgebra.Basis.liftHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R}, (QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) -> (AlgHom.{u1, u1, u2} R (QuaternionAlgebra.{u1} R c₁ c₂) A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.ring.{u1} R _inst_1 c₁ c₂)) (Ring.toSemiring.{u2} A _inst_2) (QuaternionAlgebra.algebra.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) _inst_4)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R}, (QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) -> (AlgHom.{u1, u1, u2} R (QuaternionAlgebra.{u1} R c₁ c₂) A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.instRing.{u1} R _inst_1 c₁ c₂)) (Ring.toSemiring.{u2} A _inst_2) (QuaternionAlgebra.instAlgebraQuaternionAlgebraToSemiringInstRing.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) _inst_4)
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.basis.lift_hom QuaternionAlgebra.Basis.liftHomₓ'. -/
/-- A `quaternion_algebra.basis` implies an `alg_hom` from the quaternions. -/
@[simps]
def liftHom : ℍ[R,c₁,c₂] →ₐ[R] A :=
  AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul
#align quaternion_algebra.basis.lift_hom QuaternionAlgebra.Basis.liftHom

#print QuaternionAlgebra.Basis.compHom /-
/-- Transform a `quaternion_algebra.basis` through an `alg_hom`. -/
@[simps i j k]
def compHom (F : A →ₐ[R] B) : Basis B c₁ c₂
    where
  i := F q.i
  i_mul_i := by rw [← F.map_mul, q.i_mul_i, F.map_smul, F.map_one]
  j := F q.j
  j_mul_j := by rw [← F.map_mul, q.j_mul_j, F.map_smul, F.map_one]
  k := F q.k
  i_mul_j := by rw [← F.map_mul, q.i_mul_j]
  j_mul_i := by rw [← F.map_mul, q.j_mul_i, F.map_neg]
#align quaternion_algebra.basis.comp_hom QuaternionAlgebra.Basis.compHom
-/

end Basis

/- warning: quaternion_algebra.lift -> QuaternionAlgebra.lift is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R}, Equiv.{succ u2, max (succ u1) (succ u2)} (QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (AlgHom.{u1, u1, u2} R (QuaternionAlgebra.{u1} R c₁ c₂) A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.ring.{u1} R _inst_1 c₁ c₂)) (Ring.toSemiring.{u2} A _inst_2) (QuaternionAlgebra.algebra.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) _inst_4)
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Ring.{u2} A] [_inst_4 : Algebra.{u1, u2} R A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} A _inst_2)] {c₁ : R} {c₂ : R}, Equiv.{succ u2, max (succ u2) (succ u1)} (QuaternionAlgebra.Basis.{u1, u2} R A _inst_1 _inst_2 _inst_4 c₁ c₂) (AlgHom.{u1, u1, u2} R (QuaternionAlgebra.{u1} R c₁ c₂) A (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} (QuaternionAlgebra.{u1} R c₁ c₂) (QuaternionAlgebra.instRing.{u1} R _inst_1 c₁ c₂)) (Ring.toSemiring.{u2} A _inst_2) (QuaternionAlgebra.instAlgebraQuaternionAlgebraToSemiringInstRing.{u1, u1} R R _inst_1 c₁ c₂ (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) _inst_4)
Case conversion may be inaccurate. Consider using '#align quaternion_algebra.lift QuaternionAlgebra.liftₓ'. -/
/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
def lift : Basis A c₁ c₂ ≃ (ℍ[R,c₁,c₂] →ₐ[R] A)
    where
  toFun := Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [basis.lift]
  right_inv F := by
    ext
    dsimp [basis.lift]
    rw [← F.commutes]
    simp only [← F.commutes, ← F.map_smul, ← F.map_add, mk_add_mk, smul_mk, smul_zero,
      algebra_map_eq]
    congr
    simp
#align quaternion_algebra.lift QuaternionAlgebra.lift

end QuaternionAlgebra

