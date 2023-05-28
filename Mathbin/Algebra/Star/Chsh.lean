/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.star.chsh
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Invertible
import Mathbin.Data.Real.Sqrt

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered `*`-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered `*`-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a `*`-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered `*`-ring
(that is, a `*`-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered `*`-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a `C^*`-algebra.
In the `C^*`-algebra case,
the order structure is completely determined by the `*`-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the `*`-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/


universe u

#print IsCHSHTuple /-
/-- A CHSH tuple in a *-monoid consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of boolean observables.
-/
@[nolint has_nonempty_instance]
structure IsCHSHTuple {R} [Monoid R] [StarSemigroup R] (A₀ A₁ B₀ B₁ : R) where
  A₀_inv : A₀ ^ 2 = 1
  A₁_inv : A₁ ^ 2 = 1
  B₀_inv : B₀ ^ 2 = 1
  B₁_inv : B₁ ^ 2 = 1
  A₀_sa : star A₀ = A₀
  A₁_sa : star A₁ = A₁
  B₀_sa : star B₀ = B₀
  B₁_sa : star B₁ = B₁
  A₀B₀_commutes : A₀ * B₀ = B₀ * A₀
  A₀B₁_commutes : A₀ * B₁ = B₁ * A₀
  A₁B₀_commutes : A₁ * B₀ = B₀ * A₁
  A₁B₁_commutes : A₁ * B₁ = B₁ * A₁
#align is_CHSH_tuple IsCHSHTuple
-/

variable {R : Type u}

/- warning: CHSH_id -> CHSH_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align CHSH_id CHSH_idₓ'. -/
theorem CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1)
    (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) :
    (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) =
      4 * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) :=
  by
  -- If we had a Gröbner basis algorithm, this would be trivial.
  -- Without one, it is somewhat tedious!
  rw [← sub_eq_zero]
  repeat'
    ring_nf
    simp only [A₁_inv, B₁_inv, sub_eq_add_neg, add_mul, mul_add, sub_mul, mul_sub, add_assoc,
      neg_add, neg_sub, sub_add, sub_sub, neg_mul, ← sq, A₀_inv, B₀_inv, ← sq, ← mul_assoc, one_mul,
      mul_one, add_right_neg, add_zero, sub_eq_add_neg, A₀_inv, mul_one, add_right_neg,
      MulZeroClass.zero_mul]
#align CHSH_id CHSH_id

/- warning: CHSH_inequality_of_comm -> CHSH_inequality_of_comm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : OrderedCommRing.{u1} R] [_inst_2 : StarOrderedRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (OrderedAddCommGroup.toPartialOrder.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))] [_inst_3 : Algebra.{0, u1} Real R Real.commSemiring (Ring.toSemiring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))] [_inst_4 : OrderedSMul.{0, u1} Real R Real.orderedSemiring (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedRing.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) (MulActionWithZero.toSMulWithZero.{0, u1} Real R Real.monoidWithZero (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (OrderedAddCommMonoid.toAddCommMonoid.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedRing.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))))) (Module.toMulActionWithZero.{0, u1} Real R Real.semiring (AddCommGroup.toAddCommMonoid.{u1} R (OrderedAddCommGroup.toAddCommGroup.{u1} R (StarOrderedRing.orderedAddCommGroup.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1))) (OrderedAddCommGroup.toPartialOrder.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) _inst_2))) (Algebra.toModule.{0, u1} Real R Real.commSemiring (Ring.toSemiring.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) _inst_3)))] (A₀ : R) (A₁ : R) (B₀ : R) (B₁ : R), (IsCHSHTuple.{u1} R (Ring.toMonoid.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) (StarRing.toStarSemigroup.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (StarOrderedRing.toStarRing.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (OrderedAddCommGroup.toPartialOrder.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) _inst_2)) A₀ A₁ B₀ B₁) -> (LE.le.{u1} R (Preorder.toHasLe.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommGroup.toPartialOrder.{u1} R (StarOrderedRing.orderedAddCommGroup.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1))) (OrderedAddCommGroup.toPartialOrder.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))) _inst_2)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) A₀ B₀) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) A₀ B₁)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) A₁ B₀)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))))) A₁ B₁)) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : OrderedCommRing.{u1} R] [_inst_2 : StarOrderedRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (OrderedRing.toPartialOrder.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1))] [_inst_3 : Algebra.{0, u1} Real R Real.instCommSemiringReal (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))] [_inst_4 : OrderedSMul.{0, u1} Real R Real.orderedSemiring (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1))) (MulActionWithZero.toSMulWithZero.{0, u1} Real R Real.instMonoidWithZeroReal (AddMonoid.toZero.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (OrderedAddCommMonoid.toAddCommMonoid.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real R Real.semiring (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} R (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} R (OrderedRing.toOrderedAddCommGroup.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (Algebra.toModule.{0, u1} Real R Real.instCommSemiringReal (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1))) _inst_3)))] (A₀ : R) (A₁ : R) (B₀ : R) (B₁ : R), (IsCHSHTuple.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1))))) (StarRing.toStarSemigroup.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (StarOrderedRing.toStarRing.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R (OrderedCommRing.toCommRing.{u1} R _inst_1)))) (OrderedRing.toPartialOrder.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)) _inst_2)) A₀ A₁ B₀ B₁) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedRing.toPartialOrder.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))) A₀ B₀) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))) A₀ B₁)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))) A₁ B₀)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (OrderedRing.toRing.{u1} R (OrderedCommRing.toOrderedRing.{u1} R _inst_1)))))) A₁ B₁)) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (Semiring.toNatCast.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (OrderedCommRing.toOrderedCommSemiring.{u1} R _inst_1)))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align CHSH_inequality_of_comm CHSH_inequality_of_commₓ'. -/
/-- Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered `*`-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm [OrderedCommRing R] [StarOrderedRing R] [Algebra ℝ R]
    [OrderedSMul ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 :=
  by
  let P := 2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁
  have i₁ : 0 ≤ P :=
    by
    have idem : P * P = 4 * P := CHSH_id T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    have idem' : P = (1 / 4 : ℝ) • (P * P) :=
      by
      have h : 4 * P = (4 : ℝ) • P := by simp [Algebra.smul_def]
      rw [idem, h, ← mul_smul]
      norm_num
    have sa : star P = P := by
      dsimp [P]
      simp only [star_add, star_sub, star_mul, star_bit0, star_one, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa, mul_comm B₀, mul_comm B₁]
    rw [idem']
    conv_rhs =>
      congr
      skip
      congr
      rw [← sa]
    convert smul_le_smul_of_nonneg (star_mul_self_nonneg : 0 ≤ star P * P) _
    · simp
    · infer_instance
    · norm_num
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add] using i₁
#align CHSH_inequality_of_comm CHSH_inequality_of_comm

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/


-- mathport name: «expr√2»
local notation "√2" => (Real.sqrt 2 : ℝ)

namespace tsirelson_inequality

/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/


/- warning: tsirelson_inequality.tsirelson_inequality_aux -> TsirelsonInequality.tsirelson_inequality_aux is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inv.inv.{0} Real Real.hasInv (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inv.inv.{0} Real Real.hasInv (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Inv.inv.{0} Real Real.hasInv (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))))
but is expected to have type
  Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Inv.inv.{0} Real Real.instInvReal (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))))
Case conversion may be inaccurate. Consider using '#align tsirelson_inequality.tsirelson_inequality_aux TsirelsonInequality.tsirelson_inequality_auxₓ'. -/
-- This calculation, which we need for Tsirelson's bound,
-- defeated me. Thanks for the rescue from Shing Tak Lam!
theorem tsirelson_inequality_aux : √2 * √2 ^ 3 = √2 * (2 * √2⁻¹ + 4 * (√2⁻¹ * 2⁻¹)) :=
  by
  ring_nf; field_simp [(@Real.sqrt_pos 2).2 (by norm_num)]
  convert congr_arg (· ^ 2) (@Real.sq_sqrt 2 (by norm_num)) using 1 <;> simp only [← pow_mul] <;>
    norm_num
#align tsirelson_inequality.tsirelson_inequality_aux TsirelsonInequality.tsirelson_inequality_aux

/- warning: tsirelson_inequality.sqrt_two_inv_mul_self -> TsirelsonInequality.sqrt_two_inv_mul_self is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inv.inv.{0} Real Real.hasInv (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Inv.inv.{0} Real Real.hasInv (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Inv.inv.{0} Real Real.hasInv (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Inv.inv.{0} Real Real.instInvReal (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align tsirelson_inequality.sqrt_two_inv_mul_self TsirelsonInequality.sqrt_two_inv_mul_selfₓ'. -/
theorem sqrt_two_inv_mul_self : √2⁻¹ * √2⁻¹ = (2⁻¹ : ℝ) :=
  by
  rw [← mul_inv]
  norm_num
#align tsirelson_inequality.sqrt_two_inv_mul_self TsirelsonInequality.sqrt_two_inv_mul_self

end tsirelson_inequality

open tsirelson_inequality

/- warning: tsirelson_inequality -> tsirelson_inequality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align tsirelson_inequality tsirelson_inequalityₓ'. -/
/-- In a noncommutative ordered `*`-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
theorem tsirelson_inequality [OrderedRing R] [StarOrderedRing R] [Algebra ℝ R] [OrderedSMul ℝ R]
    [StarModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1 :=
  by
  -- abel will create `ℤ` multiplication. We will `simp` them away to `ℝ` multiplication.
  have M : ∀ (m : ℤ) (a : ℝ) (x : R), m • a • x = ((m : ℝ) * a) • x := fun m a x => by
    rw [zsmul_eq_smul_cast ℝ, ← mul_smul]
  let P := √2⁻¹ • (A₁ + A₀) - B₀
  let Q := √2⁻¹ • (A₁ - A₀) + B₁
  have w : √2 ^ 3 • 1 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = √2⁻¹ • (P ^ 2 + Q ^ 2) :=
    by
    dsimp [P, Q]
    -- distribute out all the powers and products appearing on the RHS
    simp only [sq, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub]
    -- pull all coefficients out to the front, and combine `√2`s where possible
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, sqrt_two_inv_mul_self]
    -- replace Aᵢ * Aᵢ = 1 and Bᵢ * Bᵢ = 1
    simp only [← sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv]
    -- move Aᵢ to the left of Bᵢ
    simp only [← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
    -- collect terms, simplify coefficients, and collect terms again:
    abel
    -- all terms coincide, but the last one. Simplify all other terms
    simp only [M]
    simp only [neg_mul, Int.cast_bit0, one_mul, mul_inv_cancel_of_invertible, Int.cast_one,
      one_smul, Int.cast_neg, add_right_inj, neg_smul, ← add_smul]
    -- just look at the coefficients now:
    congr
    exact mul_left_cancel₀ (by norm_num) tsirelson_inequality_aux
  have pos : 0 ≤ √2⁻¹ • (P ^ 2 + Q ^ 2) :=
    by
    have P_sa : star P = P := by
      dsimp [P]
      simp only [star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa]
    have Q_sa : star Q = Q := by
      dsimp [Q]
      simp only [star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa]
    have P2_nonneg : 0 ≤ P ^ 2 := by
      rw [sq]
      conv =>
        congr
        skip
        congr
        rw [← P_sa]
      convert(star_mul_self_nonneg : 0 ≤ star P * P)
    have Q2_nonneg : 0 ≤ Q ^ 2 := by
      rw [sq]
      conv =>
        congr
        skip
        congr
        rw [← Q_sa]
      convert(star_mul_self_nonneg : 0 ≤ star Q * Q)
    convert smul_le_smul_of_nonneg (add_nonneg P2_nonneg Q2_nonneg)
        (le_of_lt (show 0 < √2⁻¹ by norm_num))
    -- `norm_num` can't directly show `0 ≤ √2⁻¹`
    simp
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add, w] using Pos
#align tsirelson_inequality tsirelson_inequality

