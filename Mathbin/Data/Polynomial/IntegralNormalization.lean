/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.integral_normalization
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.Data.Polynomial.Monic

/-!
# Theory of monic polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `integral_normalization`, which relate arbitrary polynomials to monic ones.
-/


open BigOperators Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

#print Polynomial.integralNormalization /-
/-- If `f : R[X]` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
noncomputable def integralNormalization (f : R[X]) : R[X] :=
  ∑ i in f.support,
    monomial i (if f.degree = i then 1 else coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i))
#align polynomial.integral_normalization Polynomial.integralNormalization
-/

#print Polynomial.integralNormalization_zero /-
@[simp]
theorem integralNormalization_zero : integralNormalization (0 : R[X]) = 0 := by
  simp [integral_normalization]
#align polynomial.integral_normalization_zero Polynomial.integralNormalization_zero
-/

/- warning: polynomial.integral_normalization_coeff -> Polynomial.integralNormalization_coeff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (ite.{succ u1} R (Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} R _inst_1 f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) i)) (Option.decidableEq.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (Polynomial.degree.{u1} R _inst_1 f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) i)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (ite.{succ u1} R (Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} R _inst_1 f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) i)) (WithBot.instDecidableEqWithBot.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (Polynomial.degree.{u1} R _inst_1 f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) i)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i))))
Case conversion may be inaccurate. Consider using '#align polynomial.integral_normalization_coeff Polynomial.integralNormalization_coeffₓ'. -/
theorem integralNormalization_coeff {f : R[X]} {i : ℕ} :
    (integralNormalization f).coeff i =
      if f.degree = i then 1 else coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) :=
  by
  have : f.coeff i = 0 → f.degree ≠ i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  simp (config := { contextual := true }) [integral_normalization, coeff_monomial, this,
    mem_support_iff]
#align polynomial.integral_normalization_coeff Polynomial.integralNormalization_coeff

#print Polynomial.integralNormalization_support /-
theorem integralNormalization_support {f : R[X]} : (integralNormalization f).support ⊆ f.support :=
  by
  intro
  simp (config := { contextual := true }) [integral_normalization, coeff_monomial, mem_support_iff]
#align polynomial.integral_normalization_support Polynomial.integralNormalization_support
-/

#print Polynomial.integralNormalization_coeff_degree /-
theorem integralNormalization_coeff_degree {f : R[X]} {i : ℕ} (hi : f.degree = i) :
    (integralNormalization f).coeff i = 1 := by rw [integral_normalization_coeff, if_pos hi]
#align polynomial.integral_normalization_coeff_degree Polynomial.integralNormalization_coeff_degree
-/

#print Polynomial.integralNormalization_coeff_natDegree /-
theorem integralNormalization_coeff_natDegree {f : R[X]} (hf : f ≠ 0) :
    (integralNormalization f).coeff (natDegree f) = 1 :=
  integralNormalization_coeff_degree (degree_eq_natDegree hf)
#align polynomial.integral_normalization_coeff_nat_degree Polynomial.integralNormalization_coeff_natDegree
-/

/- warning: polynomial.integral_normalization_coeff_ne_degree -> Polynomial.integralNormalization_coeff_ne_degree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, (Ne.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} R _inst_1 f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) i)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, (Ne.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} R _inst_1 f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) i)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i))))
Case conversion may be inaccurate. Consider using '#align polynomial.integral_normalization_coeff_ne_degree Polynomial.integralNormalization_coeff_ne_degreeₓ'. -/
theorem integralNormalization_coeff_ne_degree {f : R[X]} {i : ℕ} (hi : f.degree ≠ i) :
    coeff (integralNormalization f) i = coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) := by
  rw [integral_normalization_coeff, if_neg hi]
#align polynomial.integral_normalization_coeff_ne_degree Polynomial.integralNormalization_coeff_ne_degree

/- warning: polynomial.integral_normalization_coeff_ne_nat_degree -> Polynomial.integralNormalization_coeff_ne_natDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, (Ne.{1} Nat i (Polynomial.natDegree.{u1} R _inst_1 f)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {f : Polynomial.{u1} R _inst_1} {i : Nat}, (Ne.{1} Nat i (Polynomial.natDegree.{u1} R _inst_1 f)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (Polynomial.integralNormalization.{u1} R _inst_1 f) i) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.coeff.{u1} R _inst_1 f i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 f) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} R _inst_1 f) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i))))
Case conversion may be inaccurate. Consider using '#align polynomial.integral_normalization_coeff_ne_nat_degree Polynomial.integralNormalization_coeff_ne_natDegreeₓ'. -/
theorem integralNormalization_coeff_ne_natDegree {f : R[X]} {i : ℕ} (hi : i ≠ natDegree f) :
    coeff (integralNormalization f) i = coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) :=
  integralNormalization_coeff_ne_degree (degree_ne_of_natDegree_ne hi.symm)
#align polynomial.integral_normalization_coeff_ne_nat_degree Polynomial.integralNormalization_coeff_ne_natDegree

#print Polynomial.monic_integralNormalization /-
theorem monic_integralNormalization {f : R[X]} (hf : f ≠ 0) : Monic (integralNormalization f) :=
  monic_of_degree_le f.natDegree
    (Finset.sup_le fun i h =>
      WithBot.coe_le_coe.2 <| le_natDegree_of_mem_supp i <| integralNormalization_support h)
    (integralNormalization_coeff_natDegree hf)
#align polynomial.monic_integral_normalization Polynomial.monic_integralNormalization
-/

end Semiring

section IsDomain

variable [Ring R] [IsDomain R]

#print Polynomial.support_integralNormalization /-
@[simp]
theorem support_integralNormalization {f : R[X]} : (integralNormalization f).support = f.support :=
  by
  by_cases hf : f = 0; · simp [hf]
  ext i
  refine' ⟨fun h => integral_normalization_support h, _⟩
  simp only [integral_normalization_coeff, mem_support_iff]
  intro hfi
  split_ifs with hi <;> simp [hfi, hi, pow_ne_zero _ (leading_coeff_ne_zero.mpr hf)]
#align polynomial.support_integral_normalization Polynomial.support_integralNormalization
-/

end IsDomain

section IsDomain

variable [CommRing R] [IsDomain R]

variable [CommSemiring S]

/- warning: polynomial.integral_normalization_eval₂_eq_zero -> Polynomial.integralNormalization_eval₂_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : CommSemiring.{u2} S] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) {z : S}, (Eq.{succ u2} S (Polynomial.eval₂.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S _inst_3) f z p) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))))))))) -> (forall (x : R), (Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) f x) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))))))))) -> (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u2} S (Polynomial.eval₂.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S _inst_3) f (HMul.hMul.{u2, u2, u2} S S S (instHMul.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))))) z (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) f (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p))) (Polynomial.integralNormalization.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p)) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))))))))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] [_inst_3 : CommSemiring.{u2} S] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) {z : S}, (Eq.{succ u2} S (Polynomial.eval₂.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S _inst_3) f z p) (OfNat.ofNat.{u2} S 0 (Zero.toOfNat0.{u2} S (CommMonoidWithZero.toZero.{u2} S (CommSemiring.toCommMonoidWithZero.{u2} S _inst_3))))) -> (forall (x : R), (Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))))) f x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) x) 0 (Zero.toOfNat0.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) x) (CommMonoidWithZero.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) x) (CommSemiring.toCommMonoidWithZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) x) _inst_3))))) -> (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_2))))))) -> (Eq.{succ u2} S (Polynomial.eval₂.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} S _inst_3) f (HMul.hMul.{u2, u2, u2} S ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p)) S (instHMul.{u2} S (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))))) z (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_3)))))) f (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p))) (Polynomial.integralNormalization.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p)) (OfNat.ofNat.{u2} S 0 (Zero.toOfNat0.{u2} S (CommMonoidWithZero.toZero.{u2} S (CommSemiring.toCommMonoidWithZero.{u2} S _inst_3)))))
Case conversion may be inaccurate. Consider using '#align polynomial.integral_normalization_eval₂_eq_zero Polynomial.integralNormalization_eval₂_eq_zeroₓ'. -/
theorem integralNormalization_eval₂_eq_zero {p : R[X]} (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (z * f p.leadingCoeff) (integralNormalization p) = 0 :=
  calc
    eval₂ f (z * f p.leadingCoeff) (integralNormalization p) =
        p.support.attach.Sum fun i =>
          f (coeff (integralNormalization p) i.1 * p.leadingCoeff ^ i.1) * z ^ i.1 :=
      by
      rw [eval₂, sum_def, support_integral_normalization]
      simp only [mul_comm z, mul_pow, mul_assoc, RingHom.map_pow, RingHom.map_mul]
      exact finset.sum_attach.symm
    _ =
        p.support.attach.Sum fun i =>
          f (coeff p i.1 * p.leadingCoeff ^ (natDegree p - 1)) * z ^ i.1 :=
      by
      by_cases hp : p = 0; · simp [hp]
      have one_le_deg : 1 ≤ nat_degree p :=
        Nat.succ_le_of_lt (nat_degree_pos_of_eval₂_root hp f hz inj)
      congr with i
      congr 2
      by_cases hi : i.1 = nat_degree p
      · rw [hi, integral_normalization_coeff_degree, one_mul, leading_coeff, ← pow_succ,
          tsub_add_cancel_of_le one_le_deg]
        exact degree_eq_nat_degree hp
      · have : i.1 ≤ p.nat_degree - 1 :=
          Nat.le_pred_of_lt (lt_of_le_of_ne (le_nat_degree_of_ne_zero (mem_support_iff.mp i.2)) hi)
        rw [integral_normalization_coeff_ne_nat_degree hi, mul_assoc, ← pow_add,
          tsub_add_cancel_of_le this]
    _ = f p.leadingCoeff ^ (natDegree p - 1) * eval₂ f z p :=
      by
      simp_rw [eval₂, sum_def, fun i => mul_comm (coeff p i), RingHom.map_mul, RingHom.map_pow,
        mul_assoc, ← Finset.mul_sum]
      congr 1
      exact @Finset.sum_attach _ _ p.support _ fun i => f (p.coeff i) * z ^ i
    _ = 0 := by rw [hz, _root_.mul_zero]
    
#align polynomial.integral_normalization_eval₂_eq_zero Polynomial.integralNormalization_eval₂_eq_zero

#print Polynomial.integralNormalization_aeval_eq_zero /-
theorem integralNormalization_aeval_eq_zero [Algebra R S] {f : R[X]} {z : S} (hz : aeval z f = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) :
    aeval (z * algebraMap R S f.leadingCoeff) (integralNormalization f) = 0 :=
  integralNormalization_eval₂_eq_zero (algebraMap R S) hz inj
#align polynomial.integral_normalization_aeval_eq_zero Polynomial.integralNormalization_aeval_eq_zero
-/

end IsDomain

end IntegralNormalization

end Polynomial

