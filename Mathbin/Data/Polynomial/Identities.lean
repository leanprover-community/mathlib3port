/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.identities
! leanprover-community/mathlib commit 4e1eeebe63ac6d44585297e89c6e7ee5cbda487a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Derivative
import Mathbin.Tactic.LinearCombination
import Mathbin.Tactic.RingExp

/-!
# Theory of univariate polynomials

The main def is `binom_expansion`.
-/


noncomputable section

namespace Polynomial

open Polynomial

universe u v w x y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z} {a b : R}
  {m n : ℕ}

section Identities

/- warning: polynomial.pow_add_expansion -> Polynomial.powAddExpansion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (x : R) (y : R) (n : Nat), Subtype.{succ u1} R (fun (k : R) => Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) n) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x n) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) n) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) k (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (x : R) (y : R) (n : Nat), Subtype.{succ u1} R (fun (k : R) => Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) n) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x n) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) n) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) k (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align polynomial.pow_add_expansion Polynomial.powAddExpansionₓ'. -/
/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

Maybe use data.nat.choose to prove it.
 -/
/-- `(x + y)^n` can be expressed as `x^n + n*x^(n-1)*y + k * y^2` for some `k` in the ring.
-/
def powAddExpansion {R : Type _} [CommSemiring R] (x y : R) :
    ∀ n : ℕ, { k // (x + y) ^ n = x ^ n + n * x ^ (n - 1) * y + k * y ^ 2 }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | n + 2 => by
    cases' pow_add_expansion (n + 1) with z hz
    exists x * z + (n + 1) * x ^ n + z * y
    calc
      (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) := by ring
      _ = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) := by rw [hz]
      _ = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x * z + (n + 1) * x ^ n + z * y) * y ^ 2 :=
        by
        push_cast
        ring!
      
#align polynomial.pow_add_expansion Polynomial.powAddExpansion

variable [CommRing R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
    { k : R // a * (x + y) ^ e = a * (x ^ e + e * x ^ (e - 1) * y + k * y ^ 2) } :=
  by
  exists (pow_add_expansion x y e).val
  congr
  apply (pow_add_expansion _ _ _).property
#align polynomial.poly_binom_aux1 polynomial.poly_binom_aux1

private theorem poly_binom_aux2 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      f.Sum fun e a => a * (x ^ e + e * x ^ (e - 1) * y + (polyBinomAux1 x y e a).val * y ^ 2) :=
  by
  unfold eval eval₂; congr with (n z)
  apply (poly_binom_aux1 x y _ _).property
#align polynomial.poly_binom_aux2 polynomial.poly_binom_aux2

private theorem poly_binom_aux3 (f : R[X]) (x y : R) :
    f.eval (x + y) =
      ((f.Sum fun e a => a * x ^ e) + f.Sum fun e a => a * e * x ^ (e - 1) * y) +
        f.Sum fun e a => a * (polyBinomAux1 x y e a).val * y ^ 2 :=
  by
  rw [poly_binom_aux2]
  simp [left_distrib, sum_add, mul_assoc]
#align polynomial.poly_binom_aux3 polynomial.poly_binom_aux3

/- warning: polynomial.binom_expansion -> Polynomial.binomExpansion is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (x : R) (y : R), Subtype.{succ u1} R (fun (k : R) => Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x y) f) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) => (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) -> (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.derivative.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f)) y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) k (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (x : R) (y : R), Subtype.{succ u1} R (fun (k : R) => Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x y) f) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (fun (_x : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) => Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.module.{u1, u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.derivative.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f)) y)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) k (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align polynomial.binom_expansion Polynomial.binomExpansionₓ'. -/
/-- A polynomial `f` evaluated at `x + y` can be expressed as
the evaluation of `f` at `x`, plus `y` times the (polynomial) derivative of `f` at `x`,
plus some element `k : R` times `y^2`.
-/
def binomExpansion (f : R[X]) (x y : R) :
    { k : R // f.eval (x + y) = f.eval x + f.derivative.eval x * y + k * y ^ 2 } :=
  by
  exists f.sum fun e a => a * (poly_binom_aux1 x y e a).val
  rw [poly_binom_aux3]
  congr
  · rw [← eval_eq_sum]
  · rw [derivative_eval]
    exact finset.sum_mul.symm
  · exact finset.sum_mul.symm
#align polynomial.binom_expansion Polynomial.binomExpansion

/- warning: polynomial.pow_sub_pow_factor -> Polynomial.powSubPowFactor is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R) (i : Nat), Subtype.{succ u1} R (fun (z : R) => Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y i)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R) (i : Nat), Subtype.{succ u1} R (fun (z : R) => Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) x i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y i)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) x y)))
Case conversion may be inaccurate. Consider using '#align polynomial.pow_sub_pow_factor Polynomial.powSubPowFactorₓ'. -/
/-- `x^n - y^n` can be expressed as `z * (x - y)` for some `z` in the ring.
-/
def powSubPowFactor (x y : R) : ∀ i : ℕ, { z : R // x ^ i - y ^ i = z * (x - y) }
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨1, by simp⟩
  | k + 2 => by
    cases' @pow_sub_pow_factor (k + 1) with z hz
    exists z * x + y ^ (k + 1)
    linear_combination (norm := ring) x * hz
#align polynomial.pow_sub_pow_factor Polynomial.powSubPowFactor

/- warning: polynomial.eval_sub_factor -> Polynomial.evalSubFactor is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (x : R) (y : R), Subtype.{succ u1} R (fun (z : R) => Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) y f)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (x : R) (y : R), Subtype.{succ u1} R (fun (z : R) => Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) y f)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) x y)))
Case conversion may be inaccurate. Consider using '#align polynomial.eval_sub_factor Polynomial.evalSubFactorₓ'. -/
/-- For any polynomial `f`, `f.eval x - f.eval y` can be expressed as `z * (x - y)`
for some `z` in the ring.
-/
def evalSubFactor (f : R[X]) (x y : R) : { z : R // f.eval x - f.eval y = z * (x - y) } :=
  by
  refine' ⟨f.sum fun i r => r * (pow_sub_pow_factor x y i).val, _⟩
  delta eval eval₂
  simp only [Sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  dsimp
  congr with (i r)
  rw [mul_assoc, ← (pow_sub_pow_factor x y _).Prop, mul_sub]
#align polynomial.eval_sub_factor Polynomial.evalSubFactor

end Identities

end Polynomial

