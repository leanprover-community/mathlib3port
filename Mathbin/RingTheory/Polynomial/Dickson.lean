/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer

! This file was ported from Lean 3 source module ring_theory.polynomial.dickson
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Invertible
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Polynomial.Chebyshev
import Mathbin.RingTheory.Ideal.LocalRing

/-!
# Dickson polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `polynomial.dickson_one_one_char_p`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `linear_recurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/


noncomputable section

namespace Polynomial

open Polynomial

variable {R S : Type _} [CommRing R] [CommRing S] (k : ℕ) (a : R)

#print Polynomial.dickson /-
/-- `dickson` is the `n`the (generalised) Dickson polynomial of the `k`-th kind associated to the
element `a ∈ R`. -/
noncomputable def dickson : ℕ → R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n
#align polynomial.dickson Polynomial.dickson
-/

/- warning: polynomial.dickson_zero -> Polynomial.dickson_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (k : Nat) (a : R), Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 k a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 3 (OfNat.mk.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 3 (bit1.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.hasOne.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.add'.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (One.one.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.hasOne.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (HasLiftT.mk.{1, succ u1} Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (CoeTCₓ.coe.{1, succ u1} Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Nat.castCoe.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.natCast.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) k))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (k : Nat) (a : R), Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 k a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) 3 (instOfNat.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) 3 (Polynomial.natCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Nat.cast.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.natCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) k))
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_zero Polynomial.dickson_zeroₓ'. -/
@[simp]
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl
#align polynomial.dickson_zero Polynomial.dickson_zero

#print Polynomial.dickson_one /-
@[simp]
theorem dickson_one : dickson k a 1 = X :=
  rfl
#align polynomial.dickson_one Polynomial.dickson_one
-/

/- warning: polynomial.dickson_two -> Polynomial.dickson_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_two Polynomial.dickson_twoₓ'. -/
theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k) := by simp only [dickson, sq]
#align polynomial.dickson_two Polynomial.dickson_two

/- warning: polynomial.dickson_add_two -> Polynomial.dickson_add_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_add_two Polynomial.dickson_add_twoₓ'. -/
@[simp]
theorem dickson_add_two (n : ℕ) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]
#align polynomial.dickson_add_two Polynomial.dickson_add_two

/- warning: polynomial.dickson_of_two_le -> Polynomial.dickson_of_two_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_of_two_le Polynomial.dickson_of_two_leₓ'. -/
theorem dickson_of_two_le {n : ℕ} (h : 2 ≤ n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) :=
  by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n
#align polynomial.dickson_of_two_le Polynomial.dickson_of_two_le

variable {R S k a}

/- warning: polynomial.map_dickson -> Polynomial.map_dickson is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} S] {k : Nat} {a : R} (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (n : Nat), Eq.{succ u2} (Polynomial.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (Polynomial.map.{u1, u2} R S (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) f (Polynomial.dickson.{u1} R _inst_1 k a n)) (Polynomial.dickson.{u2} S _inst_2 k (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) f a) n)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} S] {k : Nat} {a : R} (f : RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) (n : Nat), Eq.{succ u1} (Polynomial.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))) (Polynomial.map.{u2, u1} R S (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)) f (Polynomial.dickson.{u2} R _inst_1 k a n)) (Polynomial.dickson.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) a) _inst_2 k (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))))) f a) n)
Case conversion may be inaccurate. Consider using '#align polynomial.map_dickson Polynomial.map_dicksonₓ'. -/
theorem map_dickson (f : R →+* S) : ∀ n : ℕ, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp only [dickson_zero, Polynomial.map_sub, Polynomial.map_nat_cast, bit1, bit0,
      Polynomial.map_add, Polynomial.map_one]
  | 1 => by simp only [dickson_one, map_X]
  | n + 2 =>
    by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    rw [map_dickson, map_dickson]
#align polynomial.map_dickson Polynomial.map_dickson

variable {R}

/- warning: polynomial.dickson_two_zero -> Polynomial.dickson_two_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))) n) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.ring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) n) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) Nat (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instHPow.{u1, 0} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (Polynomial.X.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) n)
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_two_zero Polynomial.dickson_two_zeroₓ'. -/
@[simp]
theorem dickson_two_zero : ∀ n : ℕ, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    norm_num
  | 1 => by simp only [dickson_one, pow_one]
  | n + 2 => by
    simp only [dickson_add_two, C_0, MulZeroClass.zero_mul, sub_zero]
    rw [dickson_two_zero, pow_add X (n + 1) 1, mul_comm, pow_one]
#align polynomial.dickson_two_zero Polynomial.dickson_two_zero

section Dickson

/-!

### A Lambda structure on `ℤ[X]`

Mathlib doesn't currently know what a Lambda ring is.
But once it does, we can endow `ℤ[X]` with a Lambda structure
in terms of the `dickson 1 1` polynomials defined below.
There is exactly one other Lambda structure on `ℤ[X]` in terms of binomial polynomials.

-/


variable {R}

/- warning: polynomial.dickson_one_one_eval_add_inv -> Polynomial.dickson_one_one_eval_add_inv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x y) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))) -> (forall (n : Nat), Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x y) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) n)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x n) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y n)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) x y) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) -> (forall (n : Nat), Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x y) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) n)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) x n) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) y n)))
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_eval_add_inv Polynomial.dickson_one_one_eval_add_invₓ'. -/
theorem dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
    ∀ n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by
    simp only [bit0, eval_one, eval_add, pow_zero, dickson_zero]
    norm_num
  | 1 => by simp only [eval_X, dickson_one, pow_one]
  | n + 2 =>
    by
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv, eval_X, dickson_add_two, C_1,
      eval_one]
    conv_lhs => simp only [pow_succ, add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul]
    ring
#align polynomial.dickson_one_one_eval_add_inv Polynomial.dickson_one_one_eval_add_inv

variable (R)

/- warning: polynomial.dickson_one_one_eq_chebyshev_T -> Polynomial.dickson_one_one_eq_chebyshev_T is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_eq_chebyshev_T Polynomial.dickson_one_one_eq_chebyshev_Tₓ'. -/
theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] :
    ∀ n, dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟ 2) * X)
  | 0 => by
    simp only [chebyshev.T_zero, mul_one, one_comp, dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one, chebyshev.T_one, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul, mul_invOf_self,
      C_1, one_mul]
  | n + 2 =>
    by
    simp only [dickson_add_two, chebyshev.T_add_two, dickson_one_one_eq_chebyshev_T (n + 1),
      dickson_one_one_eq_chebyshev_T n, sub_comp, mul_comp, add_comp, X_comp, bit0_comp, one_comp]
    simp only [← C_1, ← C_bit0, ← mul_assoc, ← C_mul, mul_invOf_self]
    rw [C_1, one_mul]
    ring
#align polynomial.dickson_one_one_eq_chebyshev_T Polynomial.dickson_one_one_eq_chebyshev_T

/- warning: polynomial.chebyshev_T_eq_dickson_one_one -> Polynomial.chebyshev_T_eq_dickson_one_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.chebyshev_T_eq_dickson_one_one Polynomial.chebyshev_T_eq_dickson_one_oneₓ'. -/
theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : ℕ) :
    Chebyshev.T R n = C (⅟ 2) * (dickson 1 1 n).comp (2 * X) :=
  by
  rw [dickson_one_one_eq_chebyshev_T]
  simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul]
  rw [invOf_mul_self, C_1, one_mul, one_mul, comp_X]
#align polynomial.chebyshev_T_eq_dickson_one_one Polynomial.chebyshev_T_eq_dickson_one_one

/- warning: polynomial.dickson_one_one_mul -> Polynomial.dickson_one_one_mul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (m : Nat) (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) (Polynomial.comp.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) m) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) n))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (m : Nat) (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) (Polynomial.comp.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) m) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) n))
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_mul Polynomial.dickson_one_one_mulₓ'. -/
/-- The `(m * n)`-th Dickson polynomial of the first kind is the composition of the `m`-th and
`n`-th. -/
theorem dickson_one_one_mul (m n : ℕ) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) :=
  by
  have h : (1 : R) = Int.castRingHom R 1
  simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_one_one_eq_chebyshev_T,
    chebyshev.T_mul, two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  apply eval₂_congr rfl rfl
  rw [comp_assoc]
  apply eval₂_congr rfl _ rfl
  rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_1, ← C_bit0, ← C_mul, invOf_mul_self, C_1, one_mul]
#align polynomial.dickson_one_one_mul Polynomial.dickson_one_one_mul

/- warning: polynomial.dickson_one_one_comp_comm -> Polynomial.dickson_one_one_comp_comm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (m : Nat) (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.comp.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) m) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) n)) (Polynomial.comp.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) n) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) m))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (m : Nat) (n : Nat), Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.comp.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) m) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) n)) (Polynomial.comp.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) n) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) m))
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_comp_comm Polynomial.dickson_one_one_comp_commₓ'. -/
theorem dickson_one_one_comp_comm (m n : ℕ) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul, mul_comm, dickson_one_one_mul]
#align polynomial.dickson_one_one_comp_comm Polynomial.dickson_one_one_comp_comm

/- warning: polynomial.dickson_one_one_zmod_p -> Polynomial.dickson_one_one_zmod_p is a dubious translation:
lean 3 declaration is
  forall (p : Nat) [_inst_3 : Fact (Nat.Prime p)], Eq.{1} (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) (Polynomial.dickson.{0} (ZMod p) (ZMod.commRing p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} (ZMod p) 1 (OfNat.mk.{0} (ZMod p) 1 (One.one.{0} (ZMod p) (AddMonoidWithOne.toOne.{0} (ZMod p) (AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p) (AddCommGroupWithOne.toAddGroupWithOne.{0} (ZMod p) (Ring.toAddCommGroupWithOne.{0} (ZMod p) (DivisionRing.toRing.{0} (ZMod p) (Field.toDivisionRing.{0} (ZMod p) (ZMod.field p _inst_3)))))))))) p) (HPow.hPow.{0, 0, 0} (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) Nat (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) (instHPow.{0, 0} (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) Nat (Monoid.Pow.{0} (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) (Ring.toMonoid.{0} (Polynomial.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) (Polynomial.ring.{0} (ZMod p) (DivisionRing.toRing.{0} (ZMod p) (Field.toDivisionRing.{0} (ZMod p) (ZMod.field p _inst_3))))))) (Polynomial.X.{0} (ZMod p) (Ring.toSemiring.{0} (ZMod p) (CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))) p)
but is expected to have type
  forall (p : Nat) [_inst_3 : Fact (Nat.Prime p)], Eq.{1} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) (Polynomial.dickson.{0} (ZMod p) (ZMod.commRing p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} (ZMod p) 1 (One.toOfNat1.{0} (ZMod p) (Semiring.toOne.{0} (ZMod p) (DivisionSemiring.toSemiring.{0} (ZMod p) (Semifield.toDivisionSemiring.{0} (ZMod p) (Field.toSemifield.{0} (ZMod p) (ZMod.instFieldZMod p _inst_3))))))) p) (HPow.hPow.{0, 0, 0} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) Nat (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) (instHPow.{0, 0} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) Nat (Monoid.Pow.{0} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) (MonoidWithZero.toMonoid.{0} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) (Semiring.toMonoidWithZero.{0} (Polynomial.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) (Polynomial.semiring.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))) (Polynomial.X.{0} (ZMod p) (CommSemiring.toSemiring.{0} (ZMod p) (CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))) p)
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_zmod_p Polynomial.dickson_one_one_zmod_pₓ'. -/
theorem dickson_one_one_zmod_p (p : ℕ) [Fact p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p :=
  by
  -- Recall that `dickson_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : ∃ (K : Type)(_ : Field K), ∃ _ : CharP K p, Infinite K :=
    by
    let K := FractionRing (Polynomial (ZMod p))
    let f : ZMod p →+* K := (algebraMap _ (FractionRing _)).comp C
    have : CharP K p := by
      rw [← f.char_p_iff_char_p]
      infer_instance
    haveI : Infinite K :=
      Infinite.of_injective (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        (IsFractionRing.injective _ _)
    refine' ⟨K, _, _, _⟩ <;> infer_instance
  skip
  apply map_injective (ZMod.castHom (dvd_refl p) K) (RingHom.injective _)
  rw [map_dickson, Polynomial.map_pow, map_X]
  apply eq_of_infinite_eval_eq
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @Set.Infinite.mono _ { x : K | ∃ y, x = y + y⁻¹ ∧ y ≠ 0 }
  · rintro _ ⟨x, rfl, hx⟩
    simp only [eval_X, eval_pow, Set.mem_setOf_eq, @add_pow_char K _ p,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel hx), inv_pow, ZMod.castHom_apply,
      ZMod.cast_one']
  -- Now we need to show that the set of such `x` is infinite.
  -- If the set is finite, then we will show that `K` is also finite.
  · intro h
    rw [← Set.infinite_univ_iff] at H
    apply H
    -- To each `x` of the form `x = y + y⁻¹`
    -- we `bind` the set of `y` that solve the equation `x = y + y⁻¹`.
    -- For every `x`, that set is finite (since it is governed by a quadratic equation).
    -- For the moment, we claim that all these sets together cover `K`.
    suffices
      (Set.univ : Set K) =
        { x : K | ∃ y : K, x = y + y⁻¹ ∧ y ≠ 0 } >>= fun x => { y | x = y + y⁻¹ ∨ y = 0 }
      by
      rw [this]
      clear this
      refine' h.bUnion fun x hx => _
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : K[X] := X ^ 2 - C x * X + 1
      have hφ : φ ≠ 0 := by
        intro H
        have : φ.eval 0 = 0 := by rw [H, eval_zero]
        simpa [eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add, eval_mul,
          MulZeroClass.mul_zero, sq, zero_add, one_ne_zero]
      classical
        convert(φ.roots ∪ {0}).toFinset.finite_toSet using 1
        ext1 y
        simp only [Multiset.mem_toFinset, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_union,
          mem_roots hφ, is_root, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          Multiset.mem_singleton]
        by_cases hy : y = 0
        · simp only [hy, eq_self_iff_true, or_true_iff]
        apply or_congr _ Iff.rfl
        rw [← mul_left_inj' hy, eq_comm, ← sub_eq_zero, add_mul, inv_mul_cancel hy]
        apply eq_iff_eq_cancel_right.mpr
        ring
    -- Finally, we prove the claim that our finite union of finite sets covers all of `K`.
    · apply (Set.eq_univ_of_forall _).symm
      intro x
      simp only [exists_prop, Set.mem_iUnion, Set.bind_def, Ne.def, Set.mem_setOf_eq]
      by_cases hx : x = 0
      · simp only [hx, and_true_iff, eq_self_iff_true, inv_zero, or_true_iff]
        exact ⟨_, 1, rfl, one_ne_zero⟩
      · simp only [hx, or_false_iff, exists_eq_right]
        exact ⟨_, rfl, hx⟩
#align polynomial.dickson_one_one_zmod_p Polynomial.dickson_one_one_zmod_p

/- warning: polynomial.dickson_one_one_char_p -> Polynomial.dickson_one_one_charP is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_3 : Fact (Nat.Prime p)] [_inst_4 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))) p], Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) p) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.ring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) p)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_3 : Fact (Nat.Prime p)] [_inst_4 : CharP.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (Ring.toAddGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))) p], Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.dickson.{u1} R _inst_1 (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) p) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) Nat (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instHPow.{u1, 0} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) (Polynomial.X.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) p)
Case conversion may be inaccurate. Consider using '#align polynomial.dickson_one_one_char_p Polynomial.dickson_one_one_charPₓ'. -/
theorem dickson_one_one_charP (p : ℕ) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p :=
  by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1
  simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h, ← map_dickson (ZMod.castHom (dvd_refl p) R), dickson_one_one_zmod_p, Polynomial.map_pow,
    map_X]
#align polynomial.dickson_one_one_char_p Polynomial.dickson_one_one_charP

end Dickson

end Polynomial

