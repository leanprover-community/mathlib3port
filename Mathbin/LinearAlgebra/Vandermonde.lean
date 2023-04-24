/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.vandermonde
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Algebra.GeomSum
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.LinearAlgebra.Matrix.Nondegenerate

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
-/


variable {R : Type _} [CommRing R]

open Equiv Finset

open BigOperators Matrix

namespace Matrix

#print Matrix.vandermonde /-
/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : Fin n → R) : Matrix (Fin n) (Fin n) R := fun i j => v i ^ (j : ℕ)
#align matrix.vandermonde Matrix.vandermonde
-/

/- warning: matrix.vandermonde_apply -> Matrix.vandermonde_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.vandermonde.{u1} R _inst_1 n v i j) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v i) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) j))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.vandermonde.{u1} R _inst_1 n v i j) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (v i) (Fin.val n j))
Case conversion may be inaccurate. Consider using '#align matrix.vandermonde_apply Matrix.vandermonde_applyₓ'. -/
@[simp]
theorem vandermonde_apply {n : ℕ} (v : Fin n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) :=
  rfl
#align matrix.vandermonde_apply Matrix.vandermonde_apply

/- warning: matrix.vandermonde_cons -> Matrix.vandermonde_cons is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v0 : R) (v : (Fin n) -> R), Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) R) (Matrix.vandermonde.{u1} R _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => R) v0 v)) (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> R) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) v0 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (HasLiftT.mk.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (CoeTCₓ.coe.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (coeBase.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) Nat (Fin.coeToNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) j)) (fun (i : Fin n) => Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => R) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v i) (Matrix.vandermonde.{u1} R _inst_1 n v i j))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v0 : R) (v : (Fin n) -> R), Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) R) (Matrix.vandermonde.{u1} R _inst_1 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => R) v0 v)) (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> R) (fun (j : Fin (Nat.succ n)) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) v0 (Fin.val (Nat.succ n) j)) (fun (i : Fin n) => Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => R) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (v i) (Matrix.vandermonde.{u1} R _inst_1 n v i j))))
Case conversion may be inaccurate. Consider using '#align matrix.vandermonde_cons Matrix.vandermonde_consₓ'. -/
@[simp]
theorem vandermonde_cons {n : ℕ} (v0 : R) (v : Fin n → R) :
    vandermonde (Fin.cons v0 v : Fin n.succ → R) =
      Fin.cons (fun j => v0 ^ (j : ℕ)) fun i => Fin.cons 1 fun j => v i * vandermonde v i j :=
  by
  ext (i j)
  refine' Fin.cases (by simp) (fun i => _) i
  refine' Fin.cases (by simp) (fun j => _) j
  simp [pow_succ]
#align matrix.vandermonde_cons Matrix.vandermonde_cons

/- warning: matrix.vandermonde_succ -> Matrix.vandermonde_succ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin (Nat.succ n)) -> R), Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (Nat.succ n)) (Fin (Nat.succ n)) R) (Matrix.vandermonde.{u1} R _inst_1 (Nat.succ n) v) (Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => (Fin (Nat.succ n)) -> R) (fun (j : Fin (Nat.succ n)) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (Nat.succ n)) Nat (HasLiftT.mk.{1, 1} (Fin (Nat.succ n)) Nat (CoeTCₓ.coe.{1, 1} (Fin (Nat.succ n)) Nat (coeBase.{1, 1} (Fin (Nat.succ n)) Nat (Fin.coeToNat (Nat.succ n))))) j)) (fun (i : Fin n) => Fin.cons.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => R) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v (Fin.succ n i)) (Matrix.vandermonde.{u1} R _inst_1 n (Fin.tail.{u1} n (fun (ᾰ : Fin (Nat.succ n)) => R) v) i j))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin (Nat.succ n)) -> R), Eq.{succ u1} (Matrix.{0, 0, u1} (Fin (Nat.succ n)) (Fin (Nat.succ n)) R) (Matrix.vandermonde.{u1} R _inst_1 (Nat.succ n) v) (Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => (Fin (Nat.succ n)) -> R) (fun (j : Fin (Nat.succ n)) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (v (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (Fin.val (Nat.succ n) j)) (fun (i : Fin n) => Fin.cons.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => R) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (v (Fin.succ n i)) (Matrix.vandermonde.{u1} R _inst_1 n (Fin.tail.{u1} n (fun (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => R) v) i j))))
Case conversion may be inaccurate. Consider using '#align matrix.vandermonde_succ Matrix.vandermonde_succₓ'. -/
theorem vandermonde_succ {n : ℕ} (v : Fin n.succ → R) :
    vandermonde v =
      Fin.cons (fun j => v 0 ^ (j : ℕ)) fun i =>
        Fin.cons 1 fun j => v i.succ * vandermonde (Fin.tail v) i j :=
  by
  conv_lhs => rw [← Fin.cons_self_tail v, vandermonde_cons]
  simp only [Fin.tail]
#align matrix.vandermonde_succ Matrix.vandermonde_succ

/- warning: matrix.vandermonde_mul_vandermonde_transpose -> Matrix.vandermonde_mul_vandermonde_transpose is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (w : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.mul.{u1, 0, 0, 0} (Fin n) (Fin n) (Fin n) R (Fin.fintype n) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.vandermonde.{u1} R _inst_1 n v) (Matrix.transpose.{u1, 0, 0} (Fin n) (Fin n) R (Matrix.vandermonde.{u1} R _inst_1 n w)) i j) (Finset.sum.{u1, 0} R (Fin n) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (k : Fin n) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v i) (w j)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) k)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (w : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.mul.{u1, 0, 0, 0} (Fin n) (Fin n) (Fin n) R (Fin.fintype n) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.vandermonde.{u1} R _inst_1 n v) (Matrix.transpose.{u1, 0, 0} (Fin n) (Fin n) R (Matrix.vandermonde.{u1} R _inst_1 n w)) i j) (Finset.sum.{u1, 0} R (Fin n) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (k : Fin n) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (v i) (w j)) (Fin.val n k)))
Case conversion may be inaccurate. Consider using '#align matrix.vandermonde_mul_vandermonde_transpose Matrix.vandermonde_mul_vandermonde_transposeₓ'. -/
theorem vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : Fin n → R) (i j) :
    (vandermonde v ⬝ (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]
#align matrix.vandermonde_mul_vandermonde_transpose Matrix.vandermonde_mul_vandermonde_transpose

/- warning: matrix.vandermonde_transpose_mul_vandermonde -> Matrix.vandermonde_transpose_mul_vandermonde is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.mul.{u1, 0, 0, 0} (Fin n) (Fin n) (Fin n) R (Fin.fintype n) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.transpose.{u1, 0, 0} (Fin n) (Fin n) R (Matrix.vandermonde.{u1} R _inst_1 n v)) (Matrix.vandermonde.{u1} R _inst_1 n v) i j) (Finset.sum.{u1, 0} R (Fin n) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (k : Fin n) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (v k) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) j))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {n : Nat} (v : (Fin n) -> R) (i : Fin n) (j : Fin n), Eq.{succ u1} R (Matrix.mul.{u1, 0, 0, 0} (Fin n) (Fin n) (Fin n) R (Fin.fintype n) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Matrix.transpose.{u1, 0, 0} (Fin n) (Fin n) R (Matrix.vandermonde.{u1} R _inst_1 n v)) (Matrix.vandermonde.{u1} R _inst_1 n v) i j) (Finset.sum.{u1, 0} R (Fin n) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (k : Fin n) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (v k) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n i) (Fin.val n j))))
Case conversion may be inaccurate. Consider using '#align matrix.vandermonde_transpose_mul_vandermonde Matrix.vandermonde_transpose_mul_vandermondeₓ'. -/
theorem vandermonde_transpose_mul_vandermonde {n : ℕ} (v : Fin n → R) (i j) :
    ((vandermonde v)ᵀ ⬝ vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]
#align matrix.vandermonde_transpose_mul_vandermonde Matrix.vandermonde_transpose_mul_vandermonde

#print Matrix.det_vandermonde /-
theorem det_vandermonde {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j in Ioi i, v j - v i :=
  by
  unfold vandermonde
  induction' n with n ih
  · exact det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
  calc
    det (of fun i j : Fin n.succ => v i ^ (j : ℕ)) =
        det
          (of fun i j : Fin n.succ =>
            Matrix.vecCons (v 0 ^ (j : ℕ)) (fun i => v (Fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :=
      det_eq_of_forall_row_eq_smul_add_const (Matrix.vecCons 0 1) 0 (Fin.cons_zero _ _) _
    _ =
        det
          (of fun i j : Fin n =>
            Matrix.vecCons (v 0 ^ (j.succ : ℕ))
              (fun i : Fin n => v (Fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (Fin.succAbove 0 i)) :=
      by
      simp_rw [det_succ_column_zero, Fin.sum_univ_succ, of_apply, Matrix.cons_val_zero, submatrix,
        of_apply, Matrix.cons_val_succ, Fin.val_zero, pow_zero, one_mul, sub_self,
        MulZeroClass.mul_zero, MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero]
    _ =
        det
          (of fun i j : Fin n =>
              (v (Fin.succ i) - v 0) *
                ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :
            Matrix _ _ R) :=
      by
      congr
      ext (i j)
      rw [Fin.succAbove_zero, Matrix.cons_val_succ, Fin.val_succ, mul_comm]
      exact (geom_sum₂_mul (v i.succ) (v 0) (j + 1 : ℕ)).symm
    _ =
        (∏ i : Fin n, v (Fin.succ i) - v 0) *
          det fun i j : Fin n =>
            ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :=
      (det_mul_column (fun i => v (Fin.succ i) - v 0) _)
    _ = (∏ i : Fin n, v (Fin.succ i) - v 0) * det fun i j : Fin n => v (Fin.succ i) ^ (j : ℕ) :=
      (congr_arg ((· * ·) _) _)
    _ = ∏ i : Fin n.succ, ∏ j in Ioi i, v j - v i := by
      simp_rw [ih (v ∘ Fin.succ), Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
    
  · intro i j
    simp_rw [of_apply]
    rw [Matrix.cons_val_zero]
    refine' Fin.cases _ (fun i => _) i
    · simp
    rw [Matrix.cons_val_succ, Matrix.cons_val_succ, Pi.one_apply]
    ring
  · cases n
    · simp only [det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    apply det_eq_of_forall_col_eq_smul_add_pred fun i => v 0
    · intro j
      simp
    · intro i j
      simp only [smul_eq_mul, Pi.add_apply, Fin.val_succ, Fin.coe_castSucc, Pi.smul_apply]
      rw [Finset.sum_range_succ, add_comm, tsub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine' Finset.sum_congr rfl fun i' hi' => _
      rw [mul_left_comm (v 0), Nat.succ_sub, pow_succ]
      exact nat.lt_succ_iff.mp (finset.mem_range.mp hi')
#align matrix.det_vandermonde Matrix.det_vandermonde
-/

#print Matrix.det_vandermonde_eq_zero_iff /-
theorem det_vandermonde_eq_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Fin n, v i = v j ∧ i ≠ j :=
  by
  constructor
  · simp only [det_vandermonde v, Finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index]
    exact fun i _ j h₁ h₂ => ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
  · simp only [Ne.def, forall_exists_index, and_imp]
    refine' fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => _)
    rw [vandermonde_apply, vandermonde_apply, h₁]
#align matrix.det_vandermonde_eq_zero_iff Matrix.det_vandermonde_eq_zero_iff
-/

#print Matrix.det_vandermonde_ne_zero_iff /-
theorem det_vandermonde_ne_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  simpa only [det_vandermonde_eq_zero_iff, Ne.def, not_exists, not_and, Classical.not_not]
#align matrix.det_vandermonde_ne_zero_iff Matrix.det_vandermonde_ne_zero_iff
-/

/- warning: matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero -> Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (j : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (f j) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i)) (v i))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (OfNat.mk.{u1} ((Fin n) -> R) 0 (Zero.zero.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (j : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)))))) (f j) (Fin.val n i)) (v i))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (Zero.toOfNat0.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.Vandermonde._hyg.1498 : Fin n) => R) (fun (i : Fin n) => CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))))
Case conversion may be inaccurate. Consider using '#align matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zeroₓ'. -/
theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero {R : Type _} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ j, (∑ i : Fin n, f j ^ (i : ℕ) * v i) = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero

/- warning: matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero -> Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (j : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (v i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (f j) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (OfNat.mk.{u1} ((Fin n) -> R) 0 (Zero.zero.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (j : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (v i) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)))))) (f j) (Fin.val n i)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (Zero.toOfNat0.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.Vandermonde._hyg.1571 : Fin n) => R) (fun (i : Fin n) => CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))))
Case conversion may be inaccurate. Consider using '#align matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zeroₓ'. -/
theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero {R : Type _} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f) (hfv : ∀ j, (∑ i, v i * f j ^ (i : ℕ)) = 0) :
    v = 0 := by
  apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf
  simp_rw [mul_comm]
  exact hfv
#align matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero

/- warning: matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero -> Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (i : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (v j) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_2)))) (f j) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (OfNat.mk.{u1} ((Fin n) -> R) 0 (Zero.zero.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))] {n : Nat} {f : (Fin n) -> R} {v : (Fin n) -> R}, (Function.Injective.{1, succ u1} (Fin n) R f) -> (forall (i : Fin n), Eq.{succ u1} R (Finset.sum.{u1, 0} R (Fin n) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (j : Fin n) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (v j) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)))))) (f j) (Fin.val n i)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))) -> (Eq.{succ u1} ((Fin n) -> R) v (OfNat.ofNat.{u1} ((Fin n) -> R) 0 (Zero.toOfNat0.{u1} ((Fin n) -> R) (Pi.instZero.{0, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.Vandermonde._hyg.1645 : Fin n) => R) (fun (i : Fin n) => CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2) _inst_3)))))))
Case conversion may be inaccurate. Consider using '#align matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zeroₓ'. -/
theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero {R : Type _} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero

end Matrix

