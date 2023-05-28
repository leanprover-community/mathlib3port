/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro

! This file was ported from Lean 3 source module data.mv_polynomial.variables
! leanprover-community/mathlib commit 2f5b500a507264de86d666a5f87ddb976e2d8de4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Data.MvPolynomial.Rename

/-!
# Degrees and variables of polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes many results about the degree and variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `finset` containing each $x \in X$
that appears in a monomial in $P$.

The *degree set* of a polynomial $P \in R[X]$ is a `multiset` containing, for each $x$ in the
variable set, $n$ copies of $x$, where $n$ is the maximum number of copies of $x$ appearing in a
monomial of $P$.

## Main declarations

* `mv_polynomial.degrees p` : the multiset of variables representing the union of the multisets
  corresponding to each non-zero monomial in `p`.
  For example if `7 ≠ 0` in `R` and `p = x²y+7y³` then `degrees p = {x, x, y, y, y}`

* `mv_polynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

* `mv_polynomial.degree_of n p : ℕ` : the total degree of `p` with respect to the variable `n`.
  For example if `p = x⁴y+yz` then `degree_of y p = 1`.

* `mv_polynomial.total_degree p : ℕ` :
  the max of the sizes of the multisets `s` whose monomials `X^s` occur in `p`.
  For example if `p = x⁴y+yz` then `total_degree p = 5`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

-/


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type _} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Degrees

/-! ### `degrees` -/


#print MvPolynomial.degrees /-
/-- The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset.

(For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
-/
def degrees (p : MvPolynomial σ R) : Multiset σ :=
  letI := Classical.decEq σ
  p.support.sup fun s : σ →₀ ℕ => s.toMultiset
#align mv_polynomial.degrees MvPolynomial.degrees
-/

/- warning: mv_polynomial.degrees_def -> MvPolynomial.degrees_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (p : MvPolynomial.{u2, u1} σ R _inst_1), Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (Finset.sup.{u2, u2} (Multiset.{u2} σ) (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} σ) (Multiset.lattice.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b))) (Multiset.orderBot.{u2} σ) (MvPolynomial.support.{u1, u2} R σ _inst_1 p) (fun (s : Finsupp.{u2, 0} σ Nat Nat.hasZero) => coeFn.{succ u2, succ u2} (AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (fun (_x : AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) => (Finsupp.{u2, 0} σ Nat Nat.hasZero) -> (Multiset.{u2} σ)) (AddEquiv.hasCoeToFun.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (Finsupp.toMultiset.{u2} σ) s))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (p : MvPolynomial.{u1, u2} σ R _inst_1), Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (Finset.sup.{u1, u1} (Multiset.{u1} σ) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} σ) (Multiset.instLatticeMultiset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} σ) (MvPolynomial.support.{u2, u1} R σ _inst_1 p) (fun (s : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => FunLike.coe.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (_x : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => Multiset.{u1} σ) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (AddEquivClass.toEquivLike.{u1, u1, u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ) (AddEquiv.instAddEquivClassAddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ))))) (Finsupp.toMultiset.{u1} σ) s))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_def MvPolynomial.degrees_defₓ'. -/
theorem degrees_def [DecidableEq σ] (p : MvPolynomial σ R) :
    p.degrees = p.support.sup fun s : σ →₀ ℕ => s.toMultiset := by convert rfl
#align mv_polynomial.degrees_def MvPolynomial.degrees_def

/- warning: mv_polynomial.degrees_monomial -> MvPolynomial.degrees_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (s : Finsupp.{u2, 0} σ Nat Nat.hasZero) (a : R), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R R (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MvPolynomial.monomial.{u1, u2} R σ _inst_1 s) a)) (coeFn.{succ u2, succ u2} (AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (fun (_x : AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) => (Finsupp.{u2, 0} σ Nat Nat.hasZero) -> (Multiset.{u2} σ)) (AddEquiv.hasCoeToFun.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (Finsupp.toMultiset.{u2} σ) s)
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (s : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (a : R), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (LinearMap.{u2, u2, u2, max u2 u1} R R (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u1 u2} R R R (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MvPolynomial.monomial.{u2, u1} R σ _inst_1 s) a)) (FunLike.coe.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (_x : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => Multiset.{u1} σ) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (AddEquivClass.toEquivLike.{u1, u1, u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ) (AddEquiv.instAddEquivClassAddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ))))) (Finsupp.toMultiset.{u1} σ) s)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_monomial MvPolynomial.degrees_monomialₓ'. -/
theorem degrees_monomial (s : σ →₀ ℕ) (a : R) : degrees (monomial s a) ≤ s.toMultiset := by
  classical
    refine' Finset.sup_le fun t h => _
    have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    rw [this]
#align mv_polynomial.degrees_monomial MvPolynomial.degrees_monomial

/- warning: mv_polynomial.degrees_monomial_eq -> MvPolynomial.degrees_monomial_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (s : Finsupp.{u2, 0} σ Nat Nat.hasZero) (a : R), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) -> (Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R R (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MvPolynomial.monomial.{u1, u2} R σ _inst_1 s) a)) (coeFn.{succ u2, succ u2} (AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (fun (_x : AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) => (Finsupp.{u2, 0} σ Nat Nat.hasZero) -> (Multiset.{u2} σ)) (AddEquiv.hasCoeToFun.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (Finsupp.toMultiset.{u2} σ) s))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (s : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (a : R), (Ne.{succ u2} R a (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))) -> (Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (LinearMap.{u2, u2, u2, max u2 u1} R R (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u1 u2} R R R (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MvPolynomial.monomial.{u2, u1} R σ _inst_1 s) a)) (FunLike.coe.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (_x : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => Multiset.{u1} σ) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (AddEquivClass.toEquivLike.{u1, u1, u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ) (AddEquiv.instAddEquivClassAddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ))))) (Finsupp.toMultiset.{u1} σ) s))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_monomial_eq MvPolynomial.degrees_monomial_eqₓ'. -/
theorem degrees_monomial_eq (s : σ →₀ ℕ) (a : R) (ha : a ≠ 0) :
    degrees (monomial s a) = s.toMultiset := by
  classical
    refine' le_antisymm (degrees_monomial s a) <| Finset.le_sup <| _
    rw [support_monomial, if_neg ha, Finset.mem_singleton]
#align mv_polynomial.degrees_monomial_eq MvPolynomial.degrees_monomial_eq

/- warning: mv_polynomial.degrees_C -> MvPolynomial.degrees_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : R), Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (fun (_x : RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (RingHom.hasCoeToFun.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (MvPolynomial.C.{u1, u2} R σ _inst_1) a)) (OfNat.ofNat.{u2} (Multiset.{u2} σ) 0 (OfNat.mk.{u2} (Multiset.{u2} σ) 0 (Zero.zero.{u2} (Multiset.{u2} σ) (Multiset.hasZero.{u2} σ))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : R), Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) (MvPolynomial.C.{u2, u1} R σ _inst_1) a)) (OfNat.ofNat.{u1} (Multiset.{u1} σ) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} σ) (Multiset.instZeroMultiset.{u1} σ)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_C MvPolynomial.degrees_Cₓ'. -/
theorem degrees_C (a : R) : degrees (C a : MvPolynomial σ R) = 0 :=
  Multiset.le_zero.1 <| degrees_monomial _ _
#align mv_polynomial.degrees_C MvPolynomial.degrees_C

/- warning: mv_polynomial.degrees_X' -> MvPolynomial.degrees_X' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (n : σ), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (MvPolynomial.X.{u1, u2} R σ _inst_1 n)) (Singleton.singleton.{u2, u2} σ (Multiset.{u2} σ) (Multiset.hasSingleton.{u2} σ) n)
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (n : σ), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (MvPolynomial.X.{u2, u1} R σ _inst_1 n)) (Singleton.singleton.{u1, u1} σ (Multiset.{u1} σ) (Multiset.instSingletonMultiset.{u1} σ) n)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_X' MvPolynomial.degrees_X'ₓ'. -/
theorem degrees_X' (n : σ) : degrees (X n : MvPolynomial σ R) ≤ {n} :=
  le_trans (degrees_monomial _ _) <| le_of_eq <| toMultiset_single _ _
#align mv_polynomial.degrees_X' MvPolynomial.degrees_X'

/- warning: mv_polynomial.degrees_X -> MvPolynomial.degrees_X is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] (n : σ), Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (MvPolynomial.X.{u1, u2} R σ _inst_1 n)) (Singleton.singleton.{u2, u2} σ (Multiset.{u2} σ) (Multiset.hasSingleton.{u2} σ) n)
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R] (n : σ), Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (MvPolynomial.X.{u2, u1} R σ _inst_1 n)) (Singleton.singleton.{u1, u1} σ (Multiset.{u1} σ) (Multiset.instSingletonMultiset.{u1} σ) n)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_X MvPolynomial.degrees_Xₓ'. -/
@[simp]
theorem degrees_X [Nontrivial R] (n : σ) : degrees (X n : MvPolynomial σ R) = {n} :=
  (degrees_monomial_eq _ (1 : R) one_ne_zero).trans (toMultiset_single _ _)
#align mv_polynomial.degrees_X MvPolynomial.degrees_X

/- warning: mv_polynomial.degrees_zero -> MvPolynomial.degrees_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (Zero.zero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MulZeroClass.toHasZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (OfNat.ofNat.{u2} (Multiset.{u2} σ) 0 (OfNat.mk.{u2} (Multiset.{u2} σ) 0 (Zero.zero.{u2} (Multiset.{u2} σ) (Multiset.hasZero.{u2} σ))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommMonoidWithZero.toZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toCommMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (OfNat.ofNat.{u1} (Multiset.{u1} σ) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} σ) (Multiset.instZeroMultiset.{u1} σ)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_zero MvPolynomial.degrees_zeroₓ'. -/
@[simp]
theorem degrees_zero : degrees (0 : MvPolynomial σ R) = 0 :=
  by
  rw [← C_0]
  exact degrees_C 0
#align mv_polynomial.degrees_zero MvPolynomial.degrees_zero

/- warning: mv_polynomial.degrees_one -> MvPolynomial.degrees_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (One.one.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddMonoidWithOne.toOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toAddCommMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (OfNat.ofNat.{u2} (Multiset.{u2} σ) 0 (OfNat.mk.{u2} (Multiset.{u2} σ) 0 (Zero.zero.{u2} (Multiset.{u2} σ) (Multiset.hasZero.{u2} σ))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 1 (One.toOfNat1.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toOne.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (OfNat.ofNat.{u1} (Multiset.{u1} σ) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} σ) (Multiset.instZeroMultiset.{u1} σ)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_one MvPolynomial.degrees_oneₓ'. -/
@[simp]
theorem degrees_one : degrees (1 : MvPolynomial σ R) = 0 :=
  degrees_C 1
#align mv_polynomial.degrees_one MvPolynomial.degrees_one

/- warning: mv_polynomial.degrees_add -> MvPolynomial.degrees_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (p : MvPolynomial.{u2, u1} σ R _inst_1) (q : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (Sup.sup.{u2} (Multiset.{u2} σ) (SemilatticeSup.toHasSup.{u2} (Multiset.{u2} σ) (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} σ) (Multiset.lattice.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b)))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 q))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (p : MvPolynomial.{u1, u2} σ R _inst_1) (q : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)) (Sup.sup.{u1} (Multiset.{u1} σ) (SemilatticeSup.toSup.{u1} (Multiset.{u1} σ) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} σ) (Multiset.instLatticeMultiset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b)))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 q))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_add MvPolynomial.degrees_addₓ'. -/
theorem degrees_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).degrees ≤ p.degrees ⊔ q.degrees := by
  classical
    simp_rw [degrees_def]
    refine' Finset.sup_le fun b hb => _
    have := Finsupp.support_add hb
    rw [Finset.mem_union] at this
    cases this
    · exact le_sup_of_le_left (Finset.le_sup this)
    · exact le_sup_of_le_right (Finset.le_sup this)
#align mv_polynomial.degrees_add MvPolynomial.degrees_add

/- warning: mv_polynomial.degrees_sum -> MvPolynomial.degrees_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} [_inst_2 : DecidableEq.{succ u2} σ] (s : Finset.{u3} ι) (f : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (Finset.sum.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) s (fun (i : ι) => f i))) (Finset.sup.{u2, u3} (Multiset.{u2} σ) ι (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} σ) (Multiset.lattice.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b))) (Multiset.orderBot.{u2} σ) s (fun (i : ι) => MvPolynomial.degrees.{u1, u2} R σ _inst_1 (f i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} σ] (s : Finset.{u2} ι) (f : ι -> (MvPolynomial.{u1, u3} σ R _inst_1)), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u3, u1} R σ _inst_1 (Finset.sum.{max u3 u1, u2} (MvPolynomial.{u1, u3} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1))))) s (fun (i : ι) => f i))) (Finset.sup.{u1, u2} (Multiset.{u1} σ) ι (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} σ) (Multiset.instLatticeMultiset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} σ) s (fun (i : ι) => MvPolynomial.degrees.{u3, u1} R σ _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_sum MvPolynomial.degrees_sumₓ'. -/
theorem degrees_sum {ι : Type _} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∑ i in s, f i).degrees ≤ s.sup fun i => (f i).degrees := by
  classical
    refine' s.induction _ _
    · simp only [Finset.sum_empty, Finset.sup_empty, degrees_zero]
      exact le_rfl
    · intro i s his ih
      rw [Finset.sup_insert, Finset.sum_insert his]
      exact le_trans (degrees_add _ _) (sup_le_sup_left ih _)
#align mv_polynomial.degrees_sum MvPolynomial.degrees_sum

/- warning: mv_polynomial.degrees_mul -> MvPolynomial.degrees_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u2, u1} σ R _inst_1) (q : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (HAdd.hAdd.{u2, u2, u2} (Multiset.{u2} σ) (Multiset.{u2} σ) (Multiset.{u2} σ) (instHAdd.{u2} (Multiset.{u2} σ) (Multiset.hasAdd.{u2} σ)) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 q))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1) (q : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) p q)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} σ) (Multiset.{u1} σ) (Multiset.{u1} σ) (instHAdd.{u1} (Multiset.{u1} σ) (Multiset.instAddMultiset.{u1} σ)) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 q))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_mul MvPolynomial.degrees_mulₓ'. -/
theorem degrees_mul (p q : MvPolynomial σ R) : (p * q).degrees ≤ p.degrees + q.degrees := by
  classical
    refine' Finset.sup_le fun b hb => _
    have := support_mul p q hb
    simp only [Finset.mem_biUnion, Finset.mem_singleton] at this
    rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩
    rw [Finsupp.toMultiset_add]
    exact add_le_add (Finset.le_sup h₁) (Finset.le_sup h₂)
#align mv_polynomial.degrees_mul MvPolynomial.degrees_mul

/- warning: mv_polynomial.degrees_prod -> MvPolynomial.degrees_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (Finset.prod.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) s (fun (i : ι) => f i))) (Finset.sum.{u2, u3} (Multiset.{u2} σ) ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)) s (fun (i : ι) => MvPolynomial.degrees.{u1, u2} R σ _inst_1 (f i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (MvPolynomial.{u1, u3} σ R _inst_1)), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u3, u1} R σ _inst_1 (Finset.prod.{max u3 u1, u2} (MvPolynomial.{u1, u3} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} (Multiset.{u1} σ) ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)) s (fun (i : ι) => MvPolynomial.degrees.{u3, u1} R σ _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_prod MvPolynomial.degrees_prodₓ'. -/
theorem degrees_prod {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∏ i in s, f i).degrees ≤ ∑ i in s, (f i).degrees := by
  classical
    refine' s.induction _ _
    · simp only [Finset.prod_empty, Finset.sum_empty, degrees_one]
    · intro i s his ih
      rw [Finset.prod_insert his, Finset.sum_insert his]
      exact le_trans (degrees_mul _ _) (add_le_add_left ih _)
#align mv_polynomial.degrees_prod MvPolynomial.degrees_prod

/- warning: mv_polynomial.degrees_pow -> MvPolynomial.degrees_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u2, u1} σ R _inst_1) (n : Nat), LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.{u2, u1} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) p n)) (SMul.smul.{0, u2} Nat (Multiset.{u2} σ) (AddMonoid.SMul.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) n (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1) (n : Nat), LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.{u1, u2} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) p n)) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} σ) (Multiset.{u1} σ) (instHSMul.{0, u1} Nat (Multiset.{u1} σ) (AddMonoid.SMul.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ))))))) n (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_pow MvPolynomial.degrees_powₓ'. -/
theorem degrees_pow (p : MvPolynomial σ R) : ∀ n : ℕ, (p ^ n).degrees ≤ n • p.degrees
  | 0 => by rw [pow_zero, degrees_one]; exact Multiset.zero_le _
  | n + 1 => by
    rw [pow_succ, add_smul, add_comm, one_smul]
    exact le_trans (degrees_mul _ _) (add_le_add_left (degrees_pow n) _)
#align mv_polynomial.degrees_pow MvPolynomial.degrees_pow

/- warning: mv_polynomial.mem_degrees -> MvPolynomial.mem_degrees is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} {i : σ}, Iff (Membership.Mem.{u2, u2} σ (Multiset.{u2} σ) (Multiset.hasMem.{u2} σ) i (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p)) (Exists.{succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (d : Finsupp.{u2, 0} σ Nat Nat.hasZero) => And (Ne.{succ u1} R (MvPolynomial.coeff.{u1, u2} R σ _inst_1 d p) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) (Membership.Mem.{u2, u2} σ (Finset.{u2} σ) (Finset.hasMem.{u2} σ) i (Finsupp.support.{u2, 0} σ Nat Nat.hasZero d))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} {i : σ}, Iff (Membership.mem.{u1, u1} σ (Multiset.{u1} σ) (Multiset.instMembershipMultiset.{u1} σ) i (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p)) (Exists.{succ u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (d : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => And (Ne.{succ u2} R (MvPolynomial.coeff.{u2, u1} R σ _inst_1 d p) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))) (Membership.mem.{u1, u1} σ (Finset.{u1} σ) (Finset.instMembershipFinset.{u1} σ) i (Finsupp.support.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) d))))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.mem_degrees MvPolynomial.mem_degreesₓ'. -/
theorem mem_degrees {p : MvPolynomial σ R} {i : σ} :
    i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support := by
  simp only [degrees, Multiset.mem_sup, ← mem_support_iff, Finsupp.mem_toMultiset, exists_prop]
#align mv_polynomial.mem_degrees MvPolynomial.mem_degrees

/- warning: mv_polynomial.le_degrees_add -> MvPolynomial.le_degrees_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} {q : MvPolynomial.{u2, u1} σ R _inst_1}, (Multiset.Disjoint.{u2} σ (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 q)) -> (LE.le.{u2} (Multiset.{u2} σ) (Preorder.toHasLe.{u2} (Multiset.{u2} σ) (PartialOrder.toPreorder.{u2} (Multiset.{u2} σ) (Multiset.partialOrder.{u2} σ))) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} {q : MvPolynomial.{u1, u2} σ R _inst_1}, (Multiset.Disjoint.{u1} σ (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 q)) -> (LE.le.{u1} (Multiset.{u1} σ) (Preorder.toLE.{u1} (Multiset.{u1} σ) (PartialOrder.toPreorder.{u1} (Multiset.{u1} σ) (Multiset.instPartialOrderMultiset.{u1} σ))) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.le_degrees_add MvPolynomial.le_degrees_addₓ'. -/
theorem le_degrees_add {p q : MvPolynomial σ R} (h : p.degrees.Disjoint q.degrees) :
    p.degrees ≤ (p + q).degrees := by
  classical
    apply Finset.sup_le
    intro d hd
    rw [Multiset.disjoint_iff_ne] at h
    rw [Multiset.le_iff_count]
    intro i
    rw [degrees, Multiset.count_finset_sup]
    simp only [Finsupp.count_toMultiset]
    by_cases h0 : d = 0
    · simp only [h0, zero_le, Finsupp.zero_apply]
    · refine' @Finset.le_sup _ _ _ _ (p + q).support _ d _
      rw [mem_support_iff, coeff_add]
      suffices q.coeff d = 0 by rwa [this, add_zero, coeff, ← Finsupp.mem_support_iff]
      rw [← Finsupp.support_eq_empty, ← Ne.def, ← Finset.nonempty_iff_ne_empty] at h0
      obtain ⟨j, hj⟩ := h0
      contrapose! h
      rw [mem_support_iff] at hd
      refine' ⟨j, _, j, _, rfl⟩
      all_goals rw [mem_degrees]; refine' ⟨d, _, hj⟩; assumption
#align mv_polynomial.le_degrees_add MvPolynomial.le_degrees_add

/- warning: mv_polynomial.degrees_add_of_disjoint -> MvPolynomial.degrees_add_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] {p : MvPolynomial.{u2, u1} σ R _inst_1} {q : MvPolynomial.{u2, u1} σ R _inst_1}, (Multiset.Disjoint.{u2} σ (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 q)) -> (Eq.{succ u2} (Multiset.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (Union.union.{u2} (Multiset.{u2} σ) (Multiset.hasUnion.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 q)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] {p : MvPolynomial.{u1, u2} σ R _inst_1} {q : MvPolynomial.{u1, u2} σ R _inst_1}, (Multiset.Disjoint.{u1} σ (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 q)) -> (Eq.{succ u1} (Multiset.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)) (Union.union.{u1} (Multiset.{u1} σ) (Multiset.instUnionMultiset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_add_of_disjoint MvPolynomial.degrees_add_of_disjointₓ'. -/
theorem degrees_add_of_disjoint [DecidableEq σ] {p q : MvPolynomial σ R}
    (h : Multiset.Disjoint p.degrees q.degrees) : (p + q).degrees = p.degrees ∪ q.degrees :=
  by
  apply le_antisymm
  · apply degrees_add
  · apply Multiset.union_le
    · apply le_degrees_add h
    · rw [add_comm]
      apply le_degrees_add h.symm
#align mv_polynomial.degrees_add_of_disjoint MvPolynomial.degrees_add_of_disjoint

/- warning: mv_polynomial.degrees_map -> MvPolynomial.degrees_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {σ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommSemiring.{u2} S] (p : MvPolynomial.{u3, u1} σ R _inst_1) (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))), HasSubset.Subset.{u3} (Multiset.{u3} σ) (Multiset.hasSubset.{u3} σ) (MvPolynomial.degrees.{u2, u3} S σ _inst_2 (coeFn.{max (succ (max u3 u1)) (succ (max u3 u2)), max (succ (max u3 u1)) (succ (max u3 u2))} (RingHom.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) (fun (_x : RingHom.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) => (MvPolynomial.{u3, u1} σ R _inst_1) -> (MvPolynomial.{u3, u2} σ S _inst_2)) (RingHom.hasCoeToFun.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) (MvPolynomial.map.{u1, u2, u3} R S σ _inst_1 _inst_2 f) p)) (MvPolynomial.degrees.{u1, u3} R σ _inst_1 p)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : CommSemiring.{u3} S] (p : MvPolynomial.{u1, u2} σ R _inst_1) (f : RingHom.{u2, u3} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2))), HasSubset.Subset.{u1} (Multiset.{u1} σ) (Multiset.instHasSubsetMultiset.{u1} σ) (MvPolynomial.degrees.{u3, u1} S σ _inst_2 (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (succ u2) (succ u1), max (succ u3) (succ u1)} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (fun (_x : MvPolynomial.{u1, u2} σ R _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : MvPolynomial.{u1, u2} σ R _inst_1) => MvPolynomial.{u1, u3} σ S _inst_2) _x) (MulHomClass.toFunLike.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))) (RingHom.instRingHomClassRingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))))))) (MvPolynomial.map.{u2, u3, u1} R S σ _inst_1 _inst_2 f) p)) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_map MvPolynomial.degrees_mapₓ'. -/
theorem degrees_map [CommSemiring S] (p : MvPolynomial σ R) (f : R →+* S) :
    (map f p).degrees ⊆ p.degrees := by
  dsimp only [degrees]
  apply Multiset.subset_of_le
  apply Finset.sup_mono
  apply MvPolynomial.support_map_subset
#align mv_polynomial.degrees_map MvPolynomial.degrees_map

/- warning: mv_polynomial.degrees_rename -> MvPolynomial.degrees_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_rename MvPolynomial.degrees_renameₓ'. -/
theorem degrees_rename (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).degrees ⊆ φ.degrees.map f := by
  classical
    intro i
    rw [mem_degrees, Multiset.mem_map]
    rintro ⟨d, hd, hi⟩
    obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ hd
    simp only [map_domain, Finsupp.mem_support_iff] at hi
    rw [sum_apply, Finsupp.sum] at hi
    contrapose! hi
    rw [Finset.sum_eq_zero]
    intro j hj
    simp only [exists_prop, mem_degrees] at hi
    specialize hi j ⟨x, hx, hj⟩
    rw [single_apply, if_neg hi]
#align mv_polynomial.degrees_rename MvPolynomial.degrees_rename

/- warning: mv_polynomial.degrees_map_of_injective -> MvPolynomial.degrees_map_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_map_of_injective MvPolynomial.degrees_map_of_injectiveₓ'. -/
theorem degrees_map_of_injective [CommSemiring S] (p : MvPolynomial σ R) {f : R →+* S}
    (hf : Injective f) : (map f p).degrees = p.degrees := by
  simp only [degrees, MvPolynomial.support_map_of_injective _ hf]
#align mv_polynomial.degrees_map_of_injective MvPolynomial.degrees_map_of_injective

/- warning: mv_polynomial.degrees_rename_of_injective -> MvPolynomial.degrees_rename_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degrees_rename_of_injective MvPolynomial.degrees_rename_of_injectiveₓ'. -/
theorem degrees_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f) :
    degrees (rename f p) = (degrees p).map f := by
  classical
    simp only [degrees, Multiset.map_finset_sup p.support Finsupp.toMultiset f h,
      support_rename_of_injective h, Finset.sup_image]
    refine' Finset.sup_congr rfl fun x hx => _
    exact (Finsupp.toMultiset_map _ _).symm
#align mv_polynomial.degrees_rename_of_injective MvPolynomial.degrees_rename_of_injective

end Degrees

section Vars

/-! ### `vars` -/


#print MvPolynomial.vars /-
/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : MvPolynomial σ R) : Finset σ :=
  letI := Classical.decEq σ
  p.degrees.to_finset
#align mv_polynomial.vars MvPolynomial.vars
-/

/- warning: mv_polynomial.vars_def -> MvPolynomial.vars_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (p : MvPolynomial.{u2, u1} σ R _inst_1), Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 p) (Multiset.toFinset.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (p : MvPolynomial.{u1, u2} σ R _inst_1), Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p) (Multiset.toFinset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_def MvPolynomial.vars_defₓ'. -/
theorem vars_def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFinset := by
  convert rfl
#align mv_polynomial.vars_def MvPolynomial.vars_def

/- warning: mv_polynomial.vars_0 -> MvPolynomial.vars_0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (Zero.zero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MulZeroClass.toHasZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} σ) (Finset.hasEmptyc.{u2} σ))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommMonoidWithZero.toZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toCommMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} σ) (Finset.instEmptyCollectionFinset.{u1} σ))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_0 MvPolynomial.vars_0ₓ'. -/
@[simp]
theorem vars_0 : (0 : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]
#align mv_polynomial.vars_0 MvPolynomial.vars_0

/- warning: mv_polynomial.vars_monomial -> MvPolynomial.vars_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} {r : R} {s : Finsupp.{u2, 0} σ Nat Nat.hasZero} [_inst_1 : CommSemiring.{u1} R], (Ne.{succ u1} R r (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) -> (Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R R (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MvPolynomial.monomial.{u1, u2} R σ _inst_1 s) r)) (Finsupp.support.{u2, 0} σ Nat Nat.hasZero s))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} {r : R} {s : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)} [_inst_1 : CommSemiring.{u2} R], (Ne.{succ u2} R r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))) -> (Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (LinearMap.{u2, u2, u2, max u2 u1} R R (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u1 u2} R R R (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MvPolynomial.monomial.{u2, u1} R σ _inst_1 s) r)) (Finsupp.support.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) s))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_monomial MvPolynomial.vars_monomialₓ'. -/
@[simp]
theorem vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support := by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]
#align mv_polynomial.vars_monomial MvPolynomial.vars_monomial

/- warning: mv_polynomial.vars_C -> MvPolynomial.vars_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} {r : R} [_inst_1 : CommSemiring.{u1} R], Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (fun (_x : RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (RingHom.hasCoeToFun.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (MvPolynomial.C.{u1, u2} R σ _inst_1) r)) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} σ) (Finset.hasEmptyc.{u2} σ))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} {r : R} [_inst_1 : CommSemiring.{u2} R], Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) (MvPolynomial.C.{u2, u1} R σ _inst_1) r)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} σ) (Finset.instEmptyCollectionFinset.{u1} σ))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_C MvPolynomial.vars_Cₓ'. -/
@[simp]
theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]
#align mv_polynomial.vars_C MvPolynomial.vars_C

/- warning: mv_polynomial.vars_X -> MvPolynomial.vars_X is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} {n : σ} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (MvPolynomial.X.{u1, u2} R σ _inst_1 n)) (Singleton.singleton.{u2, u2} σ (Finset.{u2} σ) (Finset.hasSingleton.{u2} σ) n)
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} {n : σ} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R], Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (MvPolynomial.X.{u2, u1} R σ _inst_1 n)) (Singleton.singleton.{u1, u1} σ (Finset.{u1} σ) (Finset.instSingletonFinset.{u1} σ) n)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_X MvPolynomial.vars_Xₓ'. -/
@[simp]
theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} := by
  rw [X, vars_monomial (one_ne_zero' R), Finsupp.support_single_ne_zero _ (one_ne_zero' ℕ)]
#align mv_polynomial.vars_X MvPolynomial.vars_X

/- warning: mv_polynomial.mem_vars -> MvPolynomial.mem_vars is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} (i : σ), Iff (Membership.Mem.{u2, u2} σ (Finset.{u2} σ) (Finset.hasMem.{u2} σ) i (MvPolynomial.vars.{u1, u2} R σ _inst_1 p)) (Exists.{succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (d : Finsupp.{u2, 0} σ Nat Nat.hasZero) => Exists.{0} (Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) d (MvPolynomial.support.{u1, u2} R σ _inst_1 p)) (fun (H : Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) d (MvPolynomial.support.{u1, u2} R σ _inst_1 p)) => Membership.Mem.{u2, u2} σ (Finset.{u2} σ) (Finset.hasMem.{u2} σ) i (Finsupp.support.{u2, 0} σ Nat Nat.hasZero d))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} (i : σ), Iff (Membership.mem.{u1, u1} σ (Finset.{u1} σ) (Finset.instMembershipFinset.{u1} σ) i (MvPolynomial.vars.{u2, u1} R σ _inst_1 p)) (Exists.{succ u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (d : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => Exists.{0} (Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) d (MvPolynomial.support.{u2, u1} R σ _inst_1 p)) (fun (H : Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) d (MvPolynomial.support.{u2, u1} R σ _inst_1 p)) => Membership.mem.{u1, u1} σ (Finset.{u1} σ) (Finset.instMembershipFinset.{u1} σ) i (Finsupp.support.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) d))))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.mem_vars MvPolynomial.mem_varsₓ'. -/
theorem mem_vars (i : σ) : i ∈ p.vars ↔ ∃ (d : σ →₀ ℕ)(H : d ∈ p.support), i ∈ d.support := by
  simp only [vars, Multiset.mem_toFinset, mem_degrees, mem_support_iff, exists_prop]
#align mv_polynomial.mem_vars MvPolynomial.mem_vars

/- warning: mv_polynomial.mem_support_not_mem_vars_zero -> MvPolynomial.mem_support_not_mem_vars_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {f : MvPolynomial.{u2, u1} σ R _inst_1} {x : Finsupp.{u2, 0} σ Nat Nat.hasZero}, (Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) x (MvPolynomial.support.{u1, u2} R σ _inst_1 f)) -> (forall {v : σ}, (Not (Membership.Mem.{u2, u2} σ (Finset.{u2} σ) (Finset.hasMem.{u2} σ) v (MvPolynomial.vars.{u1, u2} R σ _inst_1 f))) -> (Eq.{1} Nat (coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) x v) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {f : MvPolynomial.{u1, u2} σ R _inst_1} {x : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)}, (Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) x (MvPolynomial.support.{u2, u1} R σ _inst_1 f)) -> (forall {v : σ}, (Not (Membership.mem.{u1, u1} σ (Finset.{u1} σ) (Finset.instMembershipFinset.{u1} σ) v (MvPolynomial.vars.{u2, u1} R σ _inst_1 f))) -> (Eq.{1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) v) (FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) x v) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) v) 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.mem_support_not_mem_vars_zero MvPolynomial.mem_support_not_mem_vars_zeroₓ'. -/
theorem mem_support_not_mem_vars_zero {f : MvPolynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support)
    {v : σ} (h : v ∉ vars f) : x v = 0 :=
  by
  letI := Classical.decEq σ
  rw [vars_def, Multiset.mem_toFinset] at h
  rw [← Finsupp.not_mem_support_iff]
  contrapose! h
  rw [degrees_def]
  rw [show f.support = insert x f.support from Eq.symm <| Finset.insert_eq_of_mem H]
  rw [Finset.sup_insert]
  simp only [Multiset.mem_union, Multiset.sup_eq_union]
  left
  rwa [← to_finset_to_multiset, Multiset.mem_toFinset] at h
#align mv_polynomial.mem_support_not_mem_vars_zero MvPolynomial.mem_support_not_mem_vars_zero

/- warning: mv_polynomial.vars_add_subset -> MvPolynomial.vars_add_subset is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (p : MvPolynomial.{u2, u1} σ R _inst_1) (q : MvPolynomial.{u2, u1} σ R _inst_1), HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.hasSubset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (Union.union.{u2} (Finset.{u2} σ) (Finset.hasUnion.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u1, u2} R σ _inst_1 p) (MvPolynomial.vars.{u1, u2} R σ _inst_1 q))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (p : MvPolynomial.{u1, u2} σ R _inst_1) (q : MvPolynomial.{u1, u2} σ R _inst_1), HasSubset.Subset.{u1} (Finset.{u1} σ) (Finset.instHasSubsetFinset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)) (Union.union.{u1} (Finset.{u1} σ) (Finset.instUnionFinset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p) (MvPolynomial.vars.{u2, u1} R σ _inst_1 q))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_add_subset MvPolynomial.vars_add_subsetₓ'. -/
theorem vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) : (p + q).vars ⊆ p.vars ∪ q.vars :=
  by
  intro x hx
  simp only [vars, Finset.mem_union, Multiset.mem_toFinset] at hx⊢
  simpa using Multiset.mem_of_le (degrees_add _ _) hx
#align mv_polynomial.vars_add_subset MvPolynomial.vars_add_subset

/- warning: mv_polynomial.vars_add_of_disjoint -> MvPolynomial.vars_add_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} {q : MvPolynomial.{u2, u1} σ R _inst_1} [_inst_2 : DecidableEq.{succ u2} σ], (Disjoint.{u2} (Finset.{u2} σ) (Finset.partialOrder.{u2} σ) (Finset.orderBot.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 p) (MvPolynomial.vars.{u1, u2} R σ _inst_1 q)) -> (Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (Union.union.{u2} (Finset.{u2} σ) (Finset.hasUnion.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u1, u2} R σ _inst_1 p) (MvPolynomial.vars.{u1, u2} R σ _inst_1 q)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} {q : MvPolynomial.{u1, u2} σ R _inst_1} [_inst_2 : DecidableEq.{succ u1} σ], (Disjoint.{u1} (Finset.{u1} σ) (Finset.partialOrder.{u1} σ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p) (MvPolynomial.vars.{u2, u1} R σ _inst_1 q)) -> (Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)) (Union.union.{u1} (Finset.{u1} σ) (Finset.instUnionFinset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p) (MvPolynomial.vars.{u2, u1} R σ _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_add_of_disjoint MvPolynomial.vars_add_of_disjointₓ'. -/
theorem vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) :
    (p + q).vars = p.vars ∪ q.vars :=
  by
  apply Finset.Subset.antisymm (vars_add_subset p q)
  intro x hx
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx⊢
  rw [degrees_add_of_disjoint h, Multiset.toFinset_union]
  exact hx
#align mv_polynomial.vars_add_of_disjoint MvPolynomial.vars_add_of_disjoint

section Mul

/- warning: mv_polynomial.vars_mul -> MvPolynomial.vars_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (φ : MvPolynomial.{u2, u1} σ R _inst_1) (ψ : MvPolynomial.{u2, u1} σ R _inst_1), HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.hasSubset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) φ ψ)) (Union.union.{u2} (Finset.{u2} σ) (Finset.hasUnion.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u1, u2} R σ _inst_1 φ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 ψ))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (φ : MvPolynomial.{u1, u2} σ R _inst_1) (ψ : MvPolynomial.{u1, u2} σ R _inst_1), HasSubset.Subset.{u1} (Finset.{u1} σ) (Finset.instHasSubsetFinset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) φ ψ)) (Union.union.{u1} (Finset.{u1} σ) (Finset.instUnionFinset.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b)) (MvPolynomial.vars.{u2, u1} R σ _inst_1 φ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 ψ))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_mul MvPolynomial.vars_mulₓ'. -/
theorem vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R) : (φ * ψ).vars ⊆ φ.vars ∪ ψ.vars :=
  by
  intro i
  simp only [mem_vars, Finset.mem_union]
  rintro ⟨d, hd, hi⟩
  rw [mem_support_iff, coeff_mul] at hd
  contrapose! hd
  cases hd
  rw [Finset.sum_eq_zero]
  rintro ⟨d₁, d₂⟩ H
  rw [Finsupp.mem_antidiagonal] at H
  subst H
  obtain H | H : i ∈ d₁.support ∨ i ∈ d₂.support := by
    simpa only [Finset.mem_union] using Finsupp.support_add hi
  · suffices coeff d₁ φ = 0 by simp [this]
    rw [coeff, ← Finsupp.not_mem_support_iff]
    intro
    solve_by_elim
  · suffices coeff d₂ ψ = 0 by simp [this]
    rw [coeff, ← Finsupp.not_mem_support_iff]
    intro
    solve_by_elim
#align mv_polynomial.vars_mul MvPolynomial.vars_mul

/- warning: mv_polynomial.vars_one -> MvPolynomial.vars_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (One.one.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddMonoidWithOne.toOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toAddCommMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} σ) (Finset.hasEmptyc.{u2} σ))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 1 (One.toOfNat1.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toOne.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} σ) (Finset.instEmptyCollectionFinset.{u1} σ))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_one MvPolynomial.vars_oneₓ'. -/
@[simp]
theorem vars_one : (1 : MvPolynomial σ R).vars = ∅ :=
  vars_C
#align mv_polynomial.vars_one MvPolynomial.vars_one

/- warning: mv_polynomial.vars_pow -> MvPolynomial.vars_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (φ : MvPolynomial.{u2, u1} σ R _inst_1) (n : Nat), HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.hasSubset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.{u2, u1} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) φ n)) (MvPolynomial.vars.{u1, u2} R σ _inst_1 φ)
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (φ : MvPolynomial.{u1, u2} σ R _inst_1) (n : Nat), HasSubset.Subset.{u1} (Finset.{u1} σ) (Finset.instHasSubsetFinset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.{u1, u2} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) φ n)) (MvPolynomial.vars.{u2, u1} R σ _inst_1 φ)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_pow MvPolynomial.vars_powₓ'. -/
theorem vars_pow (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars := by
  classical
    simp_rw [vars_def]
    induction' n with n ih
    · simp
    · rw [pow_succ]
      apply Finset.Subset.trans (vars_mul _ _)
      exact Finset.union_subset (Finset.Subset.refl _) ih
#align mv_polynomial.vars_pow MvPolynomial.vars_pow

/- warning: mv_polynomial.vars_prod -> MvPolynomial.vars_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} [_inst_2 : DecidableEq.{succ u2} σ] {s : Finset.{u3} ι} (f : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)), HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.hasSubset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (Finset.prod.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) s (fun (i : ι) => f i))) (Finset.biUnion.{u3, u2} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) s (fun (i : ι) => MvPolynomial.vars.{u1, u2} R σ _inst_1 (f i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} σ] {s : Finset.{u2} ι} (f : ι -> (MvPolynomial.{u1, u3} σ R _inst_1)), HasSubset.Subset.{u1} (Finset.{u1} σ) (Finset.instHasSubsetFinset.{u1} σ) (MvPolynomial.vars.{u3, u1} R σ _inst_1 (Finset.prod.{max u3 u1, u2} (MvPolynomial.{u1, u3} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) s (fun (i : ι) => f i))) (Finset.biUnion.{u2, u1} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) s (fun (i : ι) => MvPolynomial.vars.{u3, u1} R σ _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_prod MvPolynomial.vars_prodₓ'. -/
/-- The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
theorem vars_prod {ι : Type _} [DecidableEq σ] {s : Finset ι} (f : ι → MvPolynomial σ R) :
    (∏ i in s, f i).vars ⊆ s.biUnion fun i => (f i).vars := by
  classical
    apply s.induction_on
    · simp
    · intro a s hs hsub
      simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
      apply Finset.Subset.trans (vars_mul _ _)
      exact Finset.union_subset_union (Finset.Subset.refl _) hsub
#align mv_polynomial.vars_prod MvPolynomial.vars_prod

section IsDomain

variable {A : Type _} [CommRing A] [IsDomain A]

/- warning: mv_polynomial.vars_C_mul -> MvPolynomial.vars_C_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_C_mul MvPolynomial.vars_C_mulₓ'. -/
theorem vars_C_mul (a : A) (ha : a ≠ 0) (φ : MvPolynomial σ A) : (C a * φ).vars = φ.vars :=
  by
  ext1 i
  simp only [mem_vars, exists_prop, mem_support_iff]
  apply exists_congr
  intro d
  apply and_congr _ Iff.rfl
  rw [coeff_C_mul, mul_ne_zero_iff, eq_true ha, true_and_iff]
#align mv_polynomial.vars_C_mul MvPolynomial.vars_C_mul

end IsDomain

end Mul

section Sum

variable {ι : Type _} (t : Finset ι) (φ : ι → MvPolynomial σ R)

/- warning: mv_polynomial.vars_sum_subset -> MvPolynomial.vars_sum_subset is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} (t : Finset.{u3} ι) (φ : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)) [_inst_2 : DecidableEq.{succ u2} σ], HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.hasSubset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (Finset.sum.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) t (fun (i : ι) => φ i))) (Finset.biUnion.{u3, u2} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) t (fun (i : ι) => MvPolynomial.vars.{u1, u2} R σ _inst_1 (φ i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u1}} (t : Finset.{u1} ι) (φ : ι -> (MvPolynomial.{u2, u3} σ R _inst_1)) [_inst_2 : DecidableEq.{succ u2} σ], HasSubset.Subset.{u2} (Finset.{u2} σ) (Finset.instHasSubsetFinset.{u2} σ) (MvPolynomial.vars.{u3, u2} R σ _inst_1 (Finset.sum.{max u3 u2, u1} (MvPolynomial.{u2, u3} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u2} R σ _inst_1))))) t (fun (i : ι) => φ i))) (Finset.biUnion.{u1, u2} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) t (fun (i : ι) => MvPolynomial.vars.{u3, u2} R σ _inst_1 (φ i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_sum_subset MvPolynomial.vars_sum_subsetₓ'. -/
theorem vars_sum_subset [DecidableEq σ] :
    (∑ i in t, φ i).vars ⊆ Finset.biUnion t fun i => (φ i).vars := by
  classical
    apply t.induction_on
    · simp
    · intro a s has hsum
      rw [Finset.biUnion_insert, Finset.sum_insert has]
      refine'
        Finset.Subset.trans (vars_add_subset _ _)
          (Finset.union_subset_union (Finset.Subset.refl _) _)
      assumption
#align mv_polynomial.vars_sum_subset MvPolynomial.vars_sum_subset

/- warning: mv_polynomial.vars_sum_of_disjoint -> MvPolynomial.vars_sum_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} (t : Finset.{u3} ι) (φ : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)) [_inst_2 : DecidableEq.{succ u2} σ], (Pairwise.{u3} ι (Function.onFun.{succ u3, succ u2, 1} ι (Finset.{u2} σ) Prop (Disjoint.{u2} (Finset.{u2} σ) (Finset.partialOrder.{u2} σ) (Finset.orderBot.{u2} σ)) (fun (i : ι) => MvPolynomial.vars.{u1, u2} R σ _inst_1 (φ i)))) -> (Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (Finset.sum.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) t (fun (i : ι) => φ i))) (Finset.biUnion.{u3, u2} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) t (fun (i : ι) => MvPolynomial.vars.{u1, u2} R σ _inst_1 (φ i))))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u1}} (t : Finset.{u1} ι) (φ : ι -> (MvPolynomial.{u2, u3} σ R _inst_1)) [_inst_2 : DecidableEq.{succ u2} σ], (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Finset.{u2} σ) Prop (Disjoint.{u2} (Finset.{u2} σ) (Finset.partialOrder.{u2} σ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} σ)) (fun (i : ι) => MvPolynomial.vars.{u3, u2} R σ _inst_1 (φ i)))) -> (Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u3, u2} R σ _inst_1 (Finset.sum.{max u3 u2, u1} (MvPolynomial.{u2, u3} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u2, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u2} R σ _inst_1))))) t (fun (i : ι) => φ i))) (Finset.biUnion.{u1, u2} ι σ (fun (a : σ) (b : σ) => _inst_2 a b) t (fun (i : ι) => MvPolynomial.vars.{u3, u2} R σ _inst_1 (φ i))))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_sum_of_disjoint MvPolynomial.vars_sum_of_disjointₓ'. -/
theorem vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars)) :
    (∑ i in t, φ i).vars = Finset.biUnion t fun i => (φ i).vars := by
  classical
    apply t.induction_on
    · simp
    · intro a s has hsum
      rw [Finset.biUnion_insert, Finset.sum_insert has, vars_add_of_disjoint, hsum]
      unfold Pairwise on_fun at h
      rw [hsum]
      simp only [Finset.disjoint_iff_ne] at h⊢
      intro v hv v2 hv2
      rw [Finset.mem_biUnion] at hv2
      rcases hv2 with ⟨i, his, hi⟩
      refine' h _ _ hv _ hi
      rintro rfl
      contradiction
#align mv_polynomial.vars_sum_of_disjoint MvPolynomial.vars_sum_of_disjoint

end Sum

section Map

variable [CommSemiring S] (f : R →+* S)

variable (p)

/- warning: mv_polynomial.vars_map -> MvPolynomial.vars_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {σ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u3, u1} σ R _inst_1) [_inst_2 : CommSemiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))), HasSubset.Subset.{u3} (Finset.{u3} σ) (Finset.hasSubset.{u3} σ) (MvPolynomial.vars.{u2, u3} S σ _inst_2 (coeFn.{max (succ (max u3 u1)) (succ (max u3 u2)), max (succ (max u3 u1)) (succ (max u3 u2))} (RingHom.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) (fun (_x : RingHom.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) => (MvPolynomial.{u3, u1} σ R _inst_1) -> (MvPolynomial.{u3, u2} σ S _inst_2)) (RingHom.hasCoeToFun.{max u3 u1, max u3 u2} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))) (MvPolynomial.map.{u1, u2, u3} R S σ _inst_1 _inst_2 f) p)) (MvPolynomial.vars.{u1, u3} R σ _inst_1 p)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1) [_inst_2 : CommSemiring.{u3} S] (f : RingHom.{u2, u3} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2))), HasSubset.Subset.{u1} (Finset.{u1} σ) (Finset.instHasSubsetFinset.{u1} σ) (MvPolynomial.vars.{u3, u1} S σ _inst_2 (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), max (succ u2) (succ u1), max (succ u3) (succ u1)} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (fun (_x : MvPolynomial.{u1, u2} σ R _inst_1) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : MvPolynomial.{u1, u2} σ R _inst_1) => MvPolynomial.{u1, u3} σ S _inst_2) _x) (MulHomClass.toFunLike.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u2 u3) u1, max u2 u1, max u3 u1} (RingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2)))) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))) (RingHom.instRingHomClassRingHom.{max u2 u1, max u3 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u3} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))))))) (MvPolynomial.map.{u2, u3, u1} R S σ _inst_1 _inst_2 f) p)) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_map MvPolynomial.vars_mapₓ'. -/
theorem vars_map : (map f p).vars ⊆ p.vars := by simp [vars, degrees_map]
#align mv_polynomial.vars_map MvPolynomial.vars_map

variable {f}

/- warning: mv_polynomial.vars_map_of_injective -> MvPolynomial.vars_map_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_map_of_injective MvPolynomial.vars_map_of_injectiveₓ'. -/
theorem vars_map_of_injective (hf : Injective f) : (map f p).vars = p.vars := by
  simp [vars, degrees_map_of_injective _ hf]
#align mv_polynomial.vars_map_of_injective MvPolynomial.vars_map_of_injective

/- warning: mv_polynomial.vars_monomial_single -> MvPolynomial.vars_monomial_single is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (i : σ) {e : Nat} {r : R}, (Ne.{1} Nat e (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{succ u1} R r (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) -> (Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R R (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MvPolynomial.monomial.{u1, u2} R σ _inst_1 (Finsupp.single.{u2, 0} σ Nat Nat.hasZero i e)) r)) (Singleton.singleton.{u2, u2} σ (Finset.{u2} σ) (Finset.hasSingleton.{u2} σ) i))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (i : σ) {e : Nat} {r : R}, (Ne.{1} Nat e (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{succ u2} R r (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))) -> (Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (LinearMap.{u2, u2, u2, max u2 u1} R R (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u1 u2} R R R (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MvPolynomial.monomial.{u2, u1} R σ _inst_1 (Finsupp.single.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) i e)) r)) (Singleton.singleton.{u1, u1} σ (Finset.{u1} σ) (Finset.instSingletonFinset.{u1} σ) i))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_monomial_single MvPolynomial.vars_monomial_singleₓ'. -/
theorem vars_monomial_single (i : σ) {e : ℕ} {r : R} (he : e ≠ 0) (hr : r ≠ 0) :
    (monomial (Finsupp.single i e) r).vars = {i} := by
  rw [vars_monomial hr, Finsupp.support_single_ne_zero _ he]
#align mv_polynomial.vars_monomial_single MvPolynomial.vars_monomial_single

/- warning: mv_polynomial.vars_eq_support_bUnion_support -> MvPolynomial.vars_eq_support_biUnion_support is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u2, u1} σ R _inst_1) [_inst_3 : DecidableEq.{succ u2} σ], Eq.{succ u2} (Finset.{u2} σ) (MvPolynomial.vars.{u1, u2} R σ _inst_1 p) (Finset.biUnion.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) σ (fun (a : σ) (b : σ) => _inst_3 a b) (MvPolynomial.support.{u1, u2} R σ _inst_1 p) (Finsupp.support.{u2, 0} σ Nat Nat.hasZero))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1) [_inst_3 : DecidableEq.{succ u1} σ], Eq.{succ u1} (Finset.{u1} σ) (MvPolynomial.vars.{u2, u1} R σ _inst_1 p) (Finset.biUnion.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (a : σ) (b : σ) => _inst_3 a b) (MvPolynomial.support.{u2, u1} R σ _inst_1 p) (Finsupp.support.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_eq_support_bUnion_support MvPolynomial.vars_eq_support_biUnion_supportₓ'. -/
theorem vars_eq_support_biUnion_support [DecidableEq σ] :
    p.vars = p.support.biUnion Finsupp.support :=
  by
  ext i
  rw [mem_vars, Finset.mem_biUnion]
#align mv_polynomial.vars_eq_support_bUnion_support MvPolynomial.vars_eq_support_biUnion_support

end Map

end Vars

section DegreeOf

/-! ### `degree_of` -/


#print MvPolynomial.degreeOf /-
/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degreeOf (n : σ) (p : MvPolynomial σ R) : ℕ :=
  letI := Classical.decEq σ
  p.degrees.count n
#align mv_polynomial.degree_of MvPolynomial.degreeOf
-/

/- warning: mv_polynomial.degree_of_def -> MvPolynomial.degreeOf_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (n : σ) (p : MvPolynomial.{u2, u1} σ R _inst_1), Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n p) (Multiset.count.{u2} σ (fun (a : σ) (b : σ) => _inst_2 a b) n (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (n : σ) (p : MvPolynomial.{u1, u2} σ R _inst_1), Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n p) (Multiset.count.{u1} σ (fun (a : σ) (b : σ) => _inst_2 a b) n (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_def MvPolynomial.degreeOf_defₓ'. -/
theorem degreeOf_def [DecidableEq σ] (n : σ) (p : MvPolynomial σ R) :
    p.degreeOf n = p.degrees.count n := by convert rfl
#align mv_polynomial.degree_of_def MvPolynomial.degreeOf_def

/- warning: mv_polynomial.degree_of_eq_sup -> MvPolynomial.degreeOf_eq_sup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (n : σ) (f : MvPolynomial.{u2, u1} σ R _inst_1), Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n f) (Finset.sup.{0, u2} Nat (Finsupp.{u2, 0} σ Nat Nat.hasZero) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) Nat.orderBot (MvPolynomial.support.{u1, u2} R σ _inst_1 f) (fun (m : Finsupp.{u2, 0} σ Nat Nat.hasZero) => coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) m n))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (n : σ) (f : MvPolynomial.{u1, u2} σ R _inst_1), Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n f) (Finset.sup.{0, u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) n) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Lattice.toSemilatticeSup.{0} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) n) Nat.instLatticeNat) Nat.orderBot (MvPolynomial.support.{u2, u1} R σ _inst_1 f) (fun (m : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) m n))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_eq_sup MvPolynomial.degreeOf_eq_supₓ'. -/
theorem degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) :
    degreeOf n f = f.support.sup fun m => m n := by
  classical
    rw [degree_of_def, degrees_def, Multiset.count_finset_sup]
    congr
    ext
    simp
#align mv_polynomial.degree_of_eq_sup MvPolynomial.degreeOf_eq_sup

/- warning: mv_polynomial.degree_of_lt_iff -> MvPolynomial.degreeOf_lt_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {n : σ} {f : MvPolynomial.{u2, u1} σ R _inst_1} {d : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) d) -> (Iff (LT.lt.{0} Nat Nat.hasLt (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n f) d) (forall (m : Finsupp.{u2, 0} σ Nat Nat.hasZero), (Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) m (MvPolynomial.support.{u1, u2} R σ _inst_1 f)) -> (LT.lt.{0} Nat Nat.hasLt (coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) m n) d)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {n : σ} {f : MvPolynomial.{u1, u2} σ R _inst_1} {d : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) d) -> (Iff (LT.lt.{0} Nat instLTNat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n f) d) (forall (m : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)), (Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) m (MvPolynomial.support.{u2, u1} R σ _inst_1 f)) -> (LT.lt.{0} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) n) instLTNat (FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) m n) d)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_lt_iff MvPolynomial.degreeOf_lt_iffₓ'. -/
theorem degreeOf_lt_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} (h : 0 < d) :
    degreeOf n f < d ↔ ∀ m : σ →₀ ℕ, m ∈ f.support → m n < d := by
  rwa [degree_of_eq_sup n f, Finset.sup_lt_iff]
#align mv_polynomial.degree_of_lt_iff MvPolynomial.degreeOf_lt_iff

/- warning: mv_polynomial.degree_of_zero -> MvPolynomial.degreeOf_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (n : σ), Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (Zero.zero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MulZeroClass.toHasZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (n : σ), Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommMonoidWithZero.toZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toCommMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_zero MvPolynomial.degreeOf_zeroₓ'. -/
@[simp]
theorem degreeOf_zero (n : σ) : degreeOf n (0 : MvPolynomial σ R) = 0 := by
  simp only [degree_of, degrees_zero, Multiset.count_zero]
#align mv_polynomial.degree_of_zero MvPolynomial.degreeOf_zero

/- warning: mv_polynomial.degree_of_C -> MvPolynomial.degreeOf_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : R) (x : σ), Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 x (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (fun (_x : RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (RingHom.hasCoeToFun.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (MvPolynomial.C.{u1, u2} R σ _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : R) (x : σ), Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 x (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) (MvPolynomial.C.{u2, u1} R σ _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_C MvPolynomial.degreeOf_Cₓ'. -/
@[simp]
theorem degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0 := by
  simp [degree_of, degrees_C]
#align mv_polynomial.degree_of_C MvPolynomial.degreeOf_C

/- warning: mv_polynomial.degree_of_X -> MvPolynomial.degreeOf_X is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : DecidableEq.{succ u2} σ] (i : σ) (j : σ) [_inst_3 : Nontrivial.{u1} R], Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i (MvPolynomial.X.{u1, u2} R σ _inst_1 j)) (ite.{1} Nat (Eq.{succ u2} σ i j) (_inst_2 i j) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : DecidableEq.{succ u1} σ] (i : σ) (j : σ) [_inst_3 : Nontrivial.{u2} R], Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i (MvPolynomial.X.{u2, u1} R σ _inst_1 j)) (ite.{1} Nat (Eq.{succ u1} σ i j) (_inst_2 i j) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_X MvPolynomial.degreeOf_Xₓ'. -/
theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0 :=
  by
  by_cases c : i = j
  · simp only [c, if_true, eq_self_iff_true, degree_of, degrees_X, Multiset.count_singleton]
  simp [c, if_false, degree_of, degrees_X]
#align mv_polynomial.degree_of_X MvPolynomial.degreeOf_X

/- warning: mv_polynomial.degree_of_add_le -> MvPolynomial.degreeOf_add_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (n : σ) (f : MvPolynomial.{u2, u1} σ R _inst_1) (g : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) f g)) (LinearOrder.max.{0} Nat Nat.linearOrder (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n f) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 n g))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (n : σ) (f : MvPolynomial.{u1, u2} σ R _inst_1) (g : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) f g)) (Max.max.{0} Nat Nat.instMaxNat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n f) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 n g))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_add_le MvPolynomial.degreeOf_add_leₓ'. -/
theorem degreeOf_add_le (n : σ) (f g : MvPolynomial σ R) :
    degreeOf n (f + g) ≤ max (degreeOf n f) (degreeOf n g) := by
  classical
    repeat' rw [degree_of_def]
    apply (Multiset.count_le_of_le n (degrees_add f g)).trans
    dsimp
    rw [Multiset.count_union]
#align mv_polynomial.degree_of_add_le MvPolynomial.degreeOf_add_le

/- warning: mv_polynomial.monomial_le_degree_of -> MvPolynomial.monomial_le_degreeOf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (i : σ) {f : MvPolynomial.{u2, u1} σ R _inst_1} {m : Finsupp.{u2, 0} σ Nat Nat.hasZero}, (Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) m (MvPolynomial.support.{u1, u2} R σ _inst_1 f)) -> (LE.le.{0} Nat Nat.hasLe (coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) m i) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i f))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (i : σ) {f : MvPolynomial.{u1, u2} σ R _inst_1} {m : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)}, (Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) m (MvPolynomial.support.{u2, u1} R σ _inst_1 f)) -> (LE.le.{0} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) i) instLENat (FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) m i) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i f))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.monomial_le_degree_of MvPolynomial.monomial_le_degreeOfₓ'. -/
theorem monomial_le_degreeOf (i : σ) {f : MvPolynomial σ R} {m : σ →₀ ℕ} (h_m : m ∈ f.support) :
    m i ≤ degreeOf i f := by
  rw [degree_of_eq_sup i]
  apply Finset.le_sup h_m
#align mv_polynomial.monomial_le_degree_of MvPolynomial.monomial_le_degreeOf

/- warning: mv_polynomial.degree_of_mul_le -> MvPolynomial.degreeOf_mul_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (i : σ) (f : MvPolynomial.{u2, u1} σ R _inst_1) (g : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) f g)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i f) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i g))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (i : σ) (f : MvPolynomial.{u1, u2} σ R _inst_1) (g : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) f g)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i f) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i g))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_mul_le MvPolynomial.degreeOf_mul_leₓ'. -/
-- TODO we can prove equality here if R is a domain
theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) ≤ degreeOf i f + degreeOf i g := by
  classical
    repeat' rw [degree_of_def]
    convert Multiset.count_le_of_le i (degrees_mul f g)
    rw [Multiset.count_add]
#align mv_polynomial.degree_of_mul_le MvPolynomial.degreeOf_mul_le

/- warning: mv_polynomial.degree_of_mul_X_ne -> MvPolynomial.degreeOf_mul_X_ne is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {i : σ} {j : σ} (f : MvPolynomial.{u2, u1} σ R _inst_1), (Ne.{succ u2} σ i j) -> (Eq.{1} Nat (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) f (MvPolynomial.X.{u1, u2} R σ _inst_1 j))) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 i f))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {i : σ} {j : σ} (f : MvPolynomial.{u1, u2} σ R _inst_1), (Ne.{succ u1} σ i j) -> (Eq.{1} Nat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i (HMul.hMul.{max u2 u1, max u1 u2, max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) f (MvPolynomial.X.{u2, u1} R σ _inst_1 j))) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 i f))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_mul_X_ne MvPolynomial.degreeOf_mul_X_neₓ'. -/
theorem degreeOf_mul_X_ne {i j : σ} (f : MvPolynomial σ R) (h : i ≠ j) :
    degreeOf i (f * X j) = degreeOf i f := by
  classical
    repeat' rw [degree_of_eq_sup i]
    rw [support_mul_X]
    simp only [Finset.sup_map]
    congr
    ext
    simp only [single, Nat.one_ne_zero, add_right_eq_self, addRightEmbedding_apply, coe_mk,
      Pi.add_apply, comp_app, ite_eq_right_iff, Finsupp.coe_add, Pi.single_eq_of_ne h]
#align mv_polynomial.degree_of_mul_X_ne MvPolynomial.degreeOf_mul_X_ne

/- warning: mv_polynomial.degree_of_mul_X_eq -> MvPolynomial.degreeOf_mul_X_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (j : σ) (f : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 j (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) f (MvPolynomial.X.{u1, u2} R σ _inst_1 j))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (MvPolynomial.degreeOf.{u1, u2} R σ _inst_1 j f) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (j : σ) (f : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 j (HMul.hMul.{max u2 u1, max u1 u2, max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) f (MvPolynomial.X.{u2, u1} R σ _inst_1 j))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (MvPolynomial.degreeOf.{u2, u1} R σ _inst_1 j f) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_mul_X_eq MvPolynomial.degreeOf_mul_X_eqₓ'. -/
-- TODO in the following we have equality iff f ≠ 0
theorem degreeOf_mul_X_eq (j : σ) (f : MvPolynomial σ R) :
    degreeOf j (f * X j) ≤ degreeOf j f + 1 := by
  classical
    repeat' rw [degree_of_def]
    apply (Multiset.count_le_of_le j (degrees_mul f (X j))).trans
    simp only [Multiset.count_add, add_le_add_iff_left]
    convert Multiset.count_le_of_le j (degrees_X' j)
    rw [Multiset.count_singleton_self]
#align mv_polynomial.degree_of_mul_X_eq MvPolynomial.degreeOf_mul_X_eq

/- warning: mv_polynomial.degree_of_rename_of_injective -> MvPolynomial.degreeOf_rename_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.degree_of_rename_of_injective MvPolynomial.degreeOf_rename_of_injectiveₓ'. -/
theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f)
    (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p := by
  classical simp only [degree_of_def, degrees_rename_of_injective h,
      Multiset.count_map_eq_count' f p.degrees h]
#align mv_polynomial.degree_of_rename_of_injective MvPolynomial.degreeOf_rename_of_injective

end DegreeOf

section TotalDegree

/-! ### `total_degree` -/


#print MvPolynomial.totalDegree /-
/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def totalDegree (p : MvPolynomial σ R) : ℕ :=
  p.support.sup fun s => s.Sum fun n e => e
#align mv_polynomial.total_degree MvPolynomial.totalDegree
-/

/- warning: mv_polynomial.total_degree_eq -> MvPolynomial.totalDegree_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u2, u1} σ R _inst_1), Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p) (Finset.sup.{0, u2} Nat (Finsupp.{u2, 0} σ Nat Nat.hasZero) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) Nat.orderBot (MvPolynomial.support.{u1, u2} R σ _inst_1 p) (fun (m : Finsupp.{u2, 0} σ Nat Nat.hasZero) => coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} σ) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} σ) (coeFn.{succ u2, succ u2} (AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (fun (_x : AddEquiv.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) => (Finsupp.{u2, 0} σ Nat Nat.hasZero) -> (Multiset.{u2} σ)) (AddEquiv.hasCoeToFun.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Multiset.{u2} σ) (Finsupp.add.{u2, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.hasAdd.{u2} σ)) (Finsupp.toMultiset.{u2} σ) m)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1), Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p) (Finset.sup.{0, u1} Nat (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) Nat.orderBot (MvPolynomial.support.{u2, u1} R σ _inst_1 p) (fun (m : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) (fun (_x : Multiset.{u1} σ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} σ) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} σ) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} σ) (FunLike.coe.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (_x : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) => Multiset.{u1} σ) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (AddEquivClass.toEquivLike.{u1, u1, u1} (AddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ)) (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ) (AddEquiv.instAddEquivClassAddEquiv.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Multiset.{u1} σ) (Finsupp.add.{u1, 0} σ Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.instAddMultiset.{u1} σ))))) (Finsupp.toMultiset.{u1} σ) m)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_eq MvPolynomial.totalDegree_eqₓ'. -/
theorem totalDegree_eq (p : MvPolynomial σ R) :
    p.totalDegree = p.support.sup fun m => m.toMultiset.card :=
  by
  rw [total_degree]
  congr ; funext m
  exact (Finsupp.card_toMultiset _).symm
#align mv_polynomial.total_degree_eq MvPolynomial.totalDegree_eq

/- warning: mv_polynomial.total_degree_le_degrees_card -> MvPolynomial.totalDegree_le_degrees_card is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (p : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p) (coeFn.{succ u2, succ u2} (AddMonoidHom.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u2} σ) -> Nat) (AddMonoidHom.hasCoeToFun.{u2, 0} (Multiset.{u2} σ) Nat (AddMonoid.toAddZeroClass.{u2} (Multiset.{u2} σ) (AddRightCancelMonoid.toAddMonoid.{u2} (Multiset.{u2} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u2} (Multiset.{u2} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u2} (Multiset.{u2} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u2} (Multiset.{u2} σ) (Multiset.orderedCancelAddCommMonoid.{u2} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u2} σ) (MvPolynomial.degrees.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (p : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) (fun (_x : Multiset.{u1} σ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} σ) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} σ) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} σ) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} σ) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} σ) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} σ) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} σ) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} σ) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} σ)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} σ) (MvPolynomial.degrees.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_le_degrees_card MvPolynomial.totalDegree_le_degrees_cardₓ'. -/
theorem totalDegree_le_degrees_card (p : MvPolynomial σ R) : p.totalDegree ≤ p.degrees.card := by
  classical
    rw [total_degree_eq]
    exact Finset.sup_le fun s hs => Multiset.card_le_of_le <| Finset.le_sup hs
#align mv_polynomial.total_degree_le_degrees_card MvPolynomial.totalDegree_le_degrees_card

/- warning: mv_polynomial.total_degree_C -> MvPolynomial.totalDegree_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : R), Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (fun (_x : RingHom.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (RingHom.hasCoeToFun.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))) (MvPolynomial.C.{u1, u2} R σ _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : R), Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u2, max u1 u2} (RingHom.{u2, max u2 u1} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))) R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) (RingHom.instRingHomClassRingHom.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) (MvPolynomial.C.{u2, u1} R σ _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_C MvPolynomial.totalDegree_Cₓ'. -/
@[simp]
theorem totalDegree_C (a : R) : (C a : MvPolynomial σ R).totalDegree = 0 :=
  Nat.eq_zero_of_le_zero <|
    Finset.sup_le fun n hn => by
      have := Finsupp.support_single_subset hn
      rw [Finset.mem_singleton] at this
      subst this
      exact le_rfl
#align mv_polynomial.total_degree_C MvPolynomial.totalDegree_C

/- warning: mv_polynomial.total_degree_zero -> MvPolynomial.totalDegree_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 0 (Zero.zero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MulZeroClass.toHasZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommMonoidWithZero.toZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toCommMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_zero MvPolynomial.totalDegree_zeroₓ'. -/
@[simp]
theorem totalDegree_zero : (0 : MvPolynomial σ R).totalDegree = 0 := by
  rw [← C_0] <;> exact total_degree_C (0 : R)
#align mv_polynomial.total_degree_zero MvPolynomial.totalDegree_zero

/- warning: mv_polynomial.total_degree_one -> MvPolynomial.totalDegree_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R], Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (OfNat.mk.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) 1 (One.one.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddMonoidWithOne.toOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toAddCommMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R], Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (OfNat.ofNat.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) 1 (One.toOfNat1.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toOne.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_one MvPolynomial.totalDegree_oneₓ'. -/
@[simp]
theorem totalDegree_one : (1 : MvPolynomial σ R).totalDegree = 0 :=
  totalDegree_C (1 : R)
#align mv_polynomial.total_degree_one MvPolynomial.totalDegree_one

#print MvPolynomial.totalDegree_X /-
@[simp]
theorem totalDegree_X {R} [CommSemiring R] [Nontrivial R] (s : σ) :
    (X s : MvPolynomial σ R).totalDegree = 1 :=
  by
  rw [total_degree, support_X]
  simp only [Finset.sup, sum_single_index, Finset.fold_singleton, sup_bot_eq]
#align mv_polynomial.total_degree_X MvPolynomial.totalDegree_X
-/

/- warning: mv_polynomial.total_degree_add -> MvPolynomial.totalDegree_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : MvPolynomial.{u2, u1} σ R _inst_1) (b : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) a b)) (LinearOrder.max.{0} Nat Nat.linearOrder (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 a) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 b))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : MvPolynomial.{u1, u2} σ R _inst_1) (b : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) a b)) (Max.max.{0} Nat Nat.instMaxNat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 a) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 b))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_add MvPolynomial.totalDegree_addₓ'. -/
theorem totalDegree_add (a b : MvPolynomial σ R) :
    (a + b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  Finset.sup_le fun n hn => by
    classical
      have := Finsupp.support_add hn
      rw [Finset.mem_union] at this
      cases this
      · exact le_max_of_le_left (Finset.le_sup this)
      · exact le_max_of_le_right (Finset.le_sup this)
#align mv_polynomial.total_degree_add MvPolynomial.totalDegree_add

/- warning: mv_polynomial.total_degree_add_eq_left_of_total_degree_lt -> MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} {q : MvPolynomial.{u2, u1} σ R _inst_1}, (LT.lt.{0} Nat Nat.hasLt (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 q) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p)) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) p q)) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} {q : MvPolynomial.{u1, u2} σ R _inst_1}, (LT.lt.{0} Nat instLTNat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 q) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p)) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) p q)) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_add_eq_left_of_total_degree_lt MvPolynomial.totalDegree_add_eq_left_of_totalDegree_ltₓ'. -/
theorem totalDegree_add_eq_left_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (p + q).totalDegree = p.totalDegree := by
  classical
    apply le_antisymm
    · rw [← max_eq_left_of_lt h]
      exact total_degree_add p q
    by_cases hp : p = 0
    · simp [hp]
    obtain ⟨b, hb₁, hb₂⟩ :=
      p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp) fun m : σ →₀ ℕ =>
        m.to_multiset.card
    have hb : ¬b ∈ q.support := by
      contrapose! h
      rw [total_degree_eq p, hb₂, total_degree_eq]
      apply Finset.le_sup h
    have hbb : b ∈ (p + q).support :=
      by
      apply support_sdiff_support_subset_support_add
      rw [Finset.mem_sdiff]
      exact ⟨hb₁, hb⟩
    rw [total_degree_eq, hb₂, total_degree_eq]
    exact Finset.le_sup hbb
#align mv_polynomial.total_degree_add_eq_left_of_total_degree_lt MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt

/- warning: mv_polynomial.total_degree_add_eq_right_of_total_degree_lt -> MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {p : MvPolynomial.{u2, u1} σ R _inst_1} {q : MvPolynomial.{u2, u1} σ R _inst_1}, (LT.lt.{0} Nat Nat.hasLt (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 q) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p)) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasAdd.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) q p)) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {p : MvPolynomial.{u1, u2} σ R _inst_1} {q : MvPolynomial.{u1, u2} σ R _inst_1}, (LT.lt.{0} Nat instLTNat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 q) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p)) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Distrib.toAdd.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))))) q p)) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 p))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_add_eq_right_of_total_degree_lt MvPolynomial.totalDegree_add_eq_right_of_totalDegree_ltₓ'. -/
theorem totalDegree_add_eq_right_of_totalDegree_lt {p q : MvPolynomial σ R}
    (h : q.totalDegree < p.totalDegree) : (q + p).totalDegree = p.totalDegree := by
  rw [add_comm, total_degree_add_eq_left_of_total_degree_lt h]
#align mv_polynomial.total_degree_add_eq_right_of_total_degree_lt MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt

/- warning: mv_polynomial.total_degree_mul -> MvPolynomial.totalDegree_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : MvPolynomial.{u2, u1} σ R _inst_1) (b : MvPolynomial.{u2, u1} σ R _inst_1), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))))) a b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 a) (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 b))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : MvPolynomial.{u1, u2} σ R _inst_1) (b : MvPolynomial.{u1, u2} σ R _inst_1), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) (instHMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) a b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 a) (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 b))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_mul MvPolynomial.totalDegree_mulₓ'. -/
theorem totalDegree_mul (a b : MvPolynomial σ R) :
    (a * b).totalDegree ≤ a.totalDegree + b.totalDegree :=
  Finset.sup_le fun n hn => by
    classical
      have := AddMonoidAlgebra.support_mul a b hn
      simp only [Finset.mem_biUnion, Finset.mem_singleton] at this
      rcases this with ⟨a₁, h₁, a₂, h₂, rfl⟩
      rw [Finsupp.sum_add_index']
      · exact add_le_add (Finset.le_sup h₁) (Finset.le_sup h₂)
      · intro a
        rfl
      · intro a b₁ b₂
        rfl
#align mv_polynomial.total_degree_mul MvPolynomial.totalDegree_mul

/- warning: mv_polynomial.total_degree_smul_le -> MvPolynomial.totalDegree_smul_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {σ : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommSemiring.{u2} S] [_inst_3 : DistribMulAction.{u1, u2} R S (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))] (a : R) (f : MvPolynomial.{u3, u2} σ S _inst_2), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u2, u3} S σ _inst_2 (SMul.smul.{u1, max u3 u2} R (MvPolynomial.{u3, u2} σ S _inst_2) (SMulZeroClass.toHasSmul.{u1, max u3 u2} R (MvPolynomial.{u3, u2} σ S _inst_2) (MulZeroClass.toHasZero.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (Semiring.toNonAssocSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ S _inst_2) (MvPolynomial.commSemiring.{u2, u3} S σ _inst_2)))))) (MvPolynomial.smulZeroClass.{u1, u2, u3} R S σ _inst_2 (DistribSMul.toSmulZeroClass.{u1, u2} R S (AddMonoid.toAddZeroClass.{u2} S (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (DistribMulAction.toDistribSMul.{u1, u2} R S (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (AddMonoidWithOne.toAddMonoid.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) _inst_3)))) a f)) (MvPolynomial.totalDegree.{u2, u3} S σ _inst_2 f)
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : CommSemiring.{u3} S] [_inst_3 : DistribMulAction.{u2, u3} R S (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (AddMonoidWithOne.toAddMonoid.{u3} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} S (NonAssocSemiring.toAddCommMonoidWithOne.{u3} S (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)))))] (a : R) (f : MvPolynomial.{u1, u3} σ S _inst_2), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u3, u1} S σ _inst_2 (HSMul.hSMul.{u2, max u3 u1, max u3 u1} R (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.{u1, u3} σ S _inst_2) (instHSMul.{u2, max u3 u1} R (MvPolynomial.{u1, u3} σ S _inst_2) (SMulZeroClass.toSMul.{u2, max u3 u1} R (MvPolynomial.{u1, u3} σ S _inst_2) (CommMonoidWithZero.toZero.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (CommSemiring.toCommMonoidWithZero.{max u3 u1} (MvPolynomial.{u1, u3} σ S _inst_2) (MvPolynomial.commSemiring.{u3, u1} S σ _inst_2))) (MvPolynomial.smulZeroClass.{u2, u3, u1} R S σ _inst_2 (DistribSMul.toSMulZeroClass.{u2, u3} R S (AddMonoid.toAddZeroClass.{u3} S (AddMonoidWithOne.toAddMonoid.{u3} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} S (NonAssocSemiring.toAddCommMonoidWithOne.{u3} S (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)))))) (DistribMulAction.toDistribSMul.{u2, u3} R S (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (AddMonoidWithOne.toAddMonoid.{u3} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} S (NonAssocSemiring.toAddCommMonoidWithOne.{u3} S (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2))))) _inst_3))))) a f)) (MvPolynomial.totalDegree.{u3, u1} S σ _inst_2 f)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_smul_le MvPolynomial.totalDegree_smul_leₓ'. -/
theorem totalDegree_smul_le [CommSemiring S] [DistribMulAction R S] (a : R) (f : MvPolynomial σ S) :
    (a • f).totalDegree ≤ f.totalDegree :=
  Finset.sup_mono support_smul
#align mv_polynomial.total_degree_smul_le MvPolynomial.totalDegree_smul_le

/- warning: mv_polynomial.total_degree_pow -> MvPolynomial.totalDegree_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (a : MvPolynomial.{u2, u1} σ R _inst_1) (n : Nat), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.{u2, u1} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) a n)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 a))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (a : MvPolynomial.{u1, u2} σ R _inst_1) (n : Nat), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.{u1, u2} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) a n)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 a))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_pow MvPolynomial.totalDegree_powₓ'. -/
theorem totalDegree_pow (a : MvPolynomial σ R) (n : ℕ) : (a ^ n).totalDegree ≤ n * a.totalDegree :=
  by
  induction' n with n ih
  · simp only [Nat.zero_eq, MulZeroClass.zero_mul, pow_zero, total_degree_one]
  rw [pow_succ]
  calc
    total_degree (a * a ^ n) ≤ a.total_degree + (a ^ n).totalDegree := total_degree_mul _ _
    _ ≤ a.total_degree + n * a.total_degree := (add_le_add_left ih _)
    _ = (n + 1) * a.total_degree := by rw [add_mul, one_mul, add_comm]
    
#align mv_polynomial.total_degree_pow MvPolynomial.totalDegree_pow

/- warning: mv_polynomial.total_degree_monomial -> MvPolynomial.totalDegree_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (s : Finsupp.{u2, 0} σ Nat Nat.hasZero) {c : R}, (Ne.{succ u1} R c (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (coeFn.{max (succ u1) (succ (max u2 u1)), max (succ u1) (succ (max u2 u1))} (LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (fun (_x : LinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) R (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) => R -> (MvPolynomial.{u2, u1} σ R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, max u2 u1} R R R (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (MvPolynomial.module.{u1, u1, u2} R R σ (CommSemiring.toSemiring.{u1} R _inst_1) _inst_1 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MvPolynomial.monomial.{u1, u2} R σ _inst_1 s) c)) (Finsupp.sum.{u2, 0, 0} σ Nat Nat Nat.hasZero Nat.addCommMonoid s (fun (_x : σ) (e : Nat) => e)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (s : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) {c : R}, (Ne.{succ u2} R c (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1))))) -> (Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (LinearMap.{u2, u2, u2, max u2 u1} R R (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) R (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : R) => MvPolynomial.{u1, u2} σ R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u2, max u1 u2} R R R (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (MvPolynomial.module.{u2, u2, u1} R R σ (CommSemiring.toSemiring.{u2} R _inst_1) _inst_1 (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MvPolynomial.monomial.{u2, u1} R σ _inst_1 s) c)) (Finsupp.sum.{u1, 0, 0} σ Nat Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) Nat.addCommMonoid s (fun (_x : σ) (e : Nat) => e)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_monomial MvPolynomial.totalDegree_monomialₓ'. -/
@[simp]
theorem totalDegree_monomial (s : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    (monomial s c : MvPolynomial σ R).totalDegree = s.Sum fun _ e => e := by
  classical simp [total_degree, support_monomial, if_neg hc]
#align mv_polynomial.total_degree_monomial MvPolynomial.totalDegree_monomial

/- warning: mv_polynomial.total_degree_X_pow -> MvPolynomial.totalDegree_X_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] (s : σ) (n : Nat), Eq.{1} Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.{u2, u1} σ R _inst_1) (instHPow.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (Monoid.Pow.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MonoidWithZero.toMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toMonoidWithZero.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) (MvPolynomial.X.{u1, u2} R σ _inst_1 s) n)) n
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R] (s : σ) (n : Nat), Eq.{1} Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (HPow.hPow.{max u1 u2, 0, max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.{u1, u2} σ R _inst_1) (instHPow.{max u1 u2, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (Monoid.Pow.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MonoidWithZero.toMonoid.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toMonoidWithZero.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)))))) (MvPolynomial.X.{u2, u1} R σ _inst_1 s) n)) n
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_X_pow MvPolynomial.totalDegree_X_powₓ'. -/
@[simp]
theorem totalDegree_X_pow [Nontrivial R] (s : σ) (n : ℕ) :
    (X s ^ n : MvPolynomial σ R).totalDegree = n := by simp [X_pow_eq_monomial, one_ne_zero]
#align mv_polynomial.total_degree_X_pow MvPolynomial.totalDegree_X_pow

/- warning: mv_polynomial.total_degree_list_prod -> MvPolynomial.totalDegree_list_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (s : List.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (List.prod.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Distrib.toHasMul.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonUnitalNonAssocSemiring.toDistrib.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) (AddMonoidWithOne.toOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (AddCommMonoidWithOne.toAddMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toAddCommMonoidWithOne.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)))))) s)) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero (List.map.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1) s))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (s : List.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1)), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (List.prod.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonUnitalNonAssocSemiring.toMul.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))))) (Semiring.toOne.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1))) s)) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) (List.map.{max u1 u2, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1) s))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_list_prod MvPolynomial.totalDegree_list_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem totalDegree_list_prod :
    ∀ s : List (MvPolynomial σ R), s.Prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).Sum
  | [] => by rw [@List.prod_nil (MvPolynomial σ R) _, total_degree_one] <;> rfl
  | p::ps => by
    rw [@List.prod_cons (MvPolynomial σ R) _, List.map, List.sum_cons]
    exact le_trans (total_degree_mul _ _) (add_le_add_left (total_degree_list_prod ps) _)
#align mv_polynomial.total_degree_list_prod MvPolynomial.totalDegree_list_prod

/- warning: mv_polynomial.total_degree_multiset_prod -> MvPolynomial.totalDegree_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] (s : Multiset.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (Multiset.prod.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) s)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{max u2 u1, 0} (MvPolynomial.{u2, u1} σ R _inst_1) Nat (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1) s))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] (s : Multiset.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1)), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 (Multiset.prod.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (CommSemiring.toCommMonoid.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) s)) (Multiset.sum.{0} Nat Nat.addCommMonoid (Multiset.map.{max u1 u2, 0} (MvPolynomial.{u1, u2} σ R _inst_1) Nat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1) s))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_multiset_prod MvPolynomial.totalDegree_multiset_prodₓ'. -/
theorem totalDegree_multiset_prod (s : Multiset (MvPolynomial σ R)) :
    s.Prod.totalDegree ≤ (s.map MvPolynomial.totalDegree).Sum :=
  by
  refine' Quotient.inductionOn s fun l => _
  rw [Multiset.quot_mk_to_coe, Multiset.coe_prod, Multiset.coe_map, Multiset.coe_sum]
  exact total_degree_list_prod l
#align mv_polynomial.total_degree_multiset_prod MvPolynomial.totalDegree_multiset_prod

/- warning: mv_polynomial.total_degree_finset_prod -> MvPolynomial.totalDegree_finset_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (Finset.prod.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) s f)) (Finset.sum.{0, u3} Nat ι Nat.addCommMonoid s (fun (i : ι) => MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (f i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (MvPolynomial.{u1, u3} σ R _inst_1)), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u3, u1} R σ _inst_1 (Finset.prod.{max u3 u1, u2} (MvPolynomial.{u1, u3} σ R _inst_1) ι (CommSemiring.toCommMonoid.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) s f)) (Finset.sum.{0, u2} Nat ι Nat.addCommMonoid s (fun (i : ι) => MvPolynomial.totalDegree.{u3, u1} R σ _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_finset_prod MvPolynomial.totalDegree_finset_prodₓ'. -/
theorem totalDegree_finset_prod {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.Prod f).totalDegree ≤ ∑ i in s, (f i).totalDegree :=
  by
  refine' le_trans (total_degree_multiset_prod _) _
  rw [Multiset.map_map]
  rfl
#align mv_polynomial.total_degree_finset_prod MvPolynomial.totalDegree_finset_prod

/- warning: mv_polynomial.total_degree_finset_sum -> MvPolynomial.totalDegree_finset_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> (MvPolynomial.{u2, u1} σ R _inst_1)), LE.le.{0} Nat Nat.hasLe (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (Finset.sum.{max u2 u1, u3} (MvPolynomial.{u2, u1} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1))))) s f)) (Finset.sup.{0, u3} Nat ι (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) Nat.orderBot s (fun (i : ι) => MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 (f i)))
but is expected to have type
  forall {R : Type.{u3}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (MvPolynomial.{u1, u3} σ R _inst_1)), LE.le.{0} Nat instLENat (MvPolynomial.totalDegree.{u3, u1} R σ _inst_1 (Finset.sum.{max u3 u1, u2} (MvPolynomial.{u1, u3} σ R _inst_1) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (Semiring.toNonAssocSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1))))) s f)) (Finset.sup.{0, u2} Nat ι (Lattice.toSemilatticeSup.{0} Nat Nat.instLatticeNat) Nat.orderBot s (fun (i : ι) => MvPolynomial.totalDegree.{u3, u1} R σ _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_finset_sum MvPolynomial.totalDegree_finset_sumₓ'. -/
theorem totalDegree_finset_sum {ι : Type _} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.Sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree :=
  by
  induction' s using Finset.cons_induction with a s has hind
  · exact zero_le _
  · rw [Finset.sum_cons, Finset.sup_cons, sup_eq_max]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)
#align mv_polynomial.total_degree_finset_sum MvPolynomial.totalDegree_finset_sum

/- warning: mv_polynomial.exists_degree_lt -> MvPolynomial.exists_degree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Fintype.{u2} σ] (f : MvPolynomial.{u2, u1} σ R _inst_1) (n : Nat), (LT.lt.{0} Nat Nat.hasLt (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 f) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Fintype.card.{u2} σ _inst_2))) -> (forall {d : Finsupp.{u2, 0} σ Nat Nat.hasZero}, (Membership.Mem.{u2, u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (Finset.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) (Finset.hasMem.{u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero)) d (MvPolynomial.support.{u1, u2} R σ _inst_1 f)) -> (Exists.{succ u2} σ (fun (i : σ) => LT.lt.{0} Nat Nat.hasLt (coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) d i) n)))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Fintype.{u1} σ] (f : MvPolynomial.{u1, u2} σ R _inst_1) (n : Nat), (LT.lt.{0} Nat instLTNat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 f) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Fintype.card.{u1} σ _inst_2))) -> (forall {d : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)}, (Membership.mem.{u1, u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (Finset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Finset.instMembershipFinset.{u1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) d (MvPolynomial.support.{u2, u1} R σ _inst_1 f)) -> (Exists.{succ u1} σ (fun (i : σ) => LT.lt.{0} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) i) instLTNat (FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) d i) n)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.exists_degree_lt MvPolynomial.exists_degree_ltₓ'. -/
theorem exists_degree_lt [Fintype σ] (f : MvPolynomial σ R) (n : ℕ)
    (h : f.totalDegree < n * Fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) : ∃ i, d i < n :=
  by
  contrapose! h
  calc
    n * Fintype.card σ = ∑ s : σ, n := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm, Finset.card_univ]
    _ ≤ ∑ s, d s := (Finset.sum_le_sum fun s _ => h s)
    _ ≤ d.sum fun i e => e := by
      rw [Finsupp.sum_fintype]
      intros
      rfl
    _ ≤ f.total_degree := Finset.le_sup hd
    
#align mv_polynomial.exists_degree_lt MvPolynomial.exists_degree_lt

/- warning: mv_polynomial.coeff_eq_zero_of_total_degree_lt -> MvPolynomial.coeff_eq_zero_of_totalDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {σ : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {f : MvPolynomial.{u2, u1} σ R _inst_1} {d : Finsupp.{u2, 0} σ Nat Nat.hasZero}, (LT.lt.{0} Nat Nat.hasLt (MvPolynomial.totalDegree.{u1, u2} R σ _inst_1 f) (Finset.sum.{0, u2} Nat σ Nat.addCommMonoid (Finsupp.support.{u2, 0} σ Nat Nat.hasZero d) (fun (i : σ) => coeFn.{succ u2, succ u2} (Finsupp.{u2, 0} σ Nat Nat.hasZero) (fun (_x : Finsupp.{u2, 0} σ Nat Nat.hasZero) => σ -> Nat) (Finsupp.coeFun.{u2, 0} σ Nat Nat.hasZero) d i))) -> (Eq.{succ u1} R (MvPolynomial.coeff.{u1, u2} R σ _inst_1 d f) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u2}} {σ : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] {f : MvPolynomial.{u1, u2} σ R _inst_1} {d : Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)}, (LT.lt.{0} Nat instLTNat (MvPolynomial.totalDegree.{u2, u1} R σ _inst_1 f) (Finset.sum.{0, u1} Nat σ Nat.addCommMonoid (Finsupp.support.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) d) (fun (i : σ) => FunLike.coe.{succ u1, succ u1, 1} (Finsupp.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) σ (fun (_x : σ) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : σ) => Nat) _x) (Finsupp.funLike.{u1, 0} σ Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) d i))) -> (Eq.{succ u2} R (MvPolynomial.coeff.{u2, u1} R σ _inst_1 d f) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.coeff_eq_zero_of_total_degree_lt MvPolynomial.coeff_eq_zero_of_totalDegree_ltₓ'. -/
theorem coeff_eq_zero_of_totalDegree_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (h : f.totalDegree < ∑ i in d.support, d i) : coeff d f = 0 := by
  classical
    rw [total_degree, Finset.sup_lt_iff] at h
    · specialize h d
      rw [mem_support_iff] at h
      refine' not_not.mp (mt h _)
      exact lt_irrefl _
    · exact lt_of_le_of_lt (Nat.zero_le _) h
#align mv_polynomial.coeff_eq_zero_of_total_degree_lt MvPolynomial.coeff_eq_zero_of_totalDegree_lt

/- warning: mv_polynomial.total_degree_rename_le -> MvPolynomial.totalDegree_rename_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.total_degree_rename_le MvPolynomial.totalDegree_rename_leₓ'. -/
theorem totalDegree_rename_le (f : σ → τ) (p : MvPolynomial σ R) :
    (rename f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_le fun b => by
    intro h
    rw [rename_eq] at h
    classical
      have h' := Finsupp.mapDomain_support h
      rw [Finset.mem_image] at h'
      rcases h' with ⟨s, hs, rfl⟩
      rw [Finsupp.sum_mapDomain_index]
      exact le_trans le_rfl (Finset.le_sup hs)
      exact fun _ => rfl
      exact fun _ _ _ => rfl
#align mv_polynomial.total_degree_rename_le MvPolynomial.totalDegree_rename_le

end TotalDegree

section EvalVars

/-! ### `vars` and `eval` -/


variable [CommSemiring S]

/- warning: mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars -> MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars MvPolynomial.eval₂Hom_eq_constantCoeff_of_varsₓ'. -/
theorem eval₂Hom_eq_constantCoeff_of_vars (f : R →+* S) {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : eval₂Hom f g p = f (constantCoeff p) :=
  by
  conv_lhs => rw [p.as_sum]
  simp only [RingHom.map_sum, eval₂_hom_monomial]
  by_cases h0 : constant_coeff p = 0
  on_goal 1 =>
    rw [h0, f.map_zero, Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ →₀ ℕ)]
    · rw [Finsupp.prod_zero_index, mul_one]
      rfl
    intro d hd hd0
  repeat'
    obtain ⟨i, hi⟩ : d.support.nonempty :=
      by
      rw [constant_coeff_eq, coeff, ← Finsupp.not_mem_support_iff] at h0
      rw [Finset.nonempty_iff_ne_empty, Ne.def, Finsupp.support_eq_empty]
      rintro rfl
      contradiction
    rw [Finsupp.prod, Finset.prod_eq_zero hi, MulZeroClass.mul_zero]
    rw [hp, zero_pow (Nat.pos_of_ne_zero <| finsupp.mem_support_iff.mp hi)]
    rw [mem_vars]
    exact ⟨d, hd, hi⟩
  · rw [constant_coeff_eq, coeff, ← Ne.def, ← Finsupp.mem_support_iff] at h0
    intro
    contradiction
#align mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars

/- warning: mv_polynomial.aeval_eq_constant_coeff_of_vars -> MvPolynomial.aeval_eq_constantCoeff_of_vars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.aeval_eq_constant_coeff_of_vars MvPolynomial.aeval_eq_constantCoeff_of_varsₓ'. -/
theorem aeval_eq_constantCoeff_of_vars [Algebra R S] {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : aeval g p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_eq_constantCoeff_of_vars _ hp
#align mv_polynomial.aeval_eq_constant_coeff_of_vars MvPolynomial.aeval_eq_constantCoeff_of_vars

/- warning: mv_polynomial.eval₂_hom_congr' -> MvPolynomial.eval₂Hom_congr' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval₂_hom_congr' MvPolynomial.eval₂Hom_congr'ₓ'. -/
theorem eval₂Hom_congr' {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ →
      (∀ i, i ∈ p₁.vars → i ∈ p₂.vars → g₁ i = g₂ i) →
        p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ :=
  by
  rintro rfl h rfl
  rename' p₁ => p, f₁ => f
  rw [p.as_sum]
  simp only [RingHom.map_sum, eval₂_hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i ∈ p.vars := by
    rw [mem_vars]
    exact ⟨d, hd, hi⟩
  rw [h i this this]
#align mv_polynomial.eval₂_hom_congr' MvPolynomial.eval₂Hom_congr'

/- warning: mv_polynomial.hom_congr_vars -> MvPolynomial.hom_congr_vars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.hom_congr_vars MvPolynomial.hom_congr_varsₓ'. -/
/-- If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on the variables
  of `p₁`.  -/
theorem hom_congr_vars {f₁ f₂ : MvPolynomial σ R →+* S} {p₁ p₂ : MvPolynomial σ R}
    (hC : f₁.comp C = f₂.comp C) (hv : ∀ i, i ∈ p₁.vars → i ∈ p₂.vars → f₁ (X i) = f₂ (X i))
    (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
  calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := (eval₂Hom_congr' hC hv hp)
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _
    
#align mv_polynomial.hom_congr_vars MvPolynomial.hom_congr_vars

/- warning: mv_polynomial.exists_rename_eq_of_vars_subset_range -> MvPolynomial.exists_rename_eq_of_vars_subset_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.exists_rename_eq_of_vars_subset_range MvPolynomial.exists_rename_eq_of_vars_subset_rangeₓ'. -/
theorem exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ → σ) (hfi : Injective f)
    (hf : ↑p.vars ⊆ Set.range f) : ∃ q : MvPolynomial τ R, rename f q = p :=
  ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
    show (rename f).toRingHom.comp _ p = RingHom.id _ p
    refine' hom_congr_vars _ _ _
    · ext1
      simp [algebra_map_eq]
    · intro i hip _
      rcases hf hip with ⟨i, rfl⟩
      simp [partial_inv_left hfi]
    · rfl⟩
#align mv_polynomial.exists_rename_eq_of_vars_subset_range MvPolynomial.exists_rename_eq_of_vars_subset_range

/- warning: mv_polynomial.vars_rename -> MvPolynomial.vars_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.vars_rename MvPolynomial.vars_renameₓ'. -/
theorem vars_rename [DecidableEq τ] (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).vars ⊆ φ.vars.image f := by
  intro i hi
  simp only [vars, exists_prop, Multiset.mem_toFinset, Finset.mem_image] at hi⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi
#align mv_polynomial.vars_rename MvPolynomial.vars_rename

/- warning: mv_polynomial.mem_vars_rename -> MvPolynomial.mem_vars_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.mem_vars_rename MvPolynomial.mem_vars_renameₓ'. -/
theorem mem_vars_rename (f : σ → τ) (φ : MvPolynomial σ R) {j : τ} (h : j ∈ (rename f φ).vars) :
    ∃ i : σ, i ∈ φ.vars ∧ f i = j := by
  classical simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h
#align mv_polynomial.mem_vars_rename MvPolynomial.mem_vars_rename

end EvalVars

end CommSemiring

end MvPolynomial

