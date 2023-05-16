/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.polynomial.degree.trailing_degree
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Trailing degree of univariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/


noncomputable section

open Function Polynomial Finsupp Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

#print Polynomial.trailingDegree /-
/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailingDegree (p : R[X]) : ℕ∞ :=
  p.support.min
#align polynomial.trailing_degree Polynomial.trailingDegree
-/

/- warning: polynomial.trailing_degree_lt_wf -> Polynomial.trailingDegree_lt_wf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], WellFounded.{succ u1} (Polynomial.{u1} R _inst_1) (fun (p : Polynomial.{u1} R _inst_1) (q : Polynomial.{u1} R _inst_1) => LT.lt.{0} ENat (Preorder.toHasLt.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], WellFounded.{succ u1} (Polynomial.{u1} R _inst_1) (fun (p : Polynomial.{u1} R _inst_1) (q : Polynomial.{u1} R _inst_1) => LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_lt_wf Polynomial.trailingDegree_lt_wfₓ'. -/
theorem trailingDegree_lt_wf : WellFounded fun p q : R[X] => trailingDegree p < trailingDegree q :=
  InvImage.wf trailingDegree (WithTop.wellFounded_lt Nat.lt_wfRel)
#align polynomial.trailing_degree_lt_wf Polynomial.trailingDegree_lt_wf

#print Polynomial.natTrailingDegree /-
/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def natTrailingDegree (p : R[X]) : ℕ :=
  (trailingDegree p).getD 0
#align polynomial.nat_trailing_degree Polynomial.natTrailingDegree
-/

#print Polynomial.trailingCoeff /-
/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailingCoeff (p : R[X]) : R :=
  coeff p (natTrailingDegree p)
#align polynomial.trailing_coeff Polynomial.trailingCoeff
-/

#print Polynomial.TrailingMonic /-
/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def TrailingMonic (p : R[X]) :=
  trailingCoeff p = (1 : R)
#align polynomial.trailing_monic Polynomial.TrailingMonic
-/

#print Polynomial.TrailingMonic.def /-
theorem TrailingMonic.def : TrailingMonic p ↔ trailingCoeff p = 1 :=
  Iff.rfl
#align polynomial.trailing_monic.def Polynomial.TrailingMonic.def
-/

/- warning: polynomial.trailing_monic.decidable -> Polynomial.TrailingMonic.decidable is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} [_inst_2 : DecidableEq.{succ u1} R], Decidable (Polynomial.TrailingMonic.{u1} R _inst_1 p)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, Decidable (Polynomial.TrailingMonic.{u1} R _inst_1 p)
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_monic.decidable Polynomial.TrailingMonic.decidableₓ'. -/
instance TrailingMonic.decidable [DecidableEq R] : Decidable (TrailingMonic p) := by
  unfold trailing_monic <;> infer_instance
#align polynomial.trailing_monic.decidable Polynomial.TrailingMonic.decidable

#print Polynomial.TrailingMonic.trailingCoeff /-
@[simp]
theorem TrailingMonic.trailingCoeff {p : R[X]} (hp : p.TrailingMonic) : trailingCoeff p = 1 :=
  hp
#align polynomial.trailing_monic.trailing_coeff Polynomial.TrailingMonic.trailingCoeff
-/

#print Polynomial.trailingDegree_zero /-
@[simp]
theorem trailingDegree_zero : trailingDegree (0 : R[X]) = ⊤ :=
  rfl
#align polynomial.trailing_degree_zero Polynomial.trailingDegree_zero
-/

/- warning: polynomial.trailing_coeff_zero -> Polynomial.trailingCoeff_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Eq.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Eq.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_coeff_zero Polynomial.trailingCoeff_zeroₓ'. -/
@[simp]
theorem trailingCoeff_zero : trailingCoeff (0 : R[X]) = 0 :=
  rfl
#align polynomial.trailing_coeff_zero Polynomial.trailingCoeff_zero

#print Polynomial.natTrailingDegree_zero /-
@[simp]
theorem natTrailingDegree_zero : natTrailingDegree (0 : R[X]) = 0 :=
  rfl
#align polynomial.nat_trailing_degree_zero Polynomial.natTrailingDegree_zero
-/

#print Polynomial.trailingDegree_eq_top /-
theorem trailingDegree_eq_top : trailingDegree p = ⊤ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩
#align polynomial.trailing_degree_eq_top Polynomial.trailingDegree_eq_top
-/

#print Polynomial.trailingDegree_eq_natTrailingDegree /-
theorem trailingDegree_eq_natTrailingDegree (hp : p ≠ 0) :
    trailingDegree p = (natTrailingDegree p : ℕ∞) :=
  by
  let ⟨n, hn⟩ :=
    not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailingDegree_eq_top.1 hp))
  have hn : trailingDegree p = n := Classical.not_not.1 hn
  rw [nat_trailing_degree, hn] <;> rfl
#align polynomial.trailing_degree_eq_nat_trailing_degree Polynomial.trailingDegree_eq_natTrailingDegree
-/

#print Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq /-
theorem trailingDegree_eq_iff_natTrailingDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n := by
  rw [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_eq_coe]
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq
-/

#print Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos /-
theorem trailingDegree_eq_iff_natTrailingDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.trailingDegree = n ↔ p.natTrailingDegree = n :=
  by
  constructor
  · intro H
    rwa [← trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [trailing_degree_zero] at H
    exact Option.noConfusion H
  · intro H
    rwa [trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [nat_trailing_degree_zero] at H
    rw [H] at hn
    exact lt_irrefl _ hn
#align polynomial.trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos Polynomial.trailingDegree_eq_iff_natTrailingDegree_eq_of_pos
-/

#print Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some /-
theorem natTrailingDegree_eq_of_trailingDegree_eq_some {p : R[X]} {n : ℕ}
    (h : trailingDegree p = n) : natTrailingDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 <|
    show (natTrailingDegree p : ℕ∞) = n by rwa [← trailing_degree_eq_nat_trailing_degree hp0]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq_some Polynomial.natTrailingDegree_eq_of_trailingDegree_eq_some
-/

/- warning: polynomial.nat_trailing_degree_le_trailing_degree -> Polynomial.natTrailingDegree_le_trailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (Polynomial.trailingDegree.{u1} R _inst_1 p)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (Polynomial.trailingDegree.{u1} R _inst_1 p)
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_le_trailing_degree Polynomial.natTrailingDegree_le_trailingDegreeₓ'. -/
@[simp]
theorem natTrailingDegree_le_trailingDegree : ↑(natTrailingDegree p) ≤ trailingDegree p :=
  by
  by_cases hp : p = 0;
  · rw [hp, trailing_degree_zero]
    exact le_top
  rw [trailing_degree_eq_nat_trailing_degree hp]
  exact le_rfl
#align polynomial.nat_trailing_degree_le_trailing_degree Polynomial.natTrailingDegree_le_trailingDegree

#print Polynomial.natTrailingDegree_eq_of_trailingDegree_eq /-
theorem natTrailingDegree_eq_of_trailingDegree_eq [Semiring S] {q : S[X]}
    (h : trailingDegree p = trailingDegree q) : natTrailingDegree p = natTrailingDegree q := by
  unfold nat_trailing_degree <;> rw [h]
#align polynomial.nat_trailing_degree_eq_of_trailing_degree_eq Polynomial.natTrailingDegree_eq_of_trailingDegree_eq
-/

/- warning: polynomial.le_trailing_degree_of_ne_zero -> Polynomial.le_trailingDegree_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n))
but is expected to have type
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_of_ne_zero Polynomial.le_trailingDegree_of_ne_zeroₓ'. -/
theorem le_trailingDegree_of_ne_zero (h : coeff p n ≠ 0) : trailingDegree p ≤ n :=
  show @LE.le ℕ∞ _ p.support.min n from min_le (mem_support_iff.2 h)
#align polynomial.le_trailing_degree_of_ne_zero Polynomial.le_trailingDegree_of_ne_zero

/- warning: polynomial.nat_trailing_degree_le_of_ne_zero -> Polynomial.natTrailingDegree_le_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (LE.le.{0} Nat Nat.hasLe (Polynomial.natTrailingDegree.{u1} R _inst_1 p) n)
but is expected to have type
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (LE.le.{0} Nat instLENat (Polynomial.natTrailingDegree.{u1} R _inst_1 p) n)
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_le_of_ne_zero Polynomial.natTrailingDegree_le_of_ne_zeroₓ'. -/
theorem natTrailingDegree_le_of_ne_zero (h : coeff p n ≠ 0) : natTrailingDegree p ≤ n :=
  by
  rw [← WithTop.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree]
  · exact le_trailing_degree_of_ne_zero h
  · intro h
    subst h
    exact h rfl
#align polynomial.nat_trailing_degree_le_of_ne_zero Polynomial.natTrailingDegree_le_of_ne_zero

/- warning: polynomial.trailing_degree_le_trailing_degree -> Polynomial.trailingDegree_le_trailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 q (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 q) (Polynomial.trailingDegree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 q (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 q) (Polynomial.trailingDegree.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_le_trailing_degree Polynomial.trailingDegree_le_trailingDegreeₓ'. -/
theorem trailingDegree_le_trailingDegree (h : coeff q (natTrailingDegree p) ≠ 0) :
    trailingDegree q ≤ trailingDegree p :=
  by
  by_cases hp : p = 0
  · rw [hp]
    exact le_top
  · rw [trailing_degree_eq_nat_trailing_degree hp]
    exact le_trailing_degree_of_ne_zero h
#align polynomial.trailing_degree_le_trailing_degree Polynomial.trailingDegree_le_trailingDegree

#print Polynomial.trailingDegree_ne_of_natTrailingDegree_ne /-
theorem trailingDegree_ne_of_natTrailingDegree_ne {n : ℕ} :
    p.natTrailingDegree ≠ n → trailingDegree p ≠ n :=
  mt fun h => by rw [nat_trailing_degree, h, Option.getD_coe]
#align polynomial.trailing_degree_ne_of_nat_trailing_degree_ne Polynomial.trailingDegree_ne_of_natTrailingDegree_ne
-/

/- warning: polynomial.nat_trailing_degree_le_of_trailing_degree_le -> Polynomial.natTrailingDegree_le_of_trailingDegree_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : Nat} {hp : Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))}, (LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n) (Polynomial.trailingDegree.{u1} R _inst_1 p)) -> (LE.le.{0} Nat Nat.hasLe n (Polynomial.natTrailingDegree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : Nat} {hp : Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))}, (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n) (Polynomial.trailingDegree.{u1} R _inst_1 p)) -> (LE.le.{0} Nat instLENat n (Polynomial.natTrailingDegree.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_le_of_trailing_degree_le Polynomial.natTrailingDegree_le_of_trailingDegree_leₓ'. -/
theorem natTrailingDegree_le_of_trailingDegree_le {n : ℕ} {hp : p ≠ 0}
    (H : (n : ℕ∞) ≤ trailingDegree p) : n ≤ natTrailingDegree p :=
  by
  rw [trailing_degree_eq_nat_trailing_degree hp] at H
  exact with_top.coe_le_coe.mp H
#align polynomial.nat_trailing_degree_le_of_trailing_degree_le Polynomial.natTrailingDegree_le_of_trailingDegree_le

/- warning: polynomial.nat_trailing_degree_le_nat_trailing_degree -> Polynomial.natTrailingDegree_le_natTrailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1} {hq : Ne.{succ u1} (Polynomial.{u1} R _inst_1) q (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))}, (LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) -> (LE.le.{0} Nat Nat.hasLe (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1} {hq : Ne.{succ u1} (Polynomial.{u1} R _inst_1) q (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))}, (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) -> (LE.le.{0} Nat instLENat (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_le_nat_trailing_degree Polynomial.natTrailingDegree_le_natTrailingDegreeₓ'. -/
theorem natTrailingDegree_le_natTrailingDegree {hq : q ≠ 0}
    (hpq : p.trailingDegree ≤ q.trailingDegree) : p.natTrailingDegree ≤ q.natTrailingDegree :=
  by
  by_cases hp : p = 0;
  · rw [hp, nat_trailing_degree_zero]
    exact zero_le _
  rwa [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
    WithTop.coe_le_coe] at hpq
#align polynomial.nat_trailing_degree_le_nat_trailing_degree Polynomial.natTrailingDegree_le_natTrailingDegree

/- warning: polynomial.trailing_degree_monomial -> Polynomial.trailingDegree_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n))
but is expected to have type
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : R) => Polynomial.{u1} R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_monomial Polynomial.trailingDegree_monomialₓ'. -/
@[simp]
theorem trailingDegree_monomial (ha : a ≠ 0) : trailingDegree (monomial n a) = n := by
  rw [trailing_degree, support_monomial n ha, min_singleton]
#align polynomial.trailing_degree_monomial Polynomial.trailingDegree_monomial

/- warning: polynomial.nat_trailing_degree_monomial -> Polynomial.natTrailingDegree_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) n)
but is expected to have type
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : R) => Polynomial.{u1} R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) n)
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_monomial Polynomial.natTrailingDegree_monomialₓ'. -/
theorem natTrailingDegree_monomial (ha : a ≠ 0) : natTrailingDegree (monomial n a) = n := by
  rw [nat_trailing_degree, trailing_degree_monomial ha] <;> rfl
#align polynomial.nat_trailing_degree_monomial Polynomial.natTrailingDegree_monomial

/- warning: polynomial.nat_trailing_degree_monomial_le -> Polynomial.natTrailingDegree_monomial_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], LE.le.{0} Nat Nat.hasLe (Polynomial.natTrailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) n
but is expected to have type
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], LE.le.{0} Nat instLENat (Polynomial.natTrailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : R) => Polynomial.{u1} R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a)) n
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_monomial_le Polynomial.natTrailingDegree_monomial_leₓ'. -/
theorem natTrailingDegree_monomial_le : natTrailingDegree (monomial n a) ≤ n :=
  if ha : a = 0 then by simp [ha] else (natTrailingDegree_monomial ha).le
#align polynomial.nat_trailing_degree_monomial_le Polynomial.natTrailingDegree_monomial_le

/- warning: polynomial.le_trailing_degree_monomial -> Polynomial.le_trailingDegree_monomial is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n) (Polynomial.trailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a))
but is expected to have type
  forall {R : Type.{u1}} {a : R} {n : Nat} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n) (Polynomial.trailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : R) => Polynomial.{u1} R _inst_1) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R R (Polynomial.{u1} R _inst_1) _inst_1 _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R _inst_1) (Polynomial.module.{u1, u1} R _inst_1 R _inst_1 (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Polynomial.monomial.{u1} R _inst_1 n) a))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_monomial Polynomial.le_trailingDegree_monomialₓ'. -/
theorem le_trailingDegree_monomial : ↑n ≤ trailingDegree (monomial n a) :=
  if ha : a = 0 then by simp [ha] else (trailingDegree_monomial ha).ge
#align polynomial.le_trailing_degree_monomial Polynomial.le_trailingDegree_monomial

/- warning: polynomial.trailing_degree_C -> Polynomial.trailingDegree_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) a)) (OfNat.ofNat.{0} ENat 0 (OfNat.mk.{0} ENat 0 (Zero.zero.{0} ENat ENat.hasZero))))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R], (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) a)) (OfNat.ofNat.{0} ENat 0 (Zero.toOfNat0.{0} ENat instENatZero)))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_C Polynomial.trailingDegree_Cₓ'. -/
@[simp]
theorem trailingDegree_C (ha : a ≠ 0) : trailingDegree (C a) = (0 : ℕ∞) :=
  trailingDegree_monomial ha
#align polynomial.trailing_degree_C Polynomial.trailingDegree_C

/- warning: polynomial.le_trailing_degree_C -> Polynomial.le_trailingDegree_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (OfNat.ofNat.{0} ENat 0 (OfNat.mk.{0} ENat 0 (Zero.zero.{0} ENat ENat.hasZero))) (Polynomial.trailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) a))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (OfNat.ofNat.{0} ENat 0 (Zero.toOfNat0.{0} ENat instENatZero)) (Polynomial.trailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) a))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_C Polynomial.le_trailingDegree_Cₓ'. -/
theorem le_trailingDegree_C : (0 : ℕ∞) ≤ trailingDegree (C a) :=
  le_trailingDegree_monomial
#align polynomial.le_trailing_degree_C Polynomial.le_trailingDegree_C

/- warning: polynomial.trailing_degree_one_le -> Polynomial.trailingDegree_one_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (OfNat.ofNat.{0} ENat 0 (OfNat.mk.{0} ENat 0 (Zero.zero.{0} ENat ENat.hasZero))) (Polynomial.trailingDegree.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 1 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 1 (One.one.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.hasOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (OfNat.ofNat.{0} ENat 0 (Zero.toOfNat0.{0} ENat instENatZero)) (Polynomial.trailingDegree.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 1 (One.toOfNat1.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.one.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_one_le Polynomial.trailingDegree_one_leₓ'. -/
theorem trailingDegree_one_le : (0 : ℕ∞) ≤ trailingDegree (1 : R[X]) := by
  rw [← C_1] <;> exact le_trailing_degree_C
#align polynomial.trailing_degree_one_le Polynomial.trailingDegree_one_le

/- warning: polynomial.nat_trailing_degree_C -> Polynomial.natTrailingDegree_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (a : R), Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (a : R), Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) a)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_C Polynomial.natTrailingDegree_Cₓ'. -/
@[simp]
theorem natTrailingDegree_C (a : R) : natTrailingDegree (C a) = 0 :=
  nonpos_iff_eq_zero.1 natTrailingDegree_monomial_le
#align polynomial.nat_trailing_degree_C Polynomial.natTrailingDegree_C

#print Polynomial.natTrailingDegree_one /-
@[simp]
theorem natTrailingDegree_one : natTrailingDegree (1 : R[X]) = 0 :=
  natTrailingDegree_C 1
#align polynomial.nat_trailing_degree_one Polynomial.natTrailingDegree_one
-/

#print Polynomial.natTrailingDegree_nat_cast /-
@[simp]
theorem natTrailingDegree_nat_cast (n : ℕ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_nat_cast, nat_trailing_degree_C]
#align polynomial.nat_trailing_degree_nat_cast Polynomial.natTrailingDegree_nat_cast
-/

/- warning: polynomial.trailing_degree_C_mul_X_pow -> Polynomial.trailingDegree_C_mul_X_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R] (n : Nat), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) a) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Semiring.{u1} R] (n : Nat), (Ne.{succ u1} R a (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) a) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) a) (Polynomial.mul'.{u1} R _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) a) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_C_mul_X_pow Polynomial.trailingDegree_C_mul_X_powₓ'. -/
@[simp]
theorem trailingDegree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailingDegree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailing_degree_monomial ha]
#align polynomial.trailing_degree_C_mul_X_pow Polynomial.trailingDegree_C_mul_X_pow

/- warning: polynomial.le_trailing_degree_C_mul_X_pow -> Polynomial.le_trailingDegree_C_mul_X_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (n : Nat) (a : R), LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n) (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) a) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (n : Nat) (a : R), LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n) (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) a) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) a) (Polynomial.mul'.{u1} R _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) a) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n)))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_C_mul_X_pow Polynomial.le_trailingDegree_C_mul_X_powₓ'. -/
theorem le_trailingDegree_C_mul_X_pow (n : ℕ) (a : R) : (n : ℕ∞) ≤ trailingDegree (C a * X ^ n) :=
  by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailing_degree_monomial
#align polynomial.le_trailing_degree_C_mul_X_pow Polynomial.le_trailingDegree_C_mul_X_pow

/- warning: polynomial.coeff_eq_zero_of_trailing_degree_lt -> Polynomial.coeff_eq_zero_of_trailingDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (LT.lt.{0} ENat (Preorder.toHasLt.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n) (Polynomial.trailingDegree.{u1} R _inst_1 p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n) (Polynomial.trailingDegree.{u1} R _inst_1 p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_eq_zero_of_trailing_degree_lt Polynomial.coeff_eq_zero_of_trailingDegree_ltₓ'. -/
theorem coeff_eq_zero_of_trailingDegree_lt (h : (n : ℕ∞) < trailingDegree p) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_trailingDegree_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_trailing_degree_lt Polynomial.coeff_eq_zero_of_trailingDegree_lt

/- warning: polynomial.coeff_eq_zero_of_lt_nat_trailing_degree -> Polynomial.coeff_eq_zero_of_lt_natTrailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : Nat}, (LT.lt.{0} Nat Nat.hasLt n (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : Nat}, (LT.lt.{0} Nat instLTNat n (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p n) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_eq_zero_of_lt_nat_trailing_degree Polynomial.coeff_eq_zero_of_lt_natTrailingDegreeₓ'. -/
theorem coeff_eq_zero_of_lt_natTrailingDegree {p : R[X]} {n : ℕ} (h : n < p.natTrailingDegree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_trailing_degree_lt
  by_cases hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact WithTop.coe_lt_top n
  · rwa [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_lt_coe]
#align polynomial.coeff_eq_zero_of_lt_nat_trailing_degree Polynomial.coeff_eq_zero_of_lt_natTrailingDegree

/- warning: polynomial.coeff_nat_trailing_degree_pred_eq_zero -> Polynomial.coeff_natTrailingDegree_pred_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {hp : LT.lt.{0} ENat (Preorder.toHasLt.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (OfNat.ofNat.{0} ENat 0 (OfNat.mk.{0} ENat 0 (Zero.zero.{0} ENat ENat.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) (Polynomial.natTrailingDegree.{u1} R _inst_1 p))}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {hp : LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (OfNat.ofNat.{0} ENat 0 (Zero.toOfNat0.{0} ENat instENatZero)) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) (Polynomial.natTrailingDegree.{u1} R _inst_1 p))}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_nat_trailing_degree_pred_eq_zero Polynomial.coeff_natTrailingDegree_pred_eq_zeroₓ'. -/
@[simp]
theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 :=
  coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt ((WithTop.zero_lt_coe (natTrailingDegree p)).mp hp) Nat.one_pos
#align polynomial.coeff_nat_trailing_degree_pred_eq_zero Polynomial.coeff_natTrailingDegree_pred_eq_zero

/- warning: polynomial.le_trailing_degree_X_pow -> Polynomial.le_trailingDegree_X_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (n : Nat), LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENat (HasLiftT.mk.{1, 1} Nat ENat (CoeTCₓ.coe.{1, 1} Nat ENat ENat.hasCoeT)) n) (Polynomial.trailingDegree.{u1} R _inst_1 (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (n : Nat), LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Nat.cast.{0} ENat (CanonicallyOrderedCommSemiring.toNatCast.{0} ENat instENatCanonicallyOrderedCommSemiring) n) (Polynomial.trailingDegree.{u1} R _inst_1 (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) n))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_X_pow Polynomial.le_trailingDegree_X_powₓ'. -/
theorem le_trailingDegree_X_pow (n : ℕ) : (n : ℕ∞) ≤ trailingDegree (X ^ n : R[X]) := by
  simpa only [C_1, one_mul] using le_trailing_degree_C_mul_X_pow n (1 : R)
#align polynomial.le_trailing_degree_X_pow Polynomial.le_trailingDegree_X_pow

/- warning: polynomial.le_trailing_degree_X -> Polynomial.le_trailingDegree_X is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (OfNat.ofNat.{0} ENat 1 (OfNat.mk.{0} ENat 1 (One.one.{0} ENat (AddMonoidWithOne.toOne.{0} ENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENat ENat.addCommMonoidWithOne))))) (Polynomial.trailingDegree.{u1} R _inst_1 (Polynomial.X.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (OfNat.ofNat.{0} ENat 1 (One.toOfNat1.{0} ENat (CanonicallyOrderedCommSemiring.toOne.{0} ENat instENatCanonicallyOrderedCommSemiring))) (Polynomial.trailingDegree.{u1} R _inst_1 (Polynomial.X.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_X Polynomial.le_trailingDegree_Xₓ'. -/
theorem le_trailingDegree_X : (1 : ℕ∞) ≤ trailingDegree (X : R[X]) :=
  le_trailingDegree_monomial
#align polynomial.le_trailing_degree_X Polynomial.le_trailingDegree_X

#print Polynomial.natTrailingDegree_X_le /-
theorem natTrailingDegree_X_le : (X : R[X]).natTrailingDegree ≤ 1 :=
  natTrailingDegree_monomial_le
#align polynomial.nat_trailing_degree_X_le Polynomial.natTrailingDegree_X_le
-/

/- warning: polynomial.trailing_coeff_eq_zero -> Polynomial.trailingCoeff_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, Iff (Eq.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 p) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) (Eq.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, Iff (Eq.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 p) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) (Eq.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_coeff_eq_zero Polynomial.trailingCoeff_eq_zeroₓ'. -/
@[simp]
theorem trailingCoeff_eq_zero : trailingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
#align polynomial.trailing_coeff_eq_zero Polynomial.trailingCoeff_eq_zero

/- warning: polynomial.trailing_coeff_nonzero_iff_nonzero -> Polynomial.trailingCoeff_nonzero_iff_nonzero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, Iff (Ne.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 p) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, Iff (Ne.{succ u1} R (Polynomial.trailingCoeff.{u1} R _inst_1 p) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_coeff_nonzero_iff_nonzero Polynomial.trailingCoeff_nonzero_iff_nonzeroₓ'. -/
theorem trailingCoeff_nonzero_iff_nonzero : trailingCoeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailingCoeff_eq_zero
#align polynomial.trailing_coeff_nonzero_iff_nonzero Polynomial.trailingCoeff_nonzero_iff_nonzero

#print Polynomial.natTrailingDegree_mem_support_of_nonzero /-
theorem natTrailingDegree_mem_support_of_nonzero : p ≠ 0 → natTrailingDegree p ∈ p.support :=
  mem_support_iff.mpr ∘ trailingCoeff_nonzero_iff_nonzero.mpr
#align polynomial.nat_trailing_degree_mem_support_of_nonzero Polynomial.natTrailingDegree_mem_support_of_nonzero
-/

#print Polynomial.natTrailingDegree_le_of_mem_supp /-
theorem natTrailingDegree_le_of_mem_supp (a : ℕ) : a ∈ p.support → natTrailingDegree p ≤ a :=
  natTrailingDegree_le_of_ne_zero ∘ mem_support_iff.mp
#align polynomial.nat_trailing_degree_le_of_mem_supp Polynomial.natTrailingDegree_le_of_mem_supp
-/

#print Polynomial.natTrailingDegree_eq_support_min' /-
theorem natTrailingDegree_eq_support_min' (h : p ≠ 0) :
    natTrailingDegree p = p.support.min' (nonempty_support_iff.mpr h) :=
  by
  apply le_antisymm
  · apply le_min'
    intro y hy
    exact nat_trailing_degree_le_of_mem_supp y hy
  · apply Finset.min'_le
    exact mem_support_iff.mpr (trailing_coeff_nonzero_iff_nonzero.mpr h)
#align polynomial.nat_trailing_degree_eq_support_min' Polynomial.natTrailingDegree_eq_support_min'
-/

/- warning: polynomial.le_nat_trailing_degree -> Polynomial.le_natTrailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))) -> (forall (m : Nat), (LT.lt.{0} Nat Nat.hasLt m n) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p m) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))) -> (LE.le.{0} Nat Nat.hasLe n (Polynomial.natTrailingDegree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} {n : Nat} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))) -> (forall (m : Nat), (LT.lt.{0} Nat instLTNat m n) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 p m) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))) -> (LE.le.{0} Nat instLENat n (Polynomial.natTrailingDegree.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.le_nat_trailing_degree Polynomial.le_natTrailingDegreeₓ'. -/
theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) : n ≤ p.natTrailingDegree :=
  by
  rw [nat_trailing_degree_eq_support_min' hp]
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn
#align polynomial.le_nat_trailing_degree Polynomial.le_natTrailingDegree

#print Polynomial.natTrailingDegree_le_natDegree /-
theorem natTrailingDegree_le_natDegree (p : R[X]) : p.natTrailingDegree ≤ p.natDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, nat_degree_zero, nat_trailing_degree_zero]
  · exact le_nat_degree_of_ne_zero (mt trailing_coeff_eq_zero.mp hp)
#align polynomial.nat_trailing_degree_le_nat_degree Polynomial.natTrailingDegree_le_natDegree
-/

#print Polynomial.natTrailingDegree_mul_X_pow /-
theorem natTrailingDegree_mul_X_pow {p : R[X]} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.natTrailingDegree + n :=
  by
  apply le_antisymm
  · refine' nat_trailing_degree_le_of_ne_zero fun h => mt trailing_coeff_eq_zero.mp hp _
    rwa [trailing_coeff, ← coeff_mul_X_pow]
  · rw [nat_trailing_degree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (nat_trailing_degree_le_of_ne_zero hy)
#align polynomial.nat_trailing_degree_mul_X_pow Polynomial.natTrailingDegree_mul_X_pow
-/

/- warning: polynomial.le_trailing_degree_mul -> Polynomial.le_trailingDegree_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, LE.le.{0} ENat (Preorder.toHasLe.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toHasAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q))
Case conversion may be inaccurate. Consider using '#align polynomial.le_trailing_degree_mul Polynomial.le_trailingDegree_mulₓ'. -/
theorem le_trailingDegree_mul : p.trailingDegree + q.trailingDegree ≤ (p * q).trailingDegree :=
  by
  refine' Finset.le_min fun n hn => _
  rw [mem_support_iff, coeff_mul] at hn
  obtain ⟨⟨i, j⟩, hij, hpq⟩ := exists_ne_zero_of_sum_ne_zero hn
  refine'
    (add_le_add (min_le (mem_support_iff.mpr (left_ne_zero_of_mul hpq)))
          (min_le (mem_support_iff.mpr (right_ne_zero_of_mul hpq)))).trans
      (le_of_eq _)
  rwa [← WithTop.coe_add, WithTop.coe_eq_coe, ← nat.mem_antidiagonal]
#align polynomial.le_trailing_degree_mul Polynomial.le_trailingDegree_mul

#print Polynomial.le_natTrailingDegree_mul /-
theorem le_natTrailingDegree_mul (h : p * q ≠ 0) :
    p.natTrailingDegree + q.natTrailingDegree ≤ (p * q).natTrailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, MulZeroClass.zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, MulZeroClass.mul_zero])
  rw [← WithTop.coe_le_coe, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq, ← trailing_degree_eq_nat_trailing_degree h]
  exact le_trailing_degree_mul
#align polynomial.le_nat_trailing_degree_mul Polynomial.le_natTrailingDegree_mul
-/

/- warning: polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree -> Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegreeₓ'. -/
theorem coeff_mul_natTrailingDegree_add_natTrailingDegree :
    (p * q).coeff (p.natTrailingDegree + q.natTrailingDegree) = p.trailingCoeff * q.trailingCoeff :=
  by
  rw [coeff_mul]
  refine'
    Finset.sum_eq_single (p.nat_trailing_degree, q.nat_trailing_degree) _ fun h =>
      (h (nat.mem_antidiagonal.mpr rfl)).elim
  rintro ⟨i, j⟩ h₁ h₂
  rw [nat.mem_antidiagonal] at h₁
  by_cases hi : i < p.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hi, MulZeroClass.zero_mul]
  by_cases hj : j < q.nat_trailing_degree
  · rw [coeff_eq_zero_of_lt_nat_trailing_degree hj, MulZeroClass.mul_zero]
  rw [not_lt] at hi hj
  refine' (h₂ (prod.ext_iff.mpr _).symm).elim
  exact (add_eq_add_iff_eq_and_eq hi hj).mp h₁.symm
#align polynomial.coeff_mul_nat_trailing_degree_add_nat_trailing_degree Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree

/- warning: polynomial.trailing_degree_mul' -> Polynomial.trailingDegree_mul' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toHasAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} ENat (Polynomial.trailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align polynomial.trailing_degree_mul' Polynomial.trailingDegree_mul'ₓ'. -/
theorem trailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).trailingDegree = p.trailingDegree + q.trailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailing_coeff_zero, MulZeroClass.zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailing_coeff_zero, MulZeroClass.mul_zero])
  refine' le_antisymm _ le_trailing_degree_mul
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq, ←
    ENat.coe_add]
  apply le_trailing_degree_of_ne_zero
  rwa [coeff_mul_nat_trailing_degree_add_nat_trailing_degree]
#align polynomial.trailing_degree_mul' Polynomial.trailingDegree_mul'

/- warning: polynomial.nat_trailing_degree_mul' -> Polynomial.natTrailingDegree_mul' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Ne.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.trailingCoeff.{u1} R _inst_1 p) (Polynomial.trailingCoeff.{u1} R _inst_1 q)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_mul' Polynomial.natTrailingDegree_mul'ₓ'. -/
theorem natTrailingDegree_mul' (h : p.trailingCoeff * q.trailingCoeff ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  by
  have hp : p ≠ 0 := fun hp => h (by rw [hp, trailing_coeff_zero, MulZeroClass.zero_mul])
  have hq : q ≠ 0 := fun hq => h (by rw [hq, trailing_coeff_zero, MulZeroClass.mul_zero])
  apply nat_trailing_degree_eq_of_trailing_degree_eq_some
  rw [trailing_degree_mul' h, WithTop.coe_add, ← trailing_degree_eq_nat_trailing_degree hp, ←
    trailing_degree_eq_nat_trailing_degree hq]
#align polynomial.nat_trailing_degree_mul' Polynomial.natTrailingDegree_mul'

/- warning: polynomial.nat_trailing_degree_mul -> Polynomial.natTrailingDegree_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1} [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))], (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))) -> (Ne.{succ u1} (Polynomial.{u1} R _inst_1) q (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1} [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))], (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))) -> (Ne.{succ u1} (Polynomial.{u1} R _inst_1) q (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))) -> (Eq.{1} Nat (Polynomial.natTrailingDegree.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Polynomial.natTrailingDegree.{u1} R _inst_1 p) (Polynomial.natTrailingDegree.{u1} R _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_trailing_degree_mul Polynomial.natTrailingDegree_mulₓ'. -/
theorem natTrailingDegree_mul [NoZeroDivisors R] (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).natTrailingDegree = p.natTrailingDegree + q.natTrailingDegree :=
  natTrailingDegree_mul'
    (mul_ne_zero (mt trailingCoeff_eq_zero.mp hp) (mt trailingCoeff_eq_zero.mp hq))
#align polynomial.nat_trailing_degree_mul Polynomial.natTrailingDegree_mul

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

#print Polynomial.trailingDegree_one /-
@[simp]
theorem trailingDegree_one : trailingDegree (1 : R[X]) = (0 : ℕ∞) :=
  trailingDegree_C one_ne_zero
#align polynomial.trailing_degree_one Polynomial.trailingDegree_one
-/

#print Polynomial.trailingDegree_X /-
@[simp]
theorem trailingDegree_X : trailingDegree (X : R[X]) = 1 :=
  trailingDegree_monomial one_ne_zero
#align polynomial.trailing_degree_X Polynomial.trailingDegree_X
-/

#print Polynomial.natTrailingDegree_X /-
@[simp]
theorem natTrailingDegree_X : (X : R[X]).natTrailingDegree = 1 :=
  natTrailingDegree_monomial one_ne_zero
#align polynomial.nat_trailing_degree_X Polynomial.natTrailingDegree_X
-/

end NonzeroSemiring

section Ring

variable [Ring R]

#print Polynomial.trailingDegree_neg /-
@[simp]
theorem trailingDegree_neg (p : R[X]) : trailingDegree (-p) = trailingDegree p := by
  unfold trailing_degree <;> rw [support_neg]
#align polynomial.trailing_degree_neg Polynomial.trailingDegree_neg
-/

#print Polynomial.natTrailingDegree_neg /-
@[simp]
theorem natTrailingDegree_neg (p : R[X]) : natTrailingDegree (-p) = natTrailingDegree p := by
  simp [nat_trailing_degree]
#align polynomial.nat_trailing_degree_neg Polynomial.natTrailingDegree_neg
-/

#print Polynomial.natTrailingDegree_int_cast /-
@[simp]
theorem natTrailingDegree_int_cast (n : ℤ) : natTrailingDegree (n : R[X]) = 0 := by
  simp only [← C_eq_int_cast, nat_trailing_degree_C]
#align polynomial.nat_trailing_degree_int_cast Polynomial.natTrailingDegree_int_cast
-/

end Ring

section Semiring

variable [Semiring R]

#print Polynomial.nextCoeffUp /-
/-- The second-lowest coefficient, or 0 for constants -/
def nextCoeffUp (p : R[X]) : R :=
  if p.natTrailingDegree = 0 then 0 else p.coeff (p.natTrailingDegree + 1)
#align polynomial.next_coeff_up Polynomial.nextCoeffUp
-/

/- warning: polynomial.next_coeff_up_C_eq_zero -> Polynomial.nextCoeffUp_C_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (c : R), Eq.{succ u1} R (Polynomial.nextCoeffUp.{u1} R _inst_1 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) c)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (c : R), Eq.{succ u1} R (Polynomial.nextCoeffUp.{u1} R _inst_1 (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) c)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.next_coeff_up_C_eq_zero Polynomial.nextCoeffUp_C_eq_zeroₓ'. -/
@[simp]
theorem nextCoeffUp_C_eq_zero (c : R) : nextCoeffUp (C c) = 0 :=
  by
  rw [next_coeff_up]
  simp
#align polynomial.next_coeff_up_C_eq_zero Polynomial.nextCoeffUp_C_eq_zero

#print Polynomial.nextCoeffUp_of_pos_natTrailingDegree /-
theorem nextCoeffUp_of_pos_natTrailingDegree (p : R[X]) (hp : 0 < p.natTrailingDegree) :
    nextCoeffUp p = p.coeff (p.natTrailingDegree + 1) :=
  by
  rw [next_coeff_up, if_neg]
  contrapose! hp
  simpa
#align polynomial.next_coeff_up_of_pos_nat_trailing_degree Polynomial.nextCoeffUp_of_pos_natTrailingDegree
-/

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type _}

/- warning: polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt -> Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (LT.lt.{0} ENat (Preorder.toHasLt.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 q (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) (Polynomial.trailingDegree.{u1} R _inst_1 q)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R _inst_1 q (Polynomial.natTrailingDegree.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_ltₓ'. -/
theorem coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt
    (h : trailingDegree p < trailingDegree q) : coeff q (natTrailingDegree p) = 0 :=
  coeff_eq_zero_of_trailingDegree_lt <| natTrailingDegree_le_trailingDegree.trans_lt h
#align polynomial.coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt Polynomial.coeff_natTrailingDegree_eq_zero_of_trailingDegree_lt

/- warning: polynomial.ne_zero_of_trailing_degree_lt -> Polynomial.ne_zero_of_trailingDegree_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : ENat}, (LT.lt.{0} ENat (Preorder.toHasLt.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) n) -> (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {n : ENat}, (LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Polynomial.trailingDegree.{u1} R _inst_1 p) n) -> (Ne.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.ne_zero_of_trailing_degree_lt Polynomial.ne_zero_of_trailingDegree_ltₓ'. -/
theorem ne_zero_of_trailingDegree_lt {n : ℕ∞} (h : trailingDegree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le (by simp [h₀])
#align polynomial.ne_zero_of_trailing_degree_lt Polynomial.ne_zero_of_trailingDegree_lt

end Semiring

end Polynomial

