/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module analysis.p_series
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Nnreal

/-!
# Convergence of `p`-series

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/


open Filter

open BigOperators ENNReal NNReal Topology

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/


namespace Finset

variable {M : Type _} [OrderedAddCommMonoid M] {f : ℕ → M}

/- warning: finset.le_sum_condensed' -> Finset.le_sum_condensed' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n)) (fun (k : Nat) => f k)) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n)) (fun (k : Nat) => f k)) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => HSMul.hSMul.{0, u1, u1} Nat M M (instHSMul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)))))
Case conversion may be inaccurate. Consider using '#align finset.le_sum_condensed' Finset.le_sum_condensed'ₓ'. -/
theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in Ico 1 (2 ^ n), f k) ≤ ∑ k in range n, 2 ^ k • f (2 ^ k) :=
  by
  induction' n with n ihn; · simp
  suffices (∑ k in Ico (2 ^ n) (2 ^ (n + 1)), f k) ≤ 2 ^ n • f (2 ^ n)
    by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts[n.one_le_two_pow, Nat.pow_le_pow_of_le_right zero_lt_two n.le_succ]
  have : ∀ k ∈ Ico (2 ^ n) (2 ^ (n + 1)), f k ≤ f (2 ^ n) := fun k hk =>
    hf (pow_pos zero_lt_two _) (mem_Ico.mp hk).1
  convert sum_le_sum this
  simp [pow_succ, two_mul]
#align finset.le_sum_condensed' Finset.le_sum_condensed'

/- warning: finset.le_sum_condensed -> Finset.le_sum_condensed is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n)) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n)) (fun (k : Nat) => f k)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => HSMul.hSMul.{0, u1, u1} Nat M M (instHSMul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k))))))
Case conversion may be inaccurate. Consider using '#align finset.le_sum_condensed Finset.le_sum_condensedₓ'. -/
theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (2 ^ n), f k) ≤ f 0 + ∑ k in range n, 2 ^ k • f (2 ^ k) :=
  by
  convert add_le_add_left (le_sum_condensed' hf n) (f 0)
  rw [← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ, sum_range_zero, zero_add]
#align finset.le_sum_condensed Finset.le_sum_condensed

/- warning: finset.sum_condensed_le' -> Finset.sum_condensed_le' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range n) (fun (k : Nat) => HSMul.hSMul.{0, u1, u1} Nat M M (instHSMul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)))
Case conversion may be inaccurate. Consider using '#align finset.sum_condensed_le' Finset.sum_condensed_le'ₓ'. -/
theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k in Ico 2 (2 ^ n + 1), f k :=
  by
  induction' n with n ihn; · simp
  suffices 2 ^ n • f (2 ^ (n + 1)) ≤ ∑ k in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f k
    by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts[add_le_add_right n.one_le_two_pow _,
      add_le_add_right (Nat.pow_le_pow_of_le_right zero_lt_two n.le_succ) _]
  have : ∀ k ∈ Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ (n + 1)) ≤ f k := fun k hk =>
    hf (n.one_le_two_pow.trans_lt <| (Nat.lt_succ_of_le le_rfl).trans_le (mem_Ico.mp hk).1)
      (Nat.le_of_lt_succ <| (mem_Ico.mp hk).2)
  convert sum_le_sum this
  simp [pow_succ, two_mul]
#align finset.sum_condensed_le' Finset.sum_condensed_le'

/- warning: finset.sum_condensed_le -> Finset.sum_condensed_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toHasLe.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)))) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))))) (f (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (SMul.smul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} M] {f : Nat -> M}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (f n) (f m))) -> (forall (n : Nat), LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HSMul.hSMul.{0, u1, u1} Nat M M (instHSMul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1)))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)))) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1))))) (f (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HSMul.hSMul.{0, u1, u1} Nat M M (instHSMul.{0, u1} Nat M (AddMonoid.SMul.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Finset.sum.{u1, 0} M Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} M _inst_1) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_condensed_le Finset.sum_condensed_leₓ'. -/
theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k in Ico 2 (2 ^ n + 1), f k :=
  by
  convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1)
  simp [sum_range_succ', add_comm, pow_succ, mul_nsmul', sum_nsmul]
#align finset.sum_condensed_le Finset.sum_condensed_le

end Finset

namespace ENNReal

variable {f : ℕ → ℝ≥0∞}

/- warning: ennreal.le_tsum_condensed -> ENNReal.le_tsum_condensed is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f n) (f m))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => f k)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k))))))
but is expected to have type
  forall {f : Nat -> ENNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f n) (f m))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => f k)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k))))))
Case conversion may be inaccurate. Consider using '#align ennreal.le_tsum_condensed ENNReal.le_tsum_condensedₓ'. -/
theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (∑' k, f k) ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) :=
  by
  rw [ENNReal.tsum_eq_iSup_nat' (Nat.tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine' iSup_le fun n => (Finset.le_sum_condensed hf n).trans (add_le_add_left _ _)
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  apply ENNReal.sum_le_tsum
#align ennreal.le_tsum_condensed ENNReal.le_tsum_condensed

/- warning: ennreal.tsum_condensed_le -> ENNReal.tsum_condensed_le is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> ENNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f n) (f m))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (k : Nat) => f k)))))
but is expected to have type
  forall {f : Nat -> ENNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f n) (f m))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (f (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (k : Nat) => f k)))))
Case conversion may be inaccurate. Consider using '#align ennreal.tsum_condensed_le ENNReal.tsum_condensed_leₓ'. -/
theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k :=
  by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_at_top_mono Nat.le_succ tendsto_id), two_mul, ← two_nsmul]
  refine'
    iSup_le fun n =>
      le_trans _
        (add_le_add_left
          (nsmul_le_nsmul_of_le_right (ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)) _) _)
  simpa using Finset.sum_condensed_le hf n
#align ennreal.tsum_condensed_le ENNReal.tsum_condensed_le

end ENNReal

namespace NNReal

/- warning: nnreal.summable_condensed_iff -> NNReal.summable_condensed_iff is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> NNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (f n) (f m))) -> (Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (k : Nat) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (OfNat.ofNat.{0} NNReal 2 (OfNat.mk.{0} NNReal 2 (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)))) (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace f))
but is expected to have type
  forall {f : Nat -> NNReal}, (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (f n) (f m))) -> (Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (k : Nat) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) (OfNat.ofNat.{0} NNReal 2 (instOfNat.{0} NNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)))) (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal f))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_condensed_iff NNReal.summable_condensed_iffₓ'. -/
/-- Cauchy condensation test for a series of `nnreal` version. -/
theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f :=
  by
  simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Ne.def, not_iff_not, ENNReal.coe_mul,
    ENNReal.coe_pow, ENNReal.coe_two]
  constructor <;> intro h
  · replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    simpa [h, ENNReal.add_eq_top, ENNReal.mul_eq_top] using ENNReal.tsum_condensed_le hf
  · replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf hm hmn)
    simpa [h, ENNReal.add_eq_top] using ENNReal.le_tsum_condensed hf
#align nnreal.summable_condensed_iff NNReal.summable_condensed_iff

end NNReal

/- warning: summable_condensed_iff_of_nonneg -> summable_condensed_iff_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f n)) -> (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) m) -> (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} Real Real.hasLe (f n) (f m))) -> (Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (k : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) k) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) k)))) (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f))
but is expected to have type
  forall {f : Nat -> Real}, (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f n)) -> (forall {{m : Nat}} {{n : Nat}}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) m) -> (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} Real Real.instLEReal (f n) (f m))) -> (Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (k : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Nat.cast.{0} Real Real.natCast k)) (f (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) k)))) (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f))
Case conversion may be inaccurate. Consider using '#align summable_condensed_iff_of_nonneg summable_condensed_iff_of_nonnegₓ'. -/
/-- Cauchy condensation test for series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f :=
  by
  lift f to ℕ → ℝ≥0 using h_nonneg
  simp only [NNReal.coe_le_coe] at *
  exact_mod_cast NNReal.summable_condensed_iff h_mono
#align summable_condensed_iff_of_nonneg summable_condensed_iff_of_nonneg

open Real

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/


/- warning: real.summable_nat_rpow_inv -> Real.summable_nat_rpow_inv is a dubious translation:
lean 3 declaration is
  forall {p : Real}, Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.hasInv (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) p))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)
but is expected to have type
  forall {p : Real}, Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.instInvReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Nat.cast.{0} Real Real.natCast n) p))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)
Case conversion may be inaccurate. Consider using '#align real.summable_nat_rpow_inv Real.summable_nat_rpow_invₓ'. -/
/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_rpow_inv {p : ℝ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p :=
  by
  cases' le_or_lt 0 p with hp hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow, ← mul_pow,
        summable_geometric_iff_norm_lt_1]
      nth_rw 1 [← rpow_one 2]
      rw [← division_def, ← rpow_sub zero_lt_two, norm_eq_abs,
        abs_of_pos (rpow_pos_of_pos zero_lt_two _), rpow_lt_one_iff zero_lt_two.le]
      norm_num
    · intro n
      exact inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _)
    · intro m n hm hmn
      exact
        inv_le_inv_of_le (rpow_pos_of_pos (Nat.cast_pos.2 hm) _)
          (rpow_le_rpow m.cast_nonneg (Nat.cast_le.2 hmn) hp)
  -- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges.
  · suffices ¬Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ)
      by
      have : ¬1 < p := fun hp₁ => hp.not_le (zero_le_one.trans hp₁.le)
      simpa [this, -one_div]
    · intro h
      obtain ⟨k : ℕ, hk₁ : ((k ^ p)⁻¹ : ℝ) < 1, hk₀ : k ≠ 0⟩ :=
        ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).And
            (eventually_cofinite_ne 0)).exists
      apply hk₀
      rw [← pos_iff_ne_zero, ← @Nat.cast_pos ℝ] at hk₀
      simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
        hp.not_lt, hk₀] using hk₁
#align real.summable_nat_rpow_inv Real.summable_nat_rpow_inv

#print Real.summable_nat_rpow /-
@[simp]
theorem Real.summable_nat_rpow {p : ℝ} : Summable (fun n => n ^ p : ℕ → ℝ) ↔ p < -1 := by
  rcases neg_surjective p with ⟨p, rfl⟩; simp [rpow_neg]
#align real.summable_nat_rpow Real.summable_nat_rpow
-/

/- warning: real.summable_one_div_nat_rpow -> Real.summable_one_div_nat_rpow is a dubious translation:
lean 3 declaration is
  forall {p : Real}, Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) p))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)
but is expected to have type
  forall {p : Real}, Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Nat.cast.{0} Real Real.natCast n) p))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)
Case conversion may be inaccurate. Consider using '#align real.summable_one_div_nat_rpow Real.summable_one_div_nat_rpowₓ'. -/
/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp
#align real.summable_one_div_nat_rpow Real.summable_one_div_nat_rpow

/- warning: real.summable_nat_pow_inv -> Real.summable_nat_pow_inv is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.hasInv (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) p))) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) p)
but is expected to have type
  forall {p : Nat}, Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.instInvReal (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Nat.cast.{0} Real Real.natCast n) (Nat.cast.{0} Real Real.natCast p)))) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) p)
Case conversion may be inaccurate. Consider using '#align real.summable_nat_pow_inv Real.summable_nat_pow_invₓ'. -/
/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_pow_inv {p : ℕ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  simp only [← rpow_nat_cast, Real.summable_nat_rpow_inv, Nat.one_lt_cast]
#align real.summable_nat_pow_inv Real.summable_nat_pow_inv

/- warning: real.summable_one_div_nat_pow -> Real.summable_one_div_nat_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, Iff (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) p))) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) p)
but is expected to have type
  forall {p : Nat}, Iff (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Nat.cast.{0} Real Real.natCast n) (Nat.cast.{0} Real Real.natCast p)))) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) p)
Case conversion may be inaccurate. Consider using '#align real.summable_one_div_nat_pow Real.summable_one_div_nat_powₓ'. -/
/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_pow {p : ℕ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp
#align real.summable_one_div_nat_pow Real.summable_one_div_nat_pow

/- warning: real.summable_one_div_int_pow -> Real.summable_one_div_int_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, Iff (Summable.{0, 0} Real Int Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Int) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n) p))) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) p)
but is expected to have type
  forall {p : Nat}, Iff (Summable.{0, 0} Real Int Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Int) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Int.cast.{0} Real Real.intCast n) (Nat.cast.{0} Real Real.natCast p)))) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) p)
Case conversion may be inaccurate. Consider using '#align real.summable_one_div_int_pow Real.summable_one_div_int_powₓ'. -/
/-- Summability of the `p`-series over `ℤ`. -/
theorem Real.summable_one_div_int_pow {p : ℕ} : (Summable fun n : ℤ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  by
  refine'
    ⟨fun h => real.summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective), fun h =>
      summable_int_of_summable_nat (real.summable_one_div_nat_pow.mpr h)
        (((real.summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1) ^ p).congr fun n => _)⟩
  conv_rhs => rw [Int.cast_neg, neg_eq_neg_one_mul, mul_pow, ← div_div]
  conv_lhs => rw [mul_div, mul_one]
  rfl
#align real.summable_one_div_int_pow Real.summable_one_div_int_pow

/- warning: real.summable_abs_int_rpow -> Real.summable_abs_int_rpow is a dubious translation:
lean 3 declaration is
  forall {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) b) -> (Summable.{0, 0} Real Int Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Int) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n)) (Neg.neg.{0} Real Real.hasNeg b)))
but is expected to have type
  forall {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) b) -> (Summable.{0, 0} Real Int Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Int) => HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Int.cast.{0} Real Real.intCast n)) (Neg.neg.{0} Real Real.instNegReal b)))
Case conversion may be inaccurate. Consider using '#align real.summable_abs_int_rpow Real.summable_abs_int_rpowₓ'. -/
theorem Real.summable_abs_int_rpow {b : ℝ} (hb : 1 < b) : Summable fun n : ℤ => |(n : ℝ)| ^ (-b) :=
  by
  refine'
    summable_int_of_summable_nat (_ : Summable fun n : ℕ => |(n : ℝ)| ^ _)
      (_ : Summable fun n : ℕ => |((-n : ℤ) : ℝ)| ^ _)
  on_goal 2 => simp_rw [Int.cast_neg, Int.cast_ofNat, abs_neg]
  all_goals
    simp_rw [fun n : ℕ => abs_of_nonneg (n.cast_nonneg : 0 ≤ (n : ℝ))]
    rwa [Real.summable_nat_rpow, neg_lt_neg_iff]
#align real.summable_abs_int_rpow Real.summable_abs_int_rpow

/- warning: real.not_summable_nat_cast_inv -> Real.not_summable_nat_cast_inv is a dubious translation:
lean 3 declaration is
  Not (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))
but is expected to have type
  Not (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n)))
Case conversion may be inaccurate. Consider using '#align real.not_summable_nat_cast_inv Real.not_summable_nat_cast_invₓ'. -/
/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_nat_cast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) :=
  by
  have : ¬Summable (fun n => (n ^ 1)⁻¹ : ℕ → ℝ) := mt Real.summable_nat_pow_inv.1 (lt_irrefl 1)
  simpa
#align real.not_summable_nat_cast_inv Real.not_summable_nat_cast_inv

/- warning: real.not_summable_one_div_nat_cast -> Real.not_summable_one_div_nat_cast is a dubious translation:
lean 3 declaration is
  Not (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))
but is expected to have type
  Not (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Nat.cast.{0} Real Real.natCast n)))
Case conversion may be inaccurate. Consider using '#align real.not_summable_one_div_nat_cast Real.not_summable_one_div_nat_castₓ'. -/
/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_one_div_nat_cast : ¬Summable (fun n => 1 / n : ℕ → ℝ) := by
  simpa only [inv_eq_one_div] using Real.not_summable_nat_cast_inv
#align real.not_summable_one_div_nat_cast Real.not_summable_one_div_nat_cast

/- warning: real.tendsto_sum_range_one_div_nat_succ_at_top -> Real.tendsto_sum_range_one_div_nat_succ_atTop is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) i) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast i) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.tendsto_sum_range_one_div_nat_succ_at_top Real.tendsto_sum_range_one_div_nat_succ_atTopₓ'. -/
/-- **Divergence of the Harmonic Series** -/
theorem Real.tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i in Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop :=
  by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_nat_cast
  · exact fun i => div_nonneg zero_le_one i.cast_add_one_pos.le
#align real.tendsto_sum_range_one_div_nat_succ_at_top Real.tendsto_sum_range_one_div_nat_succ_atTop

/- warning: nnreal.summable_rpow_inv -> NNReal.summable_rpow_inv is a dubious translation:
lean 3 declaration is
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : Nat) => Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n) p))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)
but is expected to have type
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : Nat) => Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n) p))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_rpow_inv NNReal.summable_rpow_invₓ'. -/
@[simp]
theorem NNReal.summable_rpow_inv {p : ℝ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p := by
  simp [← NNReal.summable_coe]
#align nnreal.summable_rpow_inv NNReal.summable_rpow_inv

/- warning: nnreal.summable_rpow -> NNReal.summable_rpow is a dubious translation:
lean 3 declaration is
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : Nat) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n) p)) (LT.lt.{0} Real Real.hasLt p (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : Nat) => HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n) p)) (LT.lt.{0} Real Real.instLTReal p (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align nnreal.summable_rpow NNReal.summable_rpowₓ'. -/
@[simp]
theorem NNReal.summable_rpow {p : ℝ} : Summable (fun n => n ^ p : ℕ → ℝ≥0) ↔ p < -1 := by
  simp [← NNReal.summable_coe]
#align nnreal.summable_rpow NNReal.summable_rpow

/- warning: nnreal.summable_one_div_rpow -> NNReal.summable_one_div_rpow is a dubious translation:
lean 3 declaration is
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)) NNReal.topologicalSpace (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n) p))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) p)
but is expected to have type
  forall {p : Real}, Iff (Summable.{0, 0} NNReal Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal instNNRealStrictOrderedSemiring)) NNReal.instTopologicalSpaceNNReal (fun (n : Nat) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.instPowNNRealReal) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n) p))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) p)
Case conversion may be inaccurate. Consider using '#align nnreal.summable_one_div_rpow NNReal.summable_one_div_rpowₓ'. -/
theorem NNReal.summable_one_div_rpow {p : ℝ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ≥0) ↔ 1 < p := by
  simp
#align nnreal.summable_one_div_rpow NNReal.summable_one_div_rpow

section

open Finset

variable {α : Type _} [LinearOrderedField α]

/- warning: sum_Ioc_inv_sq_le_sub -> sum_Ioc_inv_sq_le_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] {k : Nat} {n : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (LE.le.{0} Nat Nat.hasLe k n) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder k n) (fun (i : Nat) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))))))) i) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))))))) k)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))))))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] {k : Nat} {n : Nat}, (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LE.le.{0} Nat instLENat k n) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.sum.{u1, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring k n) (fun (i : Nat) => Inv.inv.{u1} α (LinearOrderedField.toInv.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) i (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) (Inv.inv.{u1} α (LinearOrderedField.toInv.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) k)) (Inv.inv.{u1} α (LinearOrderedField.toInv.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) n))))
Case conversion may be inaccurate. Consider using '#align sum_Ioc_inv_sq_le_sub sum_Ioc_inv_sq_le_subₓ'. -/
theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (∑ i in Ioc k n, ((i ^ 2)⁻¹ : α)) ≤ k⁻¹ - n⁻¹ :=
  by
  refine' Nat.le_induction _ _ n h
  · simp only [Ioc_self, sum_empty, sub_self]
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  apply (add_le_add IH le_rfl).trans
  simp only [sub_eq_add_neg, add_assoc, Nat.cast_add, Nat.cast_one, le_add_neg_iff_add_le,
    add_le_iff_nonpos_right, neg_add_le_iff_le_add, add_zero]
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  have B : 0 < (n : α) + 1 := by linarith
  field_simp [B.ne']
  rw [div_le_div_iff _ A, ← sub_nonneg]
  · ring_nf; exact B.le
  · nlinarith
#align sum_Ioc_inv_sq_le_sub sum_Ioc_inv_sq_le_sub

/- warning: sum_Ioo_inv_sq_le -> sum_Ioo_inv_sq_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] (k : Nat) (n : Nat), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder k n) (fun (i : Nat) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))))))) i) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1)))))))))) k) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] (k : Nat) (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (Finset.sum.{u1, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring k n) (fun (i : Nat) => Inv.inv.{u1} α (LinearOrderedField.toInv.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) i (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedField.toDiv.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))) k) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align sum_Ioo_inv_sq_le sum_Ioo_inv_sq_leₓ'. -/
theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i in Ioo k n, ((i ^ 2)⁻¹ : α)) ≤ 2 / (k + 1) :=
  calc
    (∑ i in Ioo k n, ((i ^ 2)⁻¹ : α)) ≤ ∑ i in Ioc k (max (k + 1) n), (i ^ 2)⁻¹ :=
      by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true_iff, and_self_iff]
      · intro i hi hident
        exact inv_nonneg.2 (sq_nonneg _)
    _ ≤ ((k + 1) ^ 2)⁻¹ + ∑ i in Ioc k.succ (max (k + 1) n), (i ^ 2)⁻¹ :=
      by
      rw [← Nat.Icc_succ_left, ← Nat.Ico_succ_right, sum_eq_sum_Ico_succ_bot]
      swap; · exact Nat.succ_lt_succ ((Nat.lt_succ_self k).trans_le (le_max_left _ _))
      rw [Nat.Ico_succ_right, Nat.Icc_succ_left, Nat.cast_succ]
    _ ≤ ((k + 1) ^ 2)⁻¹ + (k + 1)⁻¹ :=
      by
      refine' add_le_add le_rfl ((sum_Ioc_inv_sq_le_sub _ (le_max_left _ _)).trans _)
      · simp only [Ne.def, Nat.succ_ne_zero, not_false_iff]
      · simp only [Nat.cast_succ, one_div, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
    _ ≤ 1 / (k + 1) + 1 / (k + 1) :=
      by
      have A : (1 : α) ≤ k + 1 := by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      simp_rw [← one_div]
      apply add_le_add_right
      refine' div_le_div zero_le_one le_rfl (zero_lt_one.trans_le A) _
      simpa using pow_le_pow A one_le_two
    _ = 2 / (k + 1) := by ring
    
#align sum_Ioo_inv_sq_le sum_Ioo_inv_sq_le

end

