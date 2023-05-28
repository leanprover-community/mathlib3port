/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module analysis.hofer
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# Hofer's lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/


open Classical Topology BigOperators

open Filter Finset

-- mathport name: exprd
local notation "d" => dist

/- warning: pos_div_pow_pos -> pos_div_pow_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) b) -> (forall (k : Nat), LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1))))))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))))) b k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedSemifield.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) b) -> (forall (k : Nat), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (LinearOrderedSemifield.toDiv.{u1} α _inst_1)) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α _inst_1)))))))) b k)))
Case conversion may be inaccurate. Consider using '#align pos_div_pow_pos pos_div_pow_posₓ'. -/
@[simp]
theorem pos_div_pow_pos {α : Type _} [LinearOrderedSemifield α] {a b : α} (ha : 0 < a) (hb : 0 < b)
    (k : ℕ) : 0 < a / b ^ k :=
  div_pos ha (pow_pos hb k)
#align pos_div_pow_pos pos_div_pow_pos

/- warning: hofer -> hofer is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : MetricSpace.{u1} X] [_inst_2 : CompleteSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1))] (x : X) (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall {ϕ : X -> Real}, (Continuous.{u1, 0} X Real (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ϕ) -> (forall (y : X), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (ϕ y)) -> (Exists.{1} Real (fun (ε' : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε' (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε' (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => Exists.{succ u1} X (fun (x' : X) => And (LE.le.{0} Real Real.hasLe ε' ε) (And (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} X (PseudoMetricSpace.toHasDist.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1)) x' x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ε)) (And (LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ε (ϕ x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ε' (ϕ x'))) (forall (y : X), (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} X (PseudoMetricSpace.toHasDist.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1)) x' y) ε') -> (LE.le.{0} Real Real.hasLe (ϕ y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (ϕ x')))))))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : MetricSpace.{u1} X] [_inst_2 : CompleteSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1))] (x : X) (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall {ϕ : X -> Real}, (Continuous.{u1, 0} X Real (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ϕ) -> (forall (y : X), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (ϕ y)) -> (Exists.{1} Real (fun (ε' : Real) => And (GT.gt.{0} Real Real.instLTReal ε' (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Exists.{succ u1} X (fun (x' : X) => And (LE.le.{0} Real Real.instLEReal ε' ε) (And (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} X (PseudoMetricSpace.toDist.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1)) x' x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) ε)) (And (LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) ε (ϕ x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) ε' (ϕ x'))) (forall (y : X), (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} X (PseudoMetricSpace.toDist.{u1} X (MetricSpace.toPseudoMetricSpace.{u1} X _inst_1)) x' y) ε') -> (LE.le.{0} Real Real.instLEReal (ϕ y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (ϕ x')))))))))))
Case conversion may be inaccurate. Consider using '#align hofer hoferₓ'. -/
theorem hofer {X : Type _} [MetricSpace X] [CompleteSpace X] (x : X) (ε : ℝ) (ε_pos : 0 < ε)
    {ϕ : X → ℝ} (cont : Continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) :
    ∃ ε' > 0,
      ∃ x' : X, ε' ≤ ε ∧ d x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧ ∀ y, d x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' :=
  by
  by_contra H
  have reformulation : ∀ (x') (k : ℕ), ε * ϕ x ≤ ε / 2 ^ k * ϕ x' ↔ 2 ^ k * ϕ x ≤ ϕ x' :=
    by
    intro x' k
    rw [div_mul_eq_mul_div, le_div_iff, mul_assoc, mul_le_mul_left ε_pos, mul_comm]
    positivity
  -- Now let's specialize to `ε/2^k`
  replace H :
    ∀ k : ℕ, ∀ x', d x' x ≤ 2 * ε ∧ 2 ^ k * ϕ x ≤ ϕ x' → ∃ y, d x' y ≤ ε / 2 ^ k ∧ 2 * ϕ x' < ϕ y
  · intro k x'
    push_neg  at H
    simpa [reformulation] using H (ε / 2 ^ k) (by simp [ε_pos]) x' (by simp [ε_pos.le, one_le_two])
  clear reformulation
  haveI : Nonempty X := ⟨x⟩
  choose! F hF using H
  -- Use the axiom of choice
  -- Now define u by induction starting at x, with u_{n+1} = F(n, u_n)
  let u : ℕ → X := fun n => Nat.recOn n x F
  have hu0 : u 0 = x := rfl
  -- The properties of F translate to properties of u
  have hu :
    ∀ n,
      d (u n) x ≤ 2 * ε ∧ 2 ^ n * ϕ x ≤ ϕ (u n) →
        d (u n) (u <| n + 1) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u <| n + 1) :=
    by
    intro n
    exact hF n (u n)
  clear hF
  -- Key properties of u, to be proven by induction
  have key : ∀ n, d (u n) (u (n + 1)) ≤ ε / 2 ^ n ∧ 2 * ϕ (u n) < ϕ (u (n + 1)) :=
    by
    intro n
    induction' n using Nat.case_strong_induction_on with n IH
    · specialize hu 0
      simpa [hu0, mul_nonneg_iff, zero_le_one, ε_pos.le, le_refl] using hu
    have A : d (u (n + 1)) x ≤ 2 * ε := by
      rw [dist_comm]
      let r := range (n + 1)
      -- range (n+1) = {0, ..., n}
      calc
        d (u 0) (u (n + 1)) ≤ ∑ i in r, d (u i) (u <| i + 1) := dist_le_range_sum_dist u (n + 1)
        _ ≤ ∑ i in r, ε / 2 ^ i :=
          (sum_le_sum fun i i_in => (IH i <| nat.lt_succ_iff.mp <| finset.mem_range.mp i_in).1)
        _ = ∑ i in r, (1 / 2) ^ i * ε := by congr with i; field_simp
        _ = (∑ i in r, (1 / 2) ^ i) * ε := finset.sum_mul.symm
        _ ≤ 2 * ε := mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (le_of_lt ε_pos)
        
    have B : 2 ^ (n + 1) * ϕ x ≤ ϕ (u (n + 1)) :=
      by
      refine' @geom_le (ϕ ∘ u) _ zero_le_two (n + 1) fun m hm => _
      exact (IH _ <| Nat.lt_add_one_iff.1 hm).2.le
    exact hu (n + 1) ⟨A, B⟩
  cases' forall_and_distrib.mp key with key₁ key₂
  clear hu key
  -- Hence u is Cauchy
  have cauchy_u : CauchySeq u :=
    by
    refine' cauchySeq_of_le_geometric _ ε one_half_lt_one fun n => _
    simpa only [one_div, inv_pow] using key₁ n
  -- So u converges to some y
  obtain ⟨y, limy⟩ : ∃ y, tendsto u at_top (𝓝 y)
  exact CompleteSpace.complete cauchy_u
  -- And ϕ ∘ u goes to +∞
  have lim_top : tendsto (ϕ ∘ u) at_top at_top :=
    by
    let v n := (ϕ ∘ u) (n + 1)
    suffices tendsto v at_top at_top by rwa [tendsto_add_at_top_iff_nat] at this
    have hv₀ : 0 < v 0 := by
      have : 0 ≤ ϕ (u 0) := nonneg x
      calc
        0 ≤ 2 * ϕ (u 0) := by linarith
        _ < ϕ (u (0 + 1)) := key₂ 0
        
    apply tendsto_atTop_of_geom_le hv₀ one_lt_two
    exact fun n => (key₂ (n + 1)).le
  -- But ϕ ∘ u also needs to go to ϕ(y)
  have lim : tendsto (ϕ ∘ u) at_top (𝓝 (ϕ y)) := tendsto.comp cont.continuous_at limy
  -- So we have our contradiction!
  exact not_tendsto_atTop_of_tendsto_nhds limUnder lim_top
#align hofer hofer

