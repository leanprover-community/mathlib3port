/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.mutually_singular
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-! # Mutually singular measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Two measures `μ`, `ν` are said to be mutually singular (`measure_theory.measure.mutually_singular`,
localized notation `μ ⟂ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`measure_theory.measure.mutually_singular.mk`) but we keep it because this way `rcases (h : μ ⟂ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `measure_theory.measure.mutually_singular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/


open Set

open MeasureTheory NNReal ENNReal

namespace MeasureTheory

namespace Measure

variable {α : Type _} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

#print MeasureTheory.Measure.MutuallySingular /-
/-- Two measures `μ`, `ν` are said to be mutually singular if there exists a measurable set `s`
such that `μ s = 0` and `ν sᶜ = 0`. -/
def MutuallySingular {m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν (sᶜ) = 0
#align measure_theory.measure.mutually_singular MeasureTheory.Measure.MutuallySingular
-/

-- mathport name: measure.mutually_singular
scoped[MeasureTheory] infixl:60 " ⟂ₘ " => MeasureTheory.Measure.MutuallySingular

namespace MutuallySingular

/- warning: measure_theory.measure.mutually_singular.mk -> MeasureTheory.Measure.MutuallySingular.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) ν t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.univ.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 μ ν)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 ν) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.univ.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 μ ν)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.mutually_singular.mk MeasureTheory.Measure.MutuallySingular.mkₓ'. -/
theorem mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ ⊆ s ∪ t) :
    MutuallySingular μ ν :=
  by
  use to_measurable μ s, measurable_set_to_measurable _ _, (measure_to_measurable _).trans hs
  refine' measure_mono_null (fun x hx => (hst trivial).resolve_left fun hxs => hx _) ht
  exact subset_to_measurable _ _ hxs
#align measure_theory.measure.mutually_singular.mk MeasureTheory.Measure.MutuallySingular.mk

#print MeasureTheory.Measure.MutuallySingular.zero_right /-
@[simp]
theorem zero_right : μ ⟂ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩
#align measure_theory.measure.mutually_singular.zero_right MeasureTheory.Measure.MutuallySingular.zero_right
-/

#print MeasureTheory.Measure.MutuallySingular.symm /-
@[symm]
theorem symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
  let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩
#align measure_theory.measure.mutually_singular.symm MeasureTheory.Measure.MutuallySingular.symm
-/

#print MeasureTheory.Measure.MutuallySingular.comm /-
theorem comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align measure_theory.measure.mutually_singular.comm MeasureTheory.Measure.MutuallySingular.comm
-/

#print MeasureTheory.Measure.MutuallySingular.zero_left /-
@[simp]
theorem zero_left : 0 ⟂ₘ μ :=
  zero_right.symm
#align measure_theory.measure.mutually_singular.zero_left MeasureTheory.Measure.MutuallySingular.zero_left
-/

#print MeasureTheory.Measure.MutuallySingular.mono_ac /-
theorem mono_ac (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂ :=
  let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩
#align measure_theory.measure.mutually_singular.mono_ac MeasureTheory.Measure.MutuallySingular.mono_ac
-/

#print MeasureTheory.Measure.MutuallySingular.mono /-
theorem mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
  h.mono_ac hμ.AbsolutelyContinuous hν.AbsolutelyContinuous
#align measure_theory.measure.mutually_singular.mono MeasureTheory.Measure.MutuallySingular.mono
-/

#print MeasureTheory.Measure.MutuallySingular.sum_left /-
@[simp]
theorem sum_left {ι : Type _} [Countable ι] {μ : ι → Measure α} : sum μ ⟂ₘ ν ↔ ∀ i, μ i ⟂ₘ ν :=
  by
  refine' ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => _⟩
  choose s hsm hsμ hsν using H
  refine' ⟨⋂ i, s i, MeasurableSet.iInter hsm, _, _⟩
  · rw [sum_apply _ (MeasurableSet.iInter hsm), ENNReal.tsum_eq_zero]
    exact fun i => measure_mono_null (Inter_subset _ _) (hsμ i)
  · rwa [compl_Inter, measure_Union_null_iff]
#align measure_theory.measure.mutually_singular.sum_left MeasureTheory.Measure.MutuallySingular.sum_left
-/

#print MeasureTheory.Measure.MutuallySingular.sum_right /-
@[simp]
theorem sum_right {ι : Type _} [Countable ι] {ν : ι → Measure α} : μ ⟂ₘ sum ν ↔ ∀ i, μ ⟂ₘ ν i :=
  comm.trans <| sum_left.trans <| forall_congr' fun i => comm
#align measure_theory.measure.mutually_singular.sum_right MeasureTheory.Measure.MutuallySingular.sum_right
-/

#print MeasureTheory.Measure.MutuallySingular.add_left_iff /-
@[simp]
theorem add_left_iff : μ₁ + μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν := by
  rw [← sum_cond, sum_left, Bool.forall_bool, cond, cond, and_comm]
#align measure_theory.measure.mutually_singular.add_left_iff MeasureTheory.Measure.MutuallySingular.add_left_iff
-/

#print MeasureTheory.Measure.MutuallySingular.add_right_iff /-
@[simp]
theorem add_right_iff : μ ⟂ₘ ν₁ + ν₂ ↔ μ ⟂ₘ ν₁ ∧ μ ⟂ₘ ν₂ :=
  comm.trans <| add_left_iff.trans <| and_congr comm comm
#align measure_theory.measure.mutually_singular.add_right_iff MeasureTheory.Measure.MutuallySingular.add_right_iff
-/

#print MeasureTheory.Measure.MutuallySingular.add_left /-
theorem add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
  add_left_iff.2 ⟨h₁, h₂⟩
#align measure_theory.measure.mutually_singular.add_left MeasureTheory.Measure.MutuallySingular.add_left
-/

#print MeasureTheory.Measure.MutuallySingular.add_right /-
theorem add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
  add_right_iff.2 ⟨h₁, h₂⟩
#align measure_theory.measure.mutually_singular.add_right MeasureTheory.Measure.MutuallySingular.add_right
-/

/- warning: measure_theory.measure.mutually_singular.smul -> MeasureTheory.Measure.MutuallySingular.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} (r : ENNReal), (MeasureTheory.Measure.MutuallySingular.{u1} α m0 ν μ) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m0) r ν) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} (r : ENNReal), (MeasureTheory.Measure.MutuallySingular.{u1} α m0 ν μ) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.{u1} α m0) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m0)) r ν) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.mutually_singular.smul MeasureTheory.Measure.MutuallySingular.smulₓ'. -/
theorem smul (r : ℝ≥0∞) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.mono_ac (AbsolutelyContinuous.rfl.smul r) AbsolutelyContinuous.rfl
#align measure_theory.measure.mutually_singular.smul MeasureTheory.Measure.MutuallySingular.smul

/- warning: measure_theory.measure.mutually_singular.smul_nnreal -> MeasureTheory.Measure.MutuallySingular.smul_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} (r : NNReal), (MeasureTheory.Measure.MutuallySingular.{u1} α m0 ν μ) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 (SMul.smul.{0, u1} NNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instSMul.{u1, 0} α NNReal (MulAction.toHasSmul.{0, 0} NNReal ENNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)) (ENNReal.mulAction.{0} ENNReal (Monoid.toMulAction.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (ENNReal.isScalarTower.{0, 0} ENNReal ENNReal (Monoid.toMulAction.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Monoid.toMulAction.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) m0) r ν) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {ν : MeasureTheory.Measure.{u1} α m0} (r : NNReal), (MeasureTheory.Measure.MutuallySingular.{u1} α m0 ν μ) -> (MeasureTheory.Measure.MutuallySingular.{u1} α m0 (HSMul.hSMul.{0, u1, u1} NNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.{u1} α m0) (instHSMul.{0, u1} NNReal (MeasureTheory.Measure.{u1} α m0) (MeasureTheory.Measure.instSMul.{u1, 0} α NNReal (Algebra.toSMul.{0, 0} NNReal ENNReal instNNRealCommSemiring (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (ENNReal.instAlgebraNNRealInstNNRealCommSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (ENNReal.instIsScalarTowerNNRealToSMulToMonoidToMonoidWithZeroInstNNRealSemiringInstMulActionNNRealToMonoidToMonoidWithZeroInstNNRealSemiringToSMulInstMulActionNNRealToMonoidToMonoidWithZeroInstNNRealSemiring.{0, 0} ENNReal ENNReal (MulActionWithZero.toMulAction.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) instENNRealZero (MonoidWithZero.toMulActionWithZero.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))) (MulActionWithZero.toMulAction.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) instENNRealZero (MonoidWithZero.toMulActionWithZero.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))) (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) m0)) r ν) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.mutually_singular.smul_nnreal MeasureTheory.Measure.MutuallySingular.smul_nnrealₓ'. -/
theorem smul_nnreal (r : ℝ≥0) (h : ν ⟂ₘ μ) : r • ν ⟂ₘ μ :=
  h.smul r
#align measure_theory.measure.mutually_singular.smul_nnreal MeasureTheory.Measure.MutuallySingular.smul_nnreal

end MutuallySingular

end Measure

end MeasureTheory

