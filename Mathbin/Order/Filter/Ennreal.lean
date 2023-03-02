/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module order.filter.ennreal
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Ennreal
import Mathbin.Order.Filter.CountableInter
import Mathbin.Order.LiminfLimsup

/-!
# Order properties of extended non-negative reals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file compiles filter-related results about `ℝ≥0∞` (see data/real/ennreal.lean).
-/


open Filter

open Filter ENNReal

namespace ENNReal

variable {α : Type _} {f : Filter α}

/- warning: ennreal.eventually_le_limsup -> ENNReal.eventually_le_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal), Filter.Eventually.{u1} α (fun (y : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (u y) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f)) f
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal), Filter.Eventually.{u1} α (fun (y : α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (u y) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f)) f
Case conversion may be inaccurate. Consider using '#align ennreal.eventually_le_limsup ENNReal.eventually_le_limsupₓ'. -/
theorem eventually_le_limsup [CountableInterFilter f] (u : α → ℝ≥0∞) :
    ∀ᶠ y in f, u y ≤ f.limsup u :=
  by
  by_cases hx_top : f.limsup u = ⊤
  · simp_rw [hx_top]
    exact eventually_of_forall fun a => le_top
  have h_forall_le : ∀ᶠ y in f, ∀ n : ℕ, u y < f.limsup u + (1 : ℝ≥0∞) / n :=
    by
    rw [eventually_countable_forall]
    refine' fun n => eventually_lt_of_limsup_lt _
    nth_rw 1 [← add_zero (f.limsup u)]
    exact (ENNReal.add_lt_add_iff_left hx_top).mpr (by simp)
  refine' h_forall_le.mono fun y hy => le_of_forall_pos_le_add fun r hr_pos hx_top => _
  have hr_ne_zero : (r : ℝ≥0∞) ≠ 0 := by
    rw [Ne.def, coe_eq_zero]
    exact (ne_of_lt hr_pos).symm
  cases' exists_inv_nat_lt hr_ne_zero with i hi
  rw [inv_eq_one_div] at hi
  exact (hy i).le.trans (add_le_add_left hi.le (f.limsup u))
#align ennreal.eventually_le_limsup ENNReal.eventually_le_limsup

/- warning: ennreal.limsup_eq_zero_iff -> ENNReal.limsup_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] {u : α -> ENNReal}, Iff (Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Filter.EventuallyEq.{u1, 0} α ENNReal f u (OfNat.ofNat.{u1} (α -> ENNReal) 0 (OfNat.mk.{u1} (α -> ENNReal) 0 (Zero.zero.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] {u : α -> ENNReal}, Iff (Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Filter.EventuallyEq.{u1, 0} α ENNReal f u (OfNat.ofNat.{u1} (α -> ENNReal) 0 (Zero.toOfNat0.{u1} (α -> ENNReal) (Pi.instZero.{u1, 0} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19139 : α) => ENNReal) (fun (i : α) => instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_eq_zero_iff ENNReal.limsup_eq_zero_iffₓ'. -/
theorem limsup_eq_zero_iff [CountableInterFilter f] {u : α → ℝ≥0∞} : f.limsup u = 0 ↔ u =ᶠ[f] 0 :=
  by
  constructor <;> intro h
  · have hu_zero :=
      eventually_le.trans (eventually_le_limsup u) (eventually_of_forall fun _ => le_of_eq h)
    exact hu_zero.mono fun x hx => le_antisymm hx (zero_le _)
  · rw [limsup_congr h]
    simp_rw [Pi.zero_apply, ← ENNReal.bot_eq_zero, limsup_const_bot]
#align ennreal.limsup_eq_zero_iff ENNReal.limsup_eq_zero_iff

/- warning: ennreal.limsup_const_mul_of_ne_top -> ENNReal.limsup_const_mul_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toHasTop.{0} ENNReal ENNReal.linearOrderedAddCommMonoidWithTop))) -> (Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (u x)) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f)))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} {u : α -> ENNReal} {a : ENNReal}, (Ne.{1} ENNReal a (Top.top.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toTop.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal))) -> (Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (u x)) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f)))
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_const_mul_of_ne_top ENNReal.limsup_const_mul_of_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_const_mul_of_ne_top {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha_top : a ≠ ⊤) :
    (f.limsup fun x : α => a * u x) = a * f.limsup u :=
  by
  by_cases ha_zero : a = 0
  · simp_rw [ha_zero, zero_mul, ← ENNReal.bot_eq_zero]
    exact limsup_const_bot
  let g := fun x : ℝ≥0∞ => a * x
  have hg_bij : Function.Bijective g :=
    function.bijective_iff_has_inverse.mpr
      ⟨fun x => a⁻¹ * x,
        ⟨fun x => by simp [← mul_assoc, ENNReal.inv_mul_cancel ha_zero ha_top], fun x => by
          simp [g, ← mul_assoc, ENNReal.mul_inv_cancel ha_zero ha_top]⟩⟩
  have hg_mono : StrictMono g :=
    Monotone.strictMono_of_injective (fun _ _ _ => by rwa [mul_le_mul_left ha_zero ha_top]) hg_bij.1
  let g_iso := StrictMono.orderIsoOfSurjective g hg_mono hg_bij.2
  refine' (OrderIso.limsup_apply g_iso _ _ _ _).symm
  all_goals
    run_tac
      is_bounded_default
#align ennreal.limsup_const_mul_of_ne_top ENNReal.limsup_const_mul_of_ne_top

/- warning: ennreal.limsup_const_mul -> ENNReal.limsup_const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] {u : α -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (u x)) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) a (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] {u : α -> ENNReal} {a : ENNReal}, Eq.{1} ENNReal (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (x : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (u x)) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) a (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f))
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_const_mul ENNReal.limsup_const_mulₓ'. -/
theorem limsup_const_mul [CountableInterFilter f] {u : α → ℝ≥0∞} {a : ℝ≥0∞} :
    (f.limsup fun x : α => a * u x) = a * f.limsup u :=
  by
  by_cases ha_top : a ≠ ⊤
  · exact limsup_const_mul_of_ne_top ha_top
  push_neg  at ha_top
  by_cases hu : u =ᶠ[f] 0
  · have hau : (fun x => a * u x) =ᶠ[f] 0 :=
      by
      refine' hu.mono fun x hx => _
      rw [Pi.zero_apply] at hx
      simp [hx]
    simp only [limsup_congr hu, limsup_congr hau, Pi.zero_apply, ← bot_eq_zero, limsup_const_bot]
    simp
  · simp_rw [ha_top, top_mul]
    have hu_mul : ∃ᶠ x : α in f, ⊤ ≤ ite (u x = 0) (0 : ℝ≥0∞) ⊤ :=
      by
      rw [eventually_eq, not_eventually] at hu
      refine' hu.mono fun x hx => _
      rw [Pi.zero_apply] at hx
      simp [hx]
    have h_top_le : (f.limsup fun x : α => ite (u x = 0) (0 : ℝ≥0∞) ⊤) = ⊤ :=
      eq_top_iff.mpr (le_limsup_of_frequently_le hu_mul)
    have hfu : f.limsup u ≠ 0 := mt limsup_eq_zero_iff.1 hu
    simp only [h_top_le, hfu, if_false]
#align ennreal.limsup_const_mul ENNReal.limsup_const_mul

/- warning: ennreal.limsup_mul_le -> ENNReal.limsup_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal) (v : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) u v) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) v f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal) (v : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (HMul.hMul.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHMul.{u1} (α -> ENNReal) (Pi.instMul.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) u v) f) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) v f))
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_mul_le ENNReal.limsup_mul_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_mul_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u * v) ≤ f.limsup u * f.limsup v :=
  calc
    f.limsup (u * v) ≤ f.limsup fun x => f.limsup u * v x :=
      by
      refine' limsup_le_limsup _ _
      · filter_upwards [@eventually_le_limsup _ f _ u]with x hx using mul_le_mul_right' hx _
      ·
        run_tac
          is_bounded_default
    _ = f.limsup u * f.limsup v := limsup_const_mul
    
#align ennreal.limsup_mul_le ENNReal.limsup_mul_le

/- warning: ennreal.limsup_add_le -> ENNReal.limsup_add_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal) (v : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) u v) f) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) u f) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) v f))
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α f] (u : α -> ENNReal) (v : α -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) u v) f) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) u f) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) v f))
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_add_le ENNReal.limsup_add_leₓ'. -/
theorem limsup_add_le [CountableInterFilter f] (u v : α → ℝ≥0∞) :
    f.limsup (u + v) ≤ f.limsup u + f.limsup v :=
  infₛ_le
    ((eventually_le_limsup u).mp
      ((eventually_le_limsup v).mono fun _ hxg hxf => add_le_add hxf hxg))
#align ennreal.limsup_add_le ENNReal.limsup_add_le

/- warning: ennreal.limsup_liminf_le_liminf_limsup -> ENNReal.limsup_liminf_le_liminf_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] {f : Filter.{u1} α} [_inst_2 : CountableInterFilter.{u1} α f] {g : Filter.{u2} β} (u : α -> β -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (a : α) => Filter.liminf.{0, u2} ENNReal β (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (b : β) => u a b) g) f) (Filter.liminf.{0, u2} ENNReal β (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (b : β) => Filter.limsup.{0, u1} ENNReal α (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)) (fun (a : α) => u a b) f) g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Countable.{succ u2} β] {f : Filter.{u1} α} [_inst_2 : CountableInterFilter.{u1} α f] {g : Filter.{u2} β} (u : α -> β -> ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (a : α) => Filter.liminf.{0, u2} ENNReal β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (b : β) => u a b) g) f) (Filter.liminf.{0, u2} ENNReal β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (b : β) => Filter.limsup.{0, u1} ENNReal α (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) (fun (a : α) => u a b) f) g)
Case conversion may be inaccurate. Consider using '#align ennreal.limsup_liminf_le_liminf_limsup ENNReal.limsup_liminf_le_liminf_limsupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_liminf_le_liminf_limsup {β} [Countable β] {f : Filter α} [CountableInterFilter f]
    {g : Filter β} (u : α → β → ℝ≥0∞) :
    (f.limsup fun a : α => g.liminf fun b : β => u a b) ≤
      g.liminf fun b => f.limsup fun a => u a b :=
  by
  have h1 : ∀ᶠ a in f, ∀ b, u a b ≤ f.limsup fun a' => u a' b :=
    by
    rw [eventually_countable_forall]
    exact fun b => ENNReal.eventually_le_limsup fun a => u a b
  refine' infₛ_le (h1.mono fun x hx => Filter.liminf_le_liminf (Filter.eventually_of_forall hx) _)
  run_tac
    filter.is_bounded_default
#align ennreal.limsup_liminf_le_liminf_limsup ENNReal.limsup_liminf_le_liminf_limsup

end ENNReal

