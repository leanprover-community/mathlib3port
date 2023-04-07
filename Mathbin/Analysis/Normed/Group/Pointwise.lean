/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.group.pointwise
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set

open Pointwise Topology

variable {E : Type _}

section SeminormedGroup

variable [SeminormedGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

/- warning: metric.bounded.mul -> Metric.Bounded.mul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E} {t : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) t) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1))))))) s t))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E} {t : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) t) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1))))))) s t))
Case conversion may be inaccurate. Consider using '#align metric.bounded.mul Metric.Bounded.mulₓ'. -/
@[to_additive]
theorem Metric.Bounded.mul (hs : Bounded s) (ht : Bounded t) : Bounded (s * t) :=
  by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  refine' bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy)
#align metric.bounded.mul Metric.Bounded.mul
#align metric.bounded.add Metric.Bounded.add

/- warning: metric.bounded.inv -> Metric.Bounded.inv is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1)))) s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (Group.toDivisionMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1)))))) s))
Case conversion may be inaccurate. Consider using '#align metric.bounded.inv Metric.Bounded.invₓ'. -/
@[to_additive]
theorem Metric.Bounded.inv : Bounded s → Bounded s⁻¹ :=
  by
  simp_rw [bounded_iff_forall_norm_le', ← image_inv, ball_image_iff, norm_inv']
  exact id
#align metric.bounded.inv Metric.Bounded.inv
#align metric.bounded.neg Metric.Bounded.neg

/- warning: metric.bounded.div -> Metric.Bounded.div is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E} {t : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) t) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1))))) s t))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedGroup.{u1} E] {s : Set.{u1} E} {t : Set.{u1} E}, (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) s) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) t) -> (Metric.Bounded.{u1} E (SeminormedGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E _inst_1))))) s t))
Case conversion may be inaccurate. Consider using '#align metric.bounded.div Metric.Bounded.divₓ'. -/
@[to_additive]
theorem Metric.Bounded.div (hs : Bounded s) (ht : Bounded t) : Bounded (s / t) :=
  (div_eq_mul_inv _ _).symm.subst <| hs.mul ht.inv
#align metric.bounded.div Metric.Bounded.div
#align metric.bounded.sub Metric.Bounded.sub

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

section Emetric

open Emetric

#print infEdist_inv /-
@[to_additive]
theorem infEdist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ :=
  eq_of_forall_le_iff fun r => by simp_rw [le_inf_edist, ← image_inv, ball_image_iff, edist_inv]
#align inf_edist_inv infEdist_inv
#align inf_edist_neg infEdist_neg
-/

#print infEdist_inv_inv /-
@[simp, to_additive]
theorem infEdist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by
  rw [infEdist_inv, inv_inv]
#align inf_edist_inv_inv infEdist_inv_inv
#align inf_edist_neg_neg infEdist_neg_neg
-/

end Emetric

variable (ε δ s t x y)

#print inv_thickening /-
@[simp, to_additive]
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ :=
  by
  simp_rw [thickening, ← infEdist_inv]
  rfl
#align inv_thickening inv_thickening
#align neg_thickening neg_thickening
-/

#print inv_cthickening /-
@[simp, to_additive]
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ :=
  by
  simp_rw [cthickening, ← infEdist_inv]
  rfl
#align inv_cthickening inv_cthickening
#align neg_cthickening neg_cthickening
-/

/- warning: inv_ball -> inv_ball is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) δ)
Case conversion may be inaccurate. Consider using '#align inv_ball inv_ballₓ'. -/
@[simp, to_additive]
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ :=
  by
  simp_rw [ball, ← dist_inv]
  rfl
#align inv_ball inv_ball
#align neg_ball neg_ball

/- warning: inv_closed_ball -> inv_closedBall is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) δ)
Case conversion may be inaccurate. Consider using '#align inv_closed_ball inv_closedBallₓ'. -/
@[simp, to_additive]
theorem inv_closedBall : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  by
  simp_rw [closed_ball, ← dist_inv]
  rfl
#align inv_closed_ball inv_closedBall
#align neg_closed_ball neg_closedBall

/- warning: singleton_mul_ball -> singleton_mul_ball is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align singleton_mul_ball singleton_mul_ballₓ'. -/
@[to_additive]
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]
#align singleton_mul_ball singleton_mul_ball
#align singleton_add_ball singleton_add_ball

/- warning: singleton_div_ball -> singleton_div_ball is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align singleton_div_ball singleton_div_ballₓ'. -/
@[to_additive]
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]
#align singleton_div_ball singleton_div_ball
#align singleton_sub_ball singleton_sub_ball

/- warning: ball_mul_singleton -> ball_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) y)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) y)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align ball_mul_singleton ball_mul_singletonₓ'. -/
@[to_additive]
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]
#align ball_mul_singleton ball_mul_singleton
#align ball_add_singleton ball_add_singleton

/- warning: ball_div_singleton -> ball_div_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) y)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) y)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align ball_div_singleton ball_div_singletonₓ'. -/
@[to_additive]
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]
#align ball_div_singleton ball_div_singleton
#align ball_sub_singleton ball_sub_singleton

/- warning: singleton_mul_ball_one -> singleton_mul_ball_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align singleton_mul_ball_one singleton_mul_ball_oneₓ'. -/
@[to_additive]
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp
#align singleton_mul_ball_one singleton_mul_ball_one
#align singleton_add_ball_zero singleton_add_ball_zero

/- warning: singleton_div_ball_one -> singleton_div_ball_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align singleton_div_ball_one singleton_div_ball_oneₓ'. -/
@[to_additive]
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by simp [singleton_div_ball]
#align singleton_div_ball_one singleton_div_ball_one
#align singleton_sub_ball_zero singleton_sub_ball_zero

/- warning: ball_one_mul_singleton -> ball_one_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align ball_one_mul_singleton ball_one_mul_singletonₓ'. -/
@[to_additive]
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp [ball_mul_singleton]
#align ball_one_mul_singleton ball_one_mul_singleton
#align ball_zero_add_singleton ball_zero_add_singleton

/- warning: ball_one_div_singleton -> ball_one_div_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) δ)
Case conversion may be inaccurate. Consider using '#align ball_one_div_singleton ball_one_div_singletonₓ'. -/
@[to_additive]
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by simp [ball_div_singleton]
#align ball_one_div_singleton ball_one_div_singleton
#align ball_zero_sub_singleton ball_zero_sub_singleton

/- warning: smul_ball_one -> smul_ball_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align smul_ball_one smul_ball_oneₓ'. -/
@[to_additive]
theorem smul_ball_one : x • ball 1 δ = ball x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_ball_one smul_ball_one
#align vadd_ball_zero vadd_ball_zero

/- warning: singleton_mul_closed_ball -> singleton_mul_closedBall is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align singleton_mul_closed_ball singleton_mul_closedBallₓ'. -/
@[simp, to_additive]
theorem singleton_mul_closedBall : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp only [mul_comm y x, preimage_mul_closedBall, image_mul_left, singleton_mul, div_inv_eq_mul]
#align singleton_mul_closed_ball singleton_mul_closedBall
#align singleton_add_closed_ball singleton_add_closedBall

/- warning: singleton_div_closed_ball -> singleton_div_closedBall is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) y δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align singleton_div_closed_ball singleton_div_closedBallₓ'. -/
@[simp, to_additive]
theorem singleton_div_closedBall : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closedBall, singleton_mul_closedBall]
#align singleton_div_closed_ball singleton_div_closedBall
#align singleton_sub_closed_ball singleton_sub_closedBall

/- warning: closed_ball_mul_singleton -> closedBall_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) y)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) y)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HMul.hMul.{u1, u1, u1} E E E (instHMul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align closed_ball_mul_singleton closedBall_mul_singletonₓ'. -/
@[simp, to_additive]
theorem closedBall_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]
#align closed_ball_mul_singleton closedBall_mul_singleton
#align closed_ball_add_singleton closedBall_add_singleton

/- warning: closed_ball_div_singleton -> closedBall_div_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) y)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E) (y : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) y)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) x y) δ)
Case conversion may be inaccurate. Consider using '#align closed_ball_div_singleton closedBall_div_singletonₓ'. -/
@[simp, to_additive]
theorem closedBall_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]
#align closed_ball_div_singleton closedBall_div_singleton
#align closed_ball_sub_singleton closedBall_sub_singleton

/- warning: singleton_mul_closed_ball_one -> singleton_mul_closedBall_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align singleton_mul_closed_ball_one singleton_mul_closedBall_oneₓ'. -/
@[to_additive]
theorem singleton_mul_closedBall_one : {x} * closedBall 1 δ = closedBall x δ := by simp
#align singleton_mul_closed_ball_one singleton_mul_closedBall_one
#align singleton_add_closed_ball_zero singleton_add_closedBall_zero

/- warning: singleton_div_closed_ball_one -> singleton_div_closedBall_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align singleton_div_closed_ball_one singleton_div_closedBall_oneₓ'. -/
@[to_additive]
theorem singleton_div_closedBall_one : {x} / closedBall 1 δ = closedBall x δ := by simp
#align singleton_div_closed_ball_one singleton_div_closedBall_one
#align singleton_sub_closed_ball_zero singleton_sub_closedBall_zero

/- warning: closed_ball_one_mul_singleton -> closedBall_one_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align closed_ball_one_mul_singleton closedBall_one_mul_singletonₓ'. -/
@[to_additive]
theorem closedBall_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp
#align closed_ball_one_mul_singleton closedBall_one_mul_singleton
#align closed_ball_zero_add_singleton closedBall_zero_add_singleton

/- warning: closed_ball_one_div_singleton -> closedBall_one_div_singleton is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.hasSingleton.{u1} E) x)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) (Singleton.singleton.{u1, u1} E (Set.{u1} E) (Set.instSingletonSet.{u1} E) x)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) δ)
Case conversion may be inaccurate. Consider using '#align closed_ball_one_div_singleton closedBall_one_div_singletonₓ'. -/
@[to_additive]
theorem closedBall_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp
#align closed_ball_one_div_singleton closedBall_one_div_singleton
#align closed_ball_zero_sub_singleton closedBall_zero_sub_singleton

/- warning: vadd_closed_ball_zero -> vadd_closedBall_zero is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (VAdd.vadd.{u1, u1} E (Set.{u1} E) (Set.vaddSet.{u1, u1} E E (Add.toVAdd.{u1} E (AddZeroClass.toHasAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_2)))))))) x (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_2))))))))) δ)) (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HVAdd.hVAdd.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHVAdd.{u1, u1} E (Set.{u1} E) (Set.vaddSet.{u1, u1} E E (AddAction.toVAdd.{u1, u1} E E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_2)))) (AddMonoid.toAddAction.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (SeminormedAddGroup.toAddGroup.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E _inst_2)))))))) x (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))) δ)) (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) x δ)
Case conversion may be inaccurate. Consider using '#align vadd_closed_ball_zero vadd_closedBall_zeroₓ'. -/
-- This is the `to_additive` version of the below, but it will later follow as a special case of
-- `vadd_closed_ball` for `normed_add_torsor`s, so we give it higher simp priority.
-- (There is no `normed_mul_torsor`, hence the asymmetry between additive and multiplicative
-- versions.)
@[simp]
theorem vadd_closedBall_zero {E : Type _} [SeminormedAddCommGroup E] (δ : ℝ) (x : E) :
    x +ᵥ Metric.closedBall 0 δ = Metric.closedBall x δ :=
  by
  ext
  simp [mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, dist_eq_norm_sub]
#align vadd_closed_ball_zero vadd_closedBall_zero

/- warning: smul_closed_ball_one -> smul_closedBall_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (x : E), Eq.{succ u1} (Set.{u1} E) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)
Case conversion may be inaccurate. Consider using '#align smul_closed_ball_one smul_closedBall_oneₓ'. -/
@[simp]
theorem smul_closedBall_one : x • closedBall 1 δ = closedBall x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_closed_ball_one smul_closedBall_one

attribute [to_additive] smul_closedBall_one

/- warning: mul_ball_one -> mul_ball_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
Case conversion may be inaccurate. Consider using '#align mul_ball_one mul_ball_oneₓ'. -/
@[to_additive]
theorem mul_ball_one : s * ball 1 δ = thickening δ s :=
  by
  rw [thickening_eq_bUnion_ball]
  convert Union₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  exact s.bUnion_of_singleton.symm
  ext (x y)
  simp_rw [singleton_mul_ball, mul_one]
#align mul_ball_one mul_ball_one
#align add_ball_zero add_ball_zero

/- warning: div_ball_one -> div_ball_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
Case conversion may be inaccurate. Consider using '#align div_ball_one div_ball_oneₓ'. -/
@[to_additive]
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]
#align div_ball_one div_ball_one
#align sub_ball_zero sub_ball_zero

/- warning: ball_mul_one -> ball_mul_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) s) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) s) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)
Case conversion may be inaccurate. Consider using '#align ball_mul_one ball_mul_oneₓ'. -/
@[to_additive]
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]
#align ball_mul_one ball_mul_one
#align ball_add_zero ball_add_zero

/- warning: ball_div_one -> ball_div_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) s) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) s) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1))))))) s))
Case conversion may be inaccurate. Consider using '#align ball_div_one ball_div_oneₓ'. -/
@[to_additive]
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]
#align ball_div_one ball_div_one
#align ball_sub_zero ball_sub_zero

/- warning: mul_ball -> mul_ball is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align mul_ball mul_ballₓ'. -/
@[simp, to_additive]
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]
#align mul_ball mul_ball
#align add_ball add_ball

/- warning: div_ball -> div_ball is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align div_ball div_ballₓ'. -/
@[simp, to_additive]
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]
#align div_ball div_ball
#align sub_ball sub_ball

/- warning: ball_mul -> ball_mul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align ball_mul ball_mulₓ'. -/
@[simp, to_additive]
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]
#align ball_mul ball_mul
#align ball_add ball_add

/- warning: ball_div -> ball_div is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] (δ : Real) (s : Set.{u1} E) (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.ball.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.thickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1))))))) s)))
Case conversion may be inaccurate. Consider using '#align ball_div ball_divₓ'. -/
@[simp, to_additive]
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]
#align ball_div ball_div
#align ball_sub ball_sub

variable {ε δ s t x y}

/- warning: is_compact.mul_closed_ball_one -> IsCompact.mul_closedBall_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align is_compact.mul_closed_ball_one IsCompact.mul_closedBall_oneₓ'. -/
@[to_additive]
theorem IsCompact.mul_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall 1 δ = cthickening δ s :=
  by
  rw [hs.cthickening_eq_bUnion_closed_ball hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_Union, mem_closed_ball, exists_and_left,
    mem_closedBall_one_iff, ← eq_div_iff_mul_eq'', exists_eq_right]
#align is_compact.mul_closed_ball_one IsCompact.mul_closedBall_one
#align is_compact.add_closed_ball_zero IsCompact.add_closedBall_zero

/- warning: is_compact.div_closed_ball_one -> IsCompact.div_closedBall_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ)) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ)) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align is_compact.div_closed_ball_one IsCompact.div_closedBall_oneₓ'. -/
@[to_additive]
theorem IsCompact.div_closedBall_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closed_ball_one hδ]
#align is_compact.div_closed_ball_one IsCompact.div_closedBall_one
#align is_compact.sub_closed_ball_zero IsCompact.sub_closedBall_zero

/- warning: is_compact.closed_ball_one_mul -> IsCompact.closedBall_one_mul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) s) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) s) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s))
Case conversion may be inaccurate. Consider using '#align is_compact.closed_ball_one_mul IsCompact.closedBall_one_mulₓ'. -/
@[to_additive]
theorem IsCompact.closedBall_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_mul IsCompact.closedBall_one_mul
#align is_compact.closed_ball_zero_add IsCompact.closedBall_zero_add

/- warning: is_compact.closed_ball_one_div -> IsCompact.closedBall_one_div is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))))))) δ) s) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1))))) s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))))) δ) s) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ (Inv.inv.{u1} (Set.{u1} E) (Set.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1))))))) s)))
Case conversion may be inaccurate. Consider using '#align is_compact.closed_ball_one_div IsCompact.closedBall_one_divₓ'. -/
@[to_additive]
theorem IsCompact.closedBall_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_div IsCompact.closedBall_one_div
#align is_compact.closed_ball_zero_sub IsCompact.closedBall_zero_sub

/- warning: is_compact.mul_closed_ball -> IsCompact.mul_closedBall is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
Case conversion may be inaccurate. Consider using '#align is_compact.mul_closed_ball IsCompact.mul_closedBallₓ'. -/
@[to_additive]
theorem IsCompact.mul_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closedBall_one, mul_smul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.mul_closed_ball IsCompact.mul_closedBall
#align is_compact.add_closed_ball IsCompact.add_closedBall

/- warning: is_compact.div_closed_ball -> IsCompact.div_closedBall is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Inv.inv.{u1} E (DivInvMonoid.toHasInv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) x) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHDiv.{u1} (Set.{u1} E) (Set.div.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))) s (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ)) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Inv.inv.{u1} E (InvOneClass.toInv.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (DivisionCommMonoid.toDivisionMonoid.{u1} E (CommGroup.toDivisionCommMonoid.{u1} E (SeminormedCommGroup.toCommGroup.{u1} E _inst_1)))))) x) (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
Case conversion may be inaccurate. Consider using '#align is_compact.div_closed_ball IsCompact.div_closedBallₓ'. -/
@[to_additive]
theorem IsCompact.div_closedBall (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.mul_closed_ball hδ]
#align is_compact.div_closed_ball IsCompact.div_closedBall
#align is_compact.sub_closed_ball IsCompact.sub_closedBall

/- warning: is_compact.closed_ball_mul -> IsCompact.closedBall_mul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
Case conversion may be inaccurate. Consider using '#align is_compact.closed_ball_mul IsCompact.closedBall_mulₓ'. -/
@[to_additive]
theorem IsCompact.closedBall_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closed_ball hδ]
#align is_compact.closed_ball_mul IsCompact.closedBall_mul
#align is_compact.closed_ball_add IsCompact.closedBall_add

/- warning: is_compact.closed_ball_div -> IsCompact.closedBall_div is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (SMul.smul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (Mul.toSMul.{u1} E (MulOneClass.toHasMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : SeminormedCommGroup.{u1} E] {δ : Real} {s : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1))) s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (forall (x : E), Eq.{succ u1} (Set.{u1} E) (HMul.hMul.{u1, u1, u1} (Set.{u1} E) (Set.{u1} E) (Set.{u1} E) (instHMul.{u1} (Set.{u1} E) (Set.mul.{u1} E (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) (Metric.closedBall.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1) x δ) s) (HSMul.hSMul.{u1, u1, u1} E (Set.{u1} E) (Set.{u1} E) (instHSMul.{u1, u1} E (Set.{u1} E) (Set.smulSet.{u1, u1} E E (MulAction.toSMul.{u1, u1} E E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))) (Monoid.toMulAction.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (SeminormedGroup.toGroup.{u1} E (SeminormedCommGroup.toSeminormedGroup.{u1} E _inst_1)))))))) x (Metric.cthickening.{u1} E (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedCommGroup.toPseudoMetricSpace.{u1} E _inst_1)) δ s)))
Case conversion may be inaccurate. Consider using '#align is_compact.closed_ball_div IsCompact.closedBall_divₓ'. -/
@[to_additive]
theorem IsCompact.closedBall_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.closed_ball_mul hδ]
#align is_compact.closed_ball_div IsCompact.closedBall_div
#align is_compact.closed_ball_sub IsCompact.closedBall_sub

end SeminormedCommGroup

