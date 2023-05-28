/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales

! This file was ported from Lean 3 source module geometry.euclidean.angle.unoriented.affine
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Between
import Mathbin.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles between points

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.

-/


noncomputable section

open BigOperators

open Real

open RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type _} {P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

include V

#print EuclideanGeometry.angle /-
/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ :=
  angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)
#align euclidean_geometry.angle EuclideanGeometry.angle
-/

-- mathport name: angle
scoped notation "∠" => EuclideanGeometry.angle

/- warning: euclidean_geometry.continuous_at_angle -> EuclideanGeometry.continuousAt_angle is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {x : Prod.{u2, u2} P (Prod.{u2, u2} P P)}, (Ne.{succ u2} P (Prod.fst.{u2, u2} P (Prod.{u2, u2} P P) x) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x))) -> (Ne.{succ u2} P (Prod.snd.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x)) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x))) -> (ContinuousAt.{u2, 0} (Prod.{u2, u2} P (Prod.{u2, u2} P P)) Real (Prod.topologicalSpace.{u2, u2} P (Prod.{u2, u2} P P) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))) (Prod.topologicalSpace.{u2, u2} P P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : Prod.{u2, u2} P (Prod.{u2, u2} P P)) => EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 (Prod.fst.{u2, u2} P (Prod.{u2, u2} P P) y) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) y)) (Prod.snd.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) y))) x)
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {x : Prod.{u2, u2} P (Prod.{u2, u2} P P)}, (Ne.{succ u2} P (Prod.fst.{u2, u2} P (Prod.{u2, u2} P P) x) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x))) -> (Ne.{succ u2} P (Prod.snd.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x)) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) x))) -> (ContinuousAt.{u2, 0} (Prod.{u2, u2} P (Prod.{u2, u2} P P)) Real (instTopologicalSpaceProd.{u2, u2} P (Prod.{u2, u2} P P) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))) (instTopologicalSpaceProd.{u2, u2} P P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (y : Prod.{u2, u2} P (Prod.{u2, u2} P P)) => EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 (Prod.fst.{u2, u2} P (Prod.{u2, u2} P P) y) (Prod.fst.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) y)) (Prod.snd.{u2, u2} P P (Prod.snd.{u2, u2} P (Prod.{u2, u2} P P) y))) x)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.continuous_at_angle EuclideanGeometry.continuousAt_angleₓ'. -/
theorem continuousAt_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
    ContinuousAt (fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) x :=
  by
  let f : P × P × P → V × V := fun y => (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1)
  have hf1 : (f x).1 ≠ 0 := by simp [hx12]
  have hf2 : (f x).2 ≠ 0 := by simp [hx32]
  exact
    (InnerProductGeometry.continuousAt_angle hf1 hf2).comp
      ((continuous_fst.vsub continuous_snd.fst).prod_mk
          (continuous_snd.snd.vsub continuous_snd.fst)).ContinuousAt
#align euclidean_geometry.continuous_at_angle EuclideanGeometry.continuousAt_angle

/- warning: affine_isometry.angle_map -> AffineIsometry.angle_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_isometry.angle_map AffineIsometry.angle_mapₓ'. -/
@[simp]
theorem AffineIsometry.angle_map {V₂ P₂ : Type _} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [MetricSpace P₂] [NormedAddTorsor V₂ P₂] (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) :
    ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ := by
  simp_rw [angle, ← AffineIsometry.map_vsub, LinearIsometry.angle_map]
#align affine_isometry.angle_map AffineIsometry.angle_map

/- warning: affine_subspace.angle_coe -> AffineSubspace.angle_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.angle_coe AffineSubspace.angle_coeₓ'. -/
@[simp, norm_cast]
theorem AffineSubspace.angle_coe {s : AffineSubspace ℝ P} (p₁ p₂ p₃ : s) :
    haveI : Nonempty s := ⟨p₁⟩
    ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
  haveI : Nonempty s := ⟨p₁⟩
  s.subtypeₐᵢ.angle_map p₁ p₂ p₃
#align affine_subspace.angle_coe AffineSubspace.angle_coe

/- warning: euclidean_geometry.angle_const_vadd -> EuclideanGeometry.angle_const_vadd is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (v : V) (p₁ : P) (p₂ : P) (p₃ : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v p₁) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v p₂) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v p₃)) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (v : V) (p₁ : P) (p₂ : P) (p₃ : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v p₁) (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v p₂) (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v p₃)) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_const_vadd EuclideanGeometry.angle_const_vaddₓ'. -/
/-- Angles are translation invariant -/
@[simp]
theorem angle_const_vadd (v : V) (p₁ p₂ p₃ : P) : ∠ (v +ᵥ p₁) (v +ᵥ p₂) (v +ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVadd ℝ P v).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_const_vadd EuclideanGeometry.angle_const_vadd

/- warning: euclidean_geometry.angle_vadd_const -> EuclideanGeometry.angle_vadd_const is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (v₁ : V) (v₂ : V) (v₃ : V) (p : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v₁ p) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v₂ p) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4))) v₃ p)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (v₁ : V) (v₂ : V) (v₃ : V) (p : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v₁ p) (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v₂ p) (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (NormedAddGroup.toAddGroup.{u2} V (NormedAddCommGroup.toNormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)))) v₃ p)) (EuclideanGeometry.angle.{u2, u2} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u2} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_vadd_const EuclideanGeometry.angle_vadd_constₓ'. -/
/-- Angles are translation invariant -/
@[simp]
theorem angle_vadd_const (v₁ v₂ v₃ : V) (p : P) : ∠ (v₁ +ᵥ p) (v₂ +ᵥ p) (v₃ +ᵥ p) = ∠ v₁ v₂ v₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_vadd_const EuclideanGeometry.angle_vadd_const

/- warning: euclidean_geometry.angle_const_vsub -> EuclideanGeometry.angle_const_vsub is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p : P) (p₁ : P) (p₂ : P) (p₃ : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p p₁) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p p₂) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p p₃)) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p : P) (p₁ : P) (p₂ : P) (p₃ : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u2} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u2} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p p₁) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p p₂) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p p₃)) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_const_vsub EuclideanGeometry.angle_const_vsubₓ'. -/
/-- Angles are translation invariant -/
@[simp]
theorem angle_const_vsub (p p₁ p₂ p₃ : P) : ∠ (p -ᵥ p₁) (p -ᵥ p₂) (p -ᵥ p₃) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.constVsub ℝ p).toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_const_vsub EuclideanGeometry.angle_const_vsub

/- warning: euclidean_geometry.angle_vsub_const -> EuclideanGeometry.angle_vsub_const is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p₁ : P) (p₂ : P) (p₃ : P) (p : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p₁ p) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p₂ p) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p₃ p)) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p₁ : P) (p₂ : P) (p₃ : P) (p : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u2} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u2} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p₁ p) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p₂ p) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4)) p₃ p)) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_vsub_const EuclideanGeometry.angle_vsub_constₓ'. -/
/-- Angles are translation invariant -/
@[simp]
theorem angle_vsub_const (p₁ p₂ p₃ p : P) : ∠ (p₁ -ᵥ p) (p₂ -ᵥ p) (p₃ -ᵥ p) = ∠ p₁ p₂ p₃ :=
  (AffineIsometryEquiv.vaddConst ℝ p).symm.toAffineIsometry.angle_map _ _ _
#align euclidean_geometry.angle_vsub_const EuclideanGeometry.angle_vsub_const

/- warning: euclidean_geometry.angle_add_const -> EuclideanGeometry.angle_add_const is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V) (v : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₁ v) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₂ v) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₃ v)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V) (v : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₁ v) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₂ v) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v₃ v)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_add_const EuclideanGeometry.angle_add_constₓ'. -/
/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_add_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ + v) (v₂ + v) (v₃ + v) = ∠ v₁ v₂ v₃ :=
  angle_vadd_const _ _ _ _
#align euclidean_geometry.angle_add_const EuclideanGeometry.angle_add_const

/- warning: euclidean_geometry.angle_const_add -> EuclideanGeometry.angle_const_add is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v : V) (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₁) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₂) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toHasAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v : V) (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₁) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₂) (HAdd.hAdd.{u1, u1, u1} V V V (instHAdd.{u1} V (AddZeroClass.toAdd.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))))) v v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_const_add EuclideanGeometry.angle_const_addₓ'. -/
/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_const_add (v : V) (v₁ v₂ v₃ : V) : ∠ (v + v₁) (v + v₂) (v + v₃) = ∠ v₁ v₂ v₃ :=
  angle_const_vadd _ _ _ _
#align euclidean_geometry.angle_const_add EuclideanGeometry.angle_const_add

/- warning: euclidean_geometry.angle_sub_const -> EuclideanGeometry.angle_sub_const is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V) (v : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₁ v) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₂ v) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₃ v)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V) (v : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₁ v) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₂ v) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v₃ v)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_sub_const EuclideanGeometry.angle_sub_constₓ'. -/
/-- Angles in a vector space are translation invariant -/
@[simp]
theorem angle_sub_const (v₁ v₂ v₃ : V) (v : V) : ∠ (v₁ - v) (v₂ - v) (v₃ - v) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_vsub_const v₁ v₂ v₃ v
#align euclidean_geometry.angle_sub_const EuclideanGeometry.angle_sub_const

/- warning: euclidean_geometry.angle_const_sub -> EuclideanGeometry.angle_const_sub is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v : V) (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₁) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₂) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toHasSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v : V) (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₁) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₂) (HSub.hSub.{u1, u1, u1} V V V (instHSub.{u1} V (SubNegMonoid.toSub.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1))))) v v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_const_sub EuclideanGeometry.angle_const_subₓ'. -/
/-- Angles in a vector space are invariant to inversion -/
@[simp]
theorem angle_const_sub (v : V) (v₁ v₂ v₃ : V) : ∠ (v - v₁) (v - v₂) (v - v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [vsub_eq_sub] using angle_const_vsub _ _ _ _
#align euclidean_geometry.angle_const_sub EuclideanGeometry.angle_const_sub

/- warning: euclidean_geometry.angle_neg -> EuclideanGeometry.angle_neg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) v₁) (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) v₂) (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
but is expected to have type
  forall {V : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] (v₁ : V) (v₂ : V) (v₃ : V), Eq.{1} Real (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) v₁) (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) v₂) (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) v₃)) (EuclideanGeometry.angle.{u1, u1} V V _inst_1 _inst_2 (NormedAddCommGroup.toMetricSpace.{u1} V _inst_1) (SeminormedAddCommGroup.toNormedAddTorsor.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1)) v₁ v₂ v₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_neg EuclideanGeometry.angle_negₓ'. -/
/-- Angles in a vector space are invariant to inversion -/
@[simp]
theorem angle_neg (v₁ v₂ v₃ : V) : ∠ (-v₁) (-v₂) (-v₃) = ∠ v₁ v₂ v₃ := by
  simpa only [zero_sub] using angle_const_sub 0 v₁ v₂ v₃
#align euclidean_geometry.angle_neg EuclideanGeometry.angle_neg

/- warning: euclidean_geometry.angle_comm -> EuclideanGeometry.angle_comm is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 p2 p1)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 p2 p1)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_comm EuclideanGeometry.angle_commₓ'. -/
/-- The angle at a point does not depend on the order of the other two
points. -/
theorem angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
  angle_comm _ _
#align euclidean_geometry.angle_comm EuclideanGeometry.angle_comm

/- warning: euclidean_geometry.angle_nonneg -> EuclideanGeometry.angle_nonneg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_nonneg EuclideanGeometry.angle_nonnegₓ'. -/
/-- The angle at a point is nonnegative. -/
theorem angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
  angle_nonneg _ _
#align euclidean_geometry.angle_nonneg EuclideanGeometry.angle_nonneg

/- warning: euclidean_geometry.angle_le_pi -> EuclideanGeometry.angle_le_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), LE.le.{0} Real Real.hasLe (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) (p2 : P) (p3 : P), LE.le.{0} Real Real.instLEReal (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_le_pi EuclideanGeometry.angle_le_piₓ'. -/
/-- The angle at a point is at most π. -/
theorem angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
  angle_le_pi _ _
#align euclidean_geometry.angle_le_pi EuclideanGeometry.angle_le_pi

/- warning: euclidean_geometry.angle_eq_left -> EuclideanGeometry.angle_eq_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) (p2 : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p1 p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) (p2 : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p1 p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_left EuclideanGeometry.angle_eq_leftₓ'. -/
/-- The angle ∠AAB at a point. -/
theorem angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 :=
  by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _
#align euclidean_geometry.angle_eq_left EuclideanGeometry.angle_eq_left

/- warning: euclidean_geometry.angle_eq_right -> EuclideanGeometry.angle_eq_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) (p2 : P), Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) (p2 : P), Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_right EuclideanGeometry.angle_eq_rightₓ'. -/
/-- The angle ∠ABB at a point. -/
theorem angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 := by rw [angle_comm, angle_eq_left]
#align euclidean_geometry.angle_eq_right EuclideanGeometry.angle_eq_right

/- warning: euclidean_geometry.angle_eq_of_ne -> EuclideanGeometry.angle_eq_of_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P}, (Ne.{succ u2} P p1 p2) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p1) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P}, (Ne.{succ u2} P p1 p2) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p1) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_of_ne EuclideanGeometry.angle_eq_of_neₓ'. -/
/-- The angle ∠ABA at a point. -/
theorem angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
  angle_self fun he => h (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.angle_eq_of_ne EuclideanGeometry.angle_eq_of_ne

/- warning: euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left -> EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p1 p3) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p1 p3) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_leftₓ'. -/
/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p1 p3 = 0 :=
  by
  unfold angle at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2
  use hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul, ← neg_vsub_eq_vsub_rev p1 p2, smul_neg]
  simp [← hpr]
#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_left EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left

/- warning: euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right -> EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p1) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p1) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_rightₓ'. -/
/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p3 p1 = 0 :=
  by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h
#align euclidean_geometry.angle_eq_zero_of_angle_eq_pi_right EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right

/- warning: euclidean_geometry.angle_eq_angle_of_angle_eq_pi -> EuclideanGeometry.angle_eq_angle_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) {p2 : P} {p3 : P} {p4 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p4) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p4))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) {p2 : P} {p3 : P} {p4 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p4) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p4))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_piₓ'. -/
/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
theorem angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p2 p3 = ∠ p1 p2 p4 := by
  unfold angle at *
  rcases angle_eq_pi_iff.1 h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one)
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr]
  simp
#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_pi

/- warning: euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi -> EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (p1 : P) {p2 : P} {p3 : P} {p4 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p4) Real.pi) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p3 p2) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p3 p4)) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] (p1 : P) {p2 : P} {p3 : P} {p4 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p3 p4) Real.pi) -> (Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p3 p2) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p3 p4)) Real.pi)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_piₓ'. -/
/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p3 p2 + ∠ p1 p3 p4 = π := by
  unfold angle at h
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
#align euclidean_geometry.angle_add_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi

/- warning: euclidean_geometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi -> EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P} {p4 : P} {p5 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p5 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p5 p4) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p5 p2) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 p5 p4))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P} {p4 : P} {p5 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p5 p3) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p2 p5 p4) Real.pi) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p5 p2) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 p5 p4))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_piₓ'. -/
/-- Vertical Angles Theorem: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P} (hapc : ∠ p1 p5 p3 = π)
    (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
    angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]
#align euclidean_geometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi

/- warning: euclidean_geometry.left_dist_ne_zero_of_angle_eq_pi -> EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Ne.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Ne.{1} Real (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p1 p2) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.left_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.left_dist_ne_zero_of_angle_eq_piₓ'. -/
/-- If ∠ABC = π then dist A B ≠ 0. -/
theorem left_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p2 ≠ 0 :=
  by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [HEq, angle_eq_left] at h
  exact Real.pi_ne_zero (by linarith)
#align euclidean_geometry.left_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.left_dist_ne_zero_of_angle_eq_pi

/- warning: euclidean_geometry.right_dist_ne_zero_of_angle_eq_pi -> EuclideanGeometry.right_dist_ne_zero_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Ne.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Ne.{1} Real (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p3 p2) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.right_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.right_dist_ne_zero_of_angle_eq_piₓ'. -/
/-- If ∠ABC = π then dist C B ≠ 0. -/
theorem right_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p3 p2 ≠ 0 :=
  left_dist_ne_zero_of_angle_eq_pi <| (angle_comm _ _ _).trans h
#align euclidean_geometry.right_dist_ne_zero_of_angle_eq_pi EuclideanGeometry.right_dist_ne_zero_of_angle_eq_pi

/- warning: euclidean_geometry.dist_eq_add_dist_of_angle_eq_pi -> EuclideanGeometry.dist_eq_add_dist_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi) -> (Eq.{1} Real (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p1 p3) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p1 p2) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p3 p2)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_eq_add_dist_of_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_of_angle_eq_piₓ'. -/
/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 :=
  by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h
#align euclidean_geometry.dist_eq_add_dist_of_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_of_angle_eq_pi

/- warning: euclidean_geometry.dist_eq_add_dist_iff_angle_eq_pi -> EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Ne.{succ u2} P p1 p2) -> (Ne.{succ u2} P p3 p2) -> (Iff (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Ne.{succ u2} P p1 p2) -> (Ne.{succ u2} P p3 p2) -> (Iff (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) Real.pi))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_eq_add_dist_iff_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_piₓ'. -/
/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π :=
  by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp3p2 (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.dist_eq_add_dist_iff_angle_eq_pi EuclideanGeometry.dist_eq_add_dist_iff_angle_eq_pi

/- warning: euclidean_geometry.dist_eq_abs_sub_dist_of_angle_eq_zero -> EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p1 p3) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p1 p2) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)) p3 p2))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_eq_abs_sub_dist_of_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zeroₓ'. -/
/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| :=
  by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h
#align euclidean_geometry.dist_eq_abs_sub_dist_of_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero

/- warning: euclidean_geometry.dist_eq_abs_sub_dist_iff_angle_eq_zero -> EuclideanGeometry.dist_eq_abs_sub_dist_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Ne.{succ u2} P p1 p2) -> (Ne.{succ u2} P p3 p2) -> (Iff (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Ne.{succ u2} P p1 p2) -> (Ne.{succ u2} P p3 p2) -> (Iff (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p3) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p1 p2) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p1 p2 p3) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.dist_eq_abs_sub_dist_iff_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_iff_angle_eq_zeroₓ'. -/
/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = |dist p1 p2 - dist p3 p2| ↔ ∠ p1 p2 p3 = 0 :=
  by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he))
      fun he => hp3p2 (vsub_eq_zero_iff_eq.1 he)
#align euclidean_geometry.dist_eq_abs_sub_dist_iff_angle_eq_zero EuclideanGeometry.dist_eq_abs_sub_dist_iff_angle_eq_zero

#print EuclideanGeometry.angle_midpoint_eq_pi /-
/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
theorem angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π :=
  by
  have : p2 -ᵥ midpoint ℝ p1 p2 = -(p1 -ᵥ midpoint ℝ p1 p2) :=
    by
    rw [neg_vsub_eq_vsub_rev]
    simp
  simp [angle, this, hp1p2, -zero_lt_one]
#align euclidean_geometry.angle_midpoint_eq_pi EuclideanGeometry.angle_midpoint_eq_pi
-/

/- warning: euclidean_geometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq -> EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p1) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 (midpoint.{0, u1, u2} Real V P Real.ring (invertibleTwo.{0} Real Real.divisionRing (IsROrC.charZero_isROrC.{0} Real Real.isROrC)) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p1 p2) p1) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p1) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 (midpoint.{0, u1, u2} Real V P Real.instRingReal (invertibleTwo.{0} Real Real.instDivisionRingReal (IsROrC.charZero_isROrC.{0} Real Real.isROrC)) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4) p1 p2) p1) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eqₓ'. -/
/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 :=
  by
  let m : P := midpoint ℝ p1 p2
  have h1 : p3 -ᵥ p1 = p3 -ᵥ m - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm
  have h2 : p3 -ᵥ p2 = p3 -ᵥ m + (p1 -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p3 p1, dist_eq_norm_vsub V p3 p2, h1, h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm
#align euclidean_geometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_left_midpoint_eq_pi_div_two_of_dist_eq

/- warning: euclidean_geometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq -> EuclideanGeometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p1) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 (midpoint.{0, u1, u2} Real V P Real.ring (invertibleTwo.{0} Real Real.divisionRing (IsROrC.charZero_isROrC.{0} Real Real.isROrC)) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p1 p2) p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p1 : P} {p2 : P} {p3 : P}, (Eq.{1} Real (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p1) (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p3 p2)) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p3 (midpoint.{0, u1, u2} Real V P Real.instRingReal (invertibleTwo.{0} Real Real.instDivisionRingReal (IsROrC.charZero_isROrC.{0} Real Real.isROrC)) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4) p1 p2) p2) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_right_midpoint_eq_pi_div_two_of_dist_eqₓ'. -/
/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 := by
  rw [midpoint_comm p1 p2, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]
#align euclidean_geometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq EuclideanGeometry.angle_right_midpoint_eq_pi_div_two_of_dist_eq

/- warning: sbtw.angle₁₂₃_eq_pi -> Sbtw.angle₁₂₃_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
Case conversion may be inaccurate. Consider using '#align sbtw.angle₁₂₃_eq_pi Sbtw.angle₁₂₃_eq_piₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
theorem Sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π :=
  by
  rw [angle, angle_eq_pi_iff]
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩
  refine' ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, _⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    rw [← hp₂] at hp₂p₁
    simpa using hp₂p₁
  have hr1' : r ≠ 1 := by
    rintro rfl
    rw [← hp₂] at hp₂p₃
    simpa using hp₂p₃
  replace hr0 := hr0.lt_of_ne hr0'.symm
  replace hr1 := hr1.lt_of_ne hr1'
  refine' ⟨div_neg_of_neg_of_pos (Left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, _⟩
  rw [← hp₂, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
    zero_sub, smul_neg, smul_smul, div_mul_cancel _ hr0', neg_smul, neg_neg, sub_eq_iff_eq_add, ←
    add_smul, sub_add_cancel, one_smul]
#align sbtw.angle₁₂₃_eq_pi Sbtw.angle₁₂₃_eq_pi

/- warning: sbtw.angle₃₂₁_eq_pi -> Sbtw.angle₃₂₁_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₂ p₁) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₂ p₁) Real.pi)
Case conversion may be inaccurate. Consider using '#align sbtw.angle₃₂₁_eq_pi Sbtw.angle₃₂₁_eq_piₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
theorem Sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π := by
  rw [← h.angle₁₂₃_eq_pi, angle_comm]
#align sbtw.angle₃₂₁_eq_pi Sbtw.angle₃₂₁_eq_pi

/- warning: euclidean_geometry.angle_eq_pi_iff_sbtw -> EuclideanGeometry.angle_eq_pi_iff_sbtw is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi) (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi) (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_pi_iff_sbtw EuclideanGeometry.angle_eq_pi_iff_sbtwₓ'. -/
/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
theorem angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ Sbtw ℝ p₁ p₂ p₃ :=
  by
  refine' ⟨_, fun h => h.angle₁₂₃_eq_pi⟩
  rw [angle, angle_eq_pi_iff]
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩
  refine'
    ⟨⟨1 / (1 - r),
        ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
          (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩,
        _⟩,
      (vsub_ne_zero.1 hp₁p₂).symm, _⟩
  · rw [← eq_vadd_iff_vsub_eq] at hp₃p₂
    rw [AffineMap.lineMap_apply, hp₃p₂, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p₂ p₁, smul_neg, ←
      neg_smul, smul_add, smul_smul, ← add_smul, eq_comm, eq_vadd_iff_vsub_eq]
    convert(one_smul ℝ (p₂ -ᵥ p₁)).symm
    field_simp [(sub_pos.2 (hr.trans zero_lt_one)).Ne.symm]
    abel
  · rw [ne_comm, ← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
    exact ⟨hr.ne, hp₁p₂⟩
#align euclidean_geometry.angle_eq_pi_iff_sbtw EuclideanGeometry.angle_eq_pi_iff_sbtw

/- warning: wbtw.angle₂₁₃_eq_zero_of_ne -> Wbtw.angle₂₁₃_eq_zero_of_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Ne.{succ u2} P p₂ p₁) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₁ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Ne.{succ u1} P p₂ p₁) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₁ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align wbtw.angle₂₁₃_eq_zero_of_ne Wbtw.angle₂₁₃_eq_zero_of_neₓ'. -/
/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
theorem Wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₂ p₁ p₃ = 0 := by
  rw [angle, angle_eq_zero_iff]
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hr0' : r ≠ 0 := by
    rintro rfl
    simpa using hp₂p₁
  replace hr0 := hr0.lt_of_ne hr0'.symm
  refine' ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, _⟩
  rw [AffineMap.lineMap_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul, inv_mul_cancel hr0',
    one_smul]
#align wbtw.angle₂₁₃_eq_zero_of_ne Wbtw.angle₂₁₃_eq_zero_of_ne

/- warning: sbtw.angle₂₁₃_eq_zero -> Sbtw.angle₂₁₃_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₁ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₁ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align sbtw.angle₂₁₃_eq_zero Sbtw.angle₂₁₃_eq_zeroₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
theorem Sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
  h.Wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left
#align sbtw.angle₂₁₃_eq_zero Sbtw.angle₂₁₃_eq_zero

/- warning: wbtw.angle₃₁₂_eq_zero_of_ne -> Wbtw.angle₃₁₂_eq_zero_of_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Ne.{succ u2} P p₂ p₁) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₁ p₂) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Ne.{succ u1} P p₂ p₁) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₁ p₂) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align wbtw.angle₃₁₂_eq_zero_of_ne Wbtw.angle₃₁₂_eq_zero_of_neₓ'. -/
/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
theorem Wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
    ∠ p₃ p₁ p₂ = 0 := by rw [← h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]
#align wbtw.angle₃₁₂_eq_zero_of_ne Wbtw.angle₃₁₂_eq_zero_of_ne

/- warning: sbtw.angle₃₁₂_eq_zero -> Sbtw.angle₃₁₂_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₁ p₂) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₃ p₁ p₂) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align sbtw.angle₃₁₂_eq_zero Sbtw.angle₃₁₂_eq_zeroₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
theorem Sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
  h.Wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left
#align sbtw.angle₃₁₂_eq_zero Sbtw.angle₃₁₂_eq_zero

/- warning: wbtw.angle₂₃₁_eq_zero_of_ne -> Wbtw.angle₂₃₁_eq_zero_of_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Ne.{succ u2} P p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₃ p₁) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Ne.{succ u1} P p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₃ p₁) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align wbtw.angle₂₃₁_eq_zero_of_ne Wbtw.angle₂₃₁_eq_zero_of_neₓ'. -/
/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
theorem Wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₂ p₃ p₁ = 0 :=
  h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃
#align wbtw.angle₂₃₁_eq_zero_of_ne Wbtw.angle₂₃₁_eq_zero_of_ne

/- warning: sbtw.angle₂₃₁_eq_zero -> Sbtw.angle₂₃₁_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₃ p₁) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₂ p₃ p₁) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align sbtw.angle₂₃₁_eq_zero Sbtw.angle₂₃₁_eq_zeroₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
theorem Sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
  h.Wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right
#align sbtw.angle₂₃₁_eq_zero Sbtw.angle₂₃₁_eq_zero

/- warning: wbtw.angle₁₃₂_eq_zero_of_ne -> Wbtw.angle₁₃₂_eq_zero_of_ne is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Ne.{succ u2} P p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₃ p₂) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Ne.{succ u1} P p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₃ p₂) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align wbtw.angle₁₃₂_eq_zero_of_ne Wbtw.angle₁₃₂_eq_zero_of_neₓ'. -/
/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
theorem Wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    ∠ p₁ p₃ p₂ = 0 :=
  h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃
#align wbtw.angle₁₃₂_eq_zero_of_ne Wbtw.angle₁₃₂_eq_zero_of_ne

/- warning: sbtw.angle₁₃₂_eq_zero -> Sbtw.angle₁₃₂_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₃ p₂) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₁ p₂ p₃) -> (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₃ p₂) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align sbtw.angle₁₃₂_eq_zero Sbtw.angle₁₃₂_eq_zeroₓ'. -/
/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
theorem Sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
  h.Wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right
#align sbtw.angle₁₃₂_eq_zero Sbtw.angle₁₃₂_eq_zero

/- warning: euclidean_geometry.angle_eq_zero_iff_ne_and_wbtw -> EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (And (Ne.{succ u2} P p₁ p₂) (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₂ p₁ p₃)) (And (Ne.{succ u2} P p₃ p₂) (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₂ p₃ p₁)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (And (Ne.{succ u1} P p₁ p₂) (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₂ p₁ p₃)) (And (Ne.{succ u1} P p₃ p₂) (Wbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₂ p₃ p₁)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_zero_iff_ne_and_wbtw EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtwₓ'. -/
/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
theorem angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ ≠ p₂ ∧ Wbtw ℝ p₂ p₁ p₃ ∨ p₃ ≠ p₂ ∧ Wbtw ℝ p₂ p₃ p₁ :=
  by
  constructor
  · rw [angle, angle_eq_zero_iff]
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩
    rcases le_or_lt 1 r with (hr1 | hr1)
    · refine' Or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one hr1⟩, _⟩
      rw [AffineMap.lineMap_apply, hp₃p₂, smul_smul, inv_mul_cancel hr0.ne.symm, one_smul,
        vsub_vadd]
    · refine' Or.inr ⟨_, r, ⟨hr0.le, hr1.le⟩, _⟩
      · rw [← @vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff]
        exact ⟨hr0.ne.symm, hp₁p₂⟩
      · rw [AffineMap.lineMap_apply, ← hp₃p₂, vsub_vadd]
  · rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩)
    · exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂
    · exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂
#align euclidean_geometry.angle_eq_zero_iff_ne_and_wbtw EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw

/- warning: euclidean_geometry.angle_eq_zero_iff_eq_and_ne_or_sbtw -> EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (And (Eq.{succ u2} P p₁ p₃) (Ne.{succ u2} P p₁ p₂)) (Or (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₂ p₁ p₃) (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p₂ p₃ p₁)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (And (Eq.{succ u1} P p₁ p₃) (Ne.{succ u1} P p₁ p₂)) (Or (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₂ p₁ p₃) (Sbtw.{0, u2, u1} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) p₂ p₃ p₁)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_eq_zero_iff_eq_and_ne_or_sbtw EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtwₓ'. -/
/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
theorem angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ = 0 ↔ p₁ = p₃ ∧ p₁ ≠ p₂ ∨ Sbtw ℝ p₂ p₁ p₃ ∨ Sbtw ℝ p₂ p₃ p₁ :=
  by
  rw [angle_eq_zero_iff_ne_and_wbtw]
  by_cases hp₁p₂ : p₁ = p₂; · simp [hp₁p₂]
  by_cases hp₁p₃ : p₁ = p₃; · simp [hp₁p₃]
  by_cases hp₃p₂ : p₃ = p₂; · simp [hp₃p₂]
  simp [hp₁p₂, hp₁p₃, Ne.symm hp₁p₃, Sbtw, hp₃p₂]
#align euclidean_geometry.angle_eq_zero_iff_eq_and_ne_or_sbtw EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw

/- warning: euclidean_geometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi -> EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃)))) (Or (Eq.{succ u2} P p₁ p₂) (Or (Eq.{succ u2} P p₃ p₂) (Or (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃)))) (Or (Eq.{succ u1} P p₁ p₂) (Or (Eq.{succ u1} P p₃ p₂) (Or (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_piₓ'. -/
/-- Three points are collinear if and only if the first or third point equals the second or the
angle between them is 0 or π. -/
theorem collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · replace h := h.wbtw_or_wbtw_or_wbtw
    by_cases h₁₂ : p₁ = p₂
    · exact Or.inl h₁₂
    by_cases h₃₂ : p₃ = p₂
    · exact Or.inr (Or.inl h₃₂)
    rw [or_iff_right h₁₂, or_iff_right h₃₂]
    rcases h with (h | h | h)
    · exact Or.inr (angle_eq_pi_iff_sbtw.2 ⟨h, Ne.symm h₁₂, Ne.symm h₃₂⟩)
    · exact Or.inl (h.angle₃₁₂_eq_zero_of_ne h₃₂)
    · exact Or.inl (h.angle₂₃₁_eq_zero_of_ne h₁₂)
  · rcases h with (rfl | rfl | h | h)
    · simpa using collinear_pair ℝ p₁ p₃
    · simpa using collinear_pair ℝ p₁ p₃
    · rw [angle_eq_zero_iff_ne_and_wbtw] at h
      rcases h with (⟨-, h⟩ | ⟨-, h⟩)
      · rw [Set.insert_comm]
        exact h.collinear
      · rw [Set.insert_comm, Set.pair_comm]
        exact h.collinear
    · rw [angle_eq_pi_iff_sbtw] at h
      exact h.wbtw.collinear
#align euclidean_geometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi

/- warning: euclidean_geometry.collinear_of_angle_eq_zero -> EuclideanGeometry.collinear_of_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.collinear_of_angle_eq_zero EuclideanGeometry.collinear_of_angle_eq_zeroₓ'. -/
/-- If the angle between three points is 0, they are collinear. -/
theorem collinear_of_angle_eq_zero {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inl h
#align euclidean_geometry.collinear_of_angle_eq_zero EuclideanGeometry.collinear_of_angle_eq_zero

/- warning: euclidean_geometry.collinear_of_angle_eq_pi -> EuclideanGeometry.collinear_of_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi) -> (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi) -> (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.collinear_of_angle_eq_pi EuclideanGeometry.collinear_of_angle_eq_piₓ'. -/
/-- If the angle between three points is π, they are collinear. -/
theorem collinear_of_angle_eq_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.2 <| Or.inr <| Or.inr <| Or.inr h
#align euclidean_geometry.collinear_of_angle_eq_pi EuclideanGeometry.collinear_of_angle_eq_pi

/- warning: euclidean_geometry.angle_ne_zero_of_not_collinear -> EuclideanGeometry.angle_ne_zero_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (Ne.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (Ne.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_ne_zero_of_not_collinear EuclideanGeometry.angle_ne_zero_of_not_collinearₓ'. -/
/-- If three points are not collinear, the angle between them is nonzero. -/
theorem angle_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ 0 :=
  mt collinear_of_angle_eq_zero h
#align euclidean_geometry.angle_ne_zero_of_not_collinear EuclideanGeometry.angle_ne_zero_of_not_collinear

/- warning: euclidean_geometry.angle_ne_pi_of_not_collinear -> EuclideanGeometry.angle_ne_pi_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (Ne.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (Ne.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_ne_pi_of_not_collinear EuclideanGeometry.angle_ne_pi_of_not_collinearₓ'. -/
/-- If three points are not collinear, the angle between them is not π. -/
theorem angle_ne_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ ≠ π :=
  mt collinear_of_angle_eq_pi h
#align euclidean_geometry.angle_ne_pi_of_not_collinear EuclideanGeometry.angle_ne_pi_of_not_collinear

/- warning: euclidean_geometry.angle_pos_of_not_collinear -> EuclideanGeometry.angle_pos_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_pos_of_not_collinear EuclideanGeometry.angle_pos_of_not_collinearₓ'. -/
/-- If three points are not collinear, the angle between them is positive. -/
theorem angle_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < ∠ p₁ p₂ p₃ :=
  (angle_nonneg _ _ _).lt_of_ne (angle_ne_zero_of_not_collinear h).symm
#align euclidean_geometry.angle_pos_of_not_collinear EuclideanGeometry.angle_pos_of_not_collinear

/- warning: euclidean_geometry.angle_lt_pi_of_not_collinear -> EuclideanGeometry.angle_lt_pi_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (LT.lt.{0} Real Real.hasLt (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (LT.lt.{0} Real Real.instLTReal (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.angle_lt_pi_of_not_collinear EuclideanGeometry.angle_lt_pi_of_not_collinearₓ'. -/
/-- If three points are not collinear, the angle between them is less than π. -/
theorem angle_lt_pi_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    ∠ p₁ p₂ p₃ < π :=
  (angle_le_pi _ _ _).lt_of_ne <| angle_ne_pi_of_not_collinear h
#align euclidean_geometry.angle_lt_pi_of_not_collinear EuclideanGeometry.angle_lt_pi_of_not_collinear

/- warning: euclidean_geometry.cos_eq_one_iff_angle_eq_zero -> EuclideanGeometry.cos_eq_one_iff_angle_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.cos_eq_one_iff_angle_eq_zero EuclideanGeometry.cos_eq_one_iff_angle_eq_zeroₓ'. -/
/-- The cosine of the angle between three points is 1 if and only if the angle is 0. -/
theorem cos_eq_one_iff_angle_eq_zero {p₁ p₂ p₃ : P} : Real.cos (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = 0 :=
  cos_eq_one_iff_angle_eq_zero
#align euclidean_geometry.cos_eq_one_iff_angle_eq_zero EuclideanGeometry.cos_eq_one_iff_angle_eq_zero

/- warning: euclidean_geometry.cos_eq_zero_iff_angle_eq_pi_div_two -> EuclideanGeometry.cos_eq_zero_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.cos_eq_zero_iff_angle_eq_pi_div_two EuclideanGeometry.cos_eq_zero_iff_angle_eq_pi_div_twoₓ'. -/
/-- The cosine of the angle between three points is 0 if and only if the angle is π / 2. -/
theorem cos_eq_zero_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  cos_eq_zero_iff_angle_eq_pi_div_two
#align euclidean_geometry.cos_eq_zero_iff_angle_eq_pi_div_two EuclideanGeometry.cos_eq_zero_iff_angle_eq_pi_div_two

/- warning: euclidean_geometry.cos_eq_neg_one_iff_angle_eq_pi -> EuclideanGeometry.cos_eq_neg_one_iff_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.cos (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.cos_eq_neg_one_iff_angle_eq_pi EuclideanGeometry.cos_eq_neg_one_iff_angle_eq_piₓ'. -/
/-- The cosine of the angle between three points is -1 if and only if the angle is π. -/
theorem cos_eq_neg_one_iff_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.cos (∠ p₁ p₂ p₃) = -1 ↔ ∠ p₁ p₂ p₃ = π :=
  cos_eq_neg_one_iff_angle_eq_pi
#align euclidean_geometry.cos_eq_neg_one_iff_angle_eq_pi EuclideanGeometry.cos_eq_neg_one_iff_angle_eq_pi

/- warning: euclidean_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi -> EuclideanGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) Real.pi))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_piₓ'. -/
/-- The sine of the angle between three points is 0 if and only if the angle is 0 or π. -/
theorem sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 0 ↔ ∠ p₁ p₂ p₃ = 0 ∨ ∠ p₁ p₂ p₃ = π :=
  sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi
#align euclidean_geometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi EuclideanGeometry.sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi

/- warning: euclidean_geometry.sin_eq_one_iff_angle_eq_pi_div_two -> EuclideanGeometry.sin_eq_one_iff_angle_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sin_eq_one_iff_angle_eq_pi_div_two EuclideanGeometry.sin_eq_one_iff_angle_eq_pi_div_twoₓ'. -/
/-- The sine of the angle between three points is 1 if and only if the angle is π / 2. -/
theorem sin_eq_one_iff_angle_eq_pi_div_two {p₁ p₂ p₃ : P} :
    Real.sin (∠ p₁ p₂ p₃) = 1 ↔ ∠ p₁ p₂ p₃ = π / 2 :=
  sin_eq_one_iff_angle_eq_pi_div_two
#align euclidean_geometry.sin_eq_one_iff_angle_eq_pi_div_two EuclideanGeometry.sin_eq_one_iff_angle_eq_pi_div_two

/- warning: euclidean_geometry.collinear_iff_eq_or_eq_or_sin_eq_zero -> EuclideanGeometry.collinear_iff_eq_or_eq_or_sin_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃)))) (Or (Eq.{succ u2} P p₁ p₂) (Or (Eq.{succ u2} P p₃ p₂) (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, Iff (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃)))) (Or (Eq.{succ u1} P p₁ p₂) (Or (Eq.{succ u1} P p₃ p₂) (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.collinear_iff_eq_or_eq_or_sin_eq_zero EuclideanGeometry.collinear_iff_eq_or_eq_or_sin_eq_zeroₓ'. -/
/-- Three points are collinear if and only if the first or third point equals the second or
the sine of the angle between three points is zero. -/
theorem collinear_iff_eq_or_eq_or_sin_eq_zero {p₁ p₂ p₃ : P} :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) ↔ p₁ = p₂ ∨ p₃ = p₂ ∨ Real.sin (∠ p₁ p₂ p₃) = 0 := by
  rw [sin_eq_zero_iff_angle_eq_zero_or_angle_eq_pi,
    collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
#align euclidean_geometry.collinear_iff_eq_or_eq_or_sin_eq_zero EuclideanGeometry.collinear_iff_eq_or_eq_or_sin_eq_zero

/- warning: euclidean_geometry.sin_pos_of_not_collinear -> EuclideanGeometry.sin_pos_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sin_pos_of_not_collinear EuclideanGeometry.sin_pos_of_not_collinearₓ'. -/
/-- If three points are not collinear, the sine of the angle between them is positive. -/
theorem sin_pos_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    0 < Real.sin (∠ p₁ p₂ p₃) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos_of_not_collinear h) (angle_lt_pi_of_not_collinear h)
#align euclidean_geometry.sin_pos_of_not_collinear EuclideanGeometry.sin_pos_of_not_collinear

/- warning: euclidean_geometry.sin_ne_zero_of_not_collinear -> EuclideanGeometry.sin_ne_zero_of_not_collinear is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))) -> (Ne.{1} Real (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Not (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))) -> (Ne.{1} Real (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sin_ne_zero_of_not_collinear EuclideanGeometry.sin_ne_zero_of_not_collinearₓ'. -/
/-- If three points are not collinear, the sine of the angle between them is nonzero. -/
theorem sin_ne_zero_of_not_collinear {p₁ p₂ p₃ : P} (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    Real.sin (∠ p₁ p₂ p₃) ≠ 0 :=
  ne_of_gt (sin_pos_of_not_collinear h)
#align euclidean_geometry.sin_ne_zero_of_not_collinear EuclideanGeometry.sin_ne_zero_of_not_collinear

/- warning: euclidean_geometry.collinear_of_sin_eq_zero -> EuclideanGeometry.collinear_of_sin_eq_zero is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Collinear.{0, u1, u2} Real V P Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₁ (Insert.insert.{u2, u2} P (Set.{u2} P) (Set.hasInsert.{u2} P) p₂ (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p₃))))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} V] [_inst_2 : InnerProductSpace.{0, u2} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3)] {p₁ : P} {p₂ : P} {p₃ : P}, (Eq.{1} Real (Real.sin (EuclideanGeometry.angle.{u2, u1} V P _inst_1 _inst_2 _inst_3 _inst_4 p₁ p₂ p₃)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Collinear.{0, u2, u1} Real V P Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u2} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u1} P _inst_3) _inst_4) (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₁ (Insert.insert.{u1, u1} P (Set.{u1} P) (Set.instInsertSet.{u1} P) p₂ (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p₃))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.collinear_of_sin_eq_zero EuclideanGeometry.collinear_of_sin_eq_zeroₓ'. -/
/-- If the sine of the angle between three points is 0, they are collinear. -/
theorem collinear_of_sin_eq_zero {p₁ p₂ p₃ : P} (h : Real.sin (∠ p₁ p₂ p₃) = 0) :
    Collinear ℝ ({p₁, p₂, p₃} : Set P) :=
  imp_of_not_imp_not _ _ sin_ne_zero_of_not_collinear h
#align euclidean_geometry.collinear_of_sin_eq_zero EuclideanGeometry.collinear_of_sin_eq_zero

end EuclideanGeometry

