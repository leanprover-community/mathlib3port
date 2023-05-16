/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed.group.add_torsor
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace
import Mathbin.LinearAlgebra.AffineSpace.Midpoint

/-!
# Torsors of additive normed group actions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/


noncomputable section

open NNReal Topology

open Filter

#print NormedAddTorsor /-
/-- A `normed_add_torsor V P` is a torsor of an additive seminormed group
action by a `seminormed_add_comm_group V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
class NormedAddTorsor (V : outParam <| Type _) (P : Type _) [outParam <| SeminormedAddCommGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where
  dist_eq_norm' : ∀ x y : P, dist x y = ‖(x -ᵥ y : V)‖
#align normed_add_torsor NormedAddTorsor
-/

#print NormedAddTorsor.toAddTorsor' /-
/-- Shortcut instance to help typeclass inference out. -/
instance (priority := 100) NormedAddTorsor.toAddTorsor' {V P : Type _} [NormedAddCommGroup V]
    [MetricSpace P] [NormedAddTorsor V P] : AddTorsor V P :=
  NormedAddTorsor.toAddTorsor
#align normed_add_torsor.to_add_torsor' NormedAddTorsor.toAddTorsor'
-/

variable {α V P W Q : Type _} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

#print NormedAddTorsor.to_isometricVAdd /-
instance (priority := 100) NormedAddTorsor.to_isometricVAdd : IsometricVAdd V P :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by simp [NormedAddTorsor.dist_eq_norm']⟩
#align normed_add_torsor.to_has_isometric_vadd NormedAddTorsor.to_isometricVAdd
-/

#print SeminormedAddCommGroup.toNormedAddTorsor /-
/-- A `seminormed_add_comm_group` is a `normed_add_torsor` over itself. -/
instance (priority := 100) SeminormedAddCommGroup.toNormedAddTorsor : NormedAddTorsor V V
    where dist_eq_norm' := dist_eq_norm
#align seminormed_add_comm_group.to_normed_add_torsor SeminormedAddCommGroup.toNormedAddTorsor
-/

#print AffineSubspace.toNormedAddTorsor /-
-- Because of the add_torsor.nonempty instance.
/-- A nonempty affine subspace of a `normed_add_torsor` is itself a `normed_add_torsor`. -/
@[nolint fails_quickly]
instance AffineSubspace.toNormedAddTorsor {R : Type _} [Ring R] [Module R V]
    (s : AffineSubspace R P) [Nonempty s] : NormedAddTorsor s.direction s :=
  { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' ↑x ↑y }
#align affine_subspace.to_normed_add_torsor AffineSubspace.toNormedAddTorsor
-/

include V

section

variable (V W)

#print dist_eq_norm_vsub /-
/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ :=
  NormedAddTorsor.dist_eq_norm' x y
#align dist_eq_norm_vsub dist_eq_norm_vsub
-/

#print dist_eq_norm_vsub' /-
/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub'` sometimes doesn't work. -/
theorem dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
  (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)
#align dist_eq_norm_vsub' dist_eq_norm_vsub'
-/

end

#print dist_vadd_cancel_left /-
theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  dist_vadd _ _ _
#align dist_vadd_cancel_left dist_vadd_cancel_left
-/

#print dist_vadd_cancel_right /-
@[simp]
theorem dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]
#align dist_vadd_cancel_right dist_vadd_cancel_right
-/

#print dist_vadd_left /-
@[simp]
theorem dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖ := by simp [dist_eq_norm_vsub V _ x]
#align dist_vadd_left dist_vadd_left
-/

#print dist_vadd_right /-
@[simp]
theorem dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖ := by rw [dist_comm, dist_vadd_left]
#align dist_vadd_right dist_vadd_right
-/

#print IsometryEquiv.vaddConst /-
/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps]
def IsometryEquiv.vaddConst (x : P) : V ≃ᵢ P
    where
  toEquiv := Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _
#align isometry_equiv.vadd_const IsometryEquiv.vaddConst
-/

/- warning: dist_vsub_cancel_left -> dist_vsub_cancel_left is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (x : P) (y : P) (z : P), Eq.{1} Real (Dist.dist.{u1} V (PseudoMetricSpace.toHasDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) x y) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) x z)) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) y z)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] (x : P) (y : P) (z : P), Eq.{1} Real (Dist.dist.{u2} V (PseudoMetricSpace.toDist.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) x y) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) x z)) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P _inst_2) y z)
Case conversion may be inaccurate. Consider using '#align dist_vsub_cancel_left dist_vsub_cancel_leftₓ'. -/
@[simp]
theorem dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z := by
  rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]
#align dist_vsub_cancel_left dist_vsub_cancel_left

#print IsometryEquiv.constVSub /-
/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps]
def IsometryEquiv.constVSub (x : P) : P ≃ᵢ V
    where
  toEquiv := Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun y z => dist_vsub_cancel_left _ _ _
#align isometry_equiv.const_vsub IsometryEquiv.constVSub
-/

/- warning: dist_vsub_cancel_right -> dist_vsub_cancel_right is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (x : P) (y : P) (z : P), Eq.{1} Real (Dist.dist.{u1} V (PseudoMetricSpace.toHasDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) x z) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) y z)) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) x y)
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] (x : P) (y : P) (z : P), Eq.{1} Real (Dist.dist.{u2} V (PseudoMetricSpace.toDist.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) x z) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) y z)) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align dist_vsub_cancel_right dist_vsub_cancel_rightₓ'. -/
@[simp]
theorem dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  (IsometryEquiv.vaddConst z).symm.dist_eq x y
#align dist_vsub_cancel_right dist_vsub_cancel_right

/- warning: dist_vadd_vadd_le -> dist_vadd_vadd_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v p) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v' p')) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} V (PseudoMetricSpace.toHasDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) v v') (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) p p'))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P _inst_2) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v p) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v' p')) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} V (PseudoMetricSpace.toDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) v v') (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P _inst_2) p p'))
Case conversion may be inaccurate. Consider using '#align dist_vadd_vadd_le dist_vadd_vadd_leₓ'. -/
theorem dist_vadd_vadd_le (v v' : V) (p p' : P) :
    dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' := by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')
#align dist_vadd_vadd_le dist_vadd_vadd_le

/- warning: dist_vsub_vsub_le -> dist_vsub_vsub_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} V (PseudoMetricSpace.toHasDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) p₁ p₃) (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P _inst_2) p₂ p₄))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} V (PseudoMetricSpace.toDist.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P _inst_2) p₁ p₃) (Dist.dist.{u1} P (PseudoMetricSpace.toDist.{u1} P _inst_2) p₂ p₄))
Case conversion may be inaccurate. Consider using '#align dist_vsub_vsub_le dist_vsub_vsub_leₓ'. -/
theorem dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ :=
  by
  rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V]
  exact norm_sub_le _ _
#align dist_vsub_vsub_le dist_vsub_vsub_le

/- warning: nndist_vadd_vadd_le -> nndist_vadd_vadd_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v p) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v' p')) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNDist.nndist.{u1} V (PseudoMetricSpace.toNNDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) v v') (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) p p'))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v p) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v' p')) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (NNDist.nndist.{u1} V (PseudoMetricSpace.toNNDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) v v') (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) p p'))
Case conversion may be inaccurate. Consider using '#align nndist_vadd_vadd_le nndist_vadd_vadd_leₓ'. -/
theorem nndist_vadd_vadd_le (v v' : V) (p p' : P) :
    nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' := by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vadd_vadd_le]
#align nndist_vadd_vadd_le nndist_vadd_vadd_le

/- warning: nndist_vsub_vsub_le -> nndist_vsub_vsub_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} V (PseudoMetricSpace.toNNDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) p₁ p₃) (NNDist.nndist.{u2} P (PseudoMetricSpace.toNNDist.{u2} P _inst_2) p₂ p₄))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} V (PseudoMetricSpace.toNNDist.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (NNDist.nndist.{u1} P (PseudoMetricSpace.toNNDist.{u1} P _inst_2) p₁ p₃) (NNDist.nndist.{u1} P (PseudoMetricSpace.toNNDist.{u1} P _inst_2) p₂ p₄))
Case conversion may be inaccurate. Consider using '#align nndist_vsub_vsub_le nndist_vsub_vsub_leₓ'. -/
theorem nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ := by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]
#align nndist_vsub_vsub_le nndist_vsub_vsub_le

/- warning: edist_vadd_vadd_le -> edist_vadd_vadd_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} P (PseudoMetricSpace.toEDist.{u2} P _inst_2) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v p) (VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) v' p')) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} V (PseudoMetricSpace.toEDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) v v') (EDist.edist.{u2} P (PseudoMetricSpace.toEDist.{u2} P _inst_2) p p'))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (v : V) (v' : V) (p : P) (p' : P), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} P (PseudoEMetricSpace.toEDist.{u2} P (PseudoMetricSpace.toPseudoEMetricSpace.{u2} P _inst_2)) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v p) (HVAdd.hVAdd.{u1, u2, u2} V P P (instHVAdd.{u1, u2} V P (AddAction.toVAdd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)))) v' p')) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} V (PseudoEMetricSpace.toEDist.{u1} V (PseudoMetricSpace.toPseudoEMetricSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) v v') (EDist.edist.{u2} P (PseudoEMetricSpace.toEDist.{u2} P (PseudoMetricSpace.toPseudoEMetricSpace.{u2} P _inst_2)) p p'))
Case conversion may be inaccurate. Consider using '#align edist_vadd_vadd_le edist_vadd_vadd_leₓ'. -/
theorem edist_vadd_vadd_le (v v' : V) (p p' : P) :
    edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' :=
  by
  simp only [edist_nndist]
  apply_mod_cast nndist_vadd_vadd_le
#align edist_vadd_vadd_le edist_vadd_vadd_le

/- warning: edist_vsub_vsub_le -> edist_vsub_vsub_le is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} V (PseudoMetricSpace.toEDist.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u2} P (PseudoMetricSpace.toEDist.{u2} P _inst_2) p₁ p₃) (EDist.edist.{u2} P (PseudoMetricSpace.toEDist.{u2} P _inst_2) p₂ p₄))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} V (PseudoEMetricSpace.toEDist.{u2} V (PseudoMetricSpace.toPseudoEMetricSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1))) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₁ p₂) (VSub.vsub.{u2, u1} V P (AddTorsor.toVSub.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)) p₃ p₄)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} P (PseudoEMetricSpace.toEDist.{u1} P (PseudoMetricSpace.toPseudoEMetricSpace.{u1} P _inst_2)) p₁ p₃) (EDist.edist.{u1} P (PseudoEMetricSpace.toEDist.{u1} P (PseudoMetricSpace.toPseudoEMetricSpace.{u1} P _inst_2)) p₂ p₄))
Case conversion may be inaccurate. Consider using '#align edist_vsub_vsub_le edist_vsub_vsub_leₓ'. -/
theorem edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ :=
  by
  simp only [edist_nndist]
  apply_mod_cast nndist_vsub_vsub_le
#align edist_vsub_vsub_le edist_vsub_vsub_le

omit V

#print pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor /-
/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type _) [SeminormedAddCommGroup V]
    [AddTorsor V P] : PseudoMetricSpace P
    where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle := by
    intro x y z
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
#align pseudo_metric_space_of_normed_add_comm_group_of_add_torsor pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor
-/

#print metricSpaceOfNormedAddCommGroupOfAddTorsor /-
/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `metric_space
P`. -/
def metricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type _) [NormedAddCommGroup V]
    [AddTorsor V P] : MetricSpace P
    where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  eq_of_dist_eq_zero x y h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle := by
    intro x y z
    change ‖x -ᵥ z‖ ≤ ‖x -ᵥ y‖ + ‖y -ᵥ z‖
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
#align metric_space_of_normed_add_comm_group_of_add_torsor metricSpaceOfNormedAddCommGroupOfAddTorsor
-/

include V

/- warning: lipschitz_with.vadd -> LipschitzWith.vadd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] [_inst_7 : PseudoEMetricSpace.{u1} α] {f : α -> V} {g : α -> P} {Kf : NNReal} {Kg : NNReal}, (LipschitzWith.{u1, u2} α V _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) Kf f) -> (LipschitzWith.{u1, u3} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u3} P _inst_2) Kg g) -> (LipschitzWith.{u1, u3} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u3} P _inst_2) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Kf Kg) (VAdd.vadd.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.vadd'.{u1, u2, u3} α (fun (ᾰ : α) => V) (fun (ᾰ : α) => P) (fun (i : α) => AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u3} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)))) f g))
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2] [_inst_7 : PseudoEMetricSpace.{u3} α] {f : α -> V} {g : α -> P} {Kf : NNReal} {Kg : NNReal}, (LipschitzWith.{u3, u2} α V _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) Kf f) -> (LipschitzWith.{u3, u1} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u1} P _inst_2) Kg g) -> (LipschitzWith.{u3, u1} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u1} P _inst_2) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) Kf Kg) (HVAdd.hVAdd.{max u3 u2, max u3 u1, max u3 u1} (α -> V) (α -> P) (α -> P) (instHVAdd.{max u3 u2, max u3 u1} (α -> V) (α -> P) (Pi.vadd'.{u3, u2, u1} α (fun (a._@.Mathlib.Analysis.Normed.Group.AddTorsor._hyg.1911 : α) => V) (fun (a._@.Mathlib.Analysis.Normed.Group.AddTorsor._hyg.1914 : α) => P) (fun (i : α) => AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3))))) f g))
Case conversion may be inaccurate. Consider using '#align lipschitz_with.vadd LipschitzWith.vaddₓ'. -/
theorem LipschitzWith.vadd [PseudoEMetricSpace α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f +ᵥ g) :=
  fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := (add_le_add (hf x y) (hg x y))
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
    
#align lipschitz_with.vadd LipschitzWith.vadd

/- warning: lipschitz_with.vsub -> LipschitzWith.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] [_inst_7 : PseudoEMetricSpace.{u1} α] {f : α -> P} {g : α -> P} {Kf : NNReal} {Kg : NNReal}, (LipschitzWith.{u1, u3} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u3} P _inst_2) Kf f) -> (LipschitzWith.{u1, u3} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u3} P _inst_2) Kg g) -> (LipschitzWith.{u1, u2} α V _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Kf Kg) (VSub.vsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (AddTorsor.toHasVsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.addGroup.{u1, u2} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1))) (Pi.addTorsor.{u1, u2, u3} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (fun (ᾰ : α) => P) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3))) f g))
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] [_inst_7 : PseudoEMetricSpace.{u3} α] {f : α -> P} {g : α -> P} {Kf : NNReal} {Kg : NNReal}, (LipschitzWith.{u3, u2} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} P _inst_2) Kf f) -> (LipschitzWith.{u3, u2} α P _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u2} P _inst_2) Kg g) -> (LipschitzWith.{u3, u1} α V _inst_7 (PseudoMetricSpace.toPseudoEMetricSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) Kf Kg) (VSub.vsub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (AddTorsor.toVSub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (Pi.addGroup.{u3, u1} α (fun (i : α) => V) (fun (i : α) => AddCommGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u1, u2} α (fun (i : α) => V) (fun (i : α) => P) (fun (ᾰ : α) => SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) f g))
Case conversion may be inaccurate. Consider using '#align lipschitz_with.vsub LipschitzWith.vsubₓ'. -/
theorem LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f -ᵥ g) :=
  fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := (add_le_add (hf x y) (hg x y))
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
    
#align lipschitz_with.vsub LipschitzWith.vsub

/- warning: uniform_continuous_vadd -> uniformContinuous_vadd is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2], UniformContinuous.{max u1 u2, u2} (Prod.{u1, u2} V P) P (Prod.uniformSpace.{u1, u2} V P (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2) (fun (x : Prod.{u1, u2} V P) => VAdd.vadd.{u1, u2} V P (AddAction.toHasVadd.{u1, u2} V P (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)))) (AddTorsor.toAddAction.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) (Prod.fst.{u1, u2} V P x) (Prod.snd.{u1, u2} V P x))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u1} P] [_inst_3 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_2], UniformContinuous.{max u2 u1, u1} (Prod.{u2, u1} V P) P (instUniformSpaceProd.{u2, u1} V P (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)) (PseudoMetricSpace.toUniformSpace.{u1} P _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} P _inst_2) (fun (x : Prod.{u2, u1} V P) => HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)))) (AddTorsor.toAddAction.{u2, u1} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_2 _inst_3)))) (Prod.fst.{u2, u1} V P x) (Prod.snd.{u2, u1} V P x))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_vadd uniformContinuous_vaddₓ'. -/
theorem uniformContinuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2 :=
  (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).UniformContinuous
#align uniform_continuous_vadd uniformContinuous_vadd

/- warning: uniform_continuous_vsub -> uniformContinuous_vsub is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2], UniformContinuous.{u2, u1} (Prod.{u2, u2} P P) V (Prod.uniformSpace.{u2, u2} P P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2) (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (fun (x : Prod.{u2, u2} P P) => VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) (Prod.fst.{u2, u2} P P x) (Prod.snd.{u2, u2} P P x))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2], UniformContinuous.{u2, u1} (Prod.{u2, u2} P P) V (instUniformSpaceProd.{u2, u2} P P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2) (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)) (fun (x : Prod.{u2, u2} P P) => VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) (Prod.fst.{u2, u2} P P x) (Prod.snd.{u2, u2} P P x))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_vsub uniformContinuous_vsubₓ'. -/
theorem uniformContinuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2 :=
  (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).UniformContinuous
#align uniform_continuous_vsub uniformContinuous_vsub

#print NormedAddTorsor.to_continuousVAdd /-
instance (priority := 100) NormedAddTorsor.to_continuousVAdd : ContinuousVAdd V P
    where continuous_vadd := uniformContinuous_vadd.Continuous
#align normed_add_torsor.to_has_continuous_vadd NormedAddTorsor.to_continuousVAdd
-/

/- warning: continuous_vsub -> continuous_vsub is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} P P) V (Prod.topologicalSpace.{u2, u2} P P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2))) (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (fun (x : Prod.{u2, u2} P P) => VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) (Prod.fst.{u2, u2} P P x) (Prod.snd.{u2, u2} P P x))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} P P) V (instTopologicalSpaceProd.{u2, u2} P P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2))) (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (fun (x : Prod.{u2, u2} P P) => VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) (Prod.fst.{u2, u2} P P x) (Prod.snd.{u2, u2} P P x))
Case conversion may be inaccurate. Consider using '#align continuous_vsub continuous_vsubₓ'. -/
theorem continuous_vsub : Continuous fun x : P × P => x.1 -ᵥ x.2 :=
  uniformContinuous_vsub.Continuous
#align continuous_vsub continuous_vsub

/- warning: filter.tendsto.vsub -> Filter.Tendsto.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] {l : Filter.{u1} α} {f : α -> P} {g : α -> P} {x : P} {y : P}, (Filter.Tendsto.{u1, u3} α P f l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) x)) -> (Filter.Tendsto.{u1, u3} α P g l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) y)) -> (Filter.Tendsto.{u1, u2} α V (VSub.vsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (AddTorsor.toHasVsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.addGroup.{u1, u2} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1))) (Pi.addTorsor.{u1, u2, u3} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (fun (ᾰ : α) => P) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3))) f g) l (nhds.{u2} V (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1))) (VSub.vsub.{u2, u3} V P (AddTorsor.toHasVsub.{u2, u3} V P (SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) x y)))
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] {l : Filter.{u3} α} {f : α -> P} {g : α -> P} {x : P} {y : P}, (Filter.Tendsto.{u3, u2} α P f l (nhds.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) x)) -> (Filter.Tendsto.{u3, u2} α P g l (nhds.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) y)) -> (Filter.Tendsto.{u3, u1} α V (VSub.vsub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (AddTorsor.toVSub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (Pi.addGroup.{u3, u1} α (fun (i : α) => V) (fun (i : α) => AddCommGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u1, u2} α (fun (i : α) => V) (fun (i : α) => P) (fun (ᾰ : α) => SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) f g) l (nhds.{u1} V (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3)) x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.vsub Filter.Tendsto.vsubₓ'. -/
theorem Filter.Tendsto.vsub {l : Filter α} {f g : α → P} {x y : P} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (f -ᵥ g) l (𝓝 (x -ᵥ y)) :=
  (continuous_vsub.Tendsto (x, y)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.vsub Filter.Tendsto.vsub

section

variable [TopologicalSpace α]

/- warning: continuous.vsub -> Continuous.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u1} α] {f : α -> P} {g : α -> P}, (Continuous.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) f) -> (Continuous.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) g) -> (Continuous.{u1, u2} α V _inst_7 (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1))) (VSub.vsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (AddTorsor.toHasVsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.addGroup.{u1, u2} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1))) (Pi.addTorsor.{u1, u2, u3} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (fun (ᾰ : α) => P) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3))) f g))
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u3} α] {f : α -> P} {g : α -> P}, (Continuous.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) f) -> (Continuous.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) g) -> (Continuous.{u3, u1} α V _inst_7 (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (VSub.vsub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (AddTorsor.toVSub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (Pi.addGroup.{u3, u1} α (fun (i : α) => V) (fun (i : α) => AddCommGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u1, u2} α (fun (i : α) => V) (fun (i : α) => P) (fun (ᾰ : α) => SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) f g))
Case conversion may be inaccurate. Consider using '#align continuous.vsub Continuous.vsubₓ'. -/
theorem Continuous.vsub {f g : α → P} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f -ᵥ g) :=
  continuous_vsub.comp (hf.prod_mk hg : _)
#align continuous.vsub Continuous.vsub

/- warning: continuous_at.vsub -> ContinuousAt.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u1} α] {f : α -> P} {g : α -> P} {x : α}, (ContinuousAt.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) f x) -> (ContinuousAt.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) g x) -> (ContinuousAt.{u1, u2} α V _inst_7 (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1))) (VSub.vsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (AddTorsor.toHasVsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.addGroup.{u1, u2} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1))) (Pi.addTorsor.{u1, u2, u3} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (fun (ᾰ : α) => P) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3))) f g) x)
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u3} α] {f : α -> P} {g : α -> P} {x : α}, (ContinuousAt.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) f x) -> (ContinuousAt.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) g x) -> (ContinuousAt.{u3, u1} α V _inst_7 (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (VSub.vsub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (AddTorsor.toVSub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (Pi.addGroup.{u3, u1} α (fun (i : α) => V) (fun (i : α) => AddCommGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u1, u2} α (fun (i : α) => V) (fun (i : α) => P) (fun (ᾰ : α) => SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) f g) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.vsub ContinuousAt.vsubₓ'. -/
theorem ContinuousAt.vsub {f g : α → P} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f -ᵥ g) x :=
  hf.vsub hg
#align continuous_at.vsub ContinuousAt.vsub

/- warning: continuous_within_at.vsub -> ContinuousWithinAt.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u1} α] {f : α -> P} {g : α -> P} {x : α} {s : Set.{u1} α}, (ContinuousWithinAt.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) f s x) -> (ContinuousWithinAt.{u1, u3} α P _inst_7 (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) g s x) -> (ContinuousWithinAt.{u1, u2} α V _inst_7 (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1))) (VSub.vsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (AddTorsor.toHasVsub.{max u1 u2, max u1 u3} (α -> V) (α -> P) (Pi.addGroup.{u1, u2} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1))) (Pi.addTorsor.{u1, u2, u3} α (fun (i : α) => V) (fun (i : α) => SeminormedAddGroup.toAddGroup.{u2} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} V _inst_1)) (fun (ᾰ : α) => P) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3))) f g) s x)
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] [_inst_7 : TopologicalSpace.{u3} α] {f : α -> P} {g : α -> P} {x : α} {s : Set.{u3} α}, (ContinuousWithinAt.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) f s x) -> (ContinuousWithinAt.{u3, u2} α P _inst_7 (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) g s x) -> (ContinuousWithinAt.{u3, u1} α V _inst_7 (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1))) (VSub.vsub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (AddTorsor.toVSub.{max u3 u1, max u3 u2} (α -> V) (α -> P) (Pi.addGroup.{u3, u1} α (fun (i : α) => V) (fun (i : α) => AddCommGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))) (AffineMap.instAddTorsorForAllForAllAddGroupToAddGroup.{u3, u1, u2} α (fun (i : α) => V) (fun (i : α) => P) (fun (ᾰ : α) => SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (fun (i : α) => NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3))) f g) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.vsub ContinuousWithinAt.vsubₓ'. -/
theorem ContinuousWithinAt.vsub {f g : α → P} {x : α} {s : Set α} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f -ᵥ g) s x :=
  hf.vsub hg
#align continuous_within_at.vsub ContinuousWithinAt.vsub

end

section

variable {R : Type _} [Ring R] [TopologicalSpace R] [Module R V] [ContinuousSMul R V]

/- warning: filter.tendsto.line_map -> Filter.Tendsto.lineMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] {R : Type.{u4}} [_inst_7 : Ring.{u4} R] [_inst_8 : TopologicalSpace.{u4} R] [_inst_9 : Module.{u4, u2} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))] [_inst_10 : ContinuousSMul.{u4, u2} R V (SMulZeroClass.toHasSmul.{u4, u2} R V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (SMulWithZero.toSmulZeroClass.{u4, u2} R V (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7))))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (MulActionWithZero.toSMulWithZero.{u4, u2} R V (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (Module.toMulActionWithZero.{u4, u2} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)) _inst_9)))) _inst_8 (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)))] {l : Filter.{u1} α} {f₁ : α -> P} {f₂ : α -> P} {g : α -> R} {p₁ : P} {p₂ : P} {c : R}, (Filter.Tendsto.{u1, u3} α P f₁ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₁)) -> (Filter.Tendsto.{u1, u3} α P f₂ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₂)) -> (Filter.Tendsto.{u1, u4} α R g l (nhds.{u4} R _inst_8 c)) -> (Filter.Tendsto.{u1, u3} α P (fun (x : α) => coeFn.{max (succ u4) (succ u2) (succ u3), max (succ u4) (succ u3)} (AffineMap.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) (fun (_x : AffineMap.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) => R -> P) (AffineMap.hasCoeToFun.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) (AffineMap.lineMap.{u4, u2, u3} R V P _inst_7 (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3) (f₁ x) (f₂ x)) (g x)) l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) (coeFn.{max (succ u4) (succ u2) (succ u3), max (succ u4) (succ u3)} (AffineMap.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) (fun (_x : AffineMap.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) => R -> P) (AffineMap.hasCoeToFun.{u4, u4, u4, u2, u3} R R R V P _inst_7 (NonUnitalNonAssocRing.toAddCommGroup.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toModule.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (addGroupIsAddTorsor.{u4} R (AddGroupWithOne.toAddGroup.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3)) (AffineMap.lineMap.{u4, u2, u3} R V P _inst_7 (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3) p₁ p₂) c)))
but is expected to have type
  forall {α : Type.{u4}} {V : Type.{u1}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u1, u3} V P _inst_1 _inst_2] {R : Type.{u2}} [_inst_7 : Ring.{u2} R] [_inst_8 : TopologicalSpace.{u2} R] [_inst_9 : Module.{u2, u1} R V (Ring.toSemiring.{u2} R _inst_7) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))] [_inst_10 : ContinuousSMul.{u2, u1} R V (SMulZeroClass.toSMul.{u2, u1} R V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R V (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_7))) (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R V (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_7)) (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{u2, u1} R V (Ring.toSemiring.{u2} R _inst_7) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) _inst_9)))) _inst_8 (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)))] {l : Filter.{u4} α} {f₁ : α -> P} {f₂ : α -> P} {g : α -> R} {p₁ : P} {p₂ : P} {c : R}, (Filter.Tendsto.{u4, u3} α P f₁ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₁)) -> (Filter.Tendsto.{u4, u3} α P f₂ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₂)) -> (Filter.Tendsto.{u4, u2} α R g l (nhds.{u2} R _inst_8 c)) -> (Filter.Tendsto.{u4, u3} α P (fun (x : α) => FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u2, succ u3} (AffineMap.{u2, u2, u2, u1, u3} R R R V P _inst_7 (Ring.toAddCommGroup.{u2} R _inst_7) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_7) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_7))) (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3)) R (fun (_x : R) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) _x) (AffineMap.funLike.{u2, u2, u2, u1, u3} R R R V P _inst_7 (Ring.toAddCommGroup.{u2} R _inst_7) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_7) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_7))) (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3)) (AffineMap.lineMap.{u2, u1, u3} R V P _inst_7 (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3) (f₁ x) (f₂ x)) (g x)) l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u2, succ u3} (AffineMap.{u2, u2, u2, u1, u3} R R R V P _inst_7 (Ring.toAddCommGroup.{u2} R _inst_7) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_7) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_7))) (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3)) R (fun (_x : R) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1004 : R) => P) _x) (AffineMap.funLike.{u2, u2, u2, u1, u3} R R R V P _inst_7 (Ring.toAddCommGroup.{u2} R _inst_7) (AffineMap.instModuleToSemiringToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonUnitalRing.{u2} R _inst_7) (addGroupIsAddTorsor.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_7))) (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3)) (AffineMap.lineMap.{u2, u1, u3} R V P _inst_7 (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u3} V P _inst_1 _inst_2 _inst_3) p₁ p₂) c)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.line_map Filter.Tendsto.lineMapₓ'. -/
theorem Filter.Tendsto.lineMap {l : Filter α} {f₁ f₂ : α → P} {g : α → R} {p₁ p₂ : P} {c : R}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) l (𝓝 <| AffineMap.lineMap p₁ p₂ c) :=
  (hg.smul (h₂.vsub h₁)).vadd h₁
#align filter.tendsto.line_map Filter.Tendsto.lineMap

/- warning: filter.tendsto.midpoint -> Filter.Tendsto.midpoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : PseudoMetricSpace.{u3} P] [_inst_3 : NormedAddTorsor.{u2, u3} V P _inst_1 _inst_2] {R : Type.{u4}} [_inst_7 : Ring.{u4} R] [_inst_8 : TopologicalSpace.{u4} R] [_inst_9 : Module.{u4, u2} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))] [_inst_10 : ContinuousSMul.{u4, u2} R V (SMulZeroClass.toHasSmul.{u4, u2} R V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (SMulWithZero.toSmulZeroClass.{u4, u2} R V (MulZeroClass.toHasZero.{u4} R (MulZeroOneClass.toMulZeroClass.{u4} R (MonoidWithZero.toMulZeroOneClass.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7))))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (MulActionWithZero.toSMulWithZero.{u4, u2} R V (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1))))) (Module.toMulActionWithZero.{u4, u2} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u2} V (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1)) _inst_9)))) _inst_8 (UniformSpace.toTopologicalSpace.{u2} V (PseudoMetricSpace.toUniformSpace.{u2} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} V _inst_1)))] [_inst_11 : Invertible.{u4} R (Distrib.toHasMul.{u4} R (Ring.toDistrib.{u4} R _inst_7)) (AddMonoidWithOne.toOne.{u4} R (AddGroupWithOne.toAddMonoidWithOne.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7)))) (OfNat.ofNat.{u4} R 2 (OfNat.mk.{u4} R 2 (bit0.{u4} R (Distrib.toHasAdd.{u4} R (Ring.toDistrib.{u4} R _inst_7)) (One.one.{u4} R (AddMonoidWithOne.toOne.{u4} R (AddGroupWithOne.toAddMonoidWithOne.{u4} R (AddCommGroupWithOne.toAddGroupWithOne.{u4} R (Ring.toAddCommGroupWithOne.{u4} R _inst_7))))))))] {l : Filter.{u1} α} {f₁ : α -> P} {f₂ : α -> P} {p₁ : P} {p₂ : P}, (Filter.Tendsto.{u1, u3} α P f₁ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₁)) -> (Filter.Tendsto.{u1, u3} α P f₂ l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) p₂)) -> (Filter.Tendsto.{u1, u3} α P (fun (x : α) => midpoint.{u4, u2, u3} R V P _inst_7 _inst_11 (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3) (f₁ x) (f₂ x)) l (nhds.{u3} P (UniformSpace.toTopologicalSpace.{u3} P (PseudoMetricSpace.toUniformSpace.{u3} P _inst_2)) (midpoint.{u4, u2, u3} R V P _inst_7 _inst_11 (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u2, u3} V P _inst_1 _inst_2 _inst_3) p₁ p₂)))
but is expected to have type
  forall {α : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : PseudoMetricSpace.{u2} P] [_inst_3 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_2] {R : Type.{u4}} [_inst_7 : Ring.{u4} R] [_inst_8 : TopologicalSpace.{u4} R] [_inst_9 : Module.{u4, u1} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))] [_inst_10 : ContinuousSMul.{u4, u1} R V (SMulZeroClass.toSMul.{u4, u1} R V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (SMulWithZero.toSMulZeroClass.{u4, u1} R V (MonoidWithZero.toZero.{u4} R (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7))) (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (MulActionWithZero.toSMulWithZero.{u4, u1} R V (Semiring.toMonoidWithZero.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) (Module.toMulActionWithZero.{u4, u1} R V (Ring.toSemiring.{u4} R _inst_7) (AddCommGroup.toAddCommMonoid.{u1} V (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)) _inst_9)))) _inst_8 (UniformSpace.toTopologicalSpace.{u1} V (PseudoMetricSpace.toUniformSpace.{u1} V (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} V _inst_1)))] [_inst_11 : Invertible.{u4} R (NonUnitalNonAssocRing.toMul.{u4} R (NonAssocRing.toNonUnitalNonAssocRing.{u4} R (Ring.toNonAssocRing.{u4} R _inst_7))) (Semiring.toOne.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (OfNat.ofNat.{u4} R 2 (instOfNat.{u4} R 2 (Semiring.toNatCast.{u4} R (Ring.toSemiring.{u4} R _inst_7)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))] {l : Filter.{u3} α} {f₁ : α -> P} {f₂ : α -> P} {p₁ : P} {p₂ : P}, (Filter.Tendsto.{u3, u2} α P f₁ l (nhds.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) p₁)) -> (Filter.Tendsto.{u3, u2} α P f₂ l (nhds.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) p₂)) -> (Filter.Tendsto.{u3, u2} α P (fun (x : α) => midpoint.{u4, u1, u2} R V P _inst_7 _inst_11 (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3) (f₁ x) (f₂ x)) l (nhds.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_2)) (midpoint.{u4, u1, u2} R V P _inst_7 _inst_11 (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) _inst_9 (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_2 _inst_3) p₁ p₂)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.midpoint Filter.Tendsto.midpointₓ'. -/
theorem Filter.Tendsto.midpoint [Invertible (2 : R)] {l : Filter α} {f₁ f₂ : α → P} {p₁ p₂ : P}
    (h₁ : Tendsto f₁ l (𝓝 p₁)) (h₂ : Tendsto f₂ l (𝓝 p₂)) :
    Tendsto (fun x => midpoint R (f₁ x) (f₂ x)) l (𝓝 <| midpoint R p₁ p₂) :=
  h₁.lineMap h₂ tendsto_const_nhds
#align filter.tendsto.midpoint Filter.Tendsto.midpoint

end

