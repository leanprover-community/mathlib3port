/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Complex.Circle
import Mathbin.Analysis.NormedSpace.BallAction
import Mathbin.GroupTheory.Subsemigroup.Membership

/-!
# Poincaré disc

In this file we define `complex.unit_disc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/


open Set Function Metric

open BigOperators

noncomputable section

-- mathport name: exprconj'
local notation "conj'" => starRingEnd ℂ

namespace Complex

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ α,
has_coe[has_coe] α exprℂ() -/
/-- Complex unit disc. -/
def UnitDisc : Type :=
  Ball (0 : ℂ) 1deriving CommSemigroup, HasDistribNeg,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler λ α,
  has_coe[has_coe] α exprℂ()», TopologicalSpace

-- mathport name: expr𝔻
localized [UnitDisc] notation "𝔻" => Complex.UnitDisc

namespace UnitDisc

theorem coe_injective : Injective (coe : 𝔻 → ℂ) :=
  Subtype.coe_injective

theorem abs_lt_one (z : 𝔻) : abs (z : ℂ) < 1 :=
  mem_ball_zero_iff.1 z.2

theorem abs_ne_one (z : 𝔻) : abs (z : ℂ) ≠ 1 :=
  z.abs_lt_one.Ne

theorem norm_sq_lt_one (z : 𝔻) : normSq z < 1 :=
  @one_pow ℝ _ 2 ▸ (Real.sqrt_lt' one_pos).1 z.abs_lt_one

theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne abs <| (map_one abs).symm ▸ z.abs_ne_one

theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne abs <| by
    rw [abs.map_neg, map_one]
    exact z.abs_ne_one

theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

/-- A constructor that assumes `abs z < 1` instead of `dist z 0 < 1` and returns an element 
of `𝔻` instead of `↥metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : abs z < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp]
theorem coe_mk (z : ℂ) (hz : abs z < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : 𝔻) (hz : abs (z : ℂ) < 1 := z.abs_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
theorem mk_neg (z : ℂ) (hz : abs (-z) < 1) : mk (-z) hz = -mk z (abs.map_neg z ▸ hz) :=
  rfl

instance : SemigroupWithZero 𝔻 :=
  { UnitDisc.commSemigroup with zero := mk 0 <| (map_zero _).trans_lt one_pos,
    zero_mul := fun z => coe_injective <| zero_mul _, mul_zero := fun z => coe_injective <| mul_zero _ }

@[simp]
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

instance : Inhabited 𝔻 :=
  ⟨0⟩

instance circleAction : MulAction circle 𝔻 :=
  mulActionSphereBall

instance is_scalar_tower_circle_circle : IsScalarTower circle circle 𝔻 :=
  is_scalar_tower_sphere_sphere_ball

instance is_scalar_tower_circle : IsScalarTower circle 𝔻 𝔻 :=
  is_scalar_tower_sphere_ball_ball

instance smul_comm_class_circle : SmulCommClass circle 𝔻 𝔻 :=
  smul_comm_class_sphere_ball_ball

instance smul_comm_class_circle' : SmulCommClass 𝔻 circle 𝔻 :=
  SmulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_circle (z : circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance closedBallAction : MulAction (ClosedBall (0 : ℂ) 1) 𝔻 :=
  mulActionClosedBallBall

instance is_scalar_tower_closed_ball_closed_ball : IsScalarTower (ClosedBall (0 : ℂ) 1) (ClosedBall (0 : ℂ) 1) 𝔻 :=
  is_scalar_tower_closed_ball_closed_ball_ball

instance is_scalar_tower_closed_ball : IsScalarTower (ClosedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  is_scalar_tower_closed_ball_ball_ball

instance smul_comm_class_closed_ball : SmulCommClass (ClosedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  ⟨fun a b c => Subtype.ext <| mul_left_comm _ _ _⟩

instance smul_comm_class_closed_ball' : SmulCommClass 𝔻 (ClosedBall (0 : ℂ) 1) 𝔻 :=
  SmulCommClass.symm _ _ _

instance smul_comm_class_circle_closed_ball : SmulCommClass circle (ClosedBall (0 : ℂ) 1) 𝔻 :=
  smul_comm_class_sphere_closed_ball_ball

instance smul_comm_class_closed_ball_circle : SmulCommClass (ClosedBall (0 : ℂ) 1) circle 𝔻 :=
  SmulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_closed_ball (z : ClosedBall (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

/-- Real part of a point of the unit disc. -/
def re (z : 𝔻) : ℝ :=
  re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝔻) : ℝ :=
  im z

@[simp, norm_cast]
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

/-- Conjugate point of the unit disc. -/
def conj (z : 𝔻) : 𝔻 :=
  mk (conj' ↑z) <| (abs_conj z).symm ▸ z.abs_lt_one

@[simp, norm_cast]
theorem coe_conj (z : 𝔻) : (z.conj : ℂ) = conj' ↑z :=
  rfl

@[simp]
theorem conj_zero : conj 0 = 0 :=
  coe_injective (map_zero conj')

@[simp]
theorem conj_conj (z : 𝔻) : conj (conj z) = z :=
  coe_injective <| Complex.conj_conj z

@[simp]
theorem conj_neg (z : 𝔻) : (-z).conj = -z.conj :=
  rfl

@[simp]
theorem re_conj (z : 𝔻) : z.conj.re = z.re :=
  rfl

@[simp]
theorem im_conj (z : 𝔻) : z.conj.im = -z.im :=
  rfl

@[simp]
theorem conj_mul (z w : 𝔻) : (z * w).conj = z.conj * w.conj :=
  Subtype.ext <| map_mul _ _ _

end UnitDisc

end Complex

