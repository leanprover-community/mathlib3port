/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.Normed.Group.BallSphere

/-!
# Algebraic structures on unit balls and spheres

In this file we define algebraic structures (`semigroup`, `comm_semigroup`, `monoid`, `comm_monoid`,
`group`, `comm_group`) on `metric.ball (0 : 𝕜) 1`, `metric.closed_ball (0 : 𝕜) 1`, and
`metric.sphere (0 : 𝕜) 1`. In each case we use the weakest possible typeclass assumption on `𝕜`,
from `non_unital_semi_normed_ring` to `normed_field`.
-/


open Set Metric

variable {𝕜 : Type _}

/-- Unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitBall (𝕜 : Type _) [NonUnitalSemiNormedRing 𝕜] : Subsemigroup 𝕜 where
  Carrier := Ball (0 : 𝕜) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

instance [NonUnitalSemiNormedRing 𝕜] : Semigroupₓ (Ball (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasContinuousMul (Ball (0 : 𝕜) 1) :=
  (Subsemigroup.unitBall 𝕜).HasContinuousMul

instance [SemiNormedCommRing 𝕜] : CommSemigroupₓ (Ball (0 : 𝕜) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasDistribNeg (Ball (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Ball (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

@[simp, norm_cast]
theorem coe_mul_unit_ball [NonUnitalSemiNormedRing 𝕜] (x y : Ball (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

/-- Closed unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitClosedBall (𝕜 : Type _) [NonUnitalSemiNormedRing 𝕜] : Subsemigroup 𝕜 where
  Carrier := ClosedBall 0 1
  mul_mem' := fun x y hx hy => by
    rw [mem_closed_ball_zero_iff] at *
    exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)

instance [NonUnitalSemiNormedRing 𝕜] : Semigroupₓ (ClosedBall (0 : 𝕜) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall 𝕜)

instance [NonUnitalSemiNormedRing 𝕜] : HasDistribNeg (ClosedBall (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : ClosedBall (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance [NonUnitalSemiNormedRing 𝕜] : HasContinuousMul (ClosedBall (0 : 𝕜) 1) :=
  (Subsemigroup.unitClosedBall 𝕜).HasContinuousMul

@[simp, norm_cast]
theorem coe_mul_unit_closed_ball [NonUnitalSemiNormedRing 𝕜] (x y : ClosedBall (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

/-- Closed unit ball in a semi normed ring as a bundled `submonoid`. -/
def Submonoid.unitClosedBall (𝕜 : Type _) [SemiNormedRing 𝕜] [NormOneClass 𝕜] : Submonoid 𝕜 :=
  { Subsemigroup.unitClosedBall 𝕜 with Carrier := ClosedBall 0 1, one_mem' := mem_closed_ball_zero_iff.2 norm_one.le }

instance [SemiNormedRing 𝕜] [NormOneClass 𝕜] : Monoidₓ (ClosedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall 𝕜)

instance [SemiNormedCommRing 𝕜] [NormOneClass 𝕜] : CommMonoidₓ (ClosedBall (0 : 𝕜) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall 𝕜)

@[simp, norm_cast]
theorem coe_one_unit_closed_ball [SemiNormedRing 𝕜] [NormOneClass 𝕜] : ((1 : ClosedBall (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_pow_unit_closed_ball [SemiNormedRing 𝕜] [NormOneClass 𝕜] (x : ClosedBall (0 : 𝕜) 1) (n : ℕ) :
    ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl

/-- Unit sphere in a normed division ring as a bundled `submonoid`. -/
def Submonoid.unitSphere (𝕜 : Type _) [NormedDivisionRing 𝕜] : Submonoid 𝕜 where
  Carrier := Sphere (0 : 𝕜) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

instance [NormedDivisionRing 𝕜] : Inv (Sphere (0 : 𝕜) 1) :=
  ⟨fun x =>
    ⟨x⁻¹,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]⟩⟩

@[simp, norm_cast]
theorem coe_inv_unit_sphere [NormedDivisionRing 𝕜] (x : Sphere (0 : 𝕜) 1) : ↑x⁻¹ = (x⁻¹ : 𝕜) :=
  rfl

instance [NormedDivisionRing 𝕜] : Div (Sphere (0 : 𝕜) 1) :=
  ⟨fun x y =>
    ⟨x / y,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div, mem_sphere_zero_iff_norm.1 x.coe_prop, mem_sphere_zero_iff_norm.1 y.coe_prop, div_one]⟩⟩

@[simp, norm_cast]
theorem coe_div_unit_sphere [NormedDivisionRing 𝕜] (x y : Sphere (0 : 𝕜) 1) : ↑(x / y) = (x / y : 𝕜) :=
  rfl

instance [NormedDivisionRing 𝕜] : Pow (Sphere (0 : 𝕜) 1) ℤ :=
  ⟨fun x n =>
    ⟨x ^ n, by
      rw [mem_sphere_zero_iff_norm, norm_zpow, mem_sphere_zero_iff_norm.1 x.coe_prop, one_zpow]⟩⟩

@[simp, norm_cast]
theorem coe_zpow_unit_sphere [NormedDivisionRing 𝕜] (x : Sphere (0 : 𝕜) 1) (n : ℤ) : ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl

instance [NormedDivisionRing 𝕜] : Monoidₓ (Sphere (0 : 𝕜) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitSphere 𝕜)

@[simp, norm_cast]
theorem coe_one_unit_sphere [NormedDivisionRing 𝕜] : ((1 : Sphere (0 : 𝕜) 1) : 𝕜) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_mul_unit_sphere [NormedDivisionRing 𝕜] (x y : Sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y : 𝕜) :=
  rfl

@[simp, norm_cast]
theorem coe_pow_unit_sphere [NormedDivisionRing 𝕜] (x : Sphere (0 : 𝕜) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : 𝕜) :=
  rfl

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unitSphereToUnits (𝕜 : Type _) [NormedDivisionRing 𝕜] : Sphere (0 : 𝕜) 1 →* Units 𝕜 :=
  Units.liftRight (Submonoid.unitSphere 𝕜).Subtype (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun x => rfl

@[simp]
theorem unit_sphere_to_units_apply_coe [NormedDivisionRing 𝕜] (x : Sphere (0 : 𝕜) 1) :
    (unitSphereToUnits 𝕜 x : 𝕜) = x :=
  rfl

theorem unit_sphere_to_units_injective [NormedDivisionRing 𝕜] : Function.Injective (unitSphereToUnits 𝕜) := fun x y h =>
  Subtype.eq <| by
    convert congr_arg Units.val h

instance [NormedDivisionRing 𝕜] : Groupₓ (Sphere (0 : 𝕜) 1) :=
  unit_sphere_to_units_injective.Group (unitSphereToUnits 𝕜) (Units.ext rfl) (fun x y => Units.ext rfl)
    (fun x => Units.ext rfl) (fun x y => Units.ext <| div_eq_mul_inv _ _)
    (fun x n => Units.ext (Units.coe_pow (unitSphereToUnits 𝕜 x) n).symm) fun x n =>
    Units.ext (Units.coe_zpow (unitSphereToUnits 𝕜 x) n).symm

instance [NormedDivisionRing 𝕜] : HasDistribNeg (Sphere (0 : 𝕜) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Sphere (0 : 𝕜) 1 → 𝕜) (fun _ => rfl) fun _ _ => rfl

instance [NormedDivisionRing 𝕜] : TopologicalGroup (Sphere (0 : 𝕜) 1) where
  to_has_continuous_mul := (Submonoid.unitSphere 𝕜).HasContinuousMul
  continuous_inv := (continuous_subtype_coe.inv₀ ne_zero_of_mem_unit_sphere).subtype_mk _

instance [NormedField 𝕜] : CommGroupₓ (Sphere (0 : 𝕜) 1) :=
  { Metric.Sphere.group, SubmonoidClass.toCommMonoid (Submonoid.unitSphere 𝕜) with }

