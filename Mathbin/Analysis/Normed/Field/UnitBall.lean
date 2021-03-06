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
`group`, `comm_group`) on `metric.ball (0 : π) 1`, `metric.closed_ball (0 : π) 1`, and
`metric.sphere (0 : π) 1`. In each case we use the weakest possible typeclass assumption on `π`,
from `non_unital_semi_normed_ring` to `normed_field`.
-/


open Set Metric

variable {π : Type _}

/-- Unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitBall (π : Type _) [NonUnitalSemiNormedRing π] : Subsemigroup π where
  Carrier := Ball (0 : π) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_ball_zero_iff] at *
    exact (norm_mul_le x y).trans_lt (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy.le)

instance [NonUnitalSemiNormedRing π] : Semigroupβ (Ball (0 : π) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitBall π)

instance [NonUnitalSemiNormedRing π] : HasContinuousMul (Ball (0 : π) 1) :=
  β¨continuous_subtype_mk _ <|
      Continuous.mul (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)β©

instance [SemiNormedCommRing π] : CommSemigroupβ (Ball (0 : π) 1) :=
  MulMemClass.toCommSemigroup (Subsemigroup.unitBall π)

instance [NonUnitalSemiNormedRing π] : HasDistribNeg (Ball (0 : π) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Ball (0 : π) 1 β π) (fun _ => rfl) fun _ _ => rfl

/-- Closed unit ball in a non unital semi normed ring as a bundled `subsemigroup`. -/
def Subsemigroup.unitClosedBall (π : Type _) [NonUnitalSemiNormedRing π] : Subsemigroup π where
  Carrier := ClosedBall 0 1
  mul_mem' := fun x y hx hy => by
    rw [mem_closed_ball_zero_iff] at *
    exact (norm_mul_le x y).trans (mul_le_one hx (norm_nonneg _) hy)

instance [NonUnitalSemiNormedRing π] : Semigroupβ (ClosedBall (0 : π) 1) :=
  MulMemClass.toSemigroup (Subsemigroup.unitClosedBall π)

instance [NonUnitalSemiNormedRing π] : HasDistribNeg (ClosedBall (0 : π) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : ClosedBall (0 : π) 1 β π) (fun _ => rfl) fun _ _ => rfl

instance [NonUnitalSemiNormedRing π] : HasContinuousMul (ClosedBall (0 : π) 1) :=
  β¨continuous_subtype_mk _ <|
      Continuous.mul (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)β©

/-- Closed unit ball in a semi normed ring as a bundled `submonoid`. -/
def Submonoid.unitClosedBall (π : Type _) [SemiNormedRing π] [NormOneClass π] : Submonoid π :=
  { Subsemigroup.unitClosedBall π with Carrier := ClosedBall 0 1, one_mem' := mem_closed_ball_zero_iff.2 norm_one.le }

instance [SemiNormedRing π] [NormOneClass π] : Monoidβ (ClosedBall (0 : π) 1) :=
  SubmonoidClass.toMonoid (Submonoid.unitClosedBall π)

instance [SemiNormedCommRing π] [NormOneClass π] : CommMonoidβ (ClosedBall (0 : π) 1) :=
  SubmonoidClass.toCommMonoid (Submonoid.unitClosedBall π)

/-- Unit sphere in a normed division ring as a bundled `submonoid`. -/
def Submonoid.unitSphere (π : Type _) [NormedDivisionRing π] : Submonoid π where
  Carrier := Sphere (0 : π) 1
  mul_mem' := fun x y hx hy => by
    rw [mem_sphere_zero_iff_norm] at *
    simp [*]
  one_mem' := mem_sphere_zero_iff_norm.2 norm_one

instance [NormedDivisionRing π] : Groupβ (Sphere (0 : π) 1) :=
  { SubmonoidClass.toMonoid (Submonoid.unitSphere π) with
    inv := fun x =>
      β¨xβ»ΒΉ,
        mem_sphere_zero_iff_norm.2 <| by
          rw [norm_inv, mem_sphere_zero_iff_norm.1 x.coe_prop, inv_one]β©,
    mul_left_inv := fun x => Subtype.coe_injective <| inv_mul_cancel <| ne_zero_of_mem_unit_sphere x }

instance [NormedDivisionRing π] : HasDistribNeg (Sphere (0 : π) 1) :=
  Subtype.coe_injective.HasDistribNeg (coe : Sphere (0 : π) 1 β π) (fun _ => rfl) fun _ _ => rfl

/-- Monoid homomorphism from the unit sphere to the group of units. -/
def unitSphereToUnits (π : Type _) [NormedDivisionRing π] : Sphere (0 : π) 1 β* Units π :=
  Units.liftRight (Submonoid.unitSphere π).Subtype (fun x => Units.mk0 x <| ne_zero_of_mem_unit_sphere _) fun x => rfl

instance [NormedDivisionRing π] : TopologicalGroup (Sphere (0 : π) 1) where
  continuous_mul :=
    continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := continuous_subtype_mk _ <| continuous_subtype_coe.invβ ne_zero_of_mem_unit_sphere

instance [NormedField π] : CommGroupβ (Sphere (0 : π) 1) :=
  { Metric.Sphere.group, SubmonoidClass.toCommMonoid (Submonoid.unitSphere π) with }

