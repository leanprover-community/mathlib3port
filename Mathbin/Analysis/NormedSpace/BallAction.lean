/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Field.UnitBall
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `π`. In this file we define the following
multiplicative actions.

- The closed unit ball in `π` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `π` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/


open Metric Set

variable {π E : Type _} [NormedField π] [SemiNormedGroup E] [NormedSpace π E] {r : β}

section ClosedBall

instance mulActionClosedBallBall : MulAction (ClosedBall (0 : π) 1) (Ball (0 : E) r) where
  smul := fun c x =>
    β¨(c : π) β’ x,
      mem_ball_zero_iff.2 <| by
        simpa only [β norm_smul, β one_mulβ] using
          mul_lt_mul' (mem_closed_ball_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _) one_posβ©
  one_smul := fun x => Subtype.ext <| one_smul π _
  mul_smul := fun cβ cβ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_ball : HasContinuousSmul (ClosedBall (0 : π) 1) (Ball (0 : E) r) :=
  β¨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)β©

instance mulActionClosedBallClosedBall : MulAction (ClosedBall (0 : π) 1) (ClosedBall (0 : E) r) where
  smul := fun c x =>
    β¨(c : π) β’ x,
      mem_closed_ball_zero_iff.2 <| by
        simpa only [β norm_smul, β one_mulβ] using
          mul_le_mul (mem_closed_ball_zero_iff.1 c.2) (mem_closed_ball_zero_iff.1 x.2) (norm_nonneg _) zero_le_oneβ©
  one_smul := fun x => Subtype.ext <| one_smul π _
  mul_smul := fun cβ cβ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_closed_ball :
    HasContinuousSmul (ClosedBall (0 : π) 1) (ClosedBall (0 : E) r) :=
  β¨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)β©

end ClosedBall

section Sphere

instance mulActionSphereBall : MulAction (Sphere (0 : π) 1) (Ball (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c β’ x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun cβ cβ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_ball : HasContinuousSmul (Sphere (0 : π) 1) (Ball (0 : E) r) :=
  β¨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)β©

instance mulActionSphereClosedBall : MulAction (Sphere (0 : π) 1) (ClosedBall (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c β’ x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun cβ cβ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_closed_ball : HasContinuousSmul (Sphere (0 : π) 1) (ClosedBall (0 : E) r) :=
  β¨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)β©

instance mulActionSphereSphere : MulAction (Sphere (0 : π) 1) (Sphere (0 : E) r) where
  smul := fun c x =>
    β¨(c : π) β’ x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop, one_mulβ]β©
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun cβ cβ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_sphere : HasContinuousSmul (Sphere (0 : π) 1) (Sphere (0 : E) r) :=
  β¨continuous_subtype_mk _ <|
      (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)β©

end Sphere

variable (π) [CharZero π]

theorem ne_neg_of_mem_sphere {r : β} (hr : r β  0) (x : Sphere (0 : E) r) : x β  -x := fun h =>
  ne_zero_of_mem_sphere hr x
    ((self_eq_neg π _).mp
      (by
        conv_lhs => rw [h]
        simp ))

theorem ne_neg_of_mem_unit_sphere (x : Sphere (0 : E) 1) : x β  -x :=
  ne_neg_of_mem_sphere π one_ne_zero x

