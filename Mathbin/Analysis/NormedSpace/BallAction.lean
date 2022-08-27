/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Normed.Field.UnitBall
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/


open Metric Set

variable {𝕜 𝕜' E : Type _} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜' E] {r : ℝ}

section ClosedBall

instance mulActionClosedBallBall : MulAction (ClosedBall (0 : 𝕜) 1) (Ball (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mulₓ] using
          mul_lt_mul' (mem_closed_ball_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _) one_pos⟩
  one_smul := fun x => Subtype.ext <| one_smul 𝕜 _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_ball : HasContinuousSmul (ClosedBall (0 : 𝕜) 1) (Ball (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mulActionClosedBallClosedBall : MulAction (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_closed_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mulₓ] using
          mul_le_mul (mem_closed_ball_zero_iff.1 c.2) (mem_closed_ball_zero_iff.1 x.2) (norm_nonneg _) zero_le_one⟩
  one_smul := fun x => Subtype.ext <| one_smul 𝕜 _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_closed_ball_closed_ball :
    HasContinuousSmul (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

end ClosedBall

section Sphere

instance mulActionSphereBall : MulAction (Sphere (0 : 𝕜) 1) (Ball (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c • x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_ball : HasContinuousSmul (Sphere (0 : 𝕜) 1) (Ball (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mulActionSphereClosedBall : MulAction (Sphere (0 : 𝕜) 1) (ClosedBall (0 : E) r) where
  smul := fun c x => inclusion sphere_subset_closed_ball c • x
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_closed_ball : HasContinuousSmul (Sphere (0 : 𝕜) 1) (ClosedBall (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mulActionSphereSphere : MulAction (Sphere (0 : 𝕜) 1) (Sphere (0 : E) r) where
  smul := fun c x =>
    ⟨(c : 𝕜) • x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop, one_mulₓ]⟩
  one_smul := fun x => Subtype.ext <| one_smul _ _
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul _ _ _

instance has_continuous_smul_sphere_sphere : HasContinuousSmul (Sphere (0 : 𝕜) 1) (Sphere (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

instance is_scalar_tower_closed_ball_closed_ball_closed_ball :
    IsScalarTower (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_closed_ball_closed_ball_ball :
    IsScalarTower (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_closed_ball_closed_ball :
    IsScalarTower (Sphere (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_closed_ball_ball :
    IsScalarTower (Sphere (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_closed_ball :
    IsScalarTower (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_ball : IsScalarTower (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_sphere :
    IsScalarTower (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (Sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_ball_ball : IsScalarTower (Sphere (0 : 𝕜) 1) (Ball (0 : 𝕜') 1) (Ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance is_scalar_tower_closed_ball_ball_ball :
    IsScalarTower (ClosedBall (0 : 𝕜) 1) (Ball (0 : 𝕜') 1) (Ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

end IsScalarTower

section SmulCommClass

variable [SmulCommClass 𝕜 𝕜' E]

instance smul_comm_class_closed_ball_closed_ball_closed_ball :
    SmulCommClass (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_closed_ball_closed_ball_ball :
    SmulCommClass (ClosedBall (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_closed_ball_closed_ball :
    SmulCommClass (Sphere (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_closed_ball_ball :
    SmulCommClass (Sphere (0 : 𝕜) 1) (ClosedBall (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] :
    SmulCommClass (Sphere (0 : 𝕜) 1) (Ball (0 : 𝕜') 1) (Ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance smul_comm_class_sphere_sphere_closed_ball :
    SmulCommClass (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (ClosedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_sphere_ball : SmulCommClass (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (Ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_sphere_sphere :
    SmulCommClass (Sphere (0 : 𝕜) 1) (Sphere (0 : 𝕜') 1) (Sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

end SmulCommClass

variable (𝕜) [CharZero 𝕜]

theorem ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : Sphere (0 : E) r) : x ≠ -x := fun h =>
  ne_zero_of_mem_sphere hr x
    ((self_eq_neg 𝕜 _).mp
      (by
        conv_lhs => rw [h]
        simp ))

theorem ne_neg_of_mem_unit_sphere (x : Sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x

