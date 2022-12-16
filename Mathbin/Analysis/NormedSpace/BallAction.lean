/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth

! This file was ported from Lean 3 source module analysis.normed_space.ball_action
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

variable {𝕜 𝕜' E : Type _} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] {r : ℝ}

section ClosedBall

instance mulActionClosedBallBall :
    MulAction (closedBall (0 : 𝕜) 1)
      (ball (0 : E)
        r) where 
  smul c x :=
    ⟨(c : 𝕜) • x,
      mem_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closed_ball_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩
  one_smul x := Subtype.ext <| one_smul 𝕜 _
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul _ _ _
#align mul_action_closed_ball_ball mulActionClosedBallBall

instance has_continuous_smul_closed_ball_ball :
    HasContinuousSmul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩
#align has_continuous_smul_closed_ball_ball has_continuous_smul_closed_ball_ball

instance mulActionClosedBallClosedBall :
    MulAction (closedBall (0 : 𝕜) 1)
      (closedBall (0 : E)
        r) where 
  smul c x :=
    ⟨(c : 𝕜) • x,
      mem_closed_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closed_ball_zero_iff.1 c.2) (mem_closed_ball_zero_iff.1 x.2)
            (norm_nonneg _) zero_le_one⟩
  one_smul x := Subtype.ext <| one_smul 𝕜 _
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul _ _ _
#align mul_action_closed_ball_closed_ball mulActionClosedBallClosedBall

instance has_continuous_smul_closed_ball_closed_ball :
    HasContinuousSmul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩
#align has_continuous_smul_closed_ball_closed_ball has_continuous_smul_closed_ball_closed_ball

end ClosedBall

section Sphere

instance mulActionSphereBall :
    MulAction (sphere (0 : 𝕜) 1)
      (ball (0 : E)
        r) where 
  smul c x := inclusion sphere_subset_closed_ball c • x
  one_smul x := Subtype.ext <| one_smul _ _
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul _ _ _
#align mul_action_sphere_ball mulActionSphereBall

instance has_continuous_smul_sphere_ball : HasContinuousSmul (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩
#align has_continuous_smul_sphere_ball has_continuous_smul_sphere_ball

instance mulActionSphereClosedBall :
    MulAction (sphere (0 : 𝕜) 1)
      (closedBall (0 : E)
        r) where 
  smul c x := inclusion sphere_subset_closed_ball c • x
  one_smul x := Subtype.ext <| one_smul _ _
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul _ _ _
#align mul_action_sphere_closed_ball mulActionSphereClosedBall

instance has_continuous_smul_sphere_closed_ball :
    HasContinuousSmul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩
#align has_continuous_smul_sphere_closed_ball has_continuous_smul_sphere_closed_ball

instance mulActionSphereSphere :
    MulAction (sphere (0 : 𝕜) 1)
      (sphere (0 : E)
        r) where 
  smul c x :=
    ⟨(c : 𝕜) • x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop,
          one_mul]⟩
  one_smul x := Subtype.ext <| one_smul _ _
  mul_smul c₁ c₂ x := Subtype.ext <| mul_smul _ _ _
#align mul_action_sphere_sphere mulActionSphereSphere

instance has_continuous_smul_sphere_sphere :
    HasContinuousSmul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
  ⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩
#align has_continuous_smul_sphere_sphere has_continuous_smul_sphere_sphere

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

instance is_scalar_tower_closed_ball_closed_ball_closed_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align
  is_scalar_tower_closed_ball_closed_ball_closed_ball is_scalar_tower_closed_ball_closed_ball_closed_ball

instance is_scalar_tower_closed_ball_closed_ball_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_closed_ball_closed_ball_ball is_scalar_tower_closed_ball_closed_ball_ball

instance is_scalar_tower_sphere_closed_ball_closed_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_sphere_closed_ball_closed_ball is_scalar_tower_sphere_closed_ball_closed_ball

instance is_scalar_tower_sphere_closed_ball_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_sphere_closed_ball_ball is_scalar_tower_sphere_closed_ball_ball

instance is_scalar_tower_sphere_sphere_closed_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_sphere_sphere_closed_ball is_scalar_tower_sphere_sphere_closed_ball

instance is_scalar_tower_sphere_sphere_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_sphere_sphere_ball is_scalar_tower_sphere_sphere_ball

instance is_scalar_tower_sphere_sphere_sphere :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
#align is_scalar_tower_sphere_sphere_sphere is_scalar_tower_sphere_sphere_sphere

instance is_scalar_tower_sphere_ball_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩
#align is_scalar_tower_sphere_ball_ball is_scalar_tower_sphere_ball_ball

instance is_scalar_tower_closed_ball_ball_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩
#align is_scalar_tower_closed_ball_ball_ball is_scalar_tower_closed_ball_ball_ball

end IsScalarTower

section SMulCommClass

variable [SMulCommClass 𝕜 𝕜' E]

instance smul_comm_class_closed_ball_closed_ball_closed_ball :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align
  smul_comm_class_closed_ball_closed_ball_closed_ball smul_comm_class_closed_ball_closed_ball_closed_ball

instance smul_comm_class_closed_ball_closed_ball_ball :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_closed_ball_closed_ball_ball smul_comm_class_closed_ball_closed_ball_ball

instance smul_comm_class_sphere_closed_ball_closed_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_sphere_closed_ball_closed_ball smul_comm_class_sphere_closed_ball_closed_ball

instance smul_comm_class_sphere_closed_ball_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_sphere_closed_ball_ball smul_comm_class_sphere_closed_ball_ball

instance smul_comm_class_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] :
    SMulCommClass (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩
#align smul_comm_class_sphere_ball_ball smul_comm_class_sphere_ball_ball

instance smul_comm_class_sphere_sphere_closed_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_sphere_sphere_closed_ball smul_comm_class_sphere_sphere_closed_ball

instance smul_comm_class_sphere_sphere_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_sphere_sphere_ball smul_comm_class_sphere_sphere_ball

instance smul_comm_class_sphere_sphere_sphere :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
#align smul_comm_class_sphere_sphere_sphere smul_comm_class_sphere_sphere_sphere

end SMulCommClass

variable (𝕜) [CharZero 𝕜]

theorem ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : sphere (0 : E) r) : x ≠ -x := fun h =>
  ne_zero_of_mem_sphere hr x
    ((self_eq_neg 𝕜 _).mp
      (by 
        conv_lhs => rw [h]
        simp))
#align ne_neg_of_mem_sphere ne_neg_of_mem_sphere

theorem ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x
#align ne_neg_of_mem_unit_sphere ne_neg_of_mem_unit_sphere

