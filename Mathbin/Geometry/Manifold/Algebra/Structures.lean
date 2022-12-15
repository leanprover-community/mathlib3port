/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module geometry.manifold.algebra.structures
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/


open Manifold

section SmoothRing

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
set_option default_priority 100

-- see Note [default priority]
-- See note [Design choices about smooth algebraic structures]
/-- A smooth (semi)ring is a (semi)ring `R` where addition and multiplication are smooth.
If `R` is a ring, then negation is automatically smooth, as it is multiplication with `-1`. -/
class SmoothRing (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiring R] [TopologicalSpace R]
  [ChartedSpace H R] extends HasSmoothAdd I R : Prop where
  smoothMul : Smooth (I.Prod I) I fun p : R × R => p.1 * p.2
#align smooth_ring SmoothRing

instance SmoothRing.toHasSmoothMul (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiring R]
    [TopologicalSpace R] [ChartedSpace H R] [h : SmoothRing I R] : HasSmoothMul I R :=
  { h with }
#align smooth_ring.to_has_smooth_mul SmoothRing.toHasSmoothMul

instance SmoothRing.toLieAddGroup (I : ModelWithCorners 𝕜 E H) (R : Type _) [Ring R]
    [TopologicalSpace R] [ChartedSpace H R] [SmoothRing I R] :
    LieAddGroup I
      R where 
  compatible e e' := HasGroupoid.compatible (contDiffGroupoid ⊤ I)
  smoothAdd := smoothAdd I
  smoothNeg := by simpa only [neg_one_mul] using @smoothMulLeft 𝕜 _ H _ E _ _ I R _ _ _ _ (-1)
#align smooth_ring.to_lie_add_group SmoothRing.toLieAddGroup

end SmoothRing

instance fieldSmoothRing {𝕜 : Type _} [NontriviallyNormedField 𝕜] : SmoothRing 𝓘(𝕜) 𝕜 :=
  { normedSpaceLieAddGroup with
    smoothMul := by 
      rw [smooth_iff]
      refine' ⟨continuous_mul, fun x y => _⟩
      simp only [Prod.mk.eta, mfld_simps]
      rw [cont_diff_on_univ]
      exact contDiffMul }
#align field_smooth_ring fieldSmoothRing

variable {𝕜 R E H : Type _} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)

/-- A smooth (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
theorem topological_semiring_of_smooth [Semiring R] [SmoothRing I R] : TopologicalSemiring R :=
  { has_continuous_mul_of_smooth I, has_continuous_add_of_smooth I with }
#align topological_semiring_of_smooth topological_semiring_of_smooth

