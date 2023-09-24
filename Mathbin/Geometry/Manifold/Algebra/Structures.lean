/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Geometry.Manifold.Algebra.LieGroup

#align_import geometry.manifold.algebra.structures from "leanprover-community/mathlib"@"30faa0c3618ce1472bf6305ae0e3fa56affa3f95"

/-!
# Smooth structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/


open scoped Manifold

section SmoothRing

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {H : Type _} [TopologicalSpace H] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option default_priority -/
set_option default_priority 100

#print SmoothRing /-
-- see Note [default priority]
-- See note [Design choices about smooth algebraic structures]
/-- A smooth (semi)ring is a (semi)ring `R` where addition and multiplication are smooth.
If `R` is a ring, then negation is automatically smooth, as it is multiplication with `-1`. -/
class SmoothRing (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiring R] [TopologicalSpace R]
    [ChartedSpace H R] extends SmoothAdd I R : Prop where
  smooth_hMul : Smooth (I.Prod I) I fun p : R × R => p.1 * p.2
#align smooth_ring SmoothRing
-/

#print SmoothRing.toSmoothMul /-
instance SmoothRing.toSmoothMul (I : ModelWithCorners 𝕜 E H) (R : Type _) [Semiring R]
    [TopologicalSpace R] [ChartedSpace H R] [h : SmoothRing I R] : SmoothMul I R :=
  { h with }
#align smooth_ring.to_has_smooth_mul SmoothRing.toSmoothMul
-/

#print SmoothRing.toLieAddGroup /-
instance SmoothRing.toLieAddGroup (I : ModelWithCorners 𝕜 E H) (R : Type _) [Ring R]
    [TopologicalSpace R] [ChartedSpace H R] [SmoothRing I R] : LieAddGroup I R
    where
  compatible e e' := HasGroupoid.compatible (contDiffGroupoid ⊤ I)
  smooth_add := smooth_add I
  smooth_neg := by simpa only [neg_one_mul] using @smooth_mul_left 𝕜 _ H _ E _ _ I R _ _ _ _ (-1)
#align smooth_ring.to_lie_add_group SmoothRing.toLieAddGroup
-/

end SmoothRing

#print fieldSmoothRing /-
instance fieldSmoothRing {𝕜 : Type _} [NontriviallyNormedField 𝕜] : SmoothRing 𝓘(𝕜) 𝕜 :=
  { normedSpaceLieAddGroup with
    smooth_hMul := by
      rw [smooth_iff]
      refine' ⟨continuous_mul, fun x y => _⟩
      simp only [Prod.mk.eta, mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }
#align field_smooth_ring fieldSmoothRing
-/

variable {𝕜 R E H : Type _} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)

#print topologicalSemiring_of_smooth /-
/-- A smooth (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
theorem topologicalSemiring_of_smooth [Semiring R] [SmoothRing I R] : TopologicalSemiring R :=
  { continuousMul_of_smooth I, continuousAdd_of_smooth I with }
#align topological_semiring_of_smooth topologicalSemiring_of_smooth
-/

