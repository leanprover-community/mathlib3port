/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import RingTheory.SimpleModule
import Topology.Algebra.Module.Basic

#align_import topology.algebra.module.simple from "leanprover-community/mathlib"@"19cb3751e5e9b3d97adb51023949c50c13b5fdfd"

/-!
# The kernel of a linear function is closed or dense

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove (`linear_map.is_closed_or_dense_ker`) that the kernel of a linear function `f
: M →ₗ[R] N` is either closed or dense in `M` provided that `N` is a simple module over `R`. This
applies, e.g., to the case when `R = N` is a division ring.
-/


universe u v w

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [ContinuousSMul R M] [Module R N] [ContinuousAdd M]
  [IsSimpleModule R N]

#print LinearMap.isClosed_or_dense_ker /-
/-- The kernel of a linear map taking values in a simple module over the base ring is closed or
dense. Applies, e.g., to the case when `R = N` is a division ring. -/
theorem LinearMap.isClosed_or_dense_ker (l : M →ₗ[R] N) :
    IsClosed (l.ker : Set M) ∨ Dense (l.ker : Set M) :=
  by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact l.ker.is_closed_or_dense_of_is_coatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ
#align linear_map.is_closed_or_dense_ker LinearMap.isClosed_or_dense_ker
-/

