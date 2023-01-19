/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.equicontinuity
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformConvergence

/-!
# Algebra-related equicontinuity criterions
-/


open Function

open UniformConvergence

@[to_additive]
theorem equicontinuous_of_equicontinuous_at_one {ι G M hom : Type _} [TopologicalSpace G]
    [UniformSpace M] [Group G] [Group M] [TopologicalGroup G] [UniformGroup M]
    [MonoidHomClass hom G M] (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) :
    Equicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [equicontinuous_iff_continuous]
  rw [equicontinuous_at_iff_continuous_at] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact continuous_of_continuous_at_one φ hf
#align equicontinuous_of_equicontinuous_at_one equicontinuous_of_equicontinuous_at_one
#align equicontinuous_of_equicontinuous_at_zero equicontinuous_of_equicontinuous_at_zero

@[to_additive]
theorem uniform_equicontinuous_of_equicontinuous_at_one {ι G M hom : Type _} [UniformSpace G]
    [UniformSpace M] [Group G] [Group M] [UniformGroup G] [UniformGroup M] [MonoidHomClass hom G M]
    (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) : UniformEquicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [uniform_equicontinuous_iff_uniform_continuous]
  rw [equicontinuous_at_iff_continuous_at] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact uniform_continuous_of_continuous_at_one φ hf
#align uniform_equicontinuous_of_equicontinuous_at_one uniform_equicontinuous_of_equicontinuous_at_one
#align uniform_equicontinuous_of_equicontinuous_at_zero uniform_equicontinuous_of_equicontinuous_at_zero

