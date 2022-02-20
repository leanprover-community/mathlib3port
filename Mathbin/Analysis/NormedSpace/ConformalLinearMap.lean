/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.LinearIsometry

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `is_conformal_map` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `is_conformal_map`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `is_conformal_map_of_subsingleton`: all continuous linear maps on singleton spaces are conformal
* `is_conformal_map.preserves_angle`: if a continuous linear map is conformal, then it
                                      preserves all angles in the normed space

See `analysis.normed_space.conformal_linear_map.inner_product` for
* `is_conformal_map_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/


noncomputable section

open LinearIsometry ContinuousLinearMap

/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def IsConformalMap {R : Type _} {X Y : Type _} [NormedField R] [SemiNormedGroup X] [SemiNormedGroup Y] [NormedSpace R X]
    [NormedSpace R Y] (f' : X →L[R] Y) :=
  ∃ (c : R)(hc : c ≠ 0)(li : X →ₗᵢ[R] Y), (f' : X → Y) = c • li

variable {R M N G M' : Type _} [NormedField R] [SemiNormedGroup M] [SemiNormedGroup N] [SemiNormedGroup G]
  [NormedSpace R M] [NormedSpace R N] [NormedSpace R G] [NormedGroup M'] [NormedSpace R M']

theorem is_conformal_map_id : IsConformalMap (id R M) :=
  ⟨1, one_ne_zero, id, by
    ext
    simp ⟩

theorem is_conformal_map_const_smul {c : R} (hc : c ≠ 0) : IsConformalMap (c • id R M) :=
  ⟨c, hc, id, by
    ext
    simp ⟩

theorem LinearIsometry.is_conformal_map (f' : M →ₗᵢ[R] N) : IsConformalMap f'.toContinuousLinearMap :=
  ⟨1, one_ne_zero, f', by
    ext
    simp ⟩

theorem is_conformal_map_of_subsingleton [h : Subsingleton M] (f' : M →L[R] N) : IsConformalMap f' := by
  rw [subsingleton_iff] at h
  have minor : (f' : M → N) = Function.const M 0 := by
    ext x' <;> rw [h x' 0] <;> exact f'.map_zero
  have key : ∀ x' : M, ∥(0 : M →ₗ[R] N) x'∥ = ∥x'∥ := fun x' => by
    rw [LinearMap.zero_apply, h x' 0]
    repeat'
      rw [norm_zero]
  exact
    ⟨(1 : R), one_ne_zero, ⟨0, key⟩, by
      rw [Pi.smul_def]
      ext p
      rw [one_smul, minor]
      rfl⟩

namespace IsConformalMap

theorem comp {f' : M →L[R] N} {g' : N →L[R] G} (hg' : IsConformalMap g') (hf' : IsConformalMap f') :
    IsConformalMap (g'.comp f') := by
  rcases hf' with ⟨cf, hcf, lif, hlif⟩
  rcases hg' with ⟨cg, hcg, lig, hlig⟩
  refine' ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, funext fun x => _⟩
  simp only [coe_comp', LinearIsometry.coe_comp, hlif, hlig, Pi.smul_apply, Function.comp_app, LinearIsometry.map_smul,
    smul_smul]

theorem injective {f' : M' →L[R] N} (h : IsConformalMap f') : Function.Injective f' := by
  let ⟨c, hc, li, hf'⟩ := h
  simp only [hf', Pi.smul_def] <;> exact (smul_right_injective _ hc).comp li.injective

theorem ne_zero [Nontrivial M'] {f' : M' →L[R] N} (hf' : IsConformalMap f') : f' ≠ 0 := by
  intro w
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  have : f' a = f' 0 := by
    simp_rw [w, ContinuousLinearMap.zero_apply]
  exact ha (hf'.injective this)

end IsConformalMap

