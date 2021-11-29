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


noncomputable theory

open LinearIsometry ContinuousLinearMap

/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def IsConformalMap {R : Type _} {X Y : Type _} [NormedField R] [SemiNormedGroup X] [SemiNormedGroup Y]
  [SemiNormedSpace R X] [SemiNormedSpace R Y] (f' : X →L[R] Y) :=
  ∃ (c : R)(hc : c ≠ 0)(li : X →ₗᵢ[R] Y), (f' : X → Y) = c • li

variable {R M N G M' : Type _} [NormedField R] [SemiNormedGroup M] [SemiNormedGroup N] [SemiNormedGroup G]
  [SemiNormedSpace R M] [SemiNormedSpace R N] [SemiNormedSpace R G] [NormedGroup M'] [NormedSpace R M']

theorem is_conformal_map_id : IsConformalMap (id R M) :=
  ⟨1, one_ne_zero, id,
    by 
      ext 
      simp ⟩

theorem is_conformal_map_const_smul {c : R} (hc : c ≠ 0) : IsConformalMap (c • id R M) :=
  ⟨c, hc, id,
    by 
      ext 
      simp ⟩

theorem LinearIsometry.is_conformal_map (f' : M →ₗᵢ[R] N) : IsConformalMap f'.to_continuous_linear_map :=
  ⟨1, one_ne_zero, f',
    by 
      ext 
      simp ⟩

-- error in Analysis.NormedSpace.ConformalLinearMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_conformal_map_of_subsingleton [h : subsingleton M] (f' : «expr →L[ ] »(M, R, N)) : is_conformal_map f' :=
begin
  rw [expr subsingleton_iff] ["at", ident h],
  have [ident minor] [":", expr «expr = »((f' : M → N), function.const M 0)] [":=", expr by ext [] [ident x'] []; rw [expr h x' 0] []; exact [expr f'.map_zero]],
  have [ident key] [":", expr ∀
   x' : M, «expr = »(«expr∥ ∥»((0 : «expr →ₗ[ ] »(M, R, N)) x'), «expr∥ ∥»(x'))] [":=", expr λ
   x', by { rw ["[", expr linear_map.zero_apply, ",", expr h x' 0, "]"] [],
     repeat { rw [expr norm_zero] [] } }],
  exact [expr ⟨(1 : R), one_ne_zero, ⟨0, key⟩, by { rw [expr pi.smul_def] [],
      ext [] [ident p] [],
      rw ["[", expr one_smul, ",", expr minor, "]"] [],
      refl }⟩]
end

namespace IsConformalMap

theorem comp {f' : M →L[R] N} {g' : N →L[R] G} (hg' : IsConformalMap g') (hf' : IsConformalMap f') :
  IsConformalMap (g'.comp f') :=
  by 
    rcases hf' with ⟨cf, hcf, lif, hlif⟩
    rcases hg' with ⟨cg, hcg, lig, hlig⟩
    refine' ⟨cg*cf, mul_ne_zero hcg hcf, lig.comp lif, funext fun x => _⟩
    simp only [coe_comp', LinearIsometry.coe_comp, hlif, hlig, Pi.smul_apply, Function.comp_app,
      LinearIsometry.map_smul, smul_smul]

theorem injective {f' : M' →L[R] N} (h : IsConformalMap f') : Function.Injective f' :=
  let ⟨c, hc, li, hf'⟩ := h 
  by 
    simp only [hf', Pi.smul_def] <;> exact (smul_right_injective _ hc).comp li.injective

-- error in Analysis.NormedSpace.ConformalLinearMap: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ne_zero [nontrivial M'] {f' : «expr →L[ ] »(M', R, N)} (hf' : is_conformal_map f') : «expr ≠ »(f', 0) :=
begin
  intros [ident w],
  rcases [expr exists_ne (0 : M'), "with", "⟨", ident a, ",", ident ha, "⟩"],
  have [] [":", expr «expr = »(f' a, f' 0)] [],
  { simp_rw ["[", expr w, ",", expr continuous_linear_map.zero_apply, "]"] [] },
  exact [expr ha (hf'.injective this)]
end

end IsConformalMap

