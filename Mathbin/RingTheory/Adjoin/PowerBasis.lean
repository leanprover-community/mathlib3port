/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.RingTheory.Adjoin.Basic
import Mathbin.RingTheory.PowerBasis

/-!
# Power basis for `algebra.adjoin R {x}`

This file defines the canonical power basis on `algebra.adjoin R {x}`,
where `x` is an integral element over `R`.
-/


variable {K S : Type _} [Field K] [CommRingₓ S] [Algebra K S]

namespace Algebra

open Polynomial

open PowerBasis

open_locale BigOperators

/-- The elements `1, x, ..., x ^ (d - 1)` for a basis for the `K`-module `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Finₓ (minpoly K x).natDegree) K (adjoin K ({x} : Set S)) := by
  have hST : Function.Injective (algebraMap (adjoin K ({x} : Set S)) S) := Subtype.coe_injective
  have hx' : _root_.is_integral K (show adjoin K ({x} : Set S) from ⟨x, subset_adjoin (Set.mem_singleton x)⟩) := by
    apply (is_integral_algebra_map_iff hST).mp
    convert hx
    infer_instance
  have minpoly_eq := minpoly.eq_of_algebra_map_eq hST hx' rfl
  apply
    @Basis.mk (Finₓ (minpoly K x).natDegree) _ (adjoin K {x}) fun i =>
      ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : ℕ)
  · have := hx'.linear_independent_pow
    rwa [minpoly_eq] at this
    
  · rw [_root_.eq_top_iff]
    rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow
    rw [minpoly_eq] at this
    apply this
    · rw [adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
      use f
      ext
      exact (IsScalarTower.algebra_map_aeval K (adjoin K {x}) S ⟨x, _⟩ _).symm
      
    

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps gen dim]
noncomputable def adjoin.powerBasis {x : S} (hx : IsIntegral K x) : PowerBasis K (adjoin K ({x} : Set S)) where
  gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  Basis := adjoin.powerBasisAux hx
  basis_eq_pow := Basis.mk_apply _ _

end Algebra

