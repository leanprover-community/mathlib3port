/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.LocallyConvex.WithSeminorms

/-!
# Weak Dual in Topological Vector Spaces

We prove that the weak topology induced by a bilinear form `B : E ββ[π] F ββ[π] π` is locally
convex and we explicit give a neighborhood basis in terms of the family of seminorms `Ξ» x, β₯B x yβ₯`
for `y : F`.

## Main definitions

* `linear_map.to_seminorm`: turn a linear form `f : E ββ[π] π` into a seminorm `Ξ» x, β₯f xβ₯`.
* `linear_map.to_seminorm_family`: turn a bilinear form `B : E ββ[π] F ββ[π] π` into a map
`F β seminorm π E`.

## Main statements

* `linear_map.has_basis_weak_bilin`: the seminorm balls of `B.to_seminorm_family` form a
neighborhood basis of `0` in the weak topology.
* `linear_map.to_seminorm_family.with_seminorms`: the topology of a weak space is induced by the
family of seminorm `B.to_seminorm_family`.
* `weak_bilin.locally_convex_space`: a spaced endowed with a weak topology is locally convex.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

weak dual, seminorm
-/


variable {π E F ΞΉ : Type _}

open TopologicalSpace

section BilinForm

namespace LinearMap

variable [NormedField π] [AddCommGroupβ E] [Module π E] [AddCommGroupβ F] [Module π F]

/-- Construct a seminorm from a linear form `f : E ββ[π] π` over a normed field `π` by
`Ξ» x, β₯f xβ₯` -/
def toSeminorm (f : E ββ[π] π) : Seminorm π E :=
  (normSeminorm π π).comp f

theorem coe_to_seminorm {f : E ββ[π] π} : βf.toSeminorm = fun x => β₯f xβ₯ :=
  rfl

@[simp]
theorem to_seminorm_apply {f : E ββ[π] π} {x : E} : f.toSeminorm x = β₯f xβ₯ :=
  rfl

theorem to_seminorm_ball_zero {f : E ββ[π] π} {r : β} : Seminorm.Ball f.toSeminorm 0 r = { x : E | β₯f xβ₯ < r } := by
  simp only [β Seminorm.ball_zero_eq, β to_seminorm_apply]

theorem to_seminorm_comp (f : F ββ[π] π) (g : E ββ[π] F) : f.toSeminorm.comp g = (f.comp g).toSeminorm := by
  ext
  simp only [β Seminorm.comp_apply, β to_seminorm_apply, β coe_comp]

/-- Construct a family of seminorms from a bilinear form. -/
def toSeminormFamily (B : E ββ[π] F ββ[π] π) : SeminormFamily π E F := fun y => (B.flip y).toSeminorm

@[simp]
theorem to_seminorm_family_apply {B : E ββ[π] F ββ[π] π} {x y} : (B.toSeminormFamily y) x = β₯B x yβ₯ :=
  rfl

end LinearMap

end BilinForm

section Topology

variable [NormedField π] [AddCommGroupβ E] [Module π E] [AddCommGroupβ F] [Module π F]

variable [Nonempty ΞΉ]

variable {B : E ββ[π] F ββ[π] π}

theorem LinearMap.has_basis_weak_bilin (B : E ββ[π] F ββ[π] π) :
    (π (0 : WeakBilin B)).HasBasis B.toSeminormFamily.basis_sets id := by
  let p := B.to_seminorm_family
  rw [nhds_induced, nhds_pi]
  simp only [β map_zero, β LinearMap.zero_apply]
  have h := @Metric.nhds_basis_ball π _ 0
  have h' := Filter.has_basis_pi fun i : F => h
  have h'' := Filter.HasBasis.comap (fun x y => B x y) h'
  refine' h''.to_has_basis _ _
  Β· rintro (U : Set F Γ (F β β)) hU
    cases' hU with hUβ hUβ
    simp only [β id.def]
    let U' := hUβ.to_finset
    by_cases' hUβ : U.fst.nonempty
    Β· have hUβ' : U'.nonempty := hUβ.nonempty_to_finset.mpr hUβ
      refine'
        β¨(U'.sup p).ball 0 <| U'.inf' hUβ' U.snd,
          p.basis_sets_mem _ <| (Finset.lt_inf'_iff _).2 fun y hy => hUβ y <| hUβ.mem_to_finset.mp hy, fun x hx y hy =>
          _β©
      simp only [β Set.mem_preimage, β Set.mem_pi, β mem_ball_zero_iff]
      rw [Seminorm.mem_ball_zero] at hx
      rw [β LinearMap.to_seminorm_family_apply]
      have hyU' : y β U' := (Set.Finite.mem_to_finset hUβ).mpr hy
      have hp : p y β€ U'.sup p := Finset.le_sup hyU'
      refine' lt_of_le_of_ltβ (hp x) (lt_of_lt_of_leβ hx _)
      exact Finset.inf'_le _ hyU'
      
    rw [set.not_nonempty_iff_eq_empty.mp hUβ]
    simp only [β Set.empty_pi, β Set.preimage_univ, β Set.subset_univ, β and_trueβ]
    exact Exists.intro ((p 0).ball 0 1) (p.basis_sets_singleton_mem 0 one_pos)
    
  rintro U (hU : U β p.basis_sets)
  rw [SeminormFamily.basis_sets_iff] at hU
  rcases hU with β¨s, r, hr, hUβ©
  rw [hU]
  refine'
    β¨(s, fun _ => r),
      β¨by
        simp only [β s.finite_to_set], fun y hy => hrβ©,
      fun x hx => _β©
  simp only [β Set.mem_preimage, β Set.mem_pi, β Finset.mem_coe, β mem_ball_zero_iff] at hx
  simp only [β id.def, β Seminorm.mem_ball, β sub_zero]
  refine' Seminorm.finset_sup_apply_lt hr fun y hy => _
  rw [LinearMap.to_seminorm_family_apply]
  exact hx y hy

instance : WithSeminorms (LinearMap.toSeminormFamily B : F β Seminorm π (WeakBilin B)) :=
  SeminormFamily.with_seminorms_of_has_basis _ B.has_basis_weak_bilin

end Topology

section LocallyConvex

variable [NormedField π] [AddCommGroupβ E] [Module π E] [AddCommGroupβ F] [Module π F]

variable [Nonempty ΞΉ] [NormedSpace β π] [Module β E] [IsScalarTower β π E]

instance {B : E ββ[π] F ββ[π] π} : LocallyConvexSpace β (WeakBilin B) :=
  SeminormFamily.to_locally_convex_space B.toSeminormFamily

end LocallyConvex

