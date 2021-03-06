/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle KytΓΆlΓ€
-/
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.Convex.Basic
import Mathbin.LinearAlgebra.SesquilinearForm
import Mathbin.Topology.Algebra.Module.WeakDual

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E ββ[π] F ββ[π] π`, where `π` is a normed commutative ring and
`E` and `F` are modules over `π`.

## Main definitions

* `linear_map.polar`: The polar of a bilinear form `B : E ββ[π] F ββ[π] π`.

## Main statements

* `linear_map.polar_eq_Inter`: The polar as an intersection.
* `linear_map.subset_bipolar`: The polar is a subset of the bipolar.
* `linear_map.polar_weak_closed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/


variable {π E F : Type _}

namespace LinearMap

section NormedRing

variable [NormedCommRing π] [AddCommMonoidβ E] [AddCommMonoidβ F]

variable [Module π E] [Module π F]

variable (B : E ββ[π] F ββ[π] π)

/-- The (absolute) polar of `s : set E` is given by the set of all `y : F` such that `β₯B x yβ₯ β€ 1`
for all `x β s`.-/
def Polar (s : Set E) : Set F :=
  { y : F | β, β x β s, β, β₯B x yβ₯ β€ 1 }

theorem polar_mem_iff (s : Set E) (y : F) : y β B.Polar s β β, β x β s, β, β₯B x yβ₯ β€ 1 :=
  Iff.rfl

theorem polar_mem (s : Set E) (y : F) (hy : y β B.Polar s) : β, β x β s, β, β₯B x yβ₯ β€ 1 :=
  hy

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : F) β B.Polar s := fun _ _ => by
  simp only [β map_zero, β norm_zero, β zero_le_one]

theorem polar_eq_Inter {s : Set E} : B.Polar s = β x β s, { y : F | β₯B x yβ₯ β€ 1 } := by
  ext
  simp only [β polar_mem_iff, β Set.mem_Inter, β Set.mem_set_of_eq]

/-- The map `B.polar : set E β set F` forms an order-reversing Galois connection with
`B.flip.polar : set F β set E`. We use `order_dual.to_dual` and `order_dual.of_dual` to express
that `polar` is order-reversing. -/
theorem polar_gc : GaloisConnection (OrderDual.toDual β B.Polar) (B.flip.Polar β OrderDual.ofDual) := fun s t =>
  β¨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hxβ©

@[simp]
theorem polar_Union {ΞΉ} {s : ΞΉ β Set E} : B.Polar (β i, s i) = β i, B.Polar (s i) :=
  B.polar_gc.l_supr

@[simp]
theorem polar_union {s t : Set E} : B.Polar (s βͺ t) = B.Polar s β© B.Polar t :=
  B.polar_gc.l_sup

theorem polar_antitone : Antitone (B.Polar : Set E β Set F) :=
  B.polar_gc.monotone_l

@[simp]
theorem polar_empty : B.Polar β = Set.Univ :=
  B.polar_gc.l_bot

@[simp]
theorem polar_zero : B.Polar ({0} : Set E) = Set.Univ := by
  refine' set.eq_univ_iff_forall.mpr fun y x hx => _
  rw [set.mem_singleton_iff.mp hx, map_zero, LinearMap.zero_apply, norm_zero]
  exact zero_le_one

theorem subset_bipolar (s : Set E) : s β B.flip.Polar (B.Polar s) := fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
theorem tripolar_eq_polar (s : Set E) : B.Polar (B.flip.Polar (B.Polar s)) = B.Polar s := by
  refine' (B.polar_antitone (B.subset_bipolar s)).antisymm _
  convert subset_bipolar B.flip (B.polar s)
  exact B.flip_flip.symm

/-- The polar set is closed in the weak topology induced by `B.flip`. -/
theorem polar_weak_closed (s : Set E) : @IsClosed _ (WeakBilin.topologicalSpace B.flip) (B.Polar s) := by
  rw [polar_eq_Inter]
  refine' is_closed_Inter fun x => is_closed_Inter fun _ => _
  exact is_closed_le (WeakBilin.eval_continuous B.flip x).norm continuous_const

end NormedRing

section NondiscreteNormedField

variable [NondiscreteNormedField π] [AddCommMonoidβ E] [AddCommMonoidβ F]

variable [Module π E] [Module π F]

variable (B : E ββ[π] F ββ[π] π)

theorem polar_univ (h : SeparatingRight B) : B.Polar Set.Univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine'
    β¨by
      simp only [β zero_mem_polar], fun y hy => h _ fun x => _β©
  refine' norm_le_zero_iff.mp (le_of_forall_le_of_dense fun Ξ΅ hΞ΅ => _)
  rcases NormedField.exists_norm_lt π hΞ΅ with β¨c, hc, hcΞ΅β©
  calc β₯B x yβ₯ = β₯cβ₯ * β₯B (cβ»ΒΉ β’ x) yβ₯ := by
      rw [B.map_smul, LinearMap.smul_apply, Algebra.id.smul_eq_mul, norm_mul, norm_inv,
        mul_inv_cancel_leftβ hc.ne']_ β€ Ξ΅ * 1 :=
      mul_le_mul hcΞ΅.le (hy _ trivialβ) (norm_nonneg _) hΞ΅.le _ = Ξ΅ := mul_oneβ _

end NondiscreteNormedField

end LinearMap

