/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import Mathbin.Algebra.DirectSum.Algebra
import Mathbin.Algebra.DirectSum.Internal
import Mathbin.Algebra.DirectSum.Ring
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Internally-graded algebras

This file defines the typeclass `graded_algebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_algebra 𝒜`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  a constructive version of `direct_sum.submodule_is_internal 𝒜`.
* `graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i`, which breaks apart an element of the algebra into
  its constituent pieces.
* `graded_algebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.
* `graded_algebra.support 𝒜 r` is the `finset ι` containing the `i : ι` such that the degree `i`
  component of `r` is not zero.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → submodule ℕ A` and `𝒜 : ι → submodule ℤ A` respectively, since all
`semiring`s are ℕ-algebras via `algebra_nat`, and all `ring`s are `ℤ`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/


open DirectSum BigOperators

section GradedAlgebra

variable {ι R A : Type _}

variable [DecidableEq ι] [AddMonoidₓ ι] [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra 𝒜`, implies an externally-graded
algebra structure `direct_sum.galgebra R (λ i, ↥(𝒜 i))`, which in turn makes available an
`algebra R (⨁ i, 𝒜 i)` instance.
-/
class GradedAlgebra extends SetLike.GradedMonoid 𝒜 where
  decompose' : A → ⨁ i, 𝒜 i
  left_inv : Function.LeftInverse decompose' (DirectSum.submoduleCoe 𝒜)
  right_inv : Function.RightInverse decompose' (DirectSum.submoduleCoe 𝒜)

theorem GradedAlgebra.is_internal [GradedAlgebra 𝒜] : DirectSum.SubmoduleIsInternal 𝒜 :=
  ⟨GradedAlgebra.left_inv.Injective, GradedAlgebra.right_inv.Surjective⟩

/-- A helper to construct a `graded_algebra` when the `set_like.graded_monoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
@[reducible]
def GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
    (right_inv : (DirectSum.submoduleCoeAlgHom 𝒜).comp decompose = AlgHom.id R A)
    (left_inv : ∀ i x : 𝒜 i, decompose (x : A) = DirectSum.of (fun i => ↥(𝒜 i)) i x) : GradedAlgebra 𝒜 where
  decompose' := decompose
  right_inv := AlgHom.congr_fun right_inv
  left_inv := by
    suffices : decompose.comp (DirectSum.submoduleCoeAlgHom 𝒜) = AlgHom.id _ _
    exact AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.submodule_coe_alg_hom_of _ _ _).trans (left_inv i x)

variable [GradedAlgebra 𝒜]

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
def GradedAlgebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i :=
  AlgEquiv.symm
    { toFun := DirectSum.submoduleCoeAlgHom 𝒜, invFun := GradedAlgebra.decompose', left_inv := GradedAlgebra.left_inv,
      right_inv := GradedAlgebra.right_inv, map_mul' := AlgHom.map_mul _, map_add' := AlgHom.map_add _,
      commutes' := AlgHom.commutes _ }

@[simp]
theorem GradedAlgebra.decompose'_def : GradedAlgebra.decompose' = GradedAlgebra.decompose 𝒜 :=
  rfl

@[simp]
theorem GradedAlgebra.decompose_symm_of {i : ι} (x : 𝒜 i) : (GradedAlgebra.decompose 𝒜).symm (DirectSum.of _ i x) = x :=
  DirectSum.submodule_coe_alg_hom_of 𝒜 _ _

/-- The projection maps of graded algebra-/
def GradedAlgebra.proj (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A →ₗ[R] A :=
  (𝒜 i).Subtype.comp <| (Dfinsupp.lapply i).comp <| (GradedAlgebra.decompose 𝒜).toAlgHom.toLinearMap

@[simp]
theorem GradedAlgebra.proj_apply (i : ι) (r : A) :
    GradedAlgebra.proj 𝒜 i r = (GradedAlgebra.decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def GradedAlgebra.support [∀ i : ι x : 𝒜 i, Decidable (x ≠ 0)] (r : A) : Finset ι :=
  (GradedAlgebra.decompose 𝒜 r).support

theorem GradedAlgebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedAlgebra.proj 𝒜 i ((GradedAlgebra.decompose 𝒜).symm a) =
      (GradedAlgebra.decompose 𝒜).symm (DirectSum.of _ i (a i)) :=
  by
  rw [GradedAlgebra.proj_apply, GradedAlgebra.decompose_symm_of, AlgEquiv.apply_symm_apply]

@[simp]
theorem GradedAlgebra.decompose_coe {i : ι} (x : 𝒜 i) : GradedAlgebra.decompose 𝒜 x = DirectSum.of _ i x := by
  rw [← GradedAlgebra.decompose_symm_of, AlgEquiv.apply_symm_apply]

theorem GradedAlgebra.decompose_of_mem {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
    GradedAlgebra.decompose 𝒜 x = DirectSum.of _ i (⟨x, hx⟩ : 𝒜 i) :=
  GradedAlgebra.decompose_coe _ ⟨x, hx⟩

theorem GradedAlgebra.decompose_of_mem_same {x : A} {i : ι} (hx : x ∈ 𝒜 i) : (GradedAlgebra.decompose 𝒜 x i : A) = x :=
  by
  rw [GradedAlgebra.decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]

theorem GradedAlgebra.decompose_of_mem_ne {x : A} {i j : ι} (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    (GradedAlgebra.decompose 𝒜 x j : A) = 0 := by
  rw [GradedAlgebra.decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ _ hij, Submodule.coe_zero]

variable [∀ i : ι x : 𝒜 i, Decidable (x ≠ 0)]

theorem GradedAlgebra.mem_support_iff (r : A) (i : ι) : i ∈ GradedAlgebra.support 𝒜 r ↔ GradedAlgebra.proj 𝒜 i r ≠ 0 :=
  by
  rw [GradedAlgebra.support, Dfinsupp.mem_support_iff, GradedAlgebra.proj_apply]
  simp only [Ne.def, Submodule.coe_eq_zero]

theorem GradedAlgebra.sum_support_decompose (r : A) :
    (∑ i in GradedAlgebra.support 𝒜 r, (GradedAlgebra.decompose 𝒜 r i : A)) = r := by
  conv_rhs =>
    rw [← (GradedAlgebra.decompose 𝒜).symm_apply_apply r, ← DirectSum.sum_support_of _ (GradedAlgebra.decompose 𝒜 r)]
  rw [AlgEquiv.map_sum, GradedAlgebra.support]
  simp_rw [GradedAlgebra.decompose_symm_of]

end GradedAlgebra

section CanonicalOrder

open GradedAlgebra SetLike.GradedMonoid DirectSum

variable {ι R A : Type _}

variable [CommSemiringₓ R] [Semiringₓ A]

variable [Algebra R A] [DecidableEq ι]

variable [CanonicallyOrderedAddMonoid ι]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

/-- If `A` is graded by a canonically ordered add monoid, then the projection map `x ↦ x₀` is a ring
homomorphism.
-/
@[simps]
def GradedAlgebra.projZeroRingHom : A →+* A where
  toFun := fun a => decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 one_mem
  map_zero' := by
    simp only [Subtype.ext_iff_val, map_zero, zero_apply, Submodule.coe_zero]
  map_add' := fun _ _ => by
    simp [Subtype.ext_iff_val, map_add, add_apply, Submodule.coe_add]
  map_mul' := fun x y => by
    have m : ∀ x, x ∈ supr 𝒜 := fun x => (is_internal 𝒜).supr_eq_top.symm ▸ Submodule.mem_top
    refine' Submodule.supr_induction 𝒜 (m x) (fun i c hc => _) _ _
    · refine' Submodule.supr_induction 𝒜 (m y) (fun j c' hc' => _) _ _
      · by_cases' h : i + j = 0
        · rw [decompose_of_mem_same 𝒜 (show c * c' ∈ 𝒜 0 from h ▸ mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c ∈ 𝒜 0 from (add_eq_zero_iff.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' ∈ 𝒜 0 from (add_eq_zero_iff.mp h).2 ▸ hc')]
          
        · rw [decompose_of_mem_ne 𝒜 (mul_mem hc hc') h]
          cases'
            show i ≠ 0 ∨ j ≠ 0 by
              rwa [add_eq_zero_iff, not_and_distrib] at h with
            h' h'
          · simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul]
            
          · simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero]
            
          
        
      · simp only [map_zero, zero_apply, Submodule.coe_zero, mul_zero]
        
      · intro _ _ hd he
        simp only [mul_addₓ, map_add, add_apply, Submodule.coe_add, hd, he]
        
      
    · simp only [map_zero, zero_apply, Submodule.coe_zero, zero_mul]
      
    · rintro _ _ ha hb
      simp only [add_mulₓ, map_add, add_apply, Submodule.coe_add, ha, hb]
      

end CanonicalOrder

