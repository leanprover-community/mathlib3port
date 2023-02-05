/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Eric Rodriguez

! This file was ported from Lean 3 source module number_theory.number_field.norm
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.NumberField.Basic
import Mathbin.RingTheory.Norm

/-!
# Norm in number fields
Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `ring_of_integers.norm K` : `algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.
## Main results
* `algebra.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)`
  we have that `x ∣ algebra_map (𝓞 K) (𝓞 L) (norm K x)`.

-/


open NumberField BigOperators

open Finset NumberField Algebra

namespace RingOfIntegers

variable {L : Type _} (K : Type _) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `algebra.norm` as a morphism betwen the rings of integers. -/
@[simps]
noncomputable def norm [IsSeparable K L] : 𝓞 L →* 𝓞 K :=
  ((Algebra.norm K).restrict (𝓞 L)).codRestrict (𝓞 K) fun x => isIntegral_norm K x.2
#align ring_of_integers.norm RingOfIntegers.norm

attribute [local instance] NumberField.ringOfIntegersAlgebra

theorem coe_algebraMap_norm [IsSeparable K L] (x : 𝓞 L) :
    (algebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = algebraMap K L (Algebra.norm K (x : L)) :=
  rfl
#align ring_of_integers.coe_algebra_map_norm RingOfIntegers.coe_algebraMap_norm

theorem isUnit_norm [IsGalois K L] {x : 𝓞 L} : IsUnit (norm K x) ↔ IsUnit x := by
  classical
    refine' ⟨fun hx => _, IsUnit.map _⟩
    replace hx : IsUnit (algebraMap (𝓞 K) (𝓞 L) <| norm K x) := hx.map (algebraMap (𝓞 K) <| 𝓞 L)
    refine'
      @isUnit_of_mul_isUnit_right (𝓞 L) _
        ⟨(univ \ {AlgEquiv.refl}).Prod fun σ : L ≃ₐ[K] L => σ x,
          prod_mem fun σ hσ => map_isIntegral (σ : L →+* L).toIntAlgHom x.2⟩
        _ _
    convert hx using 1
    ext
    push_cast
    convert_to
      (((univ \ {AlgEquiv.refl}).Prod fun σ : L ≃ₐ[K] L => σ x) *
          ∏ σ : L ≃ₐ[K] L in {AlgEquiv.refl}, σ (x : L)) =
        _
    · rw [prod_singleton, AlgEquiv.coe_refl, id]
    · rw [prod_sdiff <| subset_univ _, ← norm_eq_prod_automorphisms, coe_algebra_map_norm]
#align ring_of_integers.is_unit_norm RingOfIntegers.isUnit_norm

/-- If `L/K` is a finite Galois extension of fields, then, for all `(x : 𝓞 L)` we have that
`x ∣ algebra_map (𝓞 K) (𝓞 L) (norm K x)`. -/
theorem dvd_norm [IsGalois K L] (x : 𝓞 L) : x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x) := by
  classical
    have hint : (∏ σ : L ≃ₐ[K] L in univ.erase AlgEquiv.refl, σ x) ∈ 𝓞 L :=
      Subalgebra.prod_mem _ fun σ hσ =>
        (mem_ring_of_integers _ _).2 (map_isIntegral σ (ring_of_integers.is_integral_coe x))
    refine' ⟨⟨_, hint⟩, Subtype.ext _⟩
    rw [coe_algebra_map_norm K x, norm_eq_prod_automorphisms]
    simp [← Finset.mul_prod_erase _ _ (mem_univ AlgEquiv.refl)]
#align ring_of_integers.dvd_norm RingOfIntegers.dvd_norm

end RingOfIntegers

