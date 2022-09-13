/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Algebra.Algebra.Spectrum

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/


namespace WeakDual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def CharacterSpace (𝕜 : Type _) (A : Type _) [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜]
    [HasContinuousConstSmul 𝕜 𝕜] [NonUnitalNonAssocSemiringₓ A] [TopologicalSpace A] [Module 𝕜 A] :=
  { φ : WeakDual 𝕜 A | φ ≠ 0 ∧ ∀ x y : A, φ (x * y) = φ x * φ y }

variable {𝕜 : Type _} {A : Type _}

namespace CharacterSpace

section NonUnitalNonAssocSemiringₓ

variable [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [NonUnitalNonAssocSemiringₓ A] [TopologicalSpace A] [Module 𝕜 A]

@[simp, norm_cast, protected]
theorem coe_coe (φ : CharacterSpace 𝕜 A) : ⇑(φ : WeakDual 𝕜 A) = φ :=
  rfl

/-- Elements of the character space are continuous linear maps. -/
instance : ContinuousLinearMapClass (CharacterSpace 𝕜 A) 𝕜 A 𝕜 where
  coe := fun φ => (φ : A → 𝕜)
  coe_injective' := fun φ ψ h => by
    ext
    exact congr_fun h x
  map_smulₛₗ := fun φ => (φ : WeakDual 𝕜 A).map_smul
  map_add := fun φ => (φ : WeakDual 𝕜 A).map_add
  map_continuous := fun φ => (φ : WeakDual 𝕜 A).cont

/-- An element of the character space, as a continuous linear map. -/
def toClm (φ : CharacterSpace 𝕜 A) : A →L[𝕜] 𝕜 :=
  (φ : WeakDual 𝕜 A)

@[simp]
theorem coe_to_clm (φ : CharacterSpace 𝕜 A) : ⇑(toClm φ) = φ :=
  rfl

/-- Elements of the character space are non-unital algebra homomorphisms. -/
instance : NonUnitalAlgHomClass (CharacterSpace 𝕜 A) 𝕜 A 𝕜 :=
  { CharacterSpace.continuousLinearMapClass with map_smul := fun φ => map_smul φ, map_zero := fun φ => map_zero φ,
    map_mul := fun φ => φ.Prop.2 }

/-- An element of the character space, as an non-unital algebra homomorphism. -/
def toNonUnitalAlgHom (φ : CharacterSpace 𝕜 A) : A →ₙₐ[𝕜] 𝕜 where
  toFun := (φ : A → 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp]
theorem coe_to_non_unital_alg_hom (φ : CharacterSpace 𝕜 A) : ⇑(toNonUnitalAlgHom φ) = φ :=
  rfl

variable (𝕜 A)

theorem union_zero : CharacterSpace 𝕜 A ∪ {0} = { φ : WeakDual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y } :=
  le_antisymmₓ
    (by
      rintro φ (hφ | h₀)
      · exact hφ.2
        
      · exact fun x y => by
          simp [Set.eq_of_mem_singleton h₀]
        )
    fun φ hφ => Or.elim (em <| φ = 0) (fun h₀ => Or.inr h₀) fun h₀ => Or.inl ⟨h₀, hφ⟩

/-- The `character_space 𝕜 A` along with `0` is always a closed set in `weak_dual 𝕜 A`. -/
theorem union_zero_is_closed [T2Space 𝕜] [HasContinuousMul 𝕜] : IsClosed (CharacterSpace 𝕜 A ∪ {0}) := by
  simp only [union_zero, Set.set_of_forall]
  exact
    is_closed_Inter fun x =>
      is_closed_Inter fun y => is_closed_eq (eval_continuous _) <| (eval_continuous _).mul (eval_continuous _)

end NonUnitalNonAssocSemiringₓ

section Unital

variable [CommRingₓ 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [TopologicalSpace A] [Semiringₓ A] [Algebra 𝕜 A]

/-- In a unital algebra, elements of the character space are algebra homomorphisms. -/
instance : AlgHomClass (CharacterSpace 𝕜 A) 𝕜 A 𝕜 :=
  have map_one' : ∀ φ : CharacterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by
      rw [mul_sub, sub_eq_zero, mul_oneₓ, ← map_mul φ, one_mulₓ]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : ∀ a, φ (a * 1) = 0 := fun a => by
        simp only [map_mul φ, h₂, mul_zero]
      exact
        False.elim
          (φ.prop.1 <|
            ContinuousLinearMap.ext <| by
              simpa only [mul_oneₓ] using this)
      
    · exact (sub_eq_zero.mp h₂).symm
      
  { CharacterSpace.nonUnitalAlgHomClass with map_one := map_one',
    commutes := fun φ r => by
      rw [Algebra.algebra_map_eq_smul_one, Algebra.id.map_eq_id, RingHom.id_apply]
      change ((φ : WeakDual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r
      rw [map_smul, Algebra.id.smul_eq_mul, character_space.coe_coe, map_one' φ, mul_oneₓ] }

/-- An element of the character space of a unital algebra, as an algebra homomorphism. -/
@[simps]
def toAlgHom (φ : CharacterSpace 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
  { toNonUnitalAlgHom φ with map_one' := map_one φ, commutes' := AlgHomClass.commutes φ }

theorem eq_set_map_one_map_mul [Nontrivial 𝕜] :
    CharacterSpace 𝕜 A = { φ : WeakDual 𝕜 A | φ 1 = 1 ∧ ∀ x y : A, φ (x * y) = φ x * φ y } := by
  ext x
  refine' ⟨fun h => ⟨map_one (⟨x, h⟩ : character_space 𝕜 A), h.2⟩, fun h => ⟨_, h.2⟩⟩
  rintro rfl
  simpa using h.1

/-- under suitable mild assumptions on `𝕜`, the character space is a closed set in
`weak_dual 𝕜 A`. -/
theorem is_closed [Nontrivial 𝕜] [T2Space 𝕜] [HasContinuousMul 𝕜] : IsClosed (CharacterSpace 𝕜 A) := by
  rw [eq_set_map_one_map_mul, Set.set_of_and]
  refine' IsClosed.inter (is_closed_eq (eval_continuous _) continuous_const) _
  simpa only [(union_zero 𝕜 A).symm] using union_zero_is_closed _ _

end Unital

section Ringₓ

variable [CommRingₓ 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [TopologicalSpace A] [Ringₓ A] [Algebra 𝕜 A]

theorem apply_mem_spectrum [Nontrivial 𝕜] (φ : CharacterSpace 𝕜 A) (a : A) : φ a ∈ Spectrum 𝕜 a :=
  AlgHom.apply_mem_spectrum φ a

end Ringₓ

end CharacterSpace

end WeakDual

