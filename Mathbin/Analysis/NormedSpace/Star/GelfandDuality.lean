/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Reeased under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Analysis.NormedSpace.Star.Spectrum
import Analysis.Normed.Group.Quotient
import Analysis.NormedSpace.Algebra
import Topology.ContinuousFunction.Units
import Topology.ContinuousFunction.Compact
import Topology.Algebra.Algebra
import Topology.ContinuousFunction.StoneWeierstrass

#align_import analysis.normed_space.star.gelfand_duality from "leanprover-community/mathlib"@"087c325ae0ab42dbdd5dee55bc37d3d5a0bf2197"

/-!
# Gelfand Duality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The `gelfand_transform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(character_space 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfand_transform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

## Main definitions

* `ideal.to_character_space` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `weak_dual.character_space.comp_continuous_map`: The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a
  continuous function `character_space ℂ B → character_space ℂ A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfand_transform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfand_transform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfand_transform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.

## TODO

* After `star_alg_equiv` is defined, realize `gelfand_transform` as a `star_alg_equiv`.
* Prove that if `A` is the unital C⋆-algebra over `ℂ` generated by a fixed normal element `x` in
  a larger C⋆-algebra `B`, then `character_space ℂ A` is homeomorphic to `spectrum ℂ x`.
* From the previous result, construct the **continuous functional calculus**.
* Show that if `X` is a compact Hausdorff space, then `X` is (canonically) homeomorphic to
  `character_space ℂ C(X, ℂ)`.
* Conclude using the previous fact that the functors `C(⬝, ℂ)` and `character_space ℂ ⬝` along with
  the canonical homeomorphisms described above constitute a natural contravariant equivalence of
  the categories of compact Hausdorff spaces (with continuous maps) and commutative unital
  C⋆-algebras (with unital ⋆-algebra homomoprhisms); this is known as **Gelfand duality**.

## Tags

Gelfand transform, character space, C⋆-algebra
-/


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type _} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

#print Ideal.toCharacterSpace /-
/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`weak_dual.character_space.equiv_alg_hom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `normed_ring.alg_equiv_complex_of_complete`. -/
noncomputable def Ideal.toCharacterSpace : characterSpace ℂ A :=
  CharacterSpace.equivAlgHom.symm <|
    ((@NormedRing.algEquivComplexOfComplete (A ⧸ I) _ _
              (letI := quotient.field I
              @isUnit_iff_ne_zero (A ⧸ I) _)
              _).symm :
          A ⧸ I →ₐ[ℂ] ℂ).comp
      (Quotient.mkₐ ℂ I)
#align ideal.to_character_space Ideal.toCharacterSpace
-/

#print Ideal.toCharacterSpace_apply_eq_zero_of_mem /-
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simpa only [character_space.equiv_alg_hom_symm_coe, AlgHom.coe_comp, AlgEquiv.coe_algHom,
    quotient.mkₐ_eq_mk, Function.comp_apply, quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq,
    NormedRing.algEquivComplexOfComplete_symm_apply] using
    Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : ℂ)).some_mem
#align ideal.to_character_space_apply_eq_zero_of_mem Ideal.toCharacterSpace_apply_eq_zero_of_mem
-/

#print WeakDual.CharacterSpace.exists_apply_eq_zero /-
/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivlaent
to `gelfand_transform ℂ A a` takes the value zero at some character. -/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    ∃ f : characterSpace ℂ A, f a = 0 :=
  by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.to_character_space,
      M.to_character_space_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩
#align weak_dual.character_space.exists_apply_eq_zero WeakDual.CharacterSpace.exists_apply_eq_zero
-/

#print WeakDual.CharacterSpace.mem_spectrum_iff_exists /-
theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
    z ∈ spectrum ℂ a ↔ ∃ f : characterSpace ℂ A, f a = z :=
  by
  refine' ⟨fun hz => _, _⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes, Algebra.id.map_eq_id,
      RingHom.id_apply] at hf 
    exact (ContinuousMap.spectrum_eq_range (gelfand_transform ℂ A a)).symm ▸ ⟨f, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a
#align weak_dual.character_space.mem_spectrum_iff_exists WeakDual.CharacterSpace.mem_spectrum_iff_exists
-/

#print spectrum.gelfandTransform_eq /-
/-- The Gelfand transform is spectrum-preserving. -/
theorem spectrum.gelfandTransform_eq (a : A) : spectrum ℂ (gelfandTransform ℂ A a) = spectrum ℂ a :=
  by
  ext z
  rw [ContinuousMap.spectrum_eq_range, WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl
#align spectrum.gelfand_transform_eq spectrum.gelfandTransform_eq
-/

instance [Nontrivial A] : Nonempty (characterSpace ℂ A) :=
  ⟨Classical.choose <|
      WeakDual.CharacterSpace.exists_apply_eq_zero <| zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCstarAlgebra

variable {A : Type _} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

variable [StarRing A] [CstarRing A] [StarModule ℂ A]

#print gelfandTransform_map_star /-
theorem gelfandTransform_map_star (a : A) :
    gelfandTransform ℂ A (star a) = star (gelfandTransform ℂ A a) :=
  ContinuousMap.ext fun φ => map_star φ a
#align gelfand_transform_map_star gelfandTransform_map_star
-/

variable (A)

#print gelfandTransform_isometry /-
/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_isometry : Isometry (gelfandTransform ℂ A) :=
  by
  nontriviality A
  refine' AddMonoidHomClass.isometry_of_norm (gelfand_transform ℂ A) fun a => _
  /- By `spectrum.gelfand_transform_eq`, the spectra of `star a * a` and its
    `gelfand_transform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius ℂ (gelfand_transform ℂ A (star a * a)) = spectralRadius ℂ (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  simp only [map_mul, (IsSelfAdjoint.star_mul_self _).spectralRadius_eq_nnnorm,
    gelfandTransform_map_star a, ENNReal.coe_eq_coe, CstarRing.nnnorm_star_mul_self, ← sq] at this 
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using
    congr_arg ((coe : ℝ≥0 → ℝ) ∘ ⇑NNReal.sqrt) this
#align gelfand_transform_isometry gelfandTransform_isometry
-/

#print gelfandTransform_bijective /-
/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform ℂ A) :=
  by
  refine' ⟨(gelfandTransform_isometry A).Injective, _⟩
  suffices (gelfand_transform ℂ A).range = ⊤ by
    exact fun x => this.symm ▸ (gelfand_transform ℂ A).mem_range.mp (this.symm ▸ Algebra.mem_top)
  /- Because the `gelfand_transform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(character_space ℂ A, ℂ)` and is closed under `star`. -/
  have h : (gelfand_transform ℂ A).range.topologicalClosure = (gelfand_transform ℂ A).range :=
    le_antisymm
      (Subalgebra.topologicalClosure_minimal _ le_rfl
        (gelfandTransform_isometry A).ClosedEmbedding.closed_range)
      (Subalgebra.le_topologicalClosure _)
  refine'
    h ▸
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (fun _ _ => _)
        fun f hf => _
  /- Separating points just means that elements of the `character_space` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  · contrapose!
    exact fun h =>
      Subtype.ext
        (ContinuousLinearMap.ext fun a =>
          h (gelfand_transform ℂ A a) ⟨gelfand_transform ℂ A a, ⟨a, rfl⟩, rfl⟩)
  /- If `f = gelfand_transform ℂ A a`, then `star f` is also in the range of `gelfand_transform ℂ A`
    using the argument `star a`. The key lemma below may be hard to spot; it's `map_star` coming from
    `weak_dual.star_hom_class`, which is a nontrivial result. -/
  · obtain ⟨f, ⟨a, rfl⟩, rfl⟩ := subalgebra.mem_map.mp hf
    refine' ⟨star a, ContinuousMap.ext fun ψ => _⟩
    simpa only [gelfandTransform_map_star a, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
#align gelfand_transform_bijective gelfandTransform_bijective
-/

#print gelfandStarTransform /-
/-- The Gelfand transform as a `star_alg_equiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `character_space`. -/
@[simps]
noncomputable def gelfandStarTransform : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  StarAlgEquiv.ofBijective
    (show A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) from
      { gelfandTransform ℂ A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)
#align gelfand_star_transform gelfandStarTransform
-/

end ComplexCstarAlgebra

section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C : Type _}

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]

variable [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B]

variable [NormedRing C] [NormedAlgebra ℂ C] [CompleteSpace C] [StarRing C]

#print WeakDual.CharacterSpace.compContinuousMap /-
/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`character_space ℂ B → character_space ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
noncomputable def compContinuousMap (ψ : A →⋆ₐ[ℂ] B) : C(characterSpace ℂ B, characterSpace ℂ A)
    where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform ℂ B (ψ a)) _
#align weak_dual.character_space.comp_continuous_map WeakDual.CharacterSpace.compContinuousMap
-/

variable (A)

#print WeakDual.CharacterSpace.compContinuousMap_id /-
/-- `weak_dual.character_space.comp_continuous_map` sends the identity to the identity. -/
@[simp]
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id ℂ A) = ContinuousMap.id (characterSpace ℂ A) :=
  ContinuousMap.ext fun a => ext fun x => rfl
#align weak_dual.character_space.comp_continuous_map_id WeakDual.CharacterSpace.compContinuousMap_id
-/

variable {A}

#print WeakDual.CharacterSpace.compContinuousMap_comp /-
/-- `weak_dual.character_space.comp_continuous_map` is functorial. -/
@[simp]
theorem compContinuousMap_comp (ψ₂ : B →⋆ₐ[ℂ] C) (ψ₁ : A →⋆ₐ[ℂ] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun a => ext fun x => rfl
#align weak_dual.character_space.comp_continuous_map_comp WeakDual.CharacterSpace.compContinuousMap_comp
-/

end CharacterSpace

end WeakDual

end Functoriality

