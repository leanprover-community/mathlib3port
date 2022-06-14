/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Order.WellFoundedSet

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gram_schmidt` : the Gram-Schmidt process
- `gram_schmidt_orthogonal` :
  `gram_schmidt` produces an orthogonal system of vectors.
- `span_gram_schmidt` :
  `gram_schmidt` preserves span of vectors.
- `gram_schmidt_ne_zero` :
  If the input vectors of `gram_schmidt` are linearly independent,
  then the output vectors are non-zero.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/


open BigOperators

open Finset

variable (𝕜 : Type _) {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

variable {ι : Type _} [LinearOrderₓ ι] [OrderBot ι]

variable [LocallyFiniteOrder ι] [IsWellOrder ι (· < ·)]

attribute [local instance] IsWellOrder.toHasWellFounded

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt (f : ι → E) : ι → E
  | n => f n - ∑ i : iio n, orthogonalProjection (𝕜∙gramSchmidt i) (f n)

/-- This lemma uses `∑ i in` instead of `∑ i :`.-/
theorem gram_schmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in iio n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
  rfl

theorem gram_schmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in iio n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  rw [gram_schmidt_def, sub_add_cancel]

@[simp]
theorem gram_schmidt_zero (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gram_schmidt_def, Iio, Finset.Ico_self, Finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**:
`gram_schmidt` produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    cases' h₀.lt_or_lt with ha hb
    · exact this _ _ ha
      
    · rw [inner_eq_zero_sym]
      exact this _ _ hb
      
  clear h₀ a b
  intro a b h₀
  revert a
  apply WellFounded.induction (@IsWellOrder.wf ι (· < ·) _) b
  intro b ih a h₀
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum, orthogonal_projection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (finset.mem_Iio.mpr h₀)]
  · by_cases' h : gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
      
    · rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self]
      rwa [Ne.def, inner_self_eq_zero]
      
    
  simp_intro i hi hia only [Finset.mem_range]
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero]
  right
  cases' hia.lt_or_lt with hia₁ hia₂
  · rw [inner_eq_zero_sym]
    exact ih a h₀ i hia₁
    
  · exact ih i (mem_Ico.1 hi).2 a hia₂
    

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ι → E) : Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 :=
  fun a b => gram_schmidt_orthogonal 𝕜 f

open Submodule Set Order

/-- `gram_schmidt` preserves span of vectors. -/
theorem span_gram_schmidt [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c) := by
  apply @Succ.rec ι _ _ _ (fun c => span 𝕜 (gramSchmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c)) ⊥ _ _ _ bot_le
  · simp only [Set.Iio_bot, Set.image_empty]
    
  intro c _ hc
  by_cases' h : succ c = c
  · rwa [h]
    
  have h₀ : ∀ b, b ∈ Finset.iio c → gramSchmidt 𝕜 f b ∈ span 𝕜 (f '' Iio c) := by
    simp_intro b hb only [Finset.mem_range, Nat.succ_eq_add_one]
    rw [← hc]
    refine' subset_span _
    simp only [Set.mem_image, Set.mem_Iio]
    refine'
      ⟨b, (Finset.mem_Ico.1 hb).2, by
        rfl⟩
  rw [not_iff_not.2 Order.succ_eq_iff_is_max] at h
  rw [Order.Iio_succ_eq_insert_of_not_is_max h]
  simp only [span_insert, image_insert_eq, hc]
  apply le_antisymmₓ
  · simp only [Nat.succ_eq_succ, gram_schmidt_def 𝕜 f c, orthogonal_projection_singleton, sup_le_iff,
      span_singleton_le_iff_mem, le_sup_right, and_trueₓ]
    apply Submodule.sub_mem _ _ _
    · exact mem_sup_left (mem_span_singleton_self (f c))
      
    · exact Submodule.sum_mem _ fun b hb => mem_sup_right (smul_mem _ _ (h₀ b hb))
      
    
  · rw [gram_schmidt_def' 𝕜 f c]
    simp only [orthogonal_projection_singleton, sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_trueₓ]
    apply Submodule.add_mem _ _ _
    · exact mem_sup_left (mem_span_singleton_self (gramSchmidt 𝕜 f c))
      
    · exact Submodule.sum_mem _ fun b hb => mem_sup_right (smul_mem _ _ (h₀ b hb))
      
    

theorem gram_schmidt_ne_zero_coe [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.Iic n → ι))) : gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Iio n) := by
    rw [← span_gram_schmidt 𝕜 f n, gram_schmidt_def' _ f, h, zero_addₓ]
    apply Submodule.sum_mem _ _
    simp_intro a ha only [Finset.mem_Ico]
    simp only [Set.mem_image, Set.mem_Iio, orthogonal_projection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    refine'
      subset_span
        ⟨a, ha, by
          rfl⟩
  have h₂ : (f ∘ (coe : Set.Iic n → ι)) ⟨n, le_reflₓ n⟩ ∈ span 𝕜 (f ∘ (coe : Set.Iic n → ι) '' Iio ⟨n, le_reflₓ n⟩) :=
    by
    rw [image_comp]
    convert h₁ using 3
    ext i
    simpa using @le_of_ltₓ _ _ i n
  apply LinearIndependent.not_mem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]

/-- If the input vectors of `gram_schmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gram_schmidt_ne_zero [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n ≠ 0 :=
  gram_schmidt_ne_zero_coe _ _ _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (∥gramSchmidt 𝕜 f n∥ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

theorem gram_schmidt_normed_unit_length_coe [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.Iic n → ι))) : ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  simp only [gram_schmidt_ne_zero_coe 𝕜 f n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne.def, not_false_iff]

theorem gram_schmidt_normed_unit_length [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (n : ι)
    (h₀ : LinearIndependent 𝕜 f) : ∥gramSchmidtNormed 𝕜 f n∥ = 1 :=
  gram_schmidt_normed_unit_length_coe _ _ _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal [SuccOrder ι] [IsSuccArchimedean ι] (f : ι → E) (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gram_schmidt_normed_unit_length, h₀, forall_const]
    
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, IsROrC.conj_inv, IsROrC.conj_of_real, mul_eq_zero,
      inv_eq_zero, IsROrC.of_real_eq_zero, norm_eq_zero]
    repeat'
      right
    exact gram_schmidt_orthogonal 𝕜 f hij
    

