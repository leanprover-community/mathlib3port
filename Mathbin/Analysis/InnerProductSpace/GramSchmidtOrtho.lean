/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard
-/
import Mathbin.Analysis.InnerProductSpace.Projection

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
  If the input of the first `n + 1` vectors of `gram_schmidt` are linearly independent,
  then the output of the first `n + 1` vectors are non-zero.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/


open BigOperators

variable (𝕜 : Type _) {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt (f : ℕ → E) : ℕ → E
  | n => f n - ∑ i : Finₓ n, orthogonalProjection (𝕜∙gramSchmidt i) (f n)

/-- `gram_schmidt_def` turns the sum over `fin n` into a sum over `ℕ`. -/
theorem gram_schmidt_def (f : ℕ → E) (n : ℕ) :
    gramSchmidt 𝕜 f n = f n - ∑ i in Finset.range n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  rw [gramSchmidt]
  congr 1
  exact Finₓ.sum_univ_eq_sum_range (fun i => (orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) : E)) n

theorem gram_schmidt_def' (f : ℕ → E) (n : ℕ) :
    f n = gramSchmidt 𝕜 f n + ∑ i in Finset.range n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  simp only [gram_schmidt_def, sub_add_cancel]

@[simp]
theorem gram_schmidt_zero (f : ℕ → E) : gramSchmidt 𝕜 f 0 = f 0 := by
  simp only [gramSchmidt, Fintype.univ_of_is_empty, Finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**:
`gram_schmidt` produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ℕ → E) {a b : ℕ} (h₀ : a ≠ b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ℕ, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    cases' h₀.lt_or_lt with ha hb
    · exact this _ _ ha
      
    · rw [inner_eq_zero_sym]
      exact this _ _ hb
      
  clear h₀ a b
  intro a b h₀
  induction' b using Nat.strong_induction_onₓ with b ih generalizing a
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum, orthogonal_projection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (finset.mem_range.mpr h₀)]
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
    
  · exact ih i hi a hia₂
    

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ℕ → E) : Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 :=
  @gram_schmidt_orthogonal 𝕜 _ _ _ f

open Submodule Set Order

/-- `gram_schmidt` preserves span of vectors. -/
theorem span_gram_schmidt (f : ℕ → E) (c : ℕ) : span 𝕜 (gramSchmidt 𝕜 f '' Iic c) = span 𝕜 (f '' Iic c) := by
  induction' c with c hc
  · simp only [Iic, gram_schmidt_zero, le_zero_iff, set_of_eq_eq_singleton, image_singleton]
    
  have h₀ : ∀ b, b ∈ Finset.range c.succ → gramSchmidt 𝕜 f b ∈ span 𝕜 (f '' Iic c) := by
    simp_intro b hb only [Finset.mem_range, Nat.succ_eq_add_one]
    rw [← hc]
    refine' subset_span _
    simp only [mem_image, mem_Iic]
    refine'
      ⟨b, by
        linarith, by
        rfl⟩
  rw [← Nat.succ_eq_succ, Iic_succ]
  simp only [span_insert, image_insert_eq, hc]
  apply le_antisymmₓ
  · simp only [Nat.succ_eq_succ, gram_schmidt_def 𝕜 f c.succ, orthogonal_projection_singleton, sup_le_iff,
      span_singleton_le_iff_mem, le_sup_right, and_trueₓ]
    apply Submodule.sub_mem _ _ _
    · exact mem_sup_left (mem_span_singleton_self (f c.succ))
      
    · exact Submodule.sum_mem _ fun b hb => mem_sup_right (smul_mem _ _ (h₀ b hb))
      
    
  · rw [Nat.succ_eq_succ, gram_schmidt_def' 𝕜 f c.succ]
    simp only [orthogonal_projection_singleton, sup_le_iff, span_singleton_le_iff_mem, le_sup_right, and_trueₓ]
    apply Submodule.add_mem _ _ _
    · exact mem_sup_left (mem_span_singleton_self (gramSchmidt 𝕜 f c.succ))
      
    · exact Submodule.sum_mem _ fun b hb => mem_sup_right (smul_mem _ _ (h₀ b hb))
      
    

/-- If the input of the first `n + 1` vectors of `gram_schmidt` are linearly independent,
then the output of the first `n + 1` vectors are non-zero. -/
theorem gram_schmidt_ne_zero (f : ℕ → E) (n : ℕ) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Finₓ n.succ → ℕ))) :
    gramSchmidt 𝕜 f n ≠ 0 := by
  induction' n with n hn
  · intro h
    simp only [gram_schmidt_zero, Ne.def] at h
    exact
      LinearIndependent.ne_zero 0 h₀
        (by
          simp only [Function.comp_app, Finₓ.coe_zero, h])
    
  · by_contra h₁
    rw [Nat.succ_eq_add_one] at hn h₀ h₁
    have h₂ := gram_schmidt_def' 𝕜 f n.succ
    simp only [Nat.succ_eq_add_one, h₁, orthogonal_projection_singleton, zero_addₓ] at h₂
    have h₃ : f (n + 1) ∈ span 𝕜 (f '' Iic n) := by
      rw [h₂, ← span_gram_schmidt 𝕜 f n]
      apply Submodule.sum_mem _ _
      simp_intro a ha only [Finset.mem_range]
      apply Submodule.smul_mem _ _ _
      refine' subset_span _
      simp only [mem_image, mem_Iic]
      exact
        ⟨a, by
          linarith, by
          rfl⟩
    change LinearIndependent 𝕜 (f ∘ (coe : Finₓ (n + 2) → ℕ)) at h₀
    have h₄ : (n + 1 : Finₓ (n + 2)) ∉ (coe : Finₓ (n + 2) → ℕ) ⁻¹' Iic n := by
      simp only [mem_preimage, mem_Iic, not_leₓ]
      norm_cast
      rw [Finₓ.coe_coe_of_lt] <;> linarith
    apply LinearIndependent.not_mem_span_image h₀ h₄
    rw [image_comp, image_preimage_eq_inter_range]
    simp only [Function.comp_app, Subtype.range_coe_subtype]
    convert h₃
    · norm_cast
      refine'
        Finₓ.coe_coe_of_lt
          (by
            linarith)
      
    · simp only [inter_eq_left_iff_subset, Iic, set_of_subset_set_of]
      exact fun a ha => by
        linarith
      
    

/-- If the input of `gram_schmidt` is linearly independent, then the output is non-zero. -/
theorem gram_schmidt_ne_zero' (f : ℕ → E) (h₀ : LinearIndependent 𝕜 f) (n : ℕ) : gramSchmidt 𝕜 f n ≠ 0 :=
  gram_schmidt_ne_zero 𝕜 f n (LinearIndependent.comp h₀ _ Finₓ.coe_injective)

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ℕ → E) (n : ℕ) : E :=
  (∥gramSchmidt 𝕜 f n∥ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

theorem gram_schmidt_normed_unit_length (f : ℕ → E) (n : ℕ) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Finₓ n.succ → ℕ))) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  simp only [gram_schmidt_ne_zero 𝕜 f n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne.def, not_false_iff]

theorem gram_schmidt_normed_unit_length' (f : ℕ → E) (n : ℕ) (h₀ : LinearIndependent 𝕜 f) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  simp only [gram_schmidt_ne_zero' 𝕜 f h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne.def, not_false_iff]

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ℕ → E) (h₀ : LinearIndependent 𝕜 f) : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gram_schmidt_normed_unit_length', h₀, forall_const]
    
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, IsROrC.conj_inv, IsROrC.conj_of_real, mul_eq_zero,
      inv_eq_zero, IsROrC.of_real_eq_zero, norm_eq_zero]
    repeat'
      right
    exact gram_schmidt_orthogonal 𝕜 f hij
    

