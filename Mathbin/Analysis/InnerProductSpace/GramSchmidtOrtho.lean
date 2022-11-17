/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Order.WellFoundedSet
import Mathbin.LinearAlgebra.Matrix.Block

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
- `gram_schmidt_basis` :
  The basis produced by the Gram-Schmidt process when given a basis as input.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.
- `gram_schmidt_orthonormal_basis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/


open BigOperators

open Finset Submodule FiniteDimensional

variable (𝕜 : Type _) {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

variable {ι : Type _} [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)]

attribute [local instance] IsWellOrder.toHasWellFounded

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt (f : ι → E) : ι → E
  | n => f n - ∑ i : iio n, orthogonalProjection (𝕜 ∙ gramSchmidt i) (f n)
#align gram_schmidt gramSchmidt

/-- This lemma uses `∑ i in` instead of `∑ i :`.-/
theorem gram_schmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in iio n, orthogonalProjection (𝕜 ∙ gramSchmidt 𝕜 f i) (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
  rfl
#align gram_schmidt_def gram_schmidt_def

theorem gram_schmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in iio n, orthogonalProjection (𝕜 ∙ gramSchmidt 𝕜 f i) (f n) := by
  rw [gram_schmidt_def, sub_add_cancel]
#align gram_schmidt_def' gram_schmidt_def'

theorem gram_schmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in iio n, (⟪gramSchmidt 𝕜 f i, f n⟫ / ∥gramSchmidt 𝕜 f i∥ ^ 2) • gramSchmidt 𝕜 f i :=
  by
  convert gram_schmidt_def' 𝕜 f n
  ext i
  rw [orthogonal_projection_singleton]
#align gram_schmidt_def'' gram_schmidt_def''

@[simp]
theorem gram_schmidt_zero {ι : Type _} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι] [IsWellOrder ι (· < ·)]
    (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gram_schmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]
#align gram_schmidt_zero gram_schmidt_zero

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
  apply WellFounded.induction (@IsWellFounded.wf ι (· < ·) _) b
  intro b ih a h₀
  simp only [gram_schmidt_def 𝕜 f b, inner_sub_right, inner_sum, orthogonal_projection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (finset.mem_Iio.mpr h₀)]
  · by_cases h:gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
      
    · rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self]
      rwa [Ne.def, inner_self_eq_zero]
      
    
  simp_intro i hi hia only [Finset.mem_range]
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero]
  right
  cases' hia.lt_or_lt with hia₁ hia₂
  · rw [inner_eq_zero_sym]
    exact ih a h₀ i hia₁
    
  · exact ih i (mem_Iio.1 hi) a hia₂
    
#align gram_schmidt_orthogonal gram_schmidt_orthogonal

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ι → E) : Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 :=
  fun a b => gram_schmidt_orthogonal 𝕜 f
#align gram_schmidt_pairwise_orthogonal gram_schmidt_pairwise_orthogonal

theorem gram_schmidt_inv_triangular (v : ι → E) {i j : ι} (hij : i < j) : ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gram_schmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι → E := gramSchmidt 𝕜 v
  convert zero_add (0 : 𝕜)
  · exact gram_schmidt_orthogonal 𝕜 v hij.ne'
    
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, b k⟫ = 0 := gram_schmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  simp [this]
#align gram_schmidt_inv_triangular gram_schmidt_inv_triangular

open Submodule Set Order

theorem mem_span_gram_schmidt (f : ι → E) {i j : ι} (hij : i ≤ j) : f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' iic j) := by
  rw [gram_schmidt_def' 𝕜 f i]
  simp_rw [orthogonal_projection_singleton]
  exact
    Submodule.add_mem _ (subset_span $ mem_image_of_mem _ hij)
      (Submodule.sum_mem _ $ fun k hk =>
        smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Iic j)) _ $
          subset_span $ mem_image_of_mem (gramSchmidt 𝕜 f) $ (Finset.mem_Iio.1 hk).le.trans hij)
#align mem_span_gram_schmidt mem_span_gram_schmidt

theorem gram_schmidt_mem_span (f : ι → E) : ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' iic j)
  | j => fun i hij => by
    rw [gram_schmidt_def 𝕜 f i]
    simp_rw [orthogonal_projection_singleton]
    refine' Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij)) (Submodule.sum_mem _ $ fun k hk => _)
    let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
    exact smul_mem _ _ (span_mono (image_subset f $ Iic_subset_Iic.2 hkj.le) $ gram_schmidt_mem_span le_rfl)
#align gram_schmidt_mem_span gram_schmidt_mem_span

theorem span_gram_schmidt_Iic (f : ι → E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' iic c) = span 𝕜 (f '' iic c) :=
  span_eq_span (Set.image_subset_iff.2 $ fun i => gram_schmidt_mem_span _ _) $
    Set.image_subset_iff.2 $ fun i => mem_span_gram_schmidt _ _
#align span_gram_schmidt_Iic span_gram_schmidt_Iic

theorem span_gram_schmidt_Iio (f : ι → E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' iio c) = span 𝕜 (f '' iio c) :=
  span_eq_span
      (Set.image_subset_iff.2 $ fun i hi =>
        span_mono (image_subset _ $ Iic_subset_Iio.2 hi) $ gram_schmidt_mem_span _ _ le_rfl) $
    Set.image_subset_iff.2 $ fun i hi =>
      span_mono (image_subset _ $ Iic_subset_Iio.2 hi) $ mem_span_gram_schmidt _ _ le_rfl
#align span_gram_schmidt_Iio span_gram_schmidt_Iio

/-- `gram_schmidt` preserves span of vectors. -/
theorem span_gram_schmidt (f : ι → E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 $ fun i => span_mono (image_subset_range _ _) $ gram_schmidt_mem_span _ _ le_rfl) $
    range_subset_iff.2 $ fun i => span_mono (image_subset_range _ _) $ mem_span_gram_schmidt _ _ le_rfl
#align span_gram_schmidt span_gram_schmidt

theorem gram_schmidt_of_orthogonal {f : ι → E} (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) : gramSchmidt 𝕜 f = f := by
  ext i
  rw [gram_schmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [coe_eq_zero]
    suffices span 𝕜 (f '' Set.iic j) ≤ (𝕜 ∙ f i)ᗮ by
      apply orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
      apply mem_orthogonal_singleton_of_inner_left
      apply inner_right_of_mem_orthogonal_singleton
      exact this (gram_schmidt_mem_span 𝕜 f (le_refl j))
    rw [span_le]
    rintro - ⟨k, hk, rfl⟩
    apply mem_orthogonal_singleton_of_inner_left
    apply hf
    refine' (lt_of_le_of_lt hk _).Ne
    simpa using hj
    
  · simp
    
#align gram_schmidt_of_orthogonal gram_schmidt_of_orthogonal

variable {𝕜}

theorem gram_schmidt_ne_zero_coe {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.iic n → ι))) :
    gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Iio n) := by
    rw [← span_gram_schmidt_Iio 𝕜 f n, gram_schmidt_def' _ f, h, zero_add]
    apply Submodule.sum_mem _ _
    simp_intro a ha only [Finset.mem_Ico]
    simp only [Set.mem_image, Set.mem_Iio, orthogonal_projection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    refine' subset_span ⟨a, ha, by rfl⟩
  have h₂ : (f ∘ (coe : Set.iic n → ι)) ⟨n, le_refl n⟩ ∈ span 𝕜 (f ∘ (coe : Set.iic n → ι) '' Iio ⟨n, le_refl n⟩) := by
    rw [image_comp]
    convert h₁ using 3
    ext i
    simpa using @le_of_lt _ _ i n
  apply LinearIndependent.not_mem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]
#align gram_schmidt_ne_zero_coe gram_schmidt_ne_zero_coe

/-- If the input vectors of `gram_schmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gram_schmidt_ne_zero {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) : gramSchmidt 𝕜 f n ≠ 0 :=
  gram_schmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)
#align gram_schmidt_ne_zero gram_schmidt_ne_zero

/-- `gram_schmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gram_schmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) : b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.iio j) := by rwa [← span_gram_schmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.iio j := Basis.repr_support_subset_of_mem_span b (Set.iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.not_mem_Iio_self
#align gram_schmidt_triangular gram_schmidt_triangular

/-- `gram_schmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gram_schmidt_linear_independent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linear_independent_of_ne_zero_of_inner_eq_zero (fun i => gram_schmidt_ne_zero _ h₀) fun i j =>
    gram_schmidt_orthogonal 𝕜 f
#align gram_schmidt_linear_independent gram_schmidt_linear_independent

/-- When given a basis, `gram_schmidt` produces a basis. -/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gram_schmidt_linear_independent b.LinearIndependent) ((span_gram_schmidt 𝕜 b).trans b.span_eq).ge
#align gram_schmidt_basis gramSchmidtBasis

theorem coe_gram_schmidt_basis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _
#align coe_gram_schmidt_basis coe_gram_schmidt_basis

variable (𝕜)

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (∥gramSchmidt 𝕜 f n∥ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n
#align gram_schmidt_normed gramSchmidtNormed

variable {𝕜}

theorem gram_schmidt_normed_unit_length_coe {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.iic n → ι))) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  simp only [gram_schmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne.def, not_false_iff]
#align gram_schmidt_normed_unit_length_coe gram_schmidt_normed_unit_length_coe

theorem gram_schmidt_normed_unit_length {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 :=
  gram_schmidt_normed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)
#align gram_schmidt_normed_unit_length gram_schmidt_normed_unit_length

theorem gram_schmidt_normed_unit_length' {f : ι → E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n ≠ 0) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn
#align gram_schmidt_normed_unit_length' gram_schmidt_normed_unit_length'

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` applied to a linearly independent set of vectors produces an orthornormal
system of vectors. -/
theorem gramSchmidtOrthonormal {f : ι → E} (h₀ : LinearIndependent 𝕜 f) : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gram_schmidt_normed_unit_length, h₀, eq_self_iff_true, imp_true_iff]
    
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, IsROrC.conj_inv, IsROrC.conj_of_real, mul_eq_zero,
      inv_eq_zero, IsROrC.of_real_eq_zero, norm_eq_zero]
    repeat' right
    exact gram_schmidt_orthogonal 𝕜 f hij
    
#align gram_schmidt_orthonormal gramSchmidtOrthonormal

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors after removing the vectors which
become zero in the process. -/
theorem gramSchmidtOrthonormal' (f : ι → E) :
    Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i ≠ 0 } => gramSchmidtNormed 𝕜 f i := by
  refine' ⟨fun i => gram_schmidt_normed_unit_length' i.Prop, _⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gram_schmidt_orthogonal 𝕜 f hij]
#align gram_schmidt_orthonormal' gramSchmidtOrthonormal'

theorem span_gram_schmidt_normed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine'
    span_eq_span (Set.image_subset_iff.2 $ fun i hi => smul_mem _ _ $ subset_span $ mem_image_of_mem _ hi)
      (Set.image_subset_iff.2 $ fun i hi => span_mono (image_subset _ $ singleton_subset_set_iff.2 hi) _)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h:gramSchmidt 𝕜 f i = 0
  · simp [h]
    
  · refine' mem_span_singleton.2 ⟨∥gramSchmidt 𝕜 f i∥, smul_inv_smul₀ _ _⟩
    exact_mod_cast norm_ne_zero_iff.2 h
    
#align span_gram_schmidt_normed span_gram_schmidt_normed

theorem span_gram_schmidt_normed_range (f : ι → E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [image_univ.symm] using span_gram_schmidt_normed f univ
#align span_gram_schmidt_normed_range span_gram_schmidt_normed_range

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι → E)

include h

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidtOrthonormal' f).exists_orthonormal_basis_extension_of_card_eq h).some
#align gram_schmidt_orthonormal_basis gramSchmidtOrthonormalBasis

theorem gram_schmidt_orthonormal_basis_apply {f : ι → E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i :=
  ((gramSchmidtOrthonormal' f).exists_orthonormal_basis_extension_of_card_eq h).some_spec i hi
#align gram_schmidt_orthonormal_basis_apply gram_schmidt_orthonormal_basis_apply

theorem gram_schmidt_orthonormal_basis_apply_of_orthogonal {f : ι → E} (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι}
    (hi : f i ≠ 0) : gramSchmidtOrthonormalBasis h f i = (∥f i∥⁻¹ : 𝕜) • f i := by
  have H : gramSchmidtNormed 𝕜 f i = (∥f i∥⁻¹ : 𝕜) • f i := by rw [gramSchmidtNormed, gram_schmidt_of_orthogonal 𝕜 hf]
  rw [gram_schmidt_orthonormal_basis_apply h, H]
  simpa [H] using hi
#align gram_schmidt_orthonormal_basis_apply_of_orthogonal gram_schmidt_orthonormal_basis_apply_of_orthogonal

theorem inner_gram_schmidt_orthonormal_basis_eq_zero {f : ι → E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i = 0) (j : ι) :
    ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  apply inner_right_of_mem_orthogonal_singleton
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Iic j) ≤ (𝕜 ∙ gramSchmidtOrthonormalBasis h f i)ᗮ by
    apply this
    rw [span_gram_schmidt_normed]
    simpa using mem_span_gram_schmidt 𝕜 f (le_refl j)
  rw [span_le]
  rintro - ⟨k, -, rfl⟩
  apply mem_orthogonal_singleton_of_inner_left
  by_cases hk:gramSchmidtNormed 𝕜 f k = 0
  · simp [hk]
    
  rw [← gram_schmidt_orthonormal_basis_apply h hk]
  have : k ≠ i := by
    rintro rfl
    exact hk hi
  exact (gramSchmidtOrthonormalBasis h f).Orthonormal.2 this
#align inner_gram_schmidt_orthonormal_basis_eq_zero inner_gram_schmidt_orthonormal_basis_eq_zero

theorem gram_schmidt_orthonormal_basis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi:gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gram_schmidt_orthonormal_basis_eq_zero h hi]
    
  · simp [gram_schmidt_orthonormal_basis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gram_schmidt_inv_triangular 𝕜 f hij]
    
#align gram_schmidt_orthonormal_basis_inv_triangular gram_schmidt_orthonormal_basis_inv_triangular

theorem gram_schmidt_orthonormal_basis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gram_schmidt_orthonormal_basis_inv_triangular h f hij
#align gram_schmidt_orthonormal_basis_inv_triangular' gram_schmidt_orthonormal_basis_inv_triangular'

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gram_schmidt_orthonormal_basis` constructed from `f` is upper-triangular. -/
theorem gram_schmidt_orthonormal_basis_inv_block_triangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).BlockTriangular id := fun i j =>
  gram_schmidt_orthonormal_basis_inv_triangular' h f
#align gram_schmidt_orthonormal_basis_inv_block_triangular gram_schmidt_orthonormal_basis_inv_block_triangular

theorem gram_schmidt_orthonormal_basis_det :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f = ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert Matrix.det_of_upper_triangular (gram_schmidt_orthonormal_basis_inv_block_triangular h f)
  ext i
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f i) i).symm
#align gram_schmidt_orthonormal_basis_det gram_schmidt_orthonormal_basis_det

end OrthonormalBasis

