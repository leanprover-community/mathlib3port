import Mathbin.RingTheory.Trace
import Mathbin.RingTheory.Norm

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `algebra.discr_zero_of_not_linear_independent` : if `b` is not linear independent, then
  `algebra.discr A b = 0`.
* `algebra.discr_of_matrix_vec_mul` and `discr_of_matrix_mul_vec` : formulas relating
  `algebra.discr A ι b` with `algebra.discr A ((P.map (algebra_map A B)).vec_mul b)` and
  `algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`.
* `algebra.discr_not_zero_of_linear_independent` : over a field, if `b` is linear independent, then
  `algebra.discr K b ≠ 0`.
* `algebra.discr_eq_det_embeddings_matrix_reindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `algebra.discr_of_power_basis_eq_prod` : the discriminant of a power basis.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/


universe u v w z

open_locale Matrix BigOperators

open Matrix FiniteDimensional Fintype Polynomial Finset

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w}

variable [CommRingₓ A] [CommRingₓ B] [Algebra A B] [CommRingₓ C] [Algebra A C]

section Discr

/-- Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define
`discr A ι b` as the determinant of `trace_matrix A ι b`. -/
noncomputable def discr (A : Type u) {B : Type v} [CommRingₓ A] [CommRingₓ B] [Algebra A B] [Fintype ι] (b : ι → B) :=
  by
  classical
  exact (trace_matrix A b).det

theorem discr_def [DecidableEq ι] [Fintype ι] (b : ι → B) : discr A b = (trace_matrix A b).det := by
  convert rfl

variable [Fintype ι]

section Basic

/-- If `b` is not linear independent, then `algebra.discr A b = 0`. -/
theorem discr_zero_of_not_linear_independent [IsDomain A] {b : ι → B} (hli : ¬LinearIndependent A b) : discr A b = 0 :=
  by
  classical
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linear_independent_iff.1 hli
  have : (trace_matrix A b).mulVec g = 0 := by
    ext i
    have : ∀ j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_commₓ]
    simp only [mul_vec, dot_product, trace_matrix, Pi.zero_apply, trace_form_apply, fun j => this j, ←
      LinearMap.map_sum, ← sum_mul, hg, zero_mul, LinearMap.map_zero]
  by_contra h
  rw [discr_def] at h
  simpa [Matrix.eq_zero_of_mul_vec_eq_zero h this] using hi

variable {A}

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).vec_mul b)`. -/
theorem discr_of_matrix_vec_mul [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).vecMul b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_vec_mul, det_mul, det_mul, det_transpose, mul_commₓ, ← mul_assocₓ, discr_def,
    pow_two]

/-- Relation between `algebra.discr A ι b` and
`algebra.discr A ((P.map (algebra_map A B)).mul_vec b)`. -/
theorem discr_of_matrix_mul_vec [DecidableEq ι] (b : ι → B) (P : Matrix ι ι A) :
    discr A ((P.map (algebraMap A B)).mulVec b) = P.det ^ 2 * discr A b := by
  rw [discr_def, trace_matrix_of_matrix_mul_vec, det_mul, det_mul, det_transpose, mul_commₓ, ← mul_assocₓ, discr_def,
    pow_two]

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]

variable [Algebra K L] [Algebra K E]

variable [Module.Finite K L] [IsSeparable K L] [IsAlgClosed E]

variable (b : ι → L) (pb : PowerBasis K L)

/-- Over a field, if `b` is linear independent, then `algebra.discr K b ≠ 0`. -/
theorem discr_not_zero_of_linear_independent [Nonempty ι] (hcard : Fintype.card ι = finrank K L)
    (hli : LinearIndependent K b) : discr K b ≠ 0 := by
  classical
  have := span_eq_top_of_linear_independent_of_card_eq_finrank hli hcard
  rw [discr_def, trace_matrix_def]
  simp_rw [← Basis.mk_apply hli this]
  rw [← trace_matrix_def, trace_matrix_of_basis, ← BilinForm.nondegenerate_iff_det_ne_zero]
  exact trace_form_nondegenerate _ _

/-- If `L/K` is a field extension and `b : ι → L`, then `discr K b` is the square of the
determinant of the matrix whose `(i, j)` coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the
embedding in an algebraically closed field `E` corresponding to `j : ι` via a bijection
`e : ι ≃ (L →ₐ[K] E)`. -/
theorem discr_eq_det_embeddings_matrix_reindex_pow_two [DecidableEq ι] (e : ι ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddings_matrix_reindex K E b e).det ^ 2 := by
  rw [discr_def, RingHom.map_det, RingHom.map_matrix_apply, trace_matrix_eq_embeddings_matrix_reindex_mul_trans,
    det_mul, det_transpose, pow_two]

/-- The discriminant of a power basis. -/
theorem discr_power_basis_eq_prod (e : Finₓ pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Finₓ pb.dim, ∏ j in Finset.univ.filter fun j => i < j, (e j pb.gen - e i pb.gen) ^ 2 :=
  by
  rw [discr_eq_det_embeddings_matrix_reindex_pow_two K E pb.basis e, embeddings_matrix_reindex_eq_vandermonde,
    det_transpose, det_vandermonde, ← prod_pow]
  congr
  ext i
  rw [← prod_pow]

/-- A variation of `of_power_basis_eq_prod`. -/
theorem of_power_basis_eq_prod' (e : Finₓ pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Finₓ pb.dim,
        ∏ j in Finset.univ.filter fun j => i < j, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) :=
  by
  rw [discr_power_basis_eq_prod _ _ _ e]
  congr
  ext i
  congr
  ext j
  ring

local notation "n" => finrank K L

/-- A variation of `of_power_basis_eq_prod`. -/
theorem of_power_basis_eq_prod'' (e : Finₓ pb.dim ≃ (L →ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      -1 ^ (n * (n - 1) / 2) *
        ∏ i : Finₓ pb.dim,
          ∏ j in Finset.univ.filter fun j => i < j, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) :=
  by
  rw [of_power_basis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)), prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  simp_rw [Finₓ.card_filter_lt]
  apply (@Nat.cast_inj ℚ _ _ _ _ _).1
  rw [Nat.cast_sum]
  have : ∀ x : Finₓ pb.dim, ↑x + 1 ≤ pb.dim := by
    simp [Nat.succ_le_iff, Finₓ.is_lt]
  simp_rw [Nat.sub_sub]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib, Nat.cast_add, Nat.cast_one,
    sum_add_distrib, mul_oneₓ]
  rw [← Nat.cast_sum, ← @Finset.sum_range ℕ _ pb.dim fun i => i, sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E, ← Fintype.card_fin pb.dim]
    exact card_congr (Equivₓ.symm e)
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := even_iff_two_dvd.1 (Nat.even_mul_self_pred _)
  have hne : ((2 : ℕ) : ℚ) ≠ 0 := by
    simp
  have hle : 1 ≤ pb.dim := by
    rw [← hn, Nat.one_le_iff_ne_zero, ← zero_lt_iff, FiniteDimensional.finrank_pos_iff]
    infer_instance
  rw [hn, Nat.cast_dvd h₂ hne, Nat.cast_mul, Nat.cast_sub hle]
  field_simp
  ring

/-- Formula for the discriminant of a power basis using the norm of the field extension. -/
theorem of_power_basis_eq_norm :
    discr K pb.basis = -1 ^ (n * (n - 1) / 2) * norm K (aeval pb.gen (minpoly K pb.gen).derivative) := by
  let E := AlgebraicClosure L
  let this' := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Finₓ pb.dim ≃ (L →ₐ[K] E) := by
    refine' equiv_of_card_eq _
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : (map (algebraMap K E) (minpoly K pb.gen)).roots.Nodup :=
    nodup_roots (separable.map (IsSeparable.separable K pb.gen))
  have hroots : ∀ σ : L →ₐ[K] E, σ pb.gen ∈ (map (algebraMap K E) (minpoly K pb.gen)).roots := by
    intro σ
    rw [mem_roots, is_root.def, eval_map, ← aeval_def, aeval_alg_hom_apply]
    repeat'
      simp [minpoly.ne_zero (IsSeparable.is_integral K pb.gen)]
  apply (algebraMap K E).Injective
  rw [RingHom.map_mul, RingHom.map_pow, RingHom.map_neg, RingHom.map_one, of_power_basis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings, Finₓ.prod_filter_lt_mul_neg_eq_prod_off_diag]
  conv_rhs =>
    congr skip ext
      rw [← aeval_alg_hom_apply,
      aeval_root_derivative_of_splits (minpoly.monic (IsSeparable.is_integral K pb.gen)) (IsAlgClosed.splits_codomain _)
        (hroots σ),
      ← Finset.prod_mk _ (Multiset.nodup_erase_of_nodup _ hnodup)]
  rw [prod_sigma', prod_sigma']
  refine'
    prod_bij (fun i hi => ⟨e i.2, e i.1 pb.gen⟩) (fun i hi => _)
      (fun i hi => by
        simp at hi)
      (fun i j hi hj hij => _) fun σ hσ => _
  · simp only [true_andₓ, mem_mk, mem_univ, mem_sigma]
    rw [Multiset.mem_erase_of_ne fun h => _]
    · exact hroots _
      
    · simp only [true_andₓ, mem_filter, mem_univ, Ne.def, mem_sigma] at hi
      refine' hi (Equivₓ.injective e (Equivₓ.injective (PowerBasis.liftEquiv pb) _))
      rw [← PowerBasis.lift_equiv_apply_coe, ← PowerBasis.lift_equiv_apply_coe] at h
      exact Subtype.eq h
      
    
  · simp only [Equivₓ.apply_eq_iff_eq, heq_iff_eq] at hij
    have h := hij.2
    rw [← PowerBasis.lift_equiv_apply_coe, ← PowerBasis.lift_equiv_apply_coe] at h
    refine'
      Sigma.eq (Equivₓ.injective e (Equivₓ.injective _ (Subtype.eq h)))
        (by
          simp [hij.1])
    
  · simp only [true_andₓ, mem_mk, mem_univ, mem_sigma] at hσ
    simp only [Sigma.exists, true_andₓ, exists_prop, mem_filter, mem_univ, Ne.def, mem_sigma]
    refine' ⟨e.symm (PowerBasis.lift pb σ.2 _), e.symm σ.1, ⟨fun h => _, Sigma.eq _ _⟩⟩
    · rw [aeval_def, eval₂_eq_eval_map, ← is_root.def, ← mem_roots]
      · exact Multiset.erase_subset _ _ hσ
        
      · simp [minpoly.ne_zero (IsSeparable.is_integral K pb.gen)]
        
      
    · replace h := AlgHom.congr_fun (Equivₓ.injective _ h) pb.gen
      rw [PowerBasis.lift_gen] at h
      rw [← h] at hσ
      refine' Multiset.mem_erase_of_nodup hnodup hσ
      
    all_goals
      simp
    

end Field

end Discr

end Algebra

