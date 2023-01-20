/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.norm
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv
import Mathbin.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathbin.FieldTheory.Galois

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `linear_map.mul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/


universe u v w

variable {R S T : Type _} [CommRing R] [Ring S]

variable [Algebra R S]

variable {K L F : Type _} [Field K] [Field L] [Field F]

variable [Algebra K L] [Algebra K F]

variable {ι : Type w}

open FiniteDimensional

open LinearMap

open Matrix Polynomial

open BigOperators

open Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom
#align algebra.norm Algebra.norm

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) :=
  rfl
#align algebra.norm_apply Algebra.norm_apply

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by
  rw [norm_apply, LinearMap.det]
  split_ifs with h
  rfl
#align algebra.norm_eq_one_of_not_exists_basis Algebra.norm_eq_one_of_not_exists_basis

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) :=
  by
  rwa [norm_apply, ← LinearMap.det_to_matrix b, ← to_matrix_lmul_eq]
  rfl
#align algebra.norm_eq_matrix_det Algebra.norm_eq_matrix_det

/-- If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebra_map_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι :=
  by
  haveI := Classical.decEq ι
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map]
  convert @det_diagonal _ _ _ _ _ fun i : ι => x
  · ext (i j)
    rw [to_matrix_lsmul, Matrix.diagonal]
  · rw [Finset.prod_const, Finset.card_univ]
#align algebra.norm_algebra_map_of_basis Algebra.norm_algebra_map_of_basis

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
protected theorem norm_algebra_map {L : Type _} [Ring L] [Algebra K L] (x : K) :
    norm K (algebraMap K L x) = x ^ finrank K L :=
  by
  by_cases H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
  · rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero]
    rintro ⟨s, ⟨b⟩⟩
    exact H ⟨s, ⟨b⟩⟩
#align algebra.norm_algebra_map Algebra.norm_algebra_map

section EqProdRoots

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix,
    Fintype.card_fin]
#align algebra.power_basis.norm_gen_eq_coeff_zero_minpoly Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly

/-- Given `pb : power_basis R S`, then the norm of `pb.gen` is
`((minpoly R pb.gen).map (algebra_map R F)).roots.prod`. -/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : (minpoly R pb.gen).Splits (algebraMap R F)) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).map (algebraMap R F)).roots.Prod :=
  by
  haveI := Module.nontrivial R F
  have := minpoly.monic pb.is_integral_gen
  rw [power_basis.norm_gen_eq_coeff_zero_minpoly, ← pb.nat_degree_minpoly, RingHom.map_mul, ←
    coeff_map,
    prod_roots_eq_coeff_zero_of_monic_of_split (this.map _) ((splits_id_iff_splits _).2 hf),
    this.nat_degree_map, map_pow, ← mul_assoc, ← mul_pow]
  · simp only [map_neg, _root_.map_one, neg_mul, neg_neg, one_pow, one_mul]; infer_instance
#align algebra.power_basis.norm_gen_eq_prod_roots Algebra.PowerBasis.norm_gen_eq_prod_roots

end EqProdRoots

section EqZeroIff

variable [Finite ι]

theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x = 0 ↔ x = 0 := by
  cases nonempty_fintype ι
  have hι : Nonempty ι := b.index_nonempty
  letI := Classical.decEq ι
  rw [Algebra.norm_eq_matrix_det b]
  constructor
  · rw [← Matrix.exists_mul_vec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
      Algebra.left_mul_matrix_mul_vec_repr] at hv
    refine'
      (mul_eq_zero.mp (b.ext_elem fun i => _)).resolve_right (show (∑ i, v i • b i) ≠ 0 from _)
    · simpa only [LinearEquiv.map_zero, Pi.zero_apply] using congr_fun hv i
    · contrapose! v_ne with sum_eq
      apply b.equiv_fun.symm.injective
      rw [b.equiv_fun_symm_apply, sum_eq, LinearEquiv.map_zero]
  · rintro rfl
    rw [AlgHom.map_zero, Matrix.det_zero hι]
#align algebra.norm_eq_zero_iff_of_basis Algebra.norm_eq_zero_iff_of_basis

theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (Algebra.norm_eq_zero_iff_of_basis b)
#align algebra.norm_ne_zero_iff_of_basis Algebra.norm_ne_zero_iff_of_basis

/-- See also `algebra.norm_eq_zero_iff'` if you already have rewritten with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff {K L : Type _} [Field K] [CommRing L] [Algebra K L] [IsDomain L]
    [FiniteDimensional K L] {x : L} : Algebra.norm K x = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)
#align algebra.norm_eq_zero_iff Algebra.norm_eq_zero_iff

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' {K L : Type _} [Field K] [CommRing L] [Algebra K L] [IsDomain L]
    [FiniteDimensional K L] {x : L} : LinearMap.det (LinearMap.mul K L x) = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)
#align algebra.norm_eq_zero_iff' Algebra.norm_eq_zero_iff'

end EqZeroIff

open IntermediateField

variable (K)

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem norm_eq_norm_adjoin [FiniteDimensional K L] [IsSeparable K L] (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮⟯ L :=
  by
  letI := is_separable_tower_top_of_is_separable K K⟮⟯ L
  let pbL := Field.powerBasisOfFiniteOfSeparable K⟮⟯ L
  let pbx := IntermediateField.adjoin.powerBasis (IsSeparable.is_integral K x)
  rw [← adjoin_simple.algebra_map_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_left_mul_matrix_algebra_map, det_block_diagonal, norm_eq_matrix_det pbx.basis]
  simp only [Finset.card_fin, Finset.prod_const]
  congr
  rw [← PowerBasis.finrank, adjoin_simple.algebra_map_gen K x]
#align algebra.norm_eq_norm_adjoin Algebra.norm_eq_norm_adjoin

variable {K}

section IntermediateField

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem IntermediateField.AdjoinSimple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 :=
  by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine' is_integral_of_mem_of_fg K⟮⟯.toSubalgebra _ x _
  · exact (Submodule.fg_iff_finite_dimensional _).mpr (of_fintype_basis b)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
#align intermediate_field.adjoin_simple.norm_gen_eq_one IntermediateField.AdjoinSimple.norm_gen_eq_one

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x : L)
    (hf : (minpoly K x).Splits (algebraMap K F)) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) =
      ((minpoly K x).map (algebraMap K F)).roots.Prod :=
  by
  have injKxL := (algebraMap K⟮⟯ L).Injective
  by_cases hx : _root_.is_integral K x
  swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx]
  have hx' : _root_.is_integral K (adjoin_simple.gen K x) :=
    by
    rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen]
    infer_instance
  rw [← adjoin.power_basis_gen hx, power_basis.norm_gen_eq_prod_roots] <;>
      rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'] <;>
    try simp only [adjoin_simple.algebra_map_gen _ _]
  exact hf
#align intermediate_field.adjoin_simple.norm_gen_eq_prod_roots IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (F) (E : Type _) [Field E] [Algebra K E]

theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S)
    (hE : (minpoly R pb.gen).Splits (algebraMap R F)) (hfx : (minpoly R pb.gen).Separable) :
    algebraMap R F (norm R pb.gen) = (@Finset.univ pb).Prod fun σ => σ pb.gen :=
  by
  letI := Classical.decEq F
  rw [pb.norm_gen_eq_prod_roots hE, Fintype.prod_equiv pb.lift_equiv', Finset.prod_mem_multiset,
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, multiset.dedup_eq_self.mpr,
    Multiset.map_id]
  · exact nodup_roots hfx.map
  · intro x
    rfl
  · intro σ
    rw [pb.lift_equiv'_apply_coe, id.def]
#align algebra.norm_eq_prod_embeddings_gen Algebra.norm_eq_prod_embeddings_gen

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem norm_eq_prod_roots [IsSeparable K L] [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (norm K x) = ((minpoly K x).map (algebraMap K F)).roots.Prod ^ finrank K⟮⟯ L :=
  by
  rw [norm_eq_norm_adjoin K x, map_pow, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]
#align algebra.norm_eq_prod_roots Algebra.norm_eq_prod_roots

theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
    [IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
    (∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
      ((@Finset.univ pb).Prod fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F :=
  by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : IsSeparable L F := is_separable_tower_top_of_is_separable K L F
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  letI : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ←
    Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
  refine' Finset.prod_congr rfl fun σ _ => _
  · letI : Algebra L E := σ.to_ring_hom.to_algebra
    simp only [Finset.prod_const, Finset.card_univ]
    congr
    rw [AlgHom.card L F E]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_to_alg_hom']
#align algebra.prod_embeddings_eq_finrank_pow Algebra.prod_embeddings_eq_finrank_pow

variable (K)

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
theorem norm_eq_prod_embeddings [FiniteDimensional K L] [IsSeparable K L] [IsAlgClosed E] {x : L} :
    algebraMap K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
  by
  have hx := IsSeparable.is_integral K x
  rw [norm_eq_norm_adjoin K x, RingHom.map_pow, ← adjoin.power_basis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (IsAlgClosed.splits_codomain _)]
  · exact (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm
  · haveI := is_separable_tower_bot_of_is_separable K K⟮⟯ L
    exact IsSeparable.separable K _
#align algebra.norm_eq_prod_embeddings Algebra.norm_eq_prod_embeddings

theorem norm_eq_prod_automorphisms [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (norm K x) = ∏ σ : L ≃ₐ[K] L, σ x :=
  by
  apply NoZeroSMulDivisors.algebra_map_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings]
    simp only [algebra_map_eq_smul_one, smul_one_smul]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_of_bijective, AlgHom.restrict_normal_commutes, id.map_eq_id, RingHom.id_apply]
#align algebra.norm_eq_prod_automorphisms Algebra.norm_eq_prod_automorphisms

theorem is_integral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] [IsSeparable K L]
    [FiniteDimensional K L] {x : L} (hx : IsIntegral R x) : IsIntegral R (norm K x) :=
  by
  have hx' : _root_.is_integral K x := is_integral_of_is_scalar_tower hx
  rw [← is_integral_algebra_map_iff (algebraMap K (AlgebraicClosure L)).Injective,
    norm_eq_prod_roots]
  · refine' (IsIntegral.multiset_prod fun y hy => _).pow _
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy⊢
    exact minpoly.aeval_of_is_scalar_tower R x y hy
  · apply IsAlgClosed.splits_codomain
  · infer_instance
#align algebra.is_integral_norm Algebra.is_integral_norm

end EqProdEmbeddings

end Algebra

