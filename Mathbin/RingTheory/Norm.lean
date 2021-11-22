import Mathbin.FieldTheory.PrimitiveElement 
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff 
import Mathbin.LinearAlgebra.Determinant 
import Mathbin.RingTheory.PowerBasis

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
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/


universe u v w

variable{R S T : Type _}[CommRingₓ R][IsDomain R][CommRingₓ S]

variable[Algebra R S]

variable{K L F : Type _}[Field K][Field L][Field F]

variable[Algebra K L][Algebra L F][Algebra K F]

variable{ι : Type w}[Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix

open_locale BigOperators

open_locale Matrix

namespace Algebra

variable(R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) :=
  rfl

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) : norm R x = 1 :=
  by 
    rw [norm_apply, LinearMap.det]
    splitIfs with h 
    rfl

variable{R}

theorem norm_eq_matrix_det [DecidableEq ι] (b : Basis ι R S) (s : S) :
  norm R s = Matrix.det (Algebra.leftMulMatrix b s) :=
  by 
    rw [norm_apply, ←LinearMap.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebra_map_of_basis (b : Basis ι R S) (x : R) : norm R (algebraMap R S x) = (x^Fintype.card ι) :=
  by 
    haveI  := Classical.decEq ι 
    rw [norm_apply, ←det_to_matrix b, lmul_algebra_map]
    convert @det_diagonal _ _ _ _ _ fun i : ι => x
    ·
      ext i j 
      rw [to_matrix_lsmul, Matrix.diagonalₓ]
    ·
      rw [Finset.prod_const, Finset.card_univ]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
theorem norm_algebra_map (x : K) : norm K (algebraMap K L x) = (x^finrank K L) :=
  by 
    byCases' H : ∃ s : Finset L, Nonempty (Basis s K L)
    ·
      rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
    ·
      rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zeroₓ]
      rintro ⟨s, ⟨b⟩⟩
      exact H ⟨s, ⟨b⟩⟩

section EqProdRoots

theorem norm_gen_eq_prod_roots [Algebra K S] (pb : PowerBasis K S) (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
  algebraMap K F (norm K pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.Prod :=
  by 
    rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix, RingHom.map_mul,
      RingHom.map_pow, RingHom.map_neg, RingHom.map_one, ←Polynomial.coeff_map, Fintype.card_fin]
    convLHS => rw [Polynomial.eq_prod_roots_of_splits hf]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_zero_multiset_prod, Multiset.map_map,
      (minpoly.monic pb.is_integral_gen).leadingCoeff, RingHom.map_one, one_mulₓ]
    rw [←Multiset.prod_repeat (-1 : F), ←pb.nat_degree_minpoly, Polynomial.nat_degree_eq_card_roots hf,
      ←Multiset.map_const, ←Multiset.prod_map_mul]
    congr 
    convert Multiset.map_id _ 
    ext f 
    simp 

end EqProdRoots

section EqZeroIff

theorem norm_eq_zero_iff_of_basis [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x = 0 ↔ x = 0 :=
  by 
    have hι : Nonempty ι := b.index_nonempty 
    letI this := Classical.decEq ι 
    rw [Algebra.norm_eq_matrix_det b]
    split 
    ·
      rw [←Matrix.exists_mul_vec_eq_zero_iff]
      rintro ⟨v, v_ne, hv⟩
      rw [←b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
        Algebra.left_mul_matrix_mul_vec_repr] at hv 
      refine' (mul_eq_zero.mp (b.ext_elem$ fun i => _)).resolve_right (show (∑i, v i • b i) ≠ 0 from _)
      ·
        simpa only [LinearEquiv.map_zero, Pi.zero_apply] using congr_funₓ hv i
      ·
        contrapose! v_ne with sum_eq 
        apply b.equiv_fun.symm.injective 
        rw [b.equiv_fun_symm_apply, sum_eq, LinearEquiv.map_zero]
    ·
      rintro rfl 
      rw [AlgHom.map_zero, Matrix.det_zero hι]

theorem norm_ne_zero_iff_of_basis [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (Algebra.norm_eq_zero_iff_of_basis b)

/-- See also `algebra.norm_eq_zero_iff'` if you already have rewritten with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff [FiniteDimensional K L] {x : L} : Algebra.norm K x = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' [FiniteDimensional K L] {x : L} : LinearMap.det (Algebra.lmul K L x) = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

end EqZeroIff

open IntermediateField

variable(K)

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:340:40: in letI: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
theorem norm_eq_norm_adjoin
[finite_dimensional K L]
[is_separable K L]
(x : L) : «expr = »(norm K x, «expr ^ »(norm K (adjoin_simple.gen K x), finrank «expr ⟮ , ⟯»(K, [x]) L)) :=
begin
  letI [] [] [":=", expr is_separable_tower_top_of_is_separable K «expr ⟮ , ⟯»(K, [x]) L],
  let [ident pbL] [] [":=", expr field.power_basis_of_finite_of_separable «expr ⟮ , ⟯»(K, [x]) L],
  let [ident pbx] [] [":=", expr intermediate_field.adjoin.power_basis (is_separable.is_integral K x)],
  rw ["[", "<-", expr adjoin_simple.algebra_map_gen K x, ",", expr norm_eq_matrix_det (pbx.basis.smul pbL.basis) _, ",", expr smul_left_mul_matrix_algebra_map, ",", expr det_block_diagonal, ",", expr norm_eq_matrix_det pbx.basis, "]"] [],
  simp [] [] ["only"] ["[", expr finset.card_fin, ",", expr finset.prod_const, ",", expr adjoin.power_basis_basis, "]"] [] [],
  congr,
  rw ["[", "<-", expr power_basis.finrank, ",", expr adjoin_simple.algebra_map_gen K x, "]"] []
end

section EqProdEmbeddings

variable{K}

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable(E : Type _)[Field E][Algebra K E][IsScalarTower K L F]

theorem norm_eq_prod_embeddings_gen (pb : PowerBasis K L) (hE : (minpoly K pb.gen).Splits (algebraMap K E))
  (hfx : (minpoly K pb.gen).Separable) :
  algebraMap K E (norm K pb.gen) = (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ => σ pb.gen :=
  by 
    letI this := Classical.decEq E 
    rw [norm_gen_eq_prod_roots pb hE, Fintype.prod_equiv pb.lift_equiv', Finset.prod_mem_multiset,
      Finset.prod_eq_multiset_prod, Multiset.to_finset_val,
      multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx)), Multiset.map_id]
    ·
      intro x 
      rfl
    ·
      intro σ 
      rw [PowerBasis.lift_equiv'_apply_coe, id.def]

variable(F)

theorem prod_embeddings_eq_finrank_pow [IsAlgClosed E] [IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
  (∏σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
    (((@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ : L →ₐ[K] E => σ pb.gen)^finrank L F) :=
  by 
    haveI  : FiniteDimensional L F := FiniteDimensional.right K L F 
    haveI  : IsSeparable L F := is_separable_tower_top_of_is_separable K L F 
    letI this : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb 
    letI this : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _ 
    rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ←Finset.univ_sigma_univ,
      Finset.prod_sigma, ←Finset.prod_pow]
    refine' Finset.prod_congr rfl fun σ _ => _
    ·
      letI this : Algebra L E := σ.to_ring_hom.to_algebra 
      simp only [Finset.prod_const, Finset.card_univ]
      congr 
      rw [AlgHom.card L F E]
    ·
      intro σ 
      simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
        IsScalarTower.coe_to_alg_hom']

variable(K)

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:340:40: in haveI: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
theorem norm_eq_prod_embeddings
[finite_dimensional K L]
[is_separable K L]
[is_alg_closed E]
{x : L} : «expr = »(algebra_map K E (norm K x), «expr∏ , »((σ : «expr →ₐ[ ] »(L, K, E)), σ x)) :=
begin
  have [ident hx] [] [":=", expr is_separable.is_integral K x],
  rw ["[", expr norm_eq_norm_adjoin K x, ",", expr ring_hom.map_pow, ",", "<-", expr adjoin.power_basis_gen hx, ",", expr norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _), "]"] [],
  { exact [expr (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm] },
  { haveI [] [] [":=", expr is_separable_tower_bot_of_is_separable K «expr ⟮ , ⟯»(K, [x]) L],
    exact [expr is_separable.separable K _] }
end

end EqProdEmbeddings

end Algebra

