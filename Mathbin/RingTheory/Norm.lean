import Mathbin.FieldTheory.PrimitiveElement 
import Mathbin.LinearAlgebra.Determinant 
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff 
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv 
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

variable {R S T : Type _} [CommRingₓ R] [IsDomain R] [CommRingₓ S]

variable [Algebra R S]

variable {K L F : Type _} [Field K] [Field L] [Field F]

variable [Algebra K L] [Algebra L F] [Algebra K F]

variable {ι : Type w} [Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix

open_locale BigOperators

open_locale Matrix

namespace Algebra

variable (R)

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

variable {R}

theorem norm_eq_matrix_det [DecidableEq ι] (b : Basis ι R S) (s : S) :
  norm R s = Matrix.det (Algebra.leftMulMatrix b s) :=
  by 
    rw [norm_apply, ←LinearMap.det_to_matrix b, to_matrix_lmul_eq]

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebra_map_of_basis
(b : basis ι R S)
(x : R) : «expr = »(norm R (algebra_map R S x), «expr ^ »(x, fintype.card ι)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  rw ["[", expr norm_apply, ",", "<-", expr det_to_matrix b, ",", expr lmul_algebra_map, "]"] [],
  convert [] [expr @det_diagonal _ _ _ _ _ (λ i : ι, x)] [],
  { ext [] [ident i, ident j] [],
    rw ["[", expr to_matrix_lsmul, ",", expr matrix.diagonal, "]"] [] },
  { rw ["[", expr finset.prod_const, ",", expr finset.card_univ, "]"] [] }
end

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

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq_zero_iff_of_basis
[is_domain S]
(b : basis ι R S)
{x : S} : «expr ↔ »(«expr = »(algebra.norm R x, 0), «expr = »(x, 0)) :=
begin
  have [ident hι] [":", expr nonempty ι] [":=", expr b.index_nonempty],
  letI [] [] [":=", expr classical.dec_eq ι],
  rw [expr algebra.norm_eq_matrix_det b] [],
  split,
  { rw ["<-", expr matrix.exists_mul_vec_eq_zero_iff] [],
    rintros ["⟨", ident v, ",", ident v_ne, ",", ident hv, "⟩"],
    rw ["[", "<-", expr b.equiv_fun.apply_symm_apply v, ",", expr b.equiv_fun_symm_apply, ",", expr b.equiv_fun_apply, ",", expr algebra.left_mul_matrix_mul_vec_repr, "]"] ["at", ident hv],
    refine [expr (mul_eq_zero.mp «expr $ »(b.ext_elem, λ
       i, _)).resolve_right (show «expr ≠ »(«expr∑ , »((i), «expr • »(v i, b i)), 0), from _)],
    { simpa [] [] ["only"] ["[", expr linear_equiv.map_zero, ",", expr pi.zero_apply, "]"] [] ["using", expr congr_fun hv i] },
    { contrapose ["!"] [ident v_ne, "with", ident sum_eq],
      apply [expr b.equiv_fun.symm.injective],
      rw ["[", expr b.equiv_fun_symm_apply, ",", expr sum_eq, ",", expr linear_equiv.map_zero, "]"] [] } },
  { rintro [ident rfl],
    rw ["[", expr alg_hom.map_zero, ",", expr matrix.det_zero hι, "]"] [] }
end

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

variable (K)

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:341:40: in letI: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
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

variable {K}

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (E : Type _) [Field E] [Algebra K E] [IsScalarTower K L F]

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq_prod_embeddings_gen
(pb : power_basis K L)
(hE : (minpoly K pb.gen).splits (algebra_map K E))
(hfx : (minpoly K pb.gen).separable) : «expr = »(algebra_map K E (norm K pb.gen), (@@finset.univ (power_basis.alg_hom.fintype pb)).prod (λ
  σ, σ pb.gen)) :=
begin
  letI [] [] [":=", expr classical.dec_eq E],
  rw ["[", expr norm_gen_eq_prod_roots pb hE, ",", expr fintype.prod_equiv pb.lift_equiv', ",", expr finset.prod_mem_multiset, ",", expr finset.prod_eq_multiset_prod, ",", expr multiset.to_finset_val, ",", expr multiset.erase_dup_eq_self.mpr, ",", expr multiset.map_id, "]"] [],
  { exact [expr nodup_roots ((separable_map _).mpr hfx)] },
  { intro [ident x],
    refl },
  { intro [ident σ],
    rw ["[", expr power_basis.lift_equiv'_apply_coe, ",", expr id.def, "]"] [] }
end

variable (F)

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_embeddings_eq_finrank_pow
[is_alg_closed E]
[is_separable K F]
[finite_dimensional K F]
(pb : power_basis K L) : «expr = »(«expr∏ , »((σ : «expr →ₐ[ ] »(F, K, E)), σ (algebra_map L F pb.gen)), «expr ^ »((@@finset.univ (power_basis.alg_hom.fintype pb)).prod (λ
   σ : «expr →ₐ[ ] »(L, K, E), σ pb.gen), finrank L F)) :=
begin
  haveI [] [":", expr finite_dimensional L F] [":=", expr finite_dimensional.right K L F],
  haveI [] [":", expr is_separable L F] [":=", expr is_separable_tower_top_of_is_separable K L F],
  letI [] [":", expr fintype «expr →ₐ[ ] »(L, K, E)] [":=", expr power_basis.alg_hom.fintype pb],
  letI [] [":", expr ∀
   f : «expr →ₐ[ ] »(L, K, E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra)] [":=", expr _],
  rw ["[", expr fintype.prod_equiv alg_hom_equiv_sigma (λ
    σ : «expr →ₐ[ ] »(F, K, E), _) (λ
    σ, σ.1 pb.gen), ",", "<-", expr finset.univ_sigma_univ, ",", expr finset.prod_sigma, ",", "<-", expr finset.prod_pow, "]"] [],
  refine [expr finset.prod_congr rfl (λ σ _, _)],
  { letI [] [":", expr algebra L E] [":=", expr σ.to_ring_hom.to_algebra],
    simp [] [] ["only"] ["[", expr finset.prod_const, ",", expr finset.card_univ, "]"] [] [],
    congr,
    rw [expr alg_hom.card L F E] [] },
  { intros [ident σ],
    simp [] [] ["only"] ["[", expr alg_hom_equiv_sigma, ",", expr equiv.coe_fn_mk, ",", expr alg_hom.restrict_domain, ",", expr alg_hom.comp_apply, ",", expr is_scalar_tower.coe_to_alg_hom', "]"] [] [] }
end

variable (K)

-- error in RingTheory.Norm: ././Mathport/Syntax/Translate/Basic.lean:341:40: in haveI: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
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

