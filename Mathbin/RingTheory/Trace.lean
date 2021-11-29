import Mathbin.LinearAlgebra.BilinearForm 
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff 
import Mathbin.LinearAlgebra.Determinant 
import Mathbin.LinearAlgebra.Vandermonde 
import Mathbin.LinearAlgebra.Trace 
import Mathbin.FieldTheory.IsAlgClosed.AlgebraicClosure 
import Mathbin.FieldTheory.PrimitiveElement 
import Mathbin.RingTheory.PowerBasis

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/


universe u v w

variable{R S T : Type _}[CommRingₓ R][CommRingₓ S][CommRingₓ T]

variable[Algebra R S][Algebra R T]

variable{K L : Type _}[Field K][Field L][Algebra K L]

variable{ι : Type w}[Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix

open_locale BigOperators

open_locale Matrix

namespace Algebra

variable(b : Basis ι R S)

variable(R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap

variable{S}

theorem trace_apply x : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl

theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) : trace R S = 0 :=
  by 
    ext s 
    simp [trace_apply, LinearMap.trace, h]

include b

variable{R}

theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
  trace R S s = Matrix.trace _ R _ (Algebra.leftMulMatrix b s) :=
  by 
    rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, to_matrix_lmul_eq]

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebra_map_of_basis (x : R) : «expr = »(trace R S (algebra_map R S x), «expr • »(fintype.card ι, x)) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  rw ["[", expr trace_apply, ",", expr linear_map.trace_eq_matrix_trace R b, ",", expr trace_diag, "]"] [],
  convert [] [expr finset.sum_const _] [],
  ext [] [ident i] [],
  simp [] [] [] [] [] []
end

omit b

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
theorem trace_algebra_map (x : K) : trace K L (algebraMap K L x) = finrank K L • x :=
  by 
    byCases' H : ∃ s : Finset L, Nonempty (Basis s K L)
    ·
      rw [trace_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
    ·
      simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finset H]

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trace_trace_of_basis
[algebra S T]
[is_scalar_tower R S T]
{ι κ : Type*}
[fintype ι]
[fintype κ]
(b : basis ι R S)
(c : basis κ S T)
(x : T) : «expr = »(trace R S (trace S T x), trace R T x) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  haveI [] [] [":=", expr classical.dec_eq κ],
  rw ["[", expr trace_eq_matrix_trace (b.smul c), ",", expr trace_eq_matrix_trace b, ",", expr trace_eq_matrix_trace c, ",", expr matrix.trace_apply, ",", expr matrix.trace_apply, ",", expr matrix.trace_apply, ",", "<-", expr finset.univ_product_univ, ",", expr finset.sum_product, "]"] [],
  refine [expr finset.sum_congr rfl (λ i _, _)],
  simp [] [] ["only"] ["[", expr alg_hom.map_sum, ",", expr smul_left_mul_matrix, ",", expr finset.sum_apply, ",", expr finset.sum_apply i _ (λ
    y, left_mul_matrix b (left_mul_matrix c x y y)), "]"] [] []
end

theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type _} [Fintype ι] [Fintype κ]
  (b : Basis ι R S) (c : Basis κ S T) : (trace R S).comp ((trace S T).restrictScalars R) = trace R T :=
  by 
    ext 
    rw [LinearMap.comp_apply, LinearMap.restrict_scalars_apply, trace_trace_of_basis b c]

@[simp]
theorem trace_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L] [FiniteDimensional L T]
  (x : T) : trace K L (trace L T x) = trace K T x :=
  trace_trace_of_basis (Basis.ofVectorSpace K L) (Basis.ofVectorSpace L T) x

@[simp]
theorem trace_comp_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L]
  [FiniteDimensional L T] : (trace K L).comp ((trace L T).restrictScalars K) = trace K T :=
  by 
    ext 
    rw [LinearMap.comp_apply, LinearMap.restrict_scalars_apply, trace_trace]

section TraceForm

variable(R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : BilinForm R S :=
  (LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)).toBilin

variable{S}

@[simp]
theorem trace_form_apply (x y : S) : trace_form R S x y = trace R S (x*y) :=
  rfl

theorem trace_form_is_symm : (trace_form R S).IsSymm :=
  fun x y => congr_argₓ (trace R S) (mul_commₓ _ _)

theorem trace_form_to_matrix [DecidableEq ι] i j : BilinForm.toMatrix b (trace_form R S) i j = trace R S (b i*b j) :=
  by 
    rw [BilinForm.to_matrix_apply, trace_form_apply]

theorem trace_form_to_matrix_power_basis (h : PowerBasis R S) :
  BilinForm.toMatrix h.basis (trace_form R S) = fun i j => trace R S (h.gen^(i+j : ℕ)) :=
  by 
    ext 
    rw [trace_form_to_matrix, pow_addₓ, h.basis_eq_pow, h.basis_eq_pow]

end TraceForm

end Algebra

section EqSumRoots

open Algebra Polynomial

variable{F : Type _}[Field F]

variable[Algebra K S][Algebra K F]

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem power_basis.trace_gen_eq_sum_roots
[nontrivial S]
(pb : power_basis K S)
(hf : (minpoly K pb.gen).splits (algebra_map K F)) : «expr = »(algebra_map K F (trace K S pb.gen), ((minpoly K pb.gen).map (algebra_map K F)).roots.sum) :=
begin
  have [ident d_pos] [":", expr «expr < »(0, pb.dim)] [":=", expr power_basis.dim_pos pb],
  have [ident d_pos'] [":", expr «expr < »(0, (minpoly K pb.gen).nat_degree)] [],
  { simpa [] [] [] [] [] [] },
  haveI [] [":", expr nonempty (fin pb.dim)] [":=", expr ⟨⟨0, d_pos⟩⟩],
  rw ["[", expr trace_eq_matrix_trace pb.basis, ",", expr trace_eq_neg_charpoly_coeff, ",", expr charpoly_left_mul_matrix, ",", expr ring_hom.map_neg, ",", "<-", expr pb.nat_degree_minpoly, ",", expr fintype.card_fin, ",", "<-", expr next_coeff_of_pos_nat_degree _ d_pos', ",", "<-", expr next_coeff_map (algebra_map K F).injective, "]"] [],
  conv_lhs [] [] { rw [expr eq_prod_roots_of_splits hf] },
  rw ["[", expr monic.next_coeff_mul, ",", expr next_coeff_C_eq_zero, ",", expr zero_add, ",", expr monic.next_coeff_multiset_prod, "]"] [],
  simp_rw ["[", expr next_coeff_X_sub_C, ",", expr multiset.sum_map_neg, ",", expr neg_neg, "]"] [],
  { intros [],
    apply [expr monic_X_sub_C] },
  { convert [] [expr monic_one] [],
    simp [] [] [] ["[", expr (minpoly.monic pb.is_integral_gen).leading_coeff, "]"] [] [] },
  { apply [expr monic_multiset_prod_of_monic],
    intros [],
    apply [expr monic_X_sub_C] }
end

namespace IntermediateField.AdjoinSimple

open IntermediateField

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:341:40: in refine: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_gen_eq_zero
{x : L}
(hx : «expr¬ »(is_integral K x)) : «expr = »(algebra.trace K «expr ⟮ , ⟯»(K, [x]) (adjoin_simple.gen K x), 0) :=
begin
  rw ["[", expr trace_eq_zero_of_not_exists_basis, ",", expr linear_map.zero_apply, "]"] [],
  contrapose ["!"] [ident hx],
  obtain ["⟨", ident s, ",", "⟨", ident b, "⟩", "⟩", ":=", expr hx],
  refine [expr is_integral_of_mem_of_fg «expr ⟮ , ⟯»(K, [x]).to_subalgebra _ x _],
  { exact [expr (submodule.fg_iff_finite_dimensional _).mpr (finite_dimensional.of_finset_basis b)] },
  { exact [expr subset_adjoin K _ (set.mem_singleton x)] }
end

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:341:40: in have: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_gen_eq_sum_roots
(x : L)
(hf : (minpoly K x).splits (algebra_map K F)) : «expr = »(algebra_map K F (trace K «expr ⟮ , ⟯»(K, [x]) (adjoin_simple.gen K x)), ((minpoly K x).map (algebra_map K F)).roots.sum) :=
begin
  have [ident injKKx] [":", expr function.injective (algebra_map K «expr ⟮ , ⟯»(K, [x]))] [":=", expr ring_hom.injective _],
  have [ident injKxL] [":", expr function.injective (algebra_map «expr ⟮ , ⟯»(K, [x]) L)] [":=", expr ring_hom.injective _],
  by_cases [expr hx, ":", expr is_integral K x],
  swap,
  { simp [] [] [] ["[", expr minpoly.eq_zero hx, ",", expr trace_gen_eq_zero hx, "]"] [] [] },
  have [ident hx'] [":", expr is_integral K (adjoin_simple.gen K x)] [],
  { rwa ["[", "<-", expr is_integral_algebra_map_iff injKxL, ",", expr adjoin_simple.algebra_map_gen, "]"] [],
    apply_instance },
  rw ["[", "<-", expr adjoin.power_basis_gen hx, ",", expr (adjoin.power_basis hx).trace_gen_eq_sum_roots, "]"] []; rw ["[", expr adjoin.power_basis_gen hx, ",", expr minpoly.eq_of_algebra_map_eq injKxL hx', "]"] []; try { simp [] [] ["only"] ["[", expr adjoin_simple.algebra_map_gen _ _, "]"] [] [] },
  exact [expr hf]
end

end IntermediateField.AdjoinSimple

open IntermediateField

variable(K)

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:341:40: in rw: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_eq_trace_adjoin
[finite_dimensional K L]
(x : L) : «expr = »(algebra.trace K L x, «expr • »(finrank «expr ⟮ , ⟯»(K, [x]) L, trace K «expr ⟮ , ⟯»(K, [x]) (adjoin_simple.gen K x))) :=
begin
  rw ["<-", expr @trace_trace _ _ K «expr ⟮ , ⟯»(K, [x]) _ _ _ _ _ _ _ _ x] [],
  conv [] ["in", expr x] { rw ["<-", expr intermediate_field.adjoin_simple.algebra_map_gen K x] },
  rw ["[", expr trace_algebra_map, ",", expr linear_map.map_smul_of_tower, "]"] []
end

variable{K}

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_eq_sum_roots
[finite_dimensional K L]
{x : L}
(hF : (minpoly K x).splits (algebra_map K F)) : «expr = »(algebra_map K F (algebra.trace K L x), «expr • »(finrank «expr ⟮ , ⟯»(K, [x]) L, ((minpoly K x).map (algebra_map K _)).roots.sum)) :=
by rw ["[", expr trace_eq_trace_adjoin K x, ",", expr algebra.smul_def, ",", expr ring_hom.map_mul, ",", "<-", expr algebra.smul_def, ",", expr intermediate_field.adjoin_simple.trace_gen_eq_sum_roots _ hF, ",", expr is_scalar_tower.algebra_map_smul, "]"] []

end EqSumRoots

variable{F : Type _}[Field F]

variable[Algebra R L][Algebra L F][Algebra R F][IsScalarTower R L F]

open Polynomial

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem algebra.is_integral_trace
[finite_dimensional L F]
{x : F}
(hx : _root_.is_integral R x) : _root_.is_integral R (algebra.trace L F x) :=
begin
  have [ident hx'] [":", expr _root_.is_integral L x] [":=", expr is_integral_of_is_scalar_tower _ hx],
  rw ["[", "<-", expr is_integral_algebra_map_iff (algebra_map L (algebraic_closure F)).injective, ",", expr trace_eq_sum_roots, "]"] [],
  { refine [expr (is_integral.multiset_sum _).nsmul _],
    intros [ident y, ident hy],
    rw [expr mem_roots_map (minpoly.ne_zero hx')] ["at", ident hy],
    use ["[", expr minpoly R x, ",", expr minpoly.monic hx, "]"],
    rw ["<-", expr aeval_def] ["at", "⊢", ident hy],
    exact [expr minpoly.aeval_of_is_scalar_tower R x y hy] },
  { apply [expr is_alg_closed.splits_codomain] },
  { apply_instance }
end

section EqSumEmbeddings

variable[Algebra K F][IsScalarTower K L F]

open Algebra IntermediateField

variable(F)(E : Type _)[Field E][Algebra K E]

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trace_eq_sum_embeddings_gen
(pb : power_basis K L)
(hE : (minpoly K pb.gen).splits (algebra_map K E))
(hfx : (minpoly K pb.gen).separable) : «expr = »(algebra_map K E (algebra.trace K L pb.gen), (@@finset.univ (power_basis.alg_hom.fintype pb)).sum (λ
  σ, σ pb.gen)) :=
begin
  letI [] [] [":=", expr classical.dec_eq E],
  rw ["[", expr pb.trace_gen_eq_sum_roots hE, ",", expr fintype.sum_equiv pb.lift_equiv', ",", expr finset.sum_mem_multiset, ",", expr finset.sum_eq_multiset_sum, ",", expr multiset.to_finset_val, ",", expr multiset.erase_dup_eq_self.mpr _, ",", expr multiset.map_id, "]"] [],
  { exact [expr nodup_roots ((separable_map _).mpr hfx)] },
  { intro [ident x],
    refl },
  { intro [ident σ],
    rw ["[", expr power_basis.lift_equiv'_apply_coe, ",", expr id.def, "]"] [] }
end

variable[IsAlgClosed E]

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_embeddings_eq_finrank_mul
[finite_dimensional K F]
[is_separable K F]
(pb : power_basis K L) : «expr = »(«expr∑ , »((σ : «expr →ₐ[ ] »(F, K, E)), σ (algebra_map L F pb.gen)), «expr • »(finrank L F, (@@finset.univ (power_basis.alg_hom.fintype pb)).sum (λ
   σ : «expr →ₐ[ ] »(L, K, E), σ pb.gen))) :=
begin
  haveI [] [":", expr finite_dimensional L F] [":=", expr finite_dimensional.right K L F],
  haveI [] [":", expr is_separable L F] [":=", expr is_separable_tower_top_of_is_separable K L F],
  letI [] [":", expr fintype «expr →ₐ[ ] »(L, K, E)] [":=", expr power_basis.alg_hom.fintype pb],
  letI [] [":", expr ∀
   f : «expr →ₐ[ ] »(L, K, E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra)] [":=", expr _],
  rw ["[", expr fintype.sum_equiv alg_hom_equiv_sigma (λ
    σ : «expr →ₐ[ ] »(F, K, E), _) (λ
    σ, σ.1 pb.gen), ",", "<-", expr finset.univ_sigma_univ, ",", expr finset.sum_sigma, ",", "<-", expr finset.sum_nsmul, "]"] [],
  refine [expr finset.sum_congr rfl (λ σ _, _)],
  { letI [] [":", expr algebra L E] [":=", expr σ.to_ring_hom.to_algebra],
    simp [] [] ["only"] ["[", expr finset.sum_const, ",", expr finset.card_univ, "]"] [] [],
    rw [expr alg_hom.card L F E] [] },
  { intros [ident σ],
    simp [] [] ["only"] ["[", expr alg_hom_equiv_sigma, ",", expr equiv.coe_fn_mk, ",", expr alg_hom.restrict_domain, ",", expr alg_hom.comp_apply, ",", expr is_scalar_tower.coe_to_alg_hom', "]"] [] [] }
end

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:341:40: in haveI: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_eq_sum_embeddings
[finite_dimensional K L]
[is_separable K L]
{x : L} : «expr = »(algebra_map K E (algebra.trace K L x), «expr∑ , »((σ : «expr →ₐ[ ] »(L, K, E)), σ x)) :=
begin
  have [ident hx] [] [":=", expr is_separable.is_integral K x],
  rw ["[", expr trace_eq_trace_adjoin K x, ",", expr algebra.smul_def, ",", expr ring_hom.map_mul, ",", "<-", expr adjoin.power_basis_gen hx, ",", expr trace_eq_sum_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _), ",", "<-", expr algebra.smul_def, ",", expr algebra_map_smul, "]"] [],
  { exact [expr (sum_embeddings_eq_finrank_mul L E (adjoin.power_basis hx)).symm] },
  { haveI [] [] [":=", expr is_separable_tower_bot_of_is_separable K «expr ⟮ , ⟯»(K, [x]) L],
    exact [expr is_separable.separable K _] }
end

end EqSumEmbeddings

section DetNeZero

open Algebra

variable(pb : PowerBasis K L)

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_trace_form_ne_zero'
[is_separable K L] : «expr ≠ »(det (bilin_form.to_matrix pb.basis (trace_form K L)), 0) :=
begin
  suffices [] [":", expr «expr ≠ »(algebra_map K (algebraic_closure L) (det (bilin_form.to_matrix pb.basis (trace_form K L))), 0)],
  { refine [expr mt (λ ht, _) this],
    rw ["[", expr ht, ",", expr ring_hom.map_zero, "]"] [] },
  haveI [] [":", expr finite_dimensional K L] [":=", expr pb.finite_dimensional],
  let [ident e] [":", expr «expr ≃ »(«expr →ₐ[ ] »(L, K, algebraic_closure L), fin pb.dim)] [":=", expr fintype.equiv_fin_of_card_eq _],
  let [ident M] [":", expr matrix (fin pb.dim) (fin pb.dim) (algebraic_closure L)] [":=", expr vandermonde (λ
    i, e.symm i pb.gen)],
  calc
    «expr = »(algebra_map K (algebraic_closure _) (bilin_form.to_matrix pb.basis (trace_form K L)).det, det «expr $ »((algebra_map K _).map_matrix, bilin_form.to_matrix pb.basis (trace_form K L))) : ring_hom.map_det _ _
    «expr = »(..., det «expr ⬝ »(«expr ᵀ»(M), M)) : _
    «expr = »(..., «expr * »(det M, det M)) : by rw ["[", expr det_mul, ",", expr det_transpose, "]"] []
    «expr ≠ »(..., 0) : mt mul_self_eq_zero.mp _,
  { refine [expr congr_arg det _],
    ext [] [ident i, ident j] [],
    rw ["[", expr vandermonde_transpose_mul_vandermonde, ",", expr ring_hom.map_matrix_apply, ",", expr matrix.map_apply, ",", expr bilin_form.to_matrix_apply, ",", expr pb.basis_eq_pow, ",", expr pb.basis_eq_pow, ",", expr trace_form_apply, ",", "<-", expr pow_add, ",", expr trace_eq_sum_embeddings (algebraic_closure L), ",", expr fintype.sum_equiv e, "]"] [],
    intros [ident σ],
    rw ["[", expr e.symm_apply_apply, ",", expr σ.map_pow, "]"] [] },
  { simp [] [] ["only"] ["[", expr det_vandermonde, ",", expr finset.prod_eq_zero_iff, ",", expr not_exists, ",", expr sub_eq_zero, "]"] [] [],
    intros [ident i, "_", ident j, ident hij, ident h],
    exact [expr (finset.mem_filter.mp hij).2.ne' «expr $ »(e.symm.injective, pb.alg_hom_ext h)] },
  { rw ["[", expr alg_hom.card, ",", expr pb.finrank, "]"] [] }
end

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_trace_form_ne_zero
[is_separable K L]
[decidable_eq ι]
(b : basis ι K L) : «expr ≠ »(det (bilin_form.to_matrix b (trace_form K L)), 0) :=
begin
  haveI [] [":", expr finite_dimensional K L] [":=", expr finite_dimensional.of_fintype_basis b],
  let [ident pb] [":", expr power_basis K L] [":=", expr field.power_basis_of_finite_of_separable _ _],
  rw ["[", "<-", expr bilin_form.to_matrix_mul_basis_to_matrix pb.basis b, ",", "<-", expr det_comm' (pb.basis.to_matrix_mul_to_matrix_flip b) _, ",", "<-", expr matrix.mul_assoc, ",", expr det_mul, "]"] [],
  swap,
  { apply [expr basis.to_matrix_mul_to_matrix_flip] },
  refine [expr mul_ne_zero (is_unit_of_mul_eq_one _ «expr ⬝ »(«expr ᵀ»(b.to_matrix pb.basis), b.to_matrix pb.basis).det _).ne_zero (det_trace_form_ne_zero' pb)],
  calc
    «expr = »(«expr * »(«expr ⬝ »(pb.basis.to_matrix b, «expr ᵀ»(pb.basis.to_matrix b)).det, «expr ⬝ »(«expr ᵀ»(b.to_matrix pb.basis), b.to_matrix pb.basis).det), «expr ⬝ »(«expr ⬝ »(pb.basis.to_matrix b, «expr ᵀ»(«expr ⬝ »(b.to_matrix pb.basis, pb.basis.to_matrix b))), b.to_matrix pb.basis).det) : by simp [] [] ["only"] ["[", "<-", expr det_mul, ",", expr matrix.mul_assoc, ",", expr matrix.transpose_mul, "]"] [] []
    «expr = »(..., 1) : by simp [] [] ["only"] ["[", expr basis.to_matrix_mul_to_matrix_flip, ",", expr matrix.transpose_one, ",", expr matrix.mul_one, ",", expr matrix.det_one, "]"] [] []
end

variable(K L)

theorem trace_form_nondegenerate [FiniteDimensional K L] [IsSeparable K L] : (trace_form K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (trace_form K L) _ (det_trace_form_ne_zero (FiniteDimensional.finBasis K L))

end DetNeZero

