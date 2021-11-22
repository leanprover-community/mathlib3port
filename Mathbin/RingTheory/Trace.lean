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

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebra_map_of_basis (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x :=
  by 
    haveI  := Classical.decEq ι 
    rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, trace_diag]
    convert Finset.sum_const _ 
    ext i 
    simp 

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

theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type _} [Fintype ι] [Fintype κ]
  (b : Basis ι R S) (c : Basis κ S T) (x : T) : trace R S (trace S T x) = trace R T x :=
  by 
    haveI  := Classical.decEq ι 
    haveI  := Classical.decEq κ 
    rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c, Matrix.trace_apply,
      Matrix.trace_apply, Matrix.trace_apply, ←Finset.univ_product_univ, Finset.sum_product]
    refine' Finset.sum_congr rfl fun i _ => _ 
    simp only [AlgHom.map_sum, smul_left_mul_matrix, Finset.sum_apply,
      Finset.sum_apply i _ fun y => left_mul_matrix b (left_mul_matrix c x y y)]

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

theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
  (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
  algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.Sum :=
  by 
    have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb 
    have d_pos' : 0 < (minpoly K pb.gen).natDegree
    ·
      simpa 
    haveI  : Nonempty (Finₓ pb.dim) := ⟨⟨0, d_pos⟩⟩
    rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_left_mul_matrix, RingHom.map_neg,
      ←pb.nat_degree_minpoly, Fintype.card_fin, ←next_coeff_of_pos_nat_degree _ d_pos',
      ←next_coeff_map (algebraMap K F).Injective]
    convLHS => rw [eq_prod_roots_of_splits hf]
    rw [monic.next_coeff_mul, next_coeff_C_eq_zero, zero_addₓ, monic.next_coeff_multiset_prod]
    simpRw [next_coeff_X_sub_C, Multiset.sum_map_neg, neg_negₓ]
    ·
      intros 
      apply monic_X_sub_C
    ·
      convert monic_one 
      simp [(minpoly.monic pb.is_integral_gen).leadingCoeff]
    ·
      apply monic_multiset_prod_of_monic 
      intros 
      apply monic_X_sub_C

namespace IntermediateField.AdjoinSimple

open IntermediateField

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in refine: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
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

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in have: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
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

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in rw: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_eq_trace_adjoin
[finite_dimensional K L]
(x : L) : «expr = »(algebra.trace K L x, «expr • »(finrank «expr ⟮ , ⟯»(K, [x]) L, trace K «expr ⟮ , ⟯»(K, [x]) (adjoin_simple.gen K x))) :=
begin
  rw ["<-", expr @trace_trace _ _ K «expr ⟮ , ⟯»(K, [x]) _ _ _ _ _ _ _ _ x] [],
  conv [] ["in", expr x] { rw ["<-", expr intermediate_field.adjoin_simple.algebra_map_gen K x] },
  rw ["[", expr trace_algebra_map, ",", expr linear_map.map_smul_of_tower, "]"] []
end

variable{K}

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
theorem trace_eq_sum_roots
[finite_dimensional K L]
{x : L}
(hF : (minpoly K x).splits (algebra_map K F)) : «expr = »(algebra_map K F (algebra.trace K L x), «expr • »(finrank «expr ⟮ , ⟯»(K, [x]) L, ((minpoly K x).map (algebra_map K _)).roots.sum)) :=
by rw ["[", expr trace_eq_trace_adjoin K x, ",", expr algebra.smul_def, ",", expr ring_hom.map_mul, ",", "<-", expr algebra.smul_def, ",", expr intermediate_field.adjoin_simple.trace_gen_eq_sum_roots _ hF, ",", expr is_scalar_tower.algebra_map_smul, "]"] []

end EqSumRoots

variable{F : Type _}[Field F]

variable[Algebra R L][Algebra L F][Algebra R F][IsScalarTower R L F]

open Polynomial

theorem Algebra.is_integral_trace [FiniteDimensional L F] {x : F} (hx : _root_.is_integral R x) :
  _root_.is_integral R (Algebra.trace L F x) :=
  by 
    have hx' : _root_.is_integral L x := is_integral_of_is_scalar_tower _ hx 
    rw [←is_integral_algebra_map_iff (algebraMap L (AlgebraicClosure F)).Injective, trace_eq_sum_roots]
    ·
      refine' (IsIntegral.multiset_sum _).nsmul _ 
      intro y hy 
      rw [mem_roots_map (minpoly.ne_zero hx')] at hy 
      use minpoly R x, minpoly.monic hx 
      rw [←aeval_def] at hy⊢
      exact minpoly.aeval_of_is_scalar_tower R x y hy
    ·
      apply IsAlgClosed.splits_codomain
    ·
      infer_instance

section EqSumEmbeddings

variable[Algebra K F][IsScalarTower K L F]

open Algebra IntermediateField

variable(F)(E : Type _)[Field E][Algebra K E]

theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L) (hE : (minpoly K pb.gen).Splits (algebraMap K E))
  (hfx : (minpoly K pb.gen).Separable) :
  algebraMap K E (Algebra.trace K L pb.gen) = (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Sum fun σ => σ pb.gen :=
  by 
    letI this := Classical.decEq E 
    rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.lift_equiv', Finset.sum_mem_multiset,
      Finset.sum_eq_multiset_sum, Multiset.to_finset_val,
      multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx)), Multiset.map_id]
    ·
      intro x 
      rfl
    ·
      intro σ 
      rw [PowerBasis.lift_equiv'_apply_coe, id.def]

variable[IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [IsSeparable K F] (pb : PowerBasis K L) :
  (∑σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
    finrank L F • (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Sum fun σ : L →ₐ[K] E => σ pb.gen :=
  by 
    haveI  : FiniteDimensional L F := FiniteDimensional.right K L F 
    haveI  : IsSeparable L F := is_separable_tower_top_of_is_separable K L F 
    letI this : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb 
    letI this : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _ 
    rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ←Finset.univ_sigma_univ,
      Finset.sum_sigma, ←Finset.sum_nsmul]
    refine' Finset.sum_congr rfl fun σ _ => _
    ·
      letI this : Algebra L E := σ.to_ring_hom.to_algebra 
      simp only [Finset.sum_const, Finset.card_univ]
      rw [AlgHom.card L F E]
    ·
      intro σ 
      simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
        IsScalarTower.coe_to_alg_hom']

-- error in RingTheory.Trace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in haveI: ././Mathport/Syntax/Translate/Basic.lean:557:61: unsupported notation `«expr ⟮ , ⟯»
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

theorem det_trace_form_ne_zero' [IsSeparable K L] : det (BilinForm.toMatrix pb.basis (trace_form K L)) ≠ 0 :=
  by 
    suffices  : algebraMap K (AlgebraicClosure L) (det (BilinForm.toMatrix pb.basis (trace_form K L))) ≠ 0
    ·
      refine' mt (fun ht => _) this 
      rw [ht, RingHom.map_zero]
    haveI  : FiniteDimensional K L := pb.finite_dimensional 
    let e : (L →ₐ[K] AlgebraicClosure L) ≃ Finₓ pb.dim := Fintype.equivFinOfCardEq _ 
    let M : Matrix (Finₓ pb.dim) (Finₓ pb.dim) (AlgebraicClosure L) := vandermonde fun i => e.symm i pb.gen 
    calc
      algebraMap K (AlgebraicClosure _) (BilinForm.toMatrix pb.basis (trace_form K L)).det =
        det ((algebraMap K _).mapMatrix$ BilinForm.toMatrix pb.basis (trace_form K L)) :=
      RingHom.map_det _ _ _ = det ((M)ᵀ ⬝ M) := _ _ = det M*det M :=
      by 
        rw [det_mul, det_transpose]_ ≠ 0 :=
      mt mul_self_eq_zero.mp _
    ·
      refine' congr_argₓ det _ 
      ext i j 
      rw [vandermonde_transpose_mul_vandermonde, RingHom.map_matrix_apply, Matrix.map_apply, BilinForm.to_matrix_apply,
        pb.basis_eq_pow, pb.basis_eq_pow, trace_form_apply, ←pow_addₓ, trace_eq_sum_embeddings (AlgebraicClosure L),
        Fintype.sum_equiv e]
      intro σ 
      rw [e.symm_apply_apply, σ.map_pow]
    ·
      simp only [det_vandermonde, Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
      intro i _ j hij h 
      exact (finset.mem_filter.mp hij).2.ne' (e.symm.injective$ pb.alg_hom_ext h)
    ·
      rw [AlgHom.card, pb.finrank]

theorem det_trace_form_ne_zero [IsSeparable K L] [DecidableEq ι] (b : Basis ι K L) :
  det (BilinForm.toMatrix b (trace_form K L)) ≠ 0 :=
  by 
    haveI  : FiniteDimensional K L := FiniteDimensional.of_fintype_basis b 
    let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _ 
    rw [←BilinForm.to_matrix_mul_basis_to_matrix pb.basis b, ←det_comm' (pb.basis.to_matrix_mul_to_matrix_flip b) _,
      ←Matrix.mul_assoc, det_mul]
    swap
    ·
      apply Basis.to_matrix_mul_to_matrix_flip 
    refine'
      mul_ne_zero (is_unit_of_mul_eq_one _ ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det _).ne_zero
        (det_trace_form_ne_zero' pb)
    calc
      ((pb.basis.to_matrix b ⬝ (pb.basis.to_matrix b)ᵀ).det*((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det) =
        (pb.basis.to_matrix b ⬝ (b.to_matrix pb.basis ⬝ pb.basis.to_matrix b)ᵀ ⬝ b.to_matrix pb.basis).det :=
      by 
        simp only [←det_mul, Matrix.mul_assoc, Matrix.transpose_mul]_ = 1 :=
      by 
        simp only [Basis.to_matrix_mul_to_matrix_flip, Matrix.transpose_one, Matrix.mul_one, Matrix.det_one]

variable(K L)

theorem trace_form_nondegenerate [FiniteDimensional K L] [IsSeparable K L] : (trace_form K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (trace_form K L) _ (det_trace_form_ne_zero (FiniteDimensional.finBasis K L))

end DetNeZero

