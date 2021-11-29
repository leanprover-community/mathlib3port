import Mathbin.LinearAlgebra.Matrix.Nondegenerate 
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse 
import Mathbin.LinearAlgebra.Matrix.ToLin 
import Mathbin.RingTheory.Localization

/-!
# Matrices and linear equivalences

This file gives the map `matrix.to_linear_equiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `matrix.to_linear_equiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

 * `matrix.exists_mul_vec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear_equiv, determinant, inverse

-/


namespace Matrix

open LinearMap

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable {n : Type _} [Fintype n]

section ToLinearEquiv'

variable [DecidableEq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
def to_linear_equiv' (P : Matrix n n R) (h : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  { P.to_lin' with invFun := (⅟ P).toLin',
    left_inv :=
      fun v =>
        show ((⅟ P).toLin'.comp P.to_lin') v = v by 
          rw [←Matrix.to_lin'_mul, P.inv_of_mul_self, Matrix.to_lin'_one, LinearMap.id_apply],
    right_inv :=
      fun v =>
        show (P.to_lin'.comp (⅟ P).toLin') v = v by 
          rw [←Matrix.to_lin'_mul, P.mul_inv_of_self, Matrix.to_lin'_one, LinearMap.id_apply] }

@[simp]
theorem to_linear_equiv'_apply (P : Matrix n n R) (h : Invertible P) :
  («expr↑ » (P.to_linear_equiv' h) : Module.End R (n → R)) = P.to_lin' :=
  rfl

@[simp]
theorem to_linear_equiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
  («expr↑ » (P.to_linear_equiv' h).symm : Module.End R (n → R)) = P⁻¹.toLin' :=
  show (⅟ P).toLin' = _ from congr_argₓ _ P.inv_of_eq_nonsing_inv

end ToLinearEquiv'

section ToLinearEquiv

variable (b : Basis n R M)

include b

/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def to_linear_equiv [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : M ≃ₗ[R] M :=
  by 
    refine'
        { to_lin b b A with toFun := to_lin b b A, invFun := to_lin b b (A⁻¹), left_inv := fun x => _,
          right_inv := fun x => _ } <;>
      rw [←LinearMap.comp_apply] <;>
        simp only [←Matrix.to_lin_mul b b b, Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hA, to_lin_one,
          LinearMap.id_apply]

theorem ker_to_lin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : (to_lin b b A).ker = ⊥ :=
  ker_eq_bot.mpr (to_linear_equiv b A hA).Injective

theorem range_to_lin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) : (to_lin b b A).range = ⊤ :=
  range_eq_top.mpr (to_linear_equiv b A hA).Surjective

end ToLinearEquiv

section Nondegenerate

open_locale Matrix

-- error in LinearAlgebra.Matrix.ToLinearEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This holds for all integral domains (see `matrix.exists_mul_vec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
theorem exists_mul_vec_eq_zero_iff_aux
{K : Type*}
[decidable_eq n]
[field K]
{M : matrix n n K} : «expr ↔ »(«expr∃ , »((v «expr ≠ » 0), «expr = »(M.mul_vec v, 0)), «expr = »(M.det, 0)) :=
begin
  split,
  { rintros ["⟨", ident v, ",", ident hv, ",", ident mul_eq, "⟩"],
    contrapose ["!"] [ident hv],
    exact [expr eq_zero_of_mul_vec_eq_zero hv mul_eq] },
  { contrapose ["!"] [],
    intros [ident h],
    have [] [":", expr function.injective M.to_lin'] [],
    { simpa [] [] ["only"] ["[", "<-", expr linear_map.ker_eq_bot, ",", expr ker_to_lin'_eq_bot_iff, ",", expr not_imp_not, "]"] [] ["using", expr h] },
    have [] [":", expr «expr = »(«expr ⬝ »(M, linear_map.to_matrix' ((linear_equiv.of_injective_endo M.to_lin' this).symm : «expr →ₗ[ ] »(n → K, K, n → K))), 1)] [],
    { refine [expr matrix.to_lin'.injective «expr $ »(linear_map.ext, λ v, _)],
      rw ["[", expr matrix.to_lin'_mul, ",", expr matrix.to_lin'_one, ",", expr matrix.to_lin'_to_matrix', ",", expr linear_map.comp_apply, "]"] [],
      exact [expr (linear_equiv.of_injective_endo M.to_lin' this).apply_symm_apply v] },
    exact [expr matrix.det_ne_zero_of_right_inverse this] }
end

-- error in LinearAlgebra.Matrix.ToLinearEquiv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_mul_vec_eq_zero_iff'
{A : Type*}
(K : Type*)
[decidable_eq n]
[comm_ring A]
[is_domain A]
[field K]
[algebra A K]
[is_fraction_ring A K]
{M : matrix n n A} : «expr ↔ »(«expr∃ , »((v «expr ≠ » 0), «expr = »(M.mul_vec v, 0)), «expr = »(M.det, 0)) :=
begin
  have [] [":", expr «expr ↔ »(«expr∃ , »((v «expr ≠ » 0), «expr = »(mul_vec ((algebra_map A K).map_matrix M) v, 0)), _)] [":=", expr exists_mul_vec_eq_zero_iff_aux],
  rw ["[", "<-", expr ring_hom.map_det, ",", expr is_fraction_ring.to_map_eq_zero_iff, "]"] ["at", ident this],
  refine [expr iff.trans _ this],
  split; rintro ["⟨", ident v, ",", ident hv, ",", ident mul_eq, "⟩"],
  { refine [expr ⟨λ i, algebra_map _ _ (v i), mt (λ h, «expr $ »(funext, λ i, _)) hv, _⟩],
    { exact [expr is_fraction_ring.to_map_eq_zero_iff.mp (congr_fun h i)] },
    { ext [] [ident i] [],
      refine [expr (ring_hom.map_mul_vec _ _ _ i).symm.trans _],
      rw ["[", expr mul_eq, ",", expr pi.zero_apply, ",", expr ring_hom.map_zero, ",", expr pi.zero_apply, "]"] [] } },
  { letI [] [] [":=", expr classical.dec_eq K],
    obtain ["⟨", "⟨", ident b, ",", ident hb, "⟩", ",", ident ba_eq, "⟩", ":=", expr is_localization.exist_integer_multiples_of_finset (non_zero_divisors A) (finset.univ.image v)],
    choose [] [ident f] [ident hf] ["using", expr ba_eq],
    refine [expr ⟨λ
      i, f _ (finset.mem_image.mpr ⟨i, finset.mem_univ i, rfl⟩), mt (λ h, «expr $ »(funext, λ i, _)) hv, _⟩],
    { have [] [] [":=", expr congr_arg (algebra_map A K) (congr_fun h i)],
      rw ["[", expr hf, ",", expr subtype.coe_mk, ",", expr pi.zero_apply, ",", expr ring_hom.map_zero, ",", expr algebra.smul_def, ",", expr mul_eq_zero, ",", expr is_fraction_ring.to_map_eq_zero_iff, "]"] ["at", ident this],
      exact [expr this.resolve_left (mem_non_zero_divisors_iff_ne_zero.mp hb)] },
    { ext [] [ident i] [],
      refine [expr is_fraction_ring.injective A K _],
      calc
        «expr = »(algebra_map A K (M.mul_vec (λ
           i : n, f (v i) _) i), ((algebra_map A K).map_matrix M).mul_vec «expr • »(algebra_map _ K b, v) i) : _
        «expr = »(..., 0) : _
        «expr = »(..., algebra_map A K 0) : (ring_hom.map_zero _).symm,
      { simp_rw ["[", expr ring_hom.map_mul_vec, ",", expr mul_vec, ",", expr dot_product, ",", expr function.comp_app, ",", expr hf, ",", expr subtype.coe_mk, ",", expr ring_hom.map_matrix_apply, ",", expr pi.smul_apply, ",", expr smul_eq_mul, ",", expr algebra.smul_def, "]"] [] },
      { rw ["[", expr mul_vec_smul, ",", expr mul_eq, ",", expr pi.smul_apply, ",", expr pi.zero_apply, ",", expr smul_zero, "]"] [] } } }
end

theorem exists_mul_vec_eq_zero_iff {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
  (∃ (v : _)(_ : v ≠ 0), M.mul_vec v = 0) ↔ M.det = 0 :=
  exists_mul_vec_eq_zero_iff' (FractionRing A)

theorem exists_vec_mul_eq_zero_iff {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
  (∃ (v : _)(_ : v ≠ 0), M.vec_mul v = 0) ↔ M.det = 0 :=
  by 
    simpa only [←M.det_transpose, ←mul_vec_transpose] using exists_mul_vec_eq_zero_iff

theorem nondegenerate_iff_det_ne_zero {A : Type _} [DecidableEq n] [CommRingₓ A] [IsDomain A] {M : Matrix n n A} :
  nondegenerate M ↔ M.det ≠ 0 :=
  by 
    refine' Iff.trans _ (not_iff_not.mpr exists_vec_mul_eq_zero_iff)
    simp only [not_exists]
    split 
    ·
      intro hM v hv hMv 
      obtain ⟨w, hwMv⟩ := hM.exists_not_ortho_of_ne_zero hv 
      simpa only [dot_product_mul_vec, hMv, zero_dot_product] using hwMv
    ·
      intro h v hv 
      refine' not_imp_not.mp (h v) (funext$ fun i => _)
      simpa only [dot_product_mul_vec, dot_product_single, mul_oneₓ] using hv (Pi.single i 1)

alias nondegenerate_iff_det_ne_zero ↔ Matrix.Nondegenerate.det_ne_zero Matrix.Nondegenerate.of_det_ne_zero

end Nondegenerate

end Matrix

