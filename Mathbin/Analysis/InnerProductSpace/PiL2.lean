import Mathbin.Analysis.InnerProductSpace.Projection 
import Mathbin.Analysis.NormedSpace.PiLp

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `basis.isometry_euclidean_of_orthonormal`: provides the isometry to Euclidean space
  from a given finite-dimensional inner product space, induced by a basis of the space.

- `linear_isometry_equiv.of_inner_product_space`: provides an arbitrary isometry to Euclidean space
  from a given finite-dimensional inner product space, induced by choosing an arbitrary basis.

- `complex.isometry_euclidean`: standard isometry from `ℂ` to `euclidean_space ℝ (fin 2)`

-/


open Real Set Filter IsROrC

open_locale BigOperators uniformity TopologicalSpace Nnreal Ennreal ComplexConjugate DirectSum

attribute [local instance] fact_one_le_two_real

attribute [local instance] fact_one_le_two_real

noncomputable theory

variable{ι : Type _}

variable{𝕜 : Type _}[IsROrC 𝕜]{E : Type _}[InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- error in Analysis.InnerProductSpace.PiL2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance pi_Lp.inner_product_space
{ι : Type*}
[fintype ι]
(f : ι → Type*)
[∀ i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp 2 f) :=
{ inner := λ x y, «expr∑ , »((i), inner (x i) (y i)),
  norm_sq_eq_inner := begin
    intro [ident x],
    have [ident h₁] [":", expr «expr = »(«expr∑ , »((i : ι), «expr ^ »(«expr∥ ∥»(x i), (2 : exprℕ()))), «expr∑ , »((i : ι), «expr ^ »(«expr∥ ∥»(x i), (2 : exprℝ()))))] [],
    { apply [expr finset.sum_congr rfl],
      intros [ident j, ident hj],
      simp [] [] [] ["[", "<-", expr rpow_nat_cast, "]"] [] [] },
    have [ident h₂] [":", expr «expr ≤ »(0, «expr∑ , »((i : ι), «expr ^ »(«expr∥ ∥»(x i), (2 : exprℝ()))))] [],
    { rw ["[", "<-", expr h₁, "]"] [],
      exact [expr finset.sum_nonneg (λ (j) (hj : «expr ∈ »(j, finset.univ)), pow_nonneg (norm_nonneg (x j)) 2)] },
    simp [] [] [] ["[", expr norm, ",", expr add_monoid_hom.map_sum, ",", "<-", expr norm_sq_eq_inner, "]"] [] [],
    rw ["[", "<-", expr rpow_nat_cast «expr ^ »(«expr∑ , »((i : ι), «expr ^ »(«expr∥ ∥»(x i), (2 : exprℝ()))), «expr ⁻¹»((2 : exprℝ()))) 2, "]"] [],
    rw ["[", "<-", expr rpow_mul h₂, "]"] [],
    norm_num ["[", expr h₁, "]"] []
  end,
  conj_sym := begin
    intros [ident x, ident y],
    unfold [ident inner] [],
    rw [expr ring_equiv.map_sum] [],
    apply [expr finset.sum_congr rfl],
    rintros [ident z, "-"],
    apply [expr inner_conj_sym]
  end,
  add_left := λ
  x
  y
  z, show «expr = »(«expr∑ , »((i), inner «expr + »(x i, y i) (z i)), «expr + »(«expr∑ , »((i), inner (x i) (z i)), «expr∑ , »((i), inner (y i) (z i)))), by simp [] [] ["only"] ["[", expr inner_add_left, ",", expr finset.sum_add_distrib, "]"] [] [],
  smul_left := λ
  x
  y
  r, show «expr = »(«expr∑ , »((i : ι), inner «expr • »(r, x i) (y i)), «expr * »(exprconj() r, «expr∑ , »((i), inner (x i) (y i)))), by simp [] [] ["only"] ["[", expr finset.mul_sum, ",", expr inner_smul_left, "]"] [] [] }

@[simp]
theorem PiLp.inner_apply {ι : Type _} [Fintype ι] {f : ι → Type _} [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) :
  ⟪x, y⟫ = ∑i, ⟪x i, y i⟫ :=
  rfl

theorem PiLp.norm_eq_of_L2 {ι : Type _} [Fintype ι] {f : ι → Type _} [∀ i, InnerProductSpace 𝕜 (f i)] (x : PiLp 2 f) :
  ∥x∥ = sqrt (∑i : ι, ∥x i∥^2) :=
  by 
    rw [PiLp.norm_eq_of_nat 2] <;> simp [sqrt_eq_rpow]

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def EuclideanSpace (𝕜 : Type _) [IsROrC 𝕜] (n : Type _) [Fintype n] : Type _ :=
  PiLp 2 fun i : n => 𝕜

theorem EuclideanSpace.norm_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x : EuclideanSpace 𝕜 n) :
  ∥x∥ = Real.sqrt (∑i : n, ∥x i∥^2) :=
  PiLp.norm_eq_of_L2 x

section 

attribute [local reducible] PiLp

variable[Fintype ι]

instance  : FiniteDimensional 𝕜 (EuclideanSpace 𝕜 ι) :=
  by 
    infer_instance

instance  : InnerProductSpace 𝕜 (EuclideanSpace 𝕜 ι) :=
  by 
    infer_instance

@[simp]
theorem finrank_euclidean_space : FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι :=
  by 
    simp 

theorem finrank_euclidean_space_fin {n : ℕ} : FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 (Finₓ n)) = n :=
  by 
    simp 

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def DirectSum.SubmoduleIsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
  (hV : DirectSum.SubmoduleIsInternal V) (hV' : OrthogonalFamily 𝕜 V) : E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i :=
  by 
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i 
    let e₂ := LinearEquiv.ofBijective _ hV.injective hV.surjective 
    refine' (e₂.symm.trans e₁).isometryOfInner _ 
    suffices  : ∀ v w, ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫
    ·
      intro v₀ w₀ 
      convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀)) <;>
        simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    intro v w 
    trans ⟪∑i, (v i : E), ∑i, (w i : E)⟫
    ·
      simp [sum_inner, hV'.inner_right_fintype]
    ·
      congr <;> simp 

@[simp]
theorem DirectSum.SubmoduleIsInternal.isometry_L2_of_orthogonal_family_symm_apply [DecidableEq ι]
  {V : ι → Submodule 𝕜 E} (hV : DirectSum.SubmoduleIsInternal V) (hV' : OrthogonalFamily 𝕜 V)
  (w : PiLp 2 fun i => V i) : (hV.isometry_L2_of_orthogonal_family hV').symm w = ∑i, (w i : E) :=
  by 
    classical 
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i 
    let e₂ := LinearEquiv.ofBijective _ hV.injective hV.surjective 
    suffices  : ∀ v : ⨁i, V i, e₂ v = ∑i, e₁ v i
    ·
      exact this (e₁.symm w)
    intro v 
    simp [e₂, DirectSum.submoduleCoe, DirectSum.toModule, Dfinsupp.sum_add_hom_apply]

-- error in Analysis.InnerProductSpace.PiL2: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An orthonormal basis on a fintype `ι` for an inner product space induces an isometry with
`euclidean_space 𝕜 ι`. -/
def basis.isometry_euclidean_of_orthonormal
(v : basis ι 𝕜 E)
(hv : orthonormal 𝕜 v) : «expr ≃ₗᵢ[ ] »(E, 𝕜, euclidean_space 𝕜 ι) :=
v.equiv_fun.isometry_of_inner (begin
   intros [ident x, ident y],
   let [ident p] [":", expr euclidean_space 𝕜 ι] [":=", expr v.equiv_fun x],
   let [ident q] [":", expr euclidean_space 𝕜 ι] [":=", expr v.equiv_fun y],
   have [ident key] [":", expr «expr = »(«expr⟪ , ⟫»(p, q), «expr⟪ , ⟫»(«expr∑ , »((i), «expr • »(p i, v i)), «expr∑ , »((i), «expr • »(q i, v i))))] [],
   { simp [] [] [] ["[", expr sum_inner, ",", expr inner_smul_left, ",", expr hv.inner_right_fintype, "]"] [] [] },
   convert [] [expr key] [],
   { rw ["[", "<-", expr v.equiv_fun.symm_apply_apply x, ",", expr v.equiv_fun_symm_apply, "]"] [] },
   { rw ["[", "<-", expr v.equiv_fun.symm_apply_apply y, ",", expr v.equiv_fun_symm_apply, "]"] [] }
 end)

@[simp]
theorem Basis.coe_isometry_euclidean_of_orthonormal (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
  (v.isometry_euclidean_of_orthonormal hv : E → EuclideanSpace 𝕜 ι) = v.equiv_fun :=
  rfl

@[simp]
theorem Basis.coe_isometry_euclidean_of_orthonormal_symm (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
  ((v.isometry_euclidean_of_orthonormal hv).symm : EuclideanSpace 𝕜 ι → E) = v.equiv_fun.symm :=
  rfl

end 

/-- `ℂ` is isometric to `ℝ²` with the Euclidean inner product. -/
def Complex.isometryEuclidean : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Finₓ 2) :=
  Complex.basisOneI.isometryEuclideanOfOrthonormal
    (by 
      rw [orthonormal_iff_ite]
      intro i 
      finCases i <;> intro j <;> finCases j <;> simp [real_inner_eq_re_inner])

@[simp]
theorem Complex.isometry_euclidean_symm_apply (x : EuclideanSpace ℝ (Finₓ 2)) :
  Complex.isometryEuclidean.symm x = x 0+x 1*I :=
  by 
    convert complex.basis_one_I.equiv_fun_symm_apply x
    ·
      simpa
    ·
      simp 

theorem Complex.isometry_euclidean_proj_eq_self (z : ℂ) :
  («expr↑ » (Complex.isometryEuclidean z 0)+«expr↑ » (Complex.isometryEuclidean z 1)*(I : ℂ)) = z :=
  by 
    rw [←Complex.isometry_euclidean_symm_apply (Complex.isometryEuclidean z),
      complex.isometry_euclidean.symm_apply_apply z]

@[simp]
theorem Complex.isometry_euclidean_apply_zero (z : ℂ) : Complex.isometryEuclidean z 0 = z.re :=
  by 
    convRHS => rw [←Complex.isometry_euclidean_proj_eq_self z]
    simp 

@[simp]
theorem Complex.isometry_euclidean_apply_one (z : ℂ) : Complex.isometryEuclidean z 1 = z.im :=
  by 
    convRHS => rw [←Complex.isometry_euclidean_proj_eq_self z]
    simp 

open FiniteDimensional

/-- Given a natural number `n` equal to the `finrank` of a finite-dimensional inner product space,
there exists an isometry from the space to `euclidean_space 𝕜 (fin n)`. -/
def LinearIsometryEquiv.ofInnerProductSpace [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Finₓ n) :=
  (finOrthonormalBasis hn).isometryEuclideanOfOrthonormal (fin_orthonormal_basis_orthonormal hn)

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def LinearIsometryEquiv.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n+1)] {v : E} (hv : v ≠ 0) :
  (𝕜∙v)ᗮ ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Finₓ n) :=
  LinearIsometryEquiv.ofInnerProductSpace (finrank_orthogonal_span_singleton hv)

