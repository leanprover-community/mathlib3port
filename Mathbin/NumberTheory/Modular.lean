import Mathbin.Analysis.Complex.UpperHalfPlane
import Mathbin.LinearAlgebra.GeneralLinearGroup

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fundamental_domain`, `𝒟`) for this action and show
(`modular_group.exists_smul_mem_fundamental_domain`) that any point in `ℍ` can be
moved inside `𝒟`.

Standard proofs make use of the identity

`g • z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`modular_group.smul_eq_lc_row0_add`):

`g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(g•z).im` (see `modular_group.exists_max_im`), and then among
those, to minimize `|(g•z).re|` (see `modular_group.exists_row_one_eq_and_min_re`).
-/


open Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane

noncomputable section

local notation "SL(" n ", " R ")" => special_linear_group (Finₓ n) R

local prefix:1024 "↑ₘ" => @coeₓ _ (Matrix (Finₓ 2) (Finₓ 2) ℤ) _

open_locale UpperHalfPlane ComplexConjugate

attribute [local instance] Fintype.card_fin_even

namespace ModularGroup

section UpperHalfPlaneAction

/-- For a subring `R` of `ℝ`, the action of `SL(2, R)` on the upper half-plane, as a restriction of
the `SL(2, ℝ)`-action defined by `upper_half_plane.mul_action`. -/
instance {R : Type _} [CommRingₓ R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ (map (algebraMap R ℝ))

theorem coe_smul (g : SL(2, ℤ)) (z : ℍ) : ↑(g • z) = Num g z / denom g z :=
  rfl

theorem re_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).re = (Num g z / denom g z).re :=
  rfl

@[simp]
theorem smul_coe (g : SL(2, ℤ)) (z : ℍ) : (g : SL(2, ℝ)) • z = g • z :=
  rfl

@[simp]
theorem neg_smul (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z :=
  show ↑(-g) • _ = _ by
    simp [neg_smul g z]

theorem im_smul (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = (Num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_norm_sq (g : SL(2, ℤ)) (z : ℍ) : (g • z).im = z.im / Complex.normSq (denom g z) :=
  im_smul_eq_div_norm_sq g z

@[simp]
theorem denom_apply (g : SL(2, ℤ)) (z : ℍ) : denom g z = ↑ₘg 1 0 * z + ↑ₘg 1 1 := by
  simp

end UpperHalfPlaneAction

section BottomRow

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
theorem bottom_row_coprime {R : Type _} [CommRingₓ R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Finₓ 2) (Finₓ 2) R) 1 0) ((↑g : Matrix (Finₓ 2) (Finₓ 2) R) 1 1) := by
  use -(↑g : Matrix (Finₓ 2) (Finₓ 2) R) 0 1, (↑g : Matrix (Finₓ 2) (Finₓ 2) R) 0 0
  rw [add_commₓ, ← neg_mul_eq_neg_mul, ← sub_eq_add_neg, ← det_fin_two]
  exact g.det_coe

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
theorem bottom_row_surj {R : Type _} [CommRingₓ R] :
    Set.SurjOn (fun g : SL(2, R) => @coeₓ _ (Matrix (Finₓ 2) (Finₓ 2) R) _ g 1) Set.Univ
      { cd | IsCoprime (cd 0) (cd 1) } :=
  by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"
  have det_A_1 : det A = 1 := by
    convert gcd_eqn
    simp [A, det_fin_two,
      (by
        ring : a * cd 1 + b₀ * cd 0 = b₀ * cd 0 + a * cd 1)]
  refine' ⟨⟨A, det_A_1⟩, Set.mem_univ _, _⟩
  ext <;> simp [A]

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local instance] Matrix.normedGroup Matrix.normedSpace

attribute [local simp] coe_smul

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_norm_sq_coprime_pair (z : ℍ) :
    Filter.Tendsto (fun p : Finₓ 2 → ℤ => ((p 0 : ℂ) * z + p 1).normSq) cofinite at_top := by
  let π₀ : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let f : (Finₓ 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smul_right (z : ℂ) + π₁.smul_right 1
  have f_def : ⇑f = fun p : Finₓ 2 → ℝ => (p 0 : ℂ) * ↑z + p 1 := by
    ext1
    dsimp only [LinearMap.coe_proj, real_smul, LinearMap.coe_smul_right, LinearMap.add_apply]
    rw [mul_oneₓ]
  have :
    (fun p : Finₓ 2 → ℤ => norm_sq ((p 0 : ℂ) * ↑z + ↑p 1)) = norm_sq ∘ f ∘ fun p : Finₓ 2 → ℤ => (coeₓ : ℤ → ℝ) ∘ p :=
    by
    ext1
    rw [f_def]
    dsimp only [Function.comp]
    rw [of_real_int_cast, of_real_int_cast]
  rw [this]
  have hf : f.ker = ⊥ := by
    let g : ℂ →ₗ[ℝ] Finₓ 2 → ℝ :=
      LinearMap.pi («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")
    suffices ((z : ℂ).im⁻¹ • g).comp f = LinearMap.id by
      exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : ℂ).im ≠ 0 := z.2.ne'
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    dsimp only [g, Pi.smul_apply, LinearMap.pi_apply, smul_eq_mul]
    fin_cases i
    · show (z : ℂ).im⁻¹ * (f c).im = c 0
      rw [f_def, add_im, of_real_mul_im, of_real_im, add_zeroₓ, mul_left_commₓ, inv_mul_cancel hz, mul_oneₓ]
      
    · show (z : ℂ).im⁻¹ * ((z : ℂ) * conj (f c)).im = c 1
      rw [f_def, RingEquiv.map_add, RingEquiv.map_mul, mul_addₓ, mul_left_commₓ, mul_conj, conj_of_real, conj_of_real, ←
        of_real_mul, add_im, of_real_im, zero_addₓ, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [of_real_im, of_real_re, mul_im, zero_addₓ, mul_zero]
      
  have h₁ := (LinearEquiv.closed_embedding_of_injective hf).tendsto_cocompact
  have h₂ : tendsto (fun p : Finₓ 2 → ℤ => (coeₓ : ℤ → ℝ) ∘ p) cofinite (cocompact _) := by
    convert tendsto.pi_map_Coprod fun i => Int.tendsto_coe_cofinite
    · rw [Coprod_cofinite]
      
    · rw [Coprod_cocompact]
      
  exact tendsto_norm_sq_cocompact_at_top.comp (h₁.comp h₂)

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lc_row0 (p : Finₓ 2 → ℤ) : Matrix (Finₓ 2) (Finₓ 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj 0 + (p 1 : ℝ) • LinearMap.proj 1 : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.proj 0)

@[simp]
theorem lc_row0_apply (p : Finₓ 2 → ℤ) (g : Matrix (Finₓ 2) (Finₓ 2) ℝ) : lc_row0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
theorem lc_row0_apply' (a b : ℝ) (c d : ℤ) (v : Finₓ 2 → ℝ) :
    lc_row0 («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")
        («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»") =
      c * a + d * b :=
  by
  simp

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps]
def lc_row0_extend {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Finₓ 2) (Finₓ 2) ℝ ≃ₗ[ℝ] Matrix (Finₓ 2) (Finₓ 2) ℝ :=
  LinearEquiv.piCongrRight
    («expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»")

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
/-- The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.-/
theorem tendsto_lc_row0 {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    tendsto (fun g : { g : SL(2, ℤ) // g 1 = cd } => lc_row0 cd (↑(↑g : SL(2, ℝ)))) cofinite (cocompact ℝ) := by
  let mB : ℝ → Matrix (Finₓ 2) (Finₓ 2) ℝ := fun t =>
    «expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»"
  have hmB : Continuous mB := by
    refine' continuous_pi fun i => _
    fin_cases i
    · refine' continuous_pi fun j => _
      fin_cases j
      · exact continuous_id
        
      · exact @continuous_const _ _ _ _ (-(1 : ℤ) : ℝ)
        
      
    exact @continuous_const _ _ _ _ (coeₓ ∘ cd)
  convert Filter.Tendsto.of_tendsto_comp _ (comap_cocompact hmB)
  let f₁ : SL(2, ℤ) → Matrix (Finₓ 2) (Finₓ 2) ℝ := fun g => Matrix.map (↑g : Matrix _ _ ℤ) (coeₓ : ℤ → ℝ)
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    tendsto (fun m : Matrix (Finₓ 2) (Finₓ 2) ℤ => Matrix.map m (coeₓ : ℤ → ℝ)) cofinite (cocompact _) := by
    convert tendsto.pi_map_Coprod fun i => tendsto.pi_map_Coprod fun j => Int.tendsto_coe_cofinite
    · simp [Coprod_cofinite]
      
    · simp only [Coprod_cocompact]
      rfl
      
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite
  have hf₂ : ClosedEmbedding (lc_row0_extend hcd) :=
    (lc_row0_extend hcd).toContinuousLinearEquiv.toHomeomorph.ClosedEmbedding
  convert hf₂.tendsto_cocompact.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1
  funext g
  obtain ⟨g, hg⟩ := g
  funext j
  fin_cases j
  · ext i
    fin_cases i
    · simp [mB, f₁, Matrix.mulVecₓ, Matrix.dotProduct, Finₓ.sum_univ_succ]
      
    · convert congr_argₓ (fun n : ℤ => (-n : ℝ)) g.det_coe.symm using 1
      simp [f₁, ← hg, Matrix.mulVecₓ, Matrix.dotProduct, Finₓ.sum_univ_succ, Matrix.det_fin_two,
        -special_linear_group.det_coe]
      ring
      
    
  · exact congr_argₓ (fun p => (coeₓ : ℤ → ℝ) ∘ p) hg.symm
    

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:

  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

  which does not need to be decomposed depending on whether `c = 0`. -/
theorem smul_eq_lc_row0_add {p : Finₓ 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) (z : ℍ) {g : SL(2, ℤ)} (hg : ↑ₘg 1 = p) :
    ↑(g • z) =
      (lc_row0 p (↑(g : SL(2, ℝ))) : ℂ) / (p 0 ^ 2 + p 1 ^ 2) +
        ((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
  by
  have nonZ1 : (p 0 : ℂ) ^ 2 + p 1 ^ 2 ≠ 0 := by
    exact_mod_cast hp.sq_add_sq_ne_zero
  have : (coeₓ : ℤ → ℝ) ∘ p ≠ 0 := fun h => hp.ne_zero ((@Int.cast_injective ℝ _ _ _).compLeft h)
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by
    simpa using linear_ne_zero _ z this
  field_simp [nonZ1, nonZ2, denom_ne_zero, -UpperHalfPlane.denom, -denom_apply]
  rw
    [(by
      simp : (p 1 : ℂ) * z - p 0 = (p 1 * z - p 0) * ↑det (↑g : Matrix (Finₓ 2) (Finₓ 2) ℤ))]
  rw [← hg, det_fin_two]
  simp only [Int.coe_cast_ring_hom, coe_matrix_coe, coe_fn_eq_coe, Int.cast_mul, of_real_int_cast, map_apply, denom,
    Int.cast_sub]
  ring

theorem tendsto_abs_re_smul (z : ℍ) {p : Finₓ 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) :
    tendsto (fun g : { g : SL(2, ℤ) // g 1 = p } => |((g : SL(2, ℤ)) • z).re|) cofinite at_top := by
  suffices tendsto (fun g : (fun g : SL(2, ℤ) => g 1) ⁻¹' {p} => ((g : SL(2, ℤ)) • z).re) cofinite (cocompact ℝ) by
    exact tendsto_norm_cocompact_at_top.comp this
  have : ((p 0 : ℝ) ^ 2 + p 1 ^ 2)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRight₀ _ this
  let ff := Homeomorph.addRight (((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re
  convert (f.trans ff).ClosedEmbedding.tendsto_cocompact.comp (tendsto_lc_row0 hp)
  ext g
  change
    ((g : SL(2, ℤ)) • z).re =
      lc_row0 p (↑(↑g : SL(2, ℝ))) / (p 0 ^ 2 + p 1 ^ 2) +
        (((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re
  exact_mod_cast congr_argₓ Complex.re (smul_eq_lc_row0_add hp z g.2)

end TendstoLemmas

section FundamentalDomain

attribute [local simp] coe_smul re_smul

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
theorem exists_max_im (z : ℍ) : ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
  classical
  let s : Set (Finₓ 2 → ℤ) := { cd | IsCoprime (cd 0) (cd 1) }
  have hs : s.nonempty :=
    ⟨«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»",
      is_coprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ := Filter.Tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine' ⟨g, fun g' => _⟩
  rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, div_le_div_left]
  · simpa [← hg] using hp (g' 1) (bottom_row_coprime g')
    
  · exact z.im_pos
    
  · exact norm_sq_denom_pos g' z
    
  · exact norm_sq_denom_pos g z
    

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
theorem exists_row_one_eq_and_min_re (z : ℍ) {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    ∃ g : SL(2, ℤ), ↑ₘg 1 = cd ∧ ∀ g' : SL(2, ℤ), ↑ₘg 1 = ↑ₘg' 1 → |(g • z).re| ≤ |(g' • z).re| := by
  have : Nonempty { g : SL(2, ℤ) // g 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine' ⟨g, g.2, _⟩
  · intro g1 hg1
    have : g1 ∈ (fun g : SL(2, ℤ) => g 1) ⁻¹' {cd} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact Eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2))
    exact hg ⟨g1, this⟩
    

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T : SL(2, ℤ) :=
  ⟨«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»", by
    norm_num [Matrix.det_fin_two]⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- The matrix `T' (= T⁻¹) = [[1,-1],[0,1]]` as an element of `SL(2,ℤ)` -/
def T' : SL(2, ℤ) :=
  ⟨«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»", by
    norm_num [Matrix.det_fin_two]⟩

-- ././Mathport/Syntax/Translate/Basic.lean:705:4: warning: unsupported notation `«expr![ , ]»
-- ././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»
/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/
def S : SL(2, ℤ) :=
  ⟨«expr![ , ]» "././Mathport/Syntax/Translate/Basic.lean:706:61: unsupported notation `«expr![ , ]»", by
    norm_num [Matrix.det_fin_two]⟩

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ` -/
def fundamental_domain : Set ℍ :=
  { z | 1 ≤ Complex.normSq z ∧ |z.re| ≤ (1 : ℝ) / 2 }

localized [Modular] notation "𝒟" => ModularGroup.FundamentalDomain

/-- If `|z|<1`, then applying `S` strictly decreases `im` -/
theorem im_lt_im_S_smul {z : ℍ} (h : norm_sq z < 1) : z.im < (S • z).im := by
  have : z.im < z.im / norm_sq (z : ℂ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff z.norm_sq_pos).mpr
    nlinarith
  convert this
  simp only [im_smul_eq_div_norm_sq]
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]

/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
theorem exists_smul_mem_fundamental_domain (z : ℍ) : ∃ g : SL(2, ℤ), g • z ∈ 𝒟 := by
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine' ⟨g, _⟩
  have hg₀' : ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
    have hg'' : (g • z).im = (g₀ • z).im := by
      rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, denom_apply, denom_apply, hg]
    simpa only [hg''] using hg₀
  constructor
  · contrapose! hg₀'
    refine' ⟨S * g, _⟩
    rw [MulAction.mul_smul]
    exact im_lt_im_S_smul hg₀'
    
  · show |(g • z).re| ≤ 1 / 2
    rw [abs_le]
    constructor
    · contrapose! hg'
      refine'
        ⟨T * g, by
          simp [T, Matrix.mul, Matrix.dotProduct, Finₓ.sum_univ_succ], _⟩
      rw [MulAction.mul_smul]
      have : |(g • z).re + 1| < |(g • z).re| := by
        cases abs_cases ((g • z).re + 1) <;> cases abs_cases (g • z).re <;> linarith
      convert this
      simp [T]
      
    · contrapose! hg'
      refine'
        ⟨T' * g, by
          simp [T', Matrix.mul, Matrix.dotProduct, Finₓ.sum_univ_succ], _⟩
      rw [MulAction.mul_smul]
      have : |(g • z).re - 1| < |(g • z).re| := by
        cases abs_cases ((g • z).re - 1) <;> cases abs_cases (g • z).re <;> linarith
      convert this
      simp [T', sub_eq_add_neg]
      
    

end FundamentalDomain

end ModularGroup

