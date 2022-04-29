/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathbin.Analysis.Complex.UpperHalfPlane
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.Analysis.Matrix

/-!
# The action of the modular group SL(2, ℤ) on the upper half-plane

We define the action of `SL(2,ℤ)` on `ℍ` (via restriction of the `SL(2,ℝ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fd`, `𝒟`) for this action and show
(`modular_group.exists_smul_mem_fd`) that any point in `ℍ` can be
moved inside `𝒟`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟`:
`fd := {z | 1 ≤ (z : ℂ).norm_sq ∧ |z.re| ≤ (1 : ℝ) / 2}`

The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`, denoted `𝒟ᵒ`:
`fdo := {z | 1 < (z : ℂ).norm_sq ∧ |z.re| < (1 : ℝ) / 2}`

These notations are localized in the `modular` locale and can be enabled via `open_locale modular`.

## Main results

Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`:
`exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2,ℤ), g • z ∈ 𝒟`

If both `z` and `γ • z` are in the open domain `𝒟ᵒ` then `z = γ • z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : ℍ} {g : SL(2,ℤ)} (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z`

# Discussion

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


/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

attribute [-instance] Matrix.GeneralLinearGroup.hasCoeToFun

open Complex hiding abs_one abs_two abs_mul abs_add

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane

noncomputable section

-- mathport name: «exprSL( , )»
local notation "SL(" n ", " R ")" => SpecialLinearGroup (Finₓ n) R

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Finₓ 2) (Finₓ 2) ℤ) _

open UpperHalfPlane ComplexConjugate

attribute [local instance] Fintype.card_fin_even

namespace ModularGroup

variable (g : SL(2, ℤ)) (z : ℍ)

section UpperHalfPlaneAction

/-- For a subring `R` of `ℝ`, the action of `SL(2, R)` on the upper half-plane, as a restriction of
the `SL(2, ℝ)`-action defined by `upper_half_plane.mul_action`. -/
instance {R : Type _} [CommRingₓ R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ (map (algebraMap R ℝ))

theorem coe_smul : ↑(g • z) = Num g z / denom g z :=
  rfl

theorem re_smul : (g • z).re = (Num g z / denom g z).re :=
  rfl

@[simp]
theorem smul_coe : (g : SL(2, ℝ)) • z = g • z :=
  rfl

@[simp]
theorem neg_smul : -g • z = g • z :=
  show ↑(-g) • _ = _ by
    simp [neg_smul g z]

theorem im_smul : (g • z).im = (Num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_norm_sq : (g • z).im = z.im / Complex.normSq (denom g z) :=
  im_smul_eq_div_norm_sq g z

@[simp]
theorem denom_apply : denom g z = ↑ₘg 1 0 * z + ↑ₘg 1 1 := by
  simp

end UpperHalfPlaneAction

variable {g}

section BottomRow

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, ℤ)` are coprime. -/
theorem bottom_row_coprime {R : Type _} [CommRingₓ R] (g : SL(2, R)) :
    IsCoprime ((↑g : Matrix (Finₓ 2) (Finₓ 2) R) 1 0) ((↑g : Matrix (Finₓ 2) (Finₓ 2) R) 1 1) := by
  use -(↑g : Matrix (Finₓ 2) (Finₓ 2) R) 0 1, (↑g : Matrix (Finₓ 2) (Finₓ 2) R) 0 0
  rw [add_commₓ, neg_mul, ← sub_eq_add_neg, ← det_fin_two]
  exact g.det_coe

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,ℤ)`. -/
theorem bottom_row_surj {R : Type _} [CommRingₓ R] :
    Set.SurjOn (fun g : SL(2, R) => @coe _ (Matrix (Finₓ 2) (Finₓ 2) R) _ g 1) Set.Univ
      { cd | IsCoprime (cd 0) (cd 1) } :=
  by
  rintro cd ⟨b₀, a, gcd_eqn⟩
  let A := ![![a, -b₀], cd]
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

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
/-- The function `(c,d) → |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_norm_sq_coprime_pair :
    Filter.Tendsto (fun p : Finₓ 2 → ℤ => ((p 0 : ℂ) * z + p 1).normSq) cofinite atTop := by
  let π₀ : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let π₁ : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  let f : (Finₓ 2 → ℝ) →ₗ[ℝ] ℂ := π₀.smul_right (z : ℂ) + π₁.smul_right 1
  have f_def : ⇑f = fun p : Finₓ 2 → ℝ => (p 0 : ℂ) * ↑z + p 1 := by
    ext1
    dsimp only [LinearMap.coe_proj, real_smul, LinearMap.coe_smul_right, LinearMap.add_apply]
    rw [mul_oneₓ]
  have :
    (fun p : Finₓ 2 → ℤ => norm_sq ((p 0 : ℂ) * ↑z + ↑(p 1))) = norm_sq ∘ f ∘ fun p : Finₓ 2 → ℤ => (coe : ℤ → ℝ) ∘ p :=
    by
    ext1
    rw [f_def]
    dsimp only [Function.comp]
    rw [of_real_int_cast, of_real_int_cast]
  rw [this]
  have hf : f.ker = ⊥ := by
    let g : ℂ →ₗ[ℝ] Finₓ 2 → ℝ := LinearMap.pi ![im_lm, im_lm.comp ((z : ℂ) • (conj_ae : ℂ →ₗ[ℝ] ℂ))]
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
      rw [f_def, RingHom.map_add, RingHom.map_mul, mul_addₓ, mul_left_commₓ, mul_conj, conj_of_real, conj_of_real, ←
        of_real_mul, add_im, of_real_im, zero_addₓ, inv_mul_eq_iff_eq_mul₀ hz]
      simp only [of_real_im, of_real_re, mul_im, zero_addₓ, mul_zero]
      
  have h₁ := (LinearEquiv.closed_embedding_of_injective hf).tendsto_cocompact
  have h₂ : tendsto (fun p : Finₓ 2 → ℤ => (coe : ℤ → ℝ) ∘ p) cofinite (cocompact _) := by
    convert tendsto.pi_map_Coprod fun i => Int.tendsto_coe_cofinite
    · rw [Coprod_cofinite]
      
    · rw [Coprod_cocompact]
      
  exact tendsto_norm_sq_cocompact_at_top.comp (h₁.comp h₂)

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Finₓ 2 → ℤ) : Matrix (Finₓ 2) (Finₓ 2) ℝ →ₗ[ℝ] ℝ :=
  ((p 0 : ℝ) • LinearMap.proj 0 + (p 1 : ℝ) • LinearMap.proj 1 : (Finₓ 2 → ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.proj 0)

@[simp]
theorem lc_row0_apply (p : Finₓ 2 → ℤ) (g : Matrix (Finₓ 2) (Finₓ 2) ℝ) : lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [ac₀ + bd₀, - ad₀ + bc₀; c, d], for
some fixed `(c₀, d₀)`. -/
@[simps]
def lcRow0Extend {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Finₓ 2) (Finₓ 2) ℝ ≃ₗ[ℝ] Matrix (Finₓ 2) (Finₓ 2) ℝ :=
  LinearEquiv.piCongrRight
    ![by
      refine'
        LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Finₓ 2 → ℝ)
          (general_linear_group.to_linear (plane_conformal_matrix (cd 0 : ℝ) (-(cd 1 : ℝ)) _))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl ℝ (Finₓ 2 → ℝ)]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
/-- The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.-/
theorem tendsto_lc_row0 {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, ℤ) // ↑ₘg 1 = cd } => lcRow0 cd ↑(↑g : SL(2, ℝ))) cofinite (cocompact ℝ) := by
  let mB : ℝ → Matrix (Finₓ 2) (Finₓ 2) ℝ := fun t => ![![t, (-(1 : ℤ) : ℝ)], coe ∘ cd]
  have hmB : Continuous mB := by
    simp only [continuous_pi_iff, Finₓ.forall_fin_two]
    have : ∀ c : ℝ, Continuous fun x : ℝ => c := fun c => continuous_const
    exact ⟨⟨continuous_id, @this (-1 : ℤ)⟩, ⟨this (cd 0), this (cd 1)⟩⟩
  refine' Filter.Tendsto.of_tendsto_comp _ (comap_cocompact hmB)
  let f₁ : SL(2, ℤ) → Matrix (Finₓ 2) (Finₓ 2) ℝ := fun g => Matrix.map (↑g : Matrix _ _ ℤ) (coe : ℤ → ℝ)
  have cocompact_ℝ_to_cofinite_ℤ_matrix :
    tendsto (fun m : Matrix (Finₓ 2) (Finₓ 2) ℤ => Matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact _) := by
    simpa only [Coprod_cofinite, Coprod_cocompact] using
      tendsto.pi_map_Coprod fun i : Finₓ 2 => tendsto.pi_map_Coprod fun j : Finₓ 2 => Int.tendsto_coe_cofinite
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite
  have hf₂ : ClosedEmbedding (lc_row0_extend hcd) :=
    (lc_row0_extend hcd).toContinuousLinearEquiv.toHomeomorph.ClosedEmbedding
  convert hf₂.tendsto_cocompact.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1
  ext ⟨g, rfl⟩ i j : 3
  fin_cases i <;> [fin_cases j, skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  · simp only [mB, mul_vec, dot_product, Finₓ.sum_univ_two, _root_.coe_coe, coe_matrix_coe, Int.coe_cast_ring_hom,
      lc_row0_apply, Function.comp_app, cons_val_zero, lc_row0_extend_apply,
      LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv, general_linear_group.to_linear_apply,
      coe_plane_conformal_matrix, neg_negₓ, mul_vec_lin_apply, cons_val_one, head_cons]
    
  · convert congr_argₓ (fun n : ℤ => (-n : ℝ)) g.det_coe.symm using 1
    simp only [f₁, mul_vec, dot_product, Finₓ.sum_univ_two, Matrix.det_fin_two, Function.comp_app, Subtype.coe_mk,
      lc_row0_extend_apply, cons_val_zero, LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, mul_vec_lin_apply, cons_val_one, head_cons,
      map_apply, neg_mul, Int.cast_sub, Int.cast_mul, neg_sub]
    ring
    
  · rfl
    

/-- This replaces `(g•z).re = a/c + *` in the standard theory with the following novel identity:

  `g • z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

  which does not need to be decomposed depending on whether `c = 0`. -/
theorem smul_eq_lc_row0_add {p : Finₓ 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) (hg : ↑ₘg 1 = p) :
    ↑(g • z) =
      (lcRow0 p ↑(g : SL(2, ℝ)) : ℂ) / (p 0 ^ 2 + p 1 ^ 2) +
        ((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
  by
  have nonZ1 : (p 0 : ℂ) ^ 2 + p 1 ^ 2 ≠ 0 := by
    exact_mod_cast hp.sq_add_sq_ne_zero
  have : (coe : ℤ → ℝ) ∘ p ≠ 0 := fun h => hp.ne_zero ((@Int.cast_injective ℝ _ _ _).compLeft h)
  have nonZ2 : (p 0 : ℂ) * z + p 1 ≠ 0 := by
    simpa using linear_ne_zero _ z this
  field_simp [nonZ1, nonZ2, denom_ne_zero, -UpperHalfPlane.denom, -denom_apply]
  rw
    [(by
      simp : (p 1 : ℂ) * z - p 0 = (p 1 * z - p 0) * ↑(det (↑g : Matrix (Finₓ 2) (Finₓ 2) ℤ)))]
  rw [← hg, det_fin_two]
  simp only [Int.coe_cast_ring_hom, coe_matrix_coe, coe_fn_eq_coe, Int.cast_mul, of_real_int_cast, map_apply, denom,
    Int.cast_sub]
  ring

theorem tendsto_abs_re_smul {p : Finₓ 2 → ℤ} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto (fun g : { g : SL(2, ℤ) // ↑ₘg 1 = p } => abs ((g : SL(2, ℤ)) • z).re) cofinite atTop := by
  suffices tendsto (fun g : (fun g : SL(2, ℤ) => ↑ₘg 1) ⁻¹' {p} => ((g : SL(2, ℤ)) • z).re) cofinite (cocompact ℝ) by
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
      lc_row0 p ↑(↑g : SL(2, ℝ)) / (p 0 ^ 2 + p 1 ^ 2) +
        (((p 1 : ℂ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re
  exact_mod_cast congr_argₓ Complex.re (smul_eq_lc_row0_add z hp g.2)

end TendstoLemmas

section FundamentalDomain

attribute [local simp] coe_smul re_smul

/-- For `z : ℍ`, there is a `g : SL(2,ℤ)` maximizing `(g•z).im` -/
theorem exists_max_im : ∃ g : SL(2, ℤ), ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
  classical
  let s : Set (Finₓ 2 → ℤ) := { cd | IsCoprime (cd 0) (cd 1) }
  have hs : s.nonempty := ⟨![1, 1], is_coprime_one_left⟩
  obtain ⟨p, hp_coprime, hp⟩ := Filter.Tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z)
  obtain ⟨g, -, hg⟩ := bottom_row_surj hp_coprime
  refine' ⟨g, fun g' => _⟩
  rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, div_le_div_left]
  · simpa [← hg] using hp (↑ₘg' 1) (bottom_row_coprime g')
    
  · exact z.im_pos
    
  · exact norm_sq_denom_pos g' z
    
  · exact norm_sq_denom_pos g z
    

/-- Given `z : ℍ` and a bottom row `(c,d)`, among the `g : SL(2,ℤ)` with this bottom row, minimize
  `|(g•z).re|`.  -/
theorem exists_row_one_eq_and_min_re {cd : Finₓ 2 → ℤ} (hcd : IsCoprime (cd 0) (cd 1)) :
    ∃ g : SL(2, ℤ), ↑ₘg 1 = cd ∧ ∀ g' : SL(2, ℤ), ↑ₘg 1 = ↑ₘg' 1 → abs (g • z).re ≤ abs (g' • z).re := by
  have : Nonempty { g : SL(2, ℤ) // ↑ₘg 1 = cd } :=
    let ⟨x, hx⟩ := bottom_row_surj hcd
    ⟨⟨x, hx.2⟩⟩
  obtain ⟨g, hg⟩ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine' ⟨g, g.2, _⟩
  · intro g1 hg1
    have : g1 ∈ (fun g : SL(2, ℤ) => ↑ₘg 1) ⁻¹' {cd} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact Eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2))
    exact hg ⟨g1, this⟩
    

/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,ℤ)` -/
def t : SL(2, ℤ) :=
  ⟨![![1, 1], ![0, 1]], by
    norm_num [Matrix.det_fin_two]⟩

/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,ℤ)` -/
def s : SL(2, ℤ) :=
  ⟨![![0, -1], ![1, 0]], by
    norm_num [Matrix.det_fin_two]⟩

theorem coe_S : ↑ₘS = ![![0, -1], ![1, 0]] :=
  rfl

theorem coe_T : ↑ₘT = ![![1, 1], ![0, 1]] :=
  rfl

theorem coe_T_inv : ↑ₘT⁻¹ = ![![1, -1], ![0, 1]] := by
  simp [coe_inv, coe_T, adjugate_fin_two]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem coe_T_zpow (n : ℤ) : ↑ₘ(T ^ n) = ![![1, n], ![0, 1]] := by
  induction' n using Int.induction_on with n h n h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    
  · rw [zpow_add, zpow_one, coe_mul, h, coe_T]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Finₓ.sum_univ_succ, add_commₓ (1 : ℤ)]
    
  · rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Finₓ.sum_univ_succ, neg_add_eq_sub (1 : ℤ)]
    

variable {z}

@[simp]
theorem coe_T_zpow_smul_eq {n : ℤ} : (↑(T ^ n • z) : ℂ) = z + n := by
  simp [coe_T_zpow]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- If instead we had `g` and `T` of type `PSL(2, ℤ)`, then we could simply state `g = T^n`.
theorem exists_eq_T_zpow_of_c_eq_zero (hc : ↑ₘg 1 0 = 0) : ∃ n : ℤ, ∀ z : ℍ, g • z = T ^ n • z := by
  have had := g.det_coe
  replace had : ↑ₘg 0 0 * ↑ₘg 1 1 = 1
  · rw [det_fin_two, hc] at had
    linarith
    
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · use ↑ₘg 0 1
    suffices g = T ^ ↑ₘg 0 1 by
      intro z
      conv_lhs => rw [this]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, coe_T_zpow]
    
  · use -↑ₘg 0 1
    suffices g = -(T ^ -↑ₘg 0 1) by
      intro z
      conv_lhs => rw [this, neg_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hc, hd, coe_T_zpow]
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
theorem g_eq_of_c_eq_one (hc : ↑ₘg 1 0 = 1) : g = T ^ ↑ₘg 0 0 * S * T ^ ↑ₘg 1 1 := by
  have hg := g.det_coe.symm
  replace hg : ↑ₘg 0 1 = ↑ₘg 0 0 * ↑ₘg 1 1 - 1
  · rw [det_fin_two, hc] at hg
    linarith
    
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_S, coe_T_zpow, Matrix.mul_apply, Finₓ.sum_univ_succ, hg, hc]

/-- If `1 < |z|`, then `|S • z| < 1`. -/
theorem norm_sq_S_smul_lt_one (h : 1 < normSq z) : normSq ↑(S • z) < 1 := by
  simpa [coe_S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S • z).im := by
  have : z.im < z.im / norm_sq (z : ℂ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff z.norm_sq_pos).mpr
    nlinarith
  convert this
  simp only [im_smul_eq_div_norm_sq]
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]

/-- The standard (closed) fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def Fd : Set ℍ :=
  { z | 1 ≤ (z : ℂ).normSq ∧ abs z.re ≤ (1 : ℝ) / 2 }

/-- The standard open fundamental domain of the action of `SL(2,ℤ)` on `ℍ`. -/
def Fdo : Set ℍ :=
  { z | 1 < (z : ℂ).normSq ∧ abs z.re < (1 : ℝ) / 2 }

-- mathport name: «expr𝒟»
localized [Modular] notation "𝒟" => ModularGroup.Fd

-- mathport name: «expr𝒟ᵒ»
localized [Modular] notation "𝒟ᵒ" => ModularGroup.Fdo

theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z ∈ 𝒟ᵒ) : abs (2 * z.re) < 1 := by
  rw [abs_mul, abs_two, ← lt_div_iff' (@two_pos ℝ _ _)]
  exact h.2

theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z ∈ 𝒟ᵒ) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by
    simpa [Complex.norm_sq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

/-- If `z ∈ 𝒟ᵒ`, and `n : ℤ`, then `|z + n| > 1`. -/
theorem one_lt_norm_sq_T_zpow_smul (hz : z ∈ 𝒟ᵒ) (n : ℤ) : 1 < normSq (T ^ n • z : ℍ) := by
  have hz₁ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + ↑n) * (z.re + ↑n) + z.im * z.im := by
    linarith
  simpa [coe_T_zpow, norm_sq]

theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : ℤ} (hz : z ∈ 𝒟ᵒ) (hg : T ^ n • z ∈ 𝒟ᵒ) : n = 0 := by
  suffices abs (n : ℝ) < 1 by
    rwa [← Int.cast_abs, ← Int.cast_oneₓ, Int.cast_lt, Int.abs_lt_one_iff] at this
  have h₁ := hz.2
  have h₂ := hg.2
  rw [← coe_re, coe_T_zpow_smul_eq, add_re, int_cast_re, coe_re] at h₂
  calc abs (n : ℝ) ≤ abs z.re + abs (z.re + (n : ℝ)) := abs_add' (n : ℝ) z.re _ < 1 / 2 + 1 / 2 :=
      add_lt_add h₁ h₂ _ = 1 := add_halves 1

/-- Any `z : ℍ` can be moved to `𝒟` by an element of `SL(2,ℤ)`  -/
theorem exists_smul_mem_fd (z : ℍ) : ∃ g : SL(2, ℤ), g • z ∈ 𝒟 := by
  -- obtain a g₀ which maximizes im (g • z),
  obtain ⟨g₀, hg₀⟩ := exists_max_im z
  -- then among those, minimize re
  obtain ⟨g, hg, hg'⟩ := exists_row_one_eq_and_min_re z (bottom_row_coprime g₀)
  refine' ⟨g, _⟩
  -- `g` has same max im property as `g₀`
  have hg₀' : ∀ g' : SL(2, ℤ), (g' • z).im ≤ (g • z).im := by
    have hg'' : (g • z).im = (g₀ • z).im := by
      rw [im_smul_eq_div_norm_sq, im_smul_eq_div_norm_sq, denom_apply, denom_apply, hg]
    simpa only [hg''] using hg₀
  constructor
  · -- Claim: `1 ≤ ⇑norm_sq ↑(g • z)`. If not, then `S•g•z` has larger imaginary part
    contrapose! hg₀'
    refine' ⟨S * g, _⟩
    rw [MulAction.mul_smul]
    exact im_lt_im_S_smul hg₀'
    
  · show abs (g • z).re ≤ 1 / 2
    -- if not, then either `T` or `T'` decrease |Re|.
    rw [abs_le]
    constructor
    · contrapose! hg'
      refine'
        ⟨T * g, by
          simp [T, Matrix.mul, Matrix.dotProduct, Finₓ.sum_univ_succ], _⟩
      rw [MulAction.mul_smul]
      have : abs ((g • z).re + 1) < abs (g • z).re := by
        cases abs_cases ((g • z).re + 1) <;> cases abs_cases (g • z).re <;> linarith
      convert this
      simp [T]
      
    · contrapose! hg'
      refine'
        ⟨T⁻¹ * g, by
          simp [coe_T_inv, Matrix.mul, Matrix.dotProduct, Finₓ.sum_univ_succ], _⟩
      rw [MulAction.mul_smul]
      have : abs ((g • z).re - 1) < abs (g • z).re := by
        cases abs_cases ((g • z).re - 1) <;> cases abs_cases (g • z).re <;> linarith
      convert this
      simp [coe_T_inv, sub_eq_add_neg]
      
    

section UniqueRepresentative

variable {z}

/-- An auxiliary result en route to `modular_group.c_eq_zero`. -/
theorem abs_c_le_one (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : abs (↑ₘg 1 0) ≤ 1 := by
  let c' : ℤ := ↑ₘg 1 0
  let c : ℝ := (c' : ℝ)
  suffices 3 * c ^ 2 < 4 by
    rw [← Int.cast_pow, ← Int.cast_three, ← Int.cast_four, ← Int.cast_mul, Int.cast_lt] at this
    replace this : c' ^ 2 ≤ 1 ^ 2
    · linarith
      
    rw [← abs_one]
    exact abs_le_abs_of_sq_le_sq this
  suffices c ≠ 0 → 9 * c ^ 4 < 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    · rw [hc]
      norm_num
      
    · refine'
        (abs_lt_of_sq_lt_sq' _
            (by
              norm_num)).2
      specialize this hc
      linarith
      
  intro hc
  replace hc : 0 < c ^ 4
  · rw [pow_bit0_pos_iff] <;> trivial
    
  have h₁ :=
    mul_lt_mul_of_pos_right
      (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg) (three_lt_four_mul_im_sq_of_mem_fdo hz)
        (by
          linarith)
        (by
          linarith))
      hc
  have h₂ : (c * z.im) ^ 4 / norm_sq (denom (↑g) z) ^ 2 ≤ 1 :=
    div_le_one_of_le (pow_four_le_pow_two_of_pow_two_le (UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom z g)) (sq_nonneg _)
  let nsq := norm_sq (denom g z)
  calc 9 * c ^ 4 < c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by
      linarith _ = c ^ 4 * z.im ^ 4 / nsq ^ 2 * 16 := by
      rw [im_smul_eq_div_norm_sq, div_pow]
      ring _ ≤ 16 := by
      rw [← mul_powₓ]
      linarith

/-- An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/
theorem c_eq_zero (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : ↑ₘg 1 0 = 0 := by
  have hp : ∀ {g' : SL(2, ℤ)} hg' : g' • z ∈ 𝒟ᵒ, ↑ₘg' 1 0 ≠ 1 := by
    intros
    by_contra hc
    let a := ↑ₘg' 0 0
    let d := ↑ₘg' 1 1
    have had : T ^ -a * g' = S * T ^ d := by
      rw [g_eq_of_c_eq_one hc]
      group
    let w := T ^ -a • g' • z
    have h₁ : w = S • T ^ d • z := by
      simp only [w, ← mul_smul, had]
    replace h₁ : norm_sq w < 1 := h₁.symm ▸ norm_sq_S_smul_lt_one (one_lt_norm_sq_T_zpow_smul hz d)
    have h₂ : 1 < norm_sq w := one_lt_norm_sq_T_zpow_smul hg' (-a)
    linarith
  have hn : ↑ₘg 1 0 ≠ -1 := by
    intro hc
    replace hc : ↑ₘ(-g) 1 0 = 1
    · simp [eq_neg_of_eq_neg hc]
      
    replace hg : -g • z ∈ 𝒟ᵒ := (neg_smul g z).symm ▸ hg
    exact hp hg hc
  specialize hp hg
  rcases int.abs_le_one_iff.mp <| abs_c_le_one hz hg with ⟨⟩ <;> tauto

/-- Second Main Fundamental Domain Lemma: if both `z` and `g • z` are in the open domain `𝒟ᵒ`,
where `z : ℍ` and `g : SL(2,ℤ)`, then `z = g • z`. -/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg)
  rw [hn] at hg⊢
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg]

end UniqueRepresentative

end FundamentalDomain

end ModularGroup

