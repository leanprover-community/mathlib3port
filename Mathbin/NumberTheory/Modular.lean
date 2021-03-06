/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.Analysis.Matrix

/-!
# The action of the modular group SL(2, โค) on the upper half-plane

We define the action of `SL(2,โค)` on `โ` (via restriction of the `SL(2,โ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fd`, `๐`) for this action and show
(`modular_group.exists_smul_mem_fd`) that any point in `โ` can be
moved inside `๐`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,โค)` on `โ`, denoted `๐`:
`fd := {z | 1 โค (z : โ).norm_sq โง |z.re| โค (1 : โ) / 2}`

The standard open fundamental domain of the action of `SL(2,โค)` on `โ`, denoted `๐แต`:
`fdo := {z | 1 < (z : โ).norm_sq โง |z.re| < (1 : โ) / 2}`

These notations are localized in the `modular` locale and can be enabled via `open_locale modular`.

## Main results

Any `z : โ` can be moved to `๐` by an element of `SL(2,โค)`:
`exists_smul_mem_fd (z : โ) : โ g : SL(2,โค), g โข z โ ๐`

If both `z` and `ฮณ โข z` are in the open domain `๐แต` then `z = ฮณ โข z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : โ} {g : SL(2,โค)} (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : z = g โข z`

# Discussion

Standard proofs make use of the identity

`g โข z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`modular_group.smul_eq_lc_row0_add`):

`g โข z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(gโขz).im` (see `modular_group.exists_max_im`), and then among
those, to minimize `|(gโขz).re|` (see `modular_group.exists_row_one_eq_and_min_re`).
-/


/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToFun

attribute [-instance] Matrix.GeneralLinearGroup.hasCoeToFun

open Complex hiding abs_one abs_two abs_mul abs_add

open Matrix hiding mul_smul

open Matrix.SpecialLinearGroup UpperHalfPlane

noncomputable section

-- mathport name: ยซexprSL( , )ยป
local notation "SL(" n ", " R ")" => SpecialLinearGroup (Finโ n) R

-- mathport name: ยซexprโโ ยป
local prefix:1024 "โโ" => @coe _ (Matrix (Finโ 2) (Finโ 2) โค) _

open UpperHalfPlane ComplexConjugate

attribute [local instance] Fintype.card_fin_even

namespace ModularGroup

variable {g : SL(2, โค)} (z : โ)

section BottomRow

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, โค)` are coprime. -/
theorem bottom_row_coprime {R : Type _} [CommRingโ R] (g : SL(2, R)) :
    IsCoprime ((โg : Matrix (Finโ 2) (Finโ 2) R) 1 0) ((โg : Matrix (Finโ 2) (Finโ 2) R) 1 1) := by
  use -(โg : Matrix (Finโ 2) (Finโ 2) R) 0 1, (โg : Matrix (Finโ 2) (Finโ 2) R) 0 0
  rw [add_commโ, neg_mul, โ sub_eq_add_neg, โ det_fin_two]
  exact g.det_coe

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,โค)`. -/
theorem bottom_row_surj {R : Type _} [CommRingโ R] :
    Set.SurjOn (fun g : SL(2, R) => @coe _ (Matrix (Finโ 2) (Finโ 2) R) _ g 1) Set.Univ
      { cd | IsCoprime (cd 0) (cd 1) } :=
  by
  rintro cd โจbโ, a, gcd_eqnโฉ
  let A := of ![![a, -bโ], cd]
  have det_A_1 : det A = 1 := by
    convert gcd_eqn
    simp [โ A, โ det_fin_two, โ
      (by
        ring : a * cd 1 + bโ * cd 0 = bโ * cd 0 + a * cd 1)]
  refine' โจโจA, det_A_1โฉ, Set.mem_univ _, _โฉ
  ext <;> simp [โ A]

end BottomRow

section TendstoLemmas

open Filter ContinuousLinearMap

attribute [local instance] Matrix.normedGroup Matrix.normedSpace

attribute [local simp] coe_smul

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The function `(c,d) โ |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
theorem tendsto_norm_sq_coprime_pair :
    Filter.Tendsto (fun p : Finโ 2 โ โค => ((p 0 : โ) * z + p 1).normSq) cofinite atTop := by
  let ฯโ : (Finโ 2 โ โ) โโ[โ] โ := LinearMap.proj 0
  let ฯโ : (Finโ 2 โ โ) โโ[โ] โ := LinearMap.proj 1
  let f : (Finโ 2 โ โ) โโ[โ] โ := ฯโ.smul_right (z : โ) + ฯโ.smul_right 1
  have f_def : โf = fun p : Finโ 2 โ โ => (p 0 : โ) * โz + p 1 := by
    ext1
    dsimp' only [โ LinearMap.coe_proj, โ real_smul, โ LinearMap.coe_smul_right, โ LinearMap.add_apply]
    rw [mul_oneโ]
  have :
    (fun p : Finโ 2 โ โค => norm_sq ((p 0 : โ) * โz + โ(p 1))) = norm_sq โ f โ fun p : Finโ 2 โ โค => (coe : โค โ โ) โ p :=
    by
    ext1
    rw [f_def]
    dsimp' only [โ Function.comp]
    rw [of_real_int_cast, of_real_int_cast]
  rw [this]
  have hf : f.ker = โฅ := by
    let g : โ โโ[โ] Finโ 2 โ โ := LinearMap.pi ![im_lm, im_lm.comp ((z : โ) โข (conj_ae : โ โโ[โ] โ))]
    suffices ((z : โ).imโปยน โข g).comp f = LinearMap.id by
      exact LinearMap.ker_eq_bot_of_inverse this
    apply LinearMap.ext
    intro c
    have hz : (z : โ).im โ? 0 := z.2.ne'
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    ext i
    dsimp' only [โ g, โ Pi.smul_apply, โ LinearMap.pi_apply, โ smul_eq_mul]
    fin_cases i
    ยท show (z : โ).imโปยน * (f c).im = c 0
      rw [f_def, add_im, of_real_mul_im, of_real_im, add_zeroโ, mul_left_commโ, inv_mul_cancel hz, mul_oneโ]
      
    ยท show (z : โ).imโปยน * ((z : โ) * conj (f c)).im = c 1
      rw [f_def, RingHom.map_add, RingHom.map_mul, mul_addโ, mul_left_commโ, mul_conj, conj_of_real, conj_of_real, โ
        of_real_mul, add_im, of_real_im, zero_addโ, inv_mul_eq_iff_eq_mulโ hz]
      simp only [โ of_real_im, โ of_real_re, โ mul_im, โ zero_addโ, โ mul_zero]
      
  have hโ := (LinearEquiv.closed_embedding_of_injective hf).tendsto_cocompact
  have hโ : tendsto (fun p : Finโ 2 โ โค => (coe : โค โ โ) โ p) cofinite (cocompact _) := by
    convert tendsto.pi_map_Coprod fun i => Int.tendsto_coe_cofinite
    ยท rw [Coprod_cofinite]
      
    ยท rw [Coprod_cocompact]
      
  exact tendsto_norm_sq_cocompact_at_top.comp (hโ.comp hโ)

/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lcRow0 (p : Finโ 2 โ โค) : Matrix (Finโ 2) (Finโ 2) โ โโ[โ] โ :=
  ((p 0 : โ) โข LinearMap.proj 0 + (p 1 : โ) โข LinearMap.proj 1 : (Finโ 2 โ โ) โโ[โ] โ).comp (LinearMap.proj 0)

@[simp]
theorem lc_row0_apply (p : Finโ 2 โ โค) (g : Matrix (Finโ 2) (Finโ 2) โ) : lcRow0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
  rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [acโ + bdโ, - adโ + bcโ; c, d], for
some fixed `(cโ, dโ)`. -/
@[simps]
def lcRow0Extend {cd : Finโ 2 โ โค} (hcd : IsCoprime (cd 0) (cd 1)) :
    Matrix (Finโ 2) (Finโ 2) โ โโ[โ] Matrix (Finโ 2) (Finโ 2) โ :=
  LinearEquiv.piCongrRight
    ![by
      refine'
        LinearMap.GeneralLinearGroup.generalLinearEquiv โ (Finโ 2 โ โ)
          (general_linear_group.to_linear (plane_conformal_matrix (cd 0 : โ) (-(cd 1 : โ)) _))
      norm_cast
      rw [neg_sq]
      exact hcd.sq_add_sq_ne_zero, LinearEquiv.refl โ (Finโ 2 โ โ)]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.-/
theorem tendsto_lc_row0 {cd : Finโ 2 โ โค} (hcd : IsCoprime (cd 0) (cd 1)) :
    Tendsto (fun g : { g : SL(2, โค) // โโg 1 = cd } => lcRow0 cd โ(โg : SL(2, โ))) cofinite (cocompact โ) := by
  let mB : โ โ Matrix (Finโ 2) (Finโ 2) โ := fun t => of ![![t, (-(1 : โค) : โ)], coe โ cd]
  have hmB : Continuous mB := by
    refine' continuous_matrix _
    simp only [โ Finโ.forall_fin_two, โ mB, โ continuous_const, โ continuous_id', โ of_apply, โ cons_val_zero, โ
      cons_val_one, โ and_selfโ]
  refine' Filter.Tendsto.of_tendsto_comp _ (comap_cocompact_le hmB)
  let fโ : SL(2, โค) โ Matrix (Finโ 2) (Finโ 2) โ := fun g => Matrix.map (โg : Matrix _ _ โค) (coe : โค โ โ)
  have cocompact_โ_to_cofinite_โค_matrix :
    tendsto (fun m : Matrix (Finโ 2) (Finโ 2) โค => Matrix.map m (coe : โค โ โ)) cofinite (cocompact _) := by
    simpa only [โ Coprod_cofinite, โ Coprod_cocompact] using
      tendsto.pi_map_Coprod fun i : Finโ 2 => tendsto.pi_map_Coprod fun j : Finโ 2 => Int.tendsto_coe_cofinite
  have hfโ : tendsto fโ cofinite (cocompact _) :=
    cocompact_โ_to_cofinite_โค_matrix.comp subtype.coe_injective.tendsto_cofinite
  have hfโ : ClosedEmbedding (lc_row0_extend hcd) :=
    (lc_row0_extend hcd).toContinuousLinearEquiv.toHomeomorph.ClosedEmbedding
  convert hfโ.tendsto_cocompact.comp (hfโ.comp subtype.coe_injective.tendsto_cofinite) using 1
  ext โจg, rflโฉ i j : 3
  fin_cases i <;> [fin_cases j, skip]
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  ยท simp only [โ mB, โ mul_vec, โ dot_product, โ Finโ.sum_univ_two, โ _root_.coe_coe, โ coe_matrix_coe, โ
      Int.coe_cast_ring_hom, โ lc_row0_apply, โ Function.comp_app, โ cons_val_zero, โ lc_row0_extend_apply, โ
      LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv, โ general_linear_group.to_linear_apply, โ
      coe_plane_conformal_matrix, โ neg_negโ, โ mul_vec_lin_apply, โ cons_val_one, โ head_cons, โ of_apply]
    
  ยท convert congr_arg (fun n : โค => (-n : โ)) g.det_coe.symm using 1
    simp only [โ fโ, โ mul_vec, โ dot_product, โ Finโ.sum_univ_two, โ Matrix.det_fin_two, โ Function.comp_app, โ
      Subtype.coe_mk, โ lc_row0_extend_apply, โ cons_val_zero, โ
      LinearMap.GeneralLinearGroup.coe_fn_general_linear_equiv, โ general_linear_group.to_linear_apply, โ
      coe_plane_conformal_matrix, โ mul_vec_lin_apply, โ cons_val_one, โ head_cons, โ map_apply, โ neg_mul, โ
      Int.cast_sub, โ Int.cast_mul, โ neg_sub, โ of_apply]
    ring
    
  ยท rfl
    

/-- This replaces `(gโขz).re = a/c + *` in the standard theory with the following novel identity:
  `g โข z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
theorem smul_eq_lc_row0_add {p : Finโ 2 โ โค} (hp : IsCoprime (p 0) (p 1)) (hg : โโg 1 = p) :
    โ(g โข z) =
      (lcRow0 p โ(g : SL(2, โ)) : โ) / (p 0 ^ 2 + p 1 ^ 2) +
        ((p 1 : โ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
  by
  have nonZ1 : (p 0 : โ) ^ 2 + p 1 ^ 2 โ? 0 := by
    exact_mod_cast hp.sq_add_sq_ne_zero
  have : (coe : โค โ โ) โ p โ? 0 := fun h =>
    hp.ne_zero
      (by
        ext i <;> simpa using congr_fun h i)
  have nonZ2 : (p 0 : โ) * z + p 1 โ? 0 := by
    simpa using linear_ne_zero _ z this
  field_simp [โ nonZ1, โ nonZ2, โ denom_ne_zero, -UpperHalfPlane.denom, -denom_apply]
  rw
    [(by
      simp : (p 1 : โ) * z - p 0 = (p 1 * z - p 0) * โ(det (โg : Matrix (Finโ 2) (Finโ 2) โค)))]
  rw [โ hg, det_fin_two]
  simp only [โ Int.coe_cast_ring_hom, โ coe_matrix_coe, โ Int.cast_mul, โ of_real_int_cast, โ map_apply, โ denom, โ
    Int.cast_sub, โ _root_.coe_coe, โ coe_GL_pos_coe_GL_coe_matrix]
  ring

theorem tendsto_abs_re_smul {p : Finโ 2 โ โค} (hp : IsCoprime (p 0) (p 1)) :
    Tendsto (fun g : { g : SL(2, โค) // โโg 1 = p } => abs ((g : SL(2, โค)) โข z).re) cofinite atTop := by
  suffices tendsto (fun g : (fun g : SL(2, โค) => โโg 1) โปยน' {p} => ((g : SL(2, โค)) โข z).re) cofinite (cocompact โ) by
    exact tendsto_norm_cocompact_at_top.comp this
  have : ((p 0 : โ) ^ 2 + p 1 ^ 2)โปยน โ? 0 := by
    apply inv_ne_zero
    exact_mod_cast hp.sq_add_sq_ne_zero
  let f := Homeomorph.mulRightโ _ this
  let ff := Homeomorph.addRight (((p 1 : โ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re
  convert (f.trans ff).ClosedEmbedding.tendsto_cocompact.comp (tendsto_lc_row0 hp)
  ext g
  change
    ((g : SL(2, โค)) โข z).re =
      lc_row0 p โ(โg : SL(2, โ)) / (p 0 ^ 2 + p 1 ^ 2) +
        (((p 1 : โ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re
  exact_mod_cast congr_arg Complex.re (smul_eq_lc_row0_add z hp g.2)

end TendstoLemmas

section FundamentalDomain

attribute [local simp] coe_smul re_smul

/-- For `z : โ`, there is a `g : SL(2,โค)` maximizing `(gโขz).im` -/
theorem exists_max_im : โ g : SL(2, โค), โ g' : SL(2, โค), (g' โข z).im โค (g โข z).im := by
  classical
  let s : Set (Finโ 2 โ โค) := { cd | IsCoprime (cd 0) (cd 1) }
  have hs : s.nonempty := โจ![1, 1], is_coprime_one_leftโฉ
  obtain โจp, hp_coprime, hpโฉ := Filter.Tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z)
  obtain โจg, -, hgโฉ := bottom_row_surj hp_coprime
  refine' โจg, fun g' => _โฉ
  rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq, div_le_div_left]
  ยท simpa [hg] using hp (โโg' 1) (bottom_row_coprime g')
    
  ยท exact z.im_pos
    
  ยท exact norm_sq_denom_pos g' z
    
  ยท exact norm_sq_denom_pos g z
    

/-- Given `z : โ` and a bottom row `(c,d)`, among the `g : SL(2,โค)` with this bottom row, minimize
  `|(gโขz).re|`.  -/
theorem exists_row_one_eq_and_min_re {cd : Finโ 2 โ โค} (hcd : IsCoprime (cd 0) (cd 1)) :
    โ g : SL(2, โค), โโg 1 = cd โง โ g' : SL(2, โค), โโg 1 = โโg' 1 โ abs (g โข z).re โค abs (g' โข z).re := by
  have : Nonempty { g : SL(2, โค) // โโg 1 = cd } :=
    let โจx, hxโฉ := bottom_row_surj hcd
    โจโจx, hx.2โฉโฉ
  obtain โจg, hgโฉ := Filter.Tendsto.exists_forall_le (tendsto_abs_re_smul z hcd)
  refine' โจg, g.2, _โฉ
  ยท intro g1 hg1
    have : g1 โ (fun g : SL(2, โค) => โโg 1) โปยน' {cd} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact Eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2))
    exact hg โจg1, thisโฉ
    

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,โค)` -/
def t : SL(2, โค) :=
  โจยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation", by
    norm_num [โ Matrix.det_fin_two_of]โฉ

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,โค)` -/
def s : SL(2, โค) :=
  โจยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation", by
    norm_num [โ Matrix.det_fin_two_of]โฉ

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem coe_S :
    โโS = ยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem coe_T :
    โโT = ยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem coe_T_inv :
    โโTโปยน =
      ยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  simp [โ coe_inv, โ coe_T, โ adjugate_fin_two]

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]]
-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]]
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `ยซexpr!![ ยป
-- ./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation
theorem coe_T_zpow (n : โค) :
    โโ(T ^ n) =
      ยซexpr!![ ยป "./././Mathport/Syntax/Translate/Basic.lean:1144:14: unsupported user notation matrix.notation" :=
  by
  induction' n using Int.induction_on with n h n h
  ยท rw [zpow_zero, coe_one, Matrix.one_fin_two]
    
  ยท simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    trace
      "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
    rw [mul_oneโ, mul_oneโ, add_commโ]
    
  ยท simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    trace
        "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]" <;>
      ring
    

@[simp]
theorem T_pow_mul_apply_one (n : โค) (g : SL(2, โค)) : โโ(T ^ n * g) 1 = โโg 1 := by
  simp [โ coe_T_zpow, โ Matrix.mul, โ Matrix.dotProduct, โ Finโ.sum_univ_succ]

@[simp]
theorem T_mul_apply_one (g : SL(2, โค)) : โโ(T * g) 1 = โโg 1 := by
  simpa using T_pow_mul_apply_one 1 g

@[simp]
theorem T_inv_mul_apply_one (g : SL(2, โค)) : โโ(Tโปยน * g) 1 = โโg 1 := by
  simpa using T_pow_mul_apply_one (-1) g

theorem coe_T_zpow_smul_eq {n : โค} : (โ(T ^ n โข z) : โ) = z + n := by
  simp [โ coe_T_zpow]

theorem re_T_zpow_smul (n : โค) : (T ^ n โข z).re = z.re + n := by
  rw [โ coe_re, coe_T_zpow_smul_eq, add_re, int_cast_re, coe_re]

theorem im_T_zpow_smul (n : โค) : (T ^ n โข z).im = z.im := by
  rw [โ coe_im, coe_T_zpow_smul_eq, add_im, int_cast_im, add_zeroโ, coe_im]

theorem re_T_smul : (T โข z).re = z.re + 1 := by
  simpa using re_T_zpow_smul z 1

theorem im_T_smul : (T โข z).im = z.im := by
  simpa using im_T_zpow_smul z 1

theorem re_T_inv_smul : (Tโปยน โข z).re = z.re - 1 := by
  simpa using re_T_zpow_smul z (-1)

theorem im_T_inv_smul : (Tโปยน โข z).im = z.im := by
  simpa using im_T_zpow_smul z (-1)

variable {z}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- If instead we had `g` and `T` of type `PSL(2, โค)`, then we could simply state `g = T^n`.
theorem exists_eq_T_zpow_of_c_eq_zero (hc : โโg 1 0 = 0) : โ n : โค, โ z : โ, g โข z = T ^ n โข z := by
  have had := g.det_coe
  replace had : โโg 0 0 * โโg 1 1 = 1
  ยท rw [det_fin_two, hc] at had
    linarith
    
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (โจha, hdโฉ | โจha, hdโฉ)
  ยท use โโg 0 1
    suffices g = T ^ โโg 0 1 by
      intro z
      conv_lhs => rw [this]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [โ ha, โ hc, โ hd, โ coe_T_zpow]
    
  ยท use -โโg 0 1
    suffices g = -(T ^ -โโg 0 1) by
      intro z
      conv_lhs => rw [this, SL_neg_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [โ ha, โ hc, โ hd, โ coe_T_zpow]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]]
-- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`.
theorem g_eq_of_c_eq_one (hc : โโg 1 0 = 1) : g = T ^ โโg 0 0 * S * T ^ โโg 1 1 := by
  have hg := g.det_coe.symm
  replace hg : โโg 0 1 = โโg 0 0 * โโg 1 1 - 1
  ยท rw [det_fin_two, hc] at hg
    linarith
    
  refine' Subtype.ext _
  conv_lhs => rw [Matrix.eta_fin_two โโg]
  rw [hc, hg]
  simp only [โ coe_mul, โ coe_T_zpow, โ coe_S, โ mul_fin_two]
  trace
      "./././Mathport/Syntax/Translate/Basic.lean:647:16: unsupported tactic `congrm #[[expr ยซexpr!![ ยป(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]" <;>
    ring

/-- If `1 < |z|`, then `|S โข z| < 1`. -/
theorem norm_sq_S_smul_lt_one (h : 1 < normSq z) : normSq โ(S โข z) < 1 := by
  simpa [โ coe_S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
theorem im_lt_im_S_smul (h : normSq z < 1) : z.im < (S โข z).im := by
  have : z.im < z.im / norm_sq (z : โ) := by
    have imz : 0 < z.im := im_pos z
    apply (lt_div_iff z.norm_sq_pos).mpr
    nlinarith
  convert this
  simp only [โ special_linear_group.im_smul_eq_div_norm_sq]
  field_simp [โ norm_sq_denom_ne_zero, โ norm_sq_ne_zero, โ S]

/-- The standard (closed) fundamental domain of the action of `SL(2,โค)` on `โ`. -/
def Fd : Set โ :=
  { z | 1 โค (z : โ).normSq โง abs z.re โค (1 : โ) / 2 }

/-- The standard open fundamental domain of the action of `SL(2,โค)` on `โ`. -/
def Fdo : Set โ :=
  { z | 1 < (z : โ).normSq โง abs z.re < (1 : โ) / 2 }

-- mathport name: ยซexpr๐ยป
localized [Modular] notation "๐" => ModularGroup.Fd

-- mathport name: ยซexpr๐แตยป
localized [Modular] notation "๐แต" => ModularGroup.Fdo

theorem abs_two_mul_re_lt_one_of_mem_fdo (h : z โ ๐แต) : abs (2 * z.re) < 1 := by
  rw [abs_mul, abs_two, โ lt_div_iff' (@two_pos โ _ _)]
  exact h.2

theorem three_lt_four_mul_im_sq_of_mem_fdo (h : z โ ๐แต) : 3 < 4 * z.im ^ 2 := by
  have : 1 < z.re * z.re + z.im * z.im := by
    simpa [โ Complex.norm_sq_apply] using h.1
  have := h.2
  cases abs_cases z.re <;> nlinarith

/-- If `z โ ๐แต`, and `n : โค`, then `|z + n| > 1`. -/
theorem one_lt_norm_sq_T_zpow_smul (hz : z โ ๐แต) (n : โค) : 1 < normSq (T ^ n โข z : โ) := by
  have hzโ : 1 < z.re * z.re + z.im * z.im := hz.1
  have hzn := Int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le
  have : 1 < (z.re + โn) * (z.re + โn) + z.im * z.im := by
    linarith
  simpa [โ coe_T_zpow, โ norm_sq]

theorem eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : โค} (hz : z โ ๐แต) (hg : T ^ n โข z โ ๐แต) : n = 0 := by
  suffices abs (n : โ) < 1 by
    rwa [โ Int.cast_abs, โ Int.cast_oneโ, Int.cast_lt, Int.abs_lt_one_iff] at this
  have hโ := hz.2
  have hโ := hg.2
  rw [re_T_zpow_smul] at hโ
  calc abs (n : โ) โค abs z.re + abs (z.re + (n : โ)) := abs_add' (n : โ) z.re _ < 1 / 2 + 1 / 2 :=
      add_lt_add hโ hโ _ = 1 := add_halves 1

/-- Any `z : โ` can be moved to `๐` by an element of `SL(2,โค)`  -/
theorem exists_smul_mem_fd (z : โ) : โ g : SL(2, โค), g โข z โ ๐ := by
  -- obtain a gโ which maximizes im (g โข z),
  obtain โจgโ, hgโโฉ := exists_max_im z
  -- then among those, minimize re
  obtain โจg, hg, hg'โฉ := exists_row_one_eq_and_min_re z (bottom_row_coprime gโ)
  refine' โจg, _โฉ
  -- `g` has same max im property as `gโ`
  have hgโ' : โ g' : SL(2, โค), (g' โข z).im โค (g โข z).im := by
    have hg'' : (g โข z).im = (gโ โข z).im := by
      rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq, denom_apply,
        denom_apply, hg]
    simpa only [โ hg''] using hgโ
  constructor
  ยท -- Claim: `1 โค โnorm_sq โ(g โข z)`. If not, then `Sโขgโขz` has larger imaginary part
    contrapose! hgโ'
    refine' โจS * g, _โฉ
    rw [mul_smul]
    exact im_lt_im_S_smul hgโ'
    
  ยท show abs (g โข z).re โค 1 / 2
    -- if not, then either `T` or `T'` decrease |Re|.
    rw [abs_le]
    constructor
    ยท contrapose! hg'
      refine' โจT * g, (T_mul_apply_one _).symm, _โฉ
      rw [mul_smul, re_T_smul]
      cases abs_cases ((g โข z).re + 1) <;> cases abs_cases (g โข z).re <;> linarith
      
    ยท contrapose! hg'
      refine' โจTโปยน * g, (T_inv_mul_apply_one _).symm, _โฉ
      rw [mul_smul, re_T_inv_smul]
      cases abs_cases ((g โข z).re - 1) <;> cases abs_cases (g โข z).re <;> linarith
      
    

section UniqueRepresentative

variable {z}

/-- An auxiliary result en route to `modular_group.c_eq_zero`. -/
theorem abs_c_le_one (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : abs (โโg 1 0) โค 1 := by
  let c' : โค := โโg 1 0
  let c : โ := (c' : โ)
  suffices 3 * c ^ 2 < 4 by
    rw [โ Int.cast_pow, โ Int.cast_three, โ Int.cast_four, โ Int.cast_mul, Int.cast_lt] at this
    replace this : c' ^ 2 โค 1 ^ 2
    ยท linarith
      
    rwa [sq_le_sq, abs_one] at this
  suffices c โ? 0 โ 9 * c ^ 4 < 16 by
    rcases eq_or_ne c 0 with (hc | hc)
    ยท rw [hc]
      norm_num
      
    ยท refine'
        (abs_lt_of_sq_lt_sq' _
            (by
              norm_num)).2
      specialize this hc
      linarith
      
  intro hc
  replace hc : 0 < c ^ 4
  ยท rw [pow_bit0_pos_iff] <;> trivial
    
  have hโ :=
    mul_lt_mul_of_pos_right
      (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg) (three_lt_four_mul_im_sq_of_mem_fdo hz)
        (by
          linarith)
        (by
          linarith))
      hc
  have hโ : (c * z.im) ^ 4 / norm_sq (denom (โg) z) ^ 2 โค 1 :=
    div_le_one_of_le (pow_four_le_pow_two_of_pow_two_le (UpperHalfPlane.c_mul_im_sq_le_norm_sq_denom z g)) (sq_nonneg _)
  let nsq := norm_sq (denom g z)
  calc 9 * c ^ 4 < c ^ 4 * z.im ^ 2 * (g โข z).im ^ 2 * 16 := by
      linarith _ = c ^ 4 * z.im ^ 4 / nsq ^ 2 * 16 := by
      rw [special_linear_group.im_smul_eq_div_norm_sq, div_pow]
      ring _ โค 16 := by
      rw [โ mul_powโ]
      linarith

/-- An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/
theorem c_eq_zero (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : โโg 1 0 = 0 := by
  have hp : โ {g' : SL(2, โค)} (hg' : g' โข z โ ๐แต), โโg' 1 0 โ? 1 := by
    intros
    by_contra hc
    let a := โโg' 0 0
    let d := โโg' 1 1
    have had : T ^ -a * g' = S * T ^ d := by
      rw [g_eq_of_c_eq_one hc]
      group
    let w := T ^ -a โข g' โข z
    have hโ : w = S โข T ^ d โข z := by
      simp only [โ w, mul_smul, โ had]
    replace hโ : norm_sq w < 1 := hโ.symm โธ norm_sq_S_smul_lt_one (one_lt_norm_sq_T_zpow_smul hz d)
    have hโ : 1 < norm_sq w := one_lt_norm_sq_T_zpow_smul hg' (-a)
    linarith
  have hn : โโg 1 0 โ? -1 := by
    intro hc
    replace hc : โโ(-g) 1 0 = 1
    ยท simp [โ eq_neg_of_eq_neg hc]
      
    replace hg : -g โข z โ ๐แต := (SL_neg_smul g z).symm โธ hg
    exact hp hg hc
  specialize hp hg
  rcases int.abs_le_one_iff.mp <| abs_c_le_one hz hg with โจโฉ <;> tauto

/-- Second Main Fundamental Domain Lemma: if both `z` and `g โข z` are in the open domain `๐แต`,
where `z : โ` and `g : SL(2,โค)`, then `z = g โข z`. -/
theorem eq_smul_self_of_mem_fdo_mem_fdo (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : z = g โข z := by
  obtain โจn, hnโฉ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg)
  rw [hn] at hgโข
  simp [โ eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, โ one_smul]

end UniqueRepresentative

end FundamentalDomain

end ModularGroup

