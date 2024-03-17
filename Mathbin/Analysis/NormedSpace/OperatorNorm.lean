/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Algebra.Algebra.Tower
import Analysis.Asymptotics.Asymptotics
import Analysis.NormedSpace.ContinuousLinearMap
import Analysis.NormedSpace.LinearIsometry
import Topology.Algebra.Module.StrongTopology

#align_import analysis.normed_space.operator_norm from "leanprover-community/mathlib"@"f7ebde7ee0d1505dfccac8644ae12371aa3c1c9f"

/-!
# Operator norm on the space of continuous linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Define the operator norm on the space of continuous (semi)linear maps between normed spaces, and
prove its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `seminormed_add_comm_group` and we specialize to `normed_add_comm_group` at the end.

Note that most of statements that apply to semilinear maps only hold when the ring homomorphism
is isometric, as expressed by the typeclass `[ring_hom_isometric σ]`.

-/


noncomputable section

open scoped Classical NNReal Topology

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type _}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

#print norm_image_of_norm_zero /-
/-- If `‖x‖ = 0` and `f` is continuous then `‖f x‖ = 0`. -/
theorem norm_image_of_norm_zero [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕) (hf : Continuous f) {x : E}
    (hx : ‖x‖ = 0) : ‖f x‖ = 0 :=
  by
  refine' le_antisymm (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg (f x))
  rcases NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩
  replace hδ := hδ x
  rw [sub_zero, hx] at hδ
  replace hδ := le_of_lt (hδ δ_pos)
  rw [map_zero, sub_zero] at hδ
  rwa [zero_add]
#align norm_image_of_norm_zero norm_image_of_norm_zero
-/

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃]

#print SemilinearMapClass.bound_of_shell_semi_normed /-
theorem SemilinearMapClass.bound_of_shell_semi_normed [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) {x : E} (hx : ‖x‖ ≠ 0) :
    ‖f x‖ ≤ C * ‖x‖ :=
  by
  rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, δinv⟩
  have := hf (δ • x) leδx δxle
  simpa only [map_smulₛₗ, norm_smul, mul_left_comm C, mul_le_mul_left (norm_pos_iff.2 hδ),
    RingHomIsometric.is_iso] using hf (δ • x) leδx δxle
#align semilinear_map_class.bound_of_shell_semi_normed SemilinearMapClass.bound_of_shell_semi_normed
-/

#print SemilinearMapClass.bound_of_continuous /-
/-- A continuous linear map between seminormed spaces is bounded when the field is nontrivially
normed. The continuity ensures boundedness on a ball of some radius `ε`. The nontriviality of the
norm is then used to rescale any element into an element of norm in `[ε/C, ε]`, whose image has a
controlled norm. The norm control for the original element follows by rescaling. -/
theorem SemilinearMapClass.bound_of_continuous [SemilinearMapClass 𝓕 σ₁₂ E F] (f : 𝓕)
    (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  by
  rcases NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩
  simp only [sub_zero, map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < ‖c‖ / ε := div_pos (zero_lt_one.trans hc) ε_pos
  refine' ⟨‖c‖ / ε, this, fun x => _⟩
  by_cases hx : ‖x‖ = 0
  · rw [hx, MulZeroClass.mul_zero]
    exact le_of_eq (norm_image_of_norm_zero f hf hx)
  refine' SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc (fun x hle hlt => _) hx
  refine' (hε _ hlt).le.trans _
  rwa [← div_le_iff' this, one_div_div]
#align semilinear_map_class.bound_of_continuous SemilinearMapClass.bound_of_continuous
-/

end

namespace ContinuousLinearMap

#print ContinuousLinearMap.bound /-
theorem bound [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) : ∃ C, 0 < C ∧ ∀ x : E, ‖f x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous f f.2
#align continuous_linear_map.bound ContinuousLinearMap.bound
-/

section

open Filter

variable (𝕜 E)

#print LinearIsometry.toSpanSingleton /-
/-- Given a unit-length element `x` of a normed space `E` over a field `𝕜`, the natural linear
    isometry map from `𝕜` to `E` by taking multiples of `x`.-/
def LinearIsometry.toSpanSingleton {v : E} (hv : ‖v‖ = 1) : 𝕜 →ₗᵢ[𝕜] E :=
  { LinearMap.toSpanSingleton 𝕜 E v with norm_map' := fun x => by simp [norm_smul, hv] }
#align linear_isometry.to_span_singleton LinearIsometry.toSpanSingleton
-/

variable {𝕜 E}

#print LinearIsometry.toSpanSingleton_apply /-
@[simp]
theorem LinearIsometry.toSpanSingleton_apply {v : E} (hv : ‖v‖ = 1) (a : 𝕜) :
    LinearIsometry.toSpanSingleton 𝕜 E hv a = a • v :=
  rfl
#align linear_isometry.to_span_singleton_apply LinearIsometry.toSpanSingleton_apply
-/

#print LinearIsometry.coe_toSpanSingleton /-
@[simp]
theorem LinearIsometry.coe_toSpanSingleton {v : E} (hv : ‖v‖ = 1) :
    (LinearIsometry.toSpanSingleton 𝕜 E hv).toLinearMap = LinearMap.toSpanSingleton 𝕜 E v :=
  rfl
#align linear_isometry.coe_to_span_singleton LinearIsometry.coe_toSpanSingleton
-/

end

section OpNorm

open Set Real

#print ContinuousLinearMap.opNorm /-
/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def opNorm (f : E →SL[σ₁₂] F) :=
  sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}
#align continuous_linear_map.op_norm ContinuousLinearMap.opNorm
-/

#print ContinuousLinearMap.hasOpNorm /-
instance hasOpNorm : Norm (E →SL[σ₁₂] F) :=
  ⟨opNorm⟩
#align continuous_linear_map.has_op_norm ContinuousLinearMap.hasOpNorm
-/

#print ContinuousLinearMap.norm_def /-
theorem norm_def (f : E →SL[σ₁₂] F) : ‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  rfl
#align continuous_linear_map.norm_def ContinuousLinearMap.norm_def
-/

#print ContinuousLinearMap.bounds_nonempty /-
-- So that invocations of `le_cInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty [RingHomIsometric σ₁₂] {f : E →SL[σ₁₂] F} :
    ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩
#align continuous_linear_map.bounds_nonempty ContinuousLinearMap.bounds_nonempty
-/

#print ContinuousLinearMap.bounds_bddBelow /-
theorem bounds_bddBelow {f : E →SL[σ₁₂] F} : BddBelow {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩
#align continuous_linear_map.bounds_bdd_below ContinuousLinearMap.bounds_bddBelow
-/

#print ContinuousLinearMap.opNorm_le_bound /-
/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
    ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩
#align continuous_linear_map.op_norm_le_bound ContinuousLinearMap.opNorm_le_bound
-/

#print ContinuousLinearMap.opNorm_le_bound' /-
/-- If one controls the norm of every `A x`, `‖x‖ ≠ 0`, then one controls the norm of `A`. -/
theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ≠ 0 → ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  opNorm_le_bound f hMp fun x =>
    (ne_or_eq ‖x‖ 0).elim (hM x) fun h => by
      simp only [h, MulZeroClass.mul_zero, norm_image_of_norm_zero f f.2 h]
#align continuous_linear_map.op_norm_le_bound' ContinuousLinearMap.opNorm_le_bound'
-/

#print ContinuousLinearMap.opNorm_le_of_lipschitz /-
theorem opNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) : ‖f‖ ≤ K :=
  f.opNorm_le_bound K.2 fun x => by
    simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0
#align continuous_linear_map.op_norm_le_of_lipschitz ContinuousLinearMap.opNorm_le_of_lipschitz
-/

#print ContinuousLinearMap.opNorm_eq_of_bounds /-
theorem opNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖) (h_below : ∀ N ≥ 0, (∀ x, ‖φ x‖ ≤ N * ‖x‖) → M ≤ N) :
    ‖φ‖ = M :=
  le_antisymm (φ.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff ContinuousLinearMap.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)
#align continuous_linear_map.op_norm_eq_of_bounds ContinuousLinearMap.opNorm_eq_of_bounds
-/

#print ContinuousLinearMap.opNorm_neg /-
theorem opNorm_neg (f : E →SL[σ₁₂] F) : ‖-f‖ = ‖f‖ := by simp only [norm_def, neg_apply, norm_neg]
#align continuous_linear_map.op_norm_neg ContinuousLinearMap.opNorm_neg
-/

section

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G)
  (x : E)

#print ContinuousLinearMap.opNorm_nonneg /-
theorem opNorm_nonneg : 0 ≤ ‖f‖ :=
  le_csInf bounds_nonempty fun _ ⟨hx, _⟩ => hx
#align continuous_linear_map.op_norm_nonneg ContinuousLinearMap.opNorm_nonneg
-/

#print ContinuousLinearMap.le_opNorm /-
/-- The fundamental property of the operator norm: `‖f x‖ ≤ ‖f‖ * ‖x‖`. -/
theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  by
  obtain ⟨C, Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, MulZeroClass.mul_zero] at hC ⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff hlt).mp
      (le_csInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff hlt).mpr <| by apply hc)
#align continuous_linear_map.le_op_norm ContinuousLinearMap.le_opNorm
-/

#print ContinuousLinearMap.dist_le_opNorm /-
theorem dist_le_opNorm (x y : E) : dist (f x) (f y) ≤ ‖f‖ * dist x y := by
  simp_rw [dist_eq_norm, ← map_sub, f.le_op_norm]
#align continuous_linear_map.dist_le_op_norm ContinuousLinearMap.dist_le_opNorm
-/

#print ContinuousLinearMap.le_opNorm_of_le /-
theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
  le_trans (f.le_opNorm x) (mul_le_mul_of_nonneg_left h f.opNorm_nonneg)
#align continuous_linear_map.le_op_norm_of_le ContinuousLinearMap.le_opNorm_of_le
-/

#print ContinuousLinearMap.le_of_opNorm_le /-
theorem le_of_opNorm_le {c : ℝ} (h : ‖f‖ ≤ c) (x : E) : ‖f x‖ ≤ c * ‖x‖ :=
  (f.le_opNorm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))
#align continuous_linear_map.le_of_op_norm_le ContinuousLinearMap.le_of_opNorm_le
-/

#print ContinuousLinearMap.ratio_le_opNorm /-
theorem ratio_le_opNorm : ‖f x‖ / ‖x‖ ≤ ‖f‖ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)
#align continuous_linear_map.ratio_le_op_norm ContinuousLinearMap.ratio_le_opNorm
-/

#print ContinuousLinearMap.unit_le_opNorm /-
/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_opNorm : ‖x‖ ≤ 1 → ‖f x‖ ≤ ‖f‖ :=
  mul_one ‖f‖ ▸ f.le_opNorm_of_le
#align continuous_linear_map.unit_le_op_norm ContinuousLinearMap.unit_le_opNorm
-/

#print ContinuousLinearMap.opNorm_le_of_shell /-
theorem opNorm_le_of_shell {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound' hC fun x hx => SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf hx
#align continuous_linear_map.op_norm_le_of_shell ContinuousLinearMap.opNorm_le_of_shell
-/

#print ContinuousLinearMap.opNorm_le_of_ball /-
theorem opNorm_le_of_ball {f : E →SL[σ₁₂] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ x ∈ ball (0 : E) ε, ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' op_norm_le_of_shell ε_pos hC hc fun x _ hx => hf x _
  rwa [ball_zero_eq]
#align continuous_linear_map.op_norm_le_of_ball ContinuousLinearMap.opNorm_le_of_ball
-/

#print ContinuousLinearMap.opNorm_le_of_nhds_zero /-
theorem opNorm_le_of_nhds_zero {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  let ⟨ε, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf
  opNorm_le_of_ball ε0 hC hε
#align continuous_linear_map.op_norm_le_of_nhds_zero ContinuousLinearMap.opNorm_le_of_nhds_zero
-/

#print ContinuousLinearMap.opNorm_le_of_shell' /-
theorem opNorm_le_of_shell' {f : E →SL[σ₁₂] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : ‖c‖ < 1) (hf : ∀ x, ε * ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) : ‖f‖ ≤ C :=
  by
  by_cases h0 : c = 0
  · refine' op_norm_le_of_ball ε_pos hC fun x hx => hf x _ _
    · simp [h0]
    · rwa [ball_zero_eq] at hx
  · rw [← inv_inv c, norm_inv, inv_lt_one_iff_of_pos (norm_pos_iff.2 <| inv_ne_zero h0)] at hc
    refine' op_norm_le_of_shell ε_pos hC hc _
    rwa [norm_inv, div_eq_mul_inv, inv_inv]
#align continuous_linear_map.op_norm_le_of_shell' ContinuousLinearMap.opNorm_le_of_shell'
-/

#print ContinuousLinearMap.opNorm_le_of_unit_norm /-
/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖ = 1`, then
one controls the norm of `f`. -/
theorem opNorm_le_of_unit_norm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C :=
  by
  refine' op_norm_le_bound' f hC fun x hx => _
  have H₁ : ‖‖x‖⁻¹ • x‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel hx]
  have H₂ := hf _ H₁
  rwa [map_smul, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul, div_le_iff] at H₂
  exact (norm_nonneg x).lt_of_ne' hx
#align continuous_linear_map.op_norm_le_of_unit_norm ContinuousLinearMap.opNorm_le_of_unit_norm
-/

#print ContinuousLinearMap.opNorm_add_le /-
/-- The operator norm satisfies the triangle inequality. -/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  (f + g).opNorm_le_bound (add_nonneg f.opNorm_nonneg g.opNorm_nonneg) fun x =>
    (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm
#align continuous_linear_map.op_norm_add_le ContinuousLinearMap.opNorm_add_le
-/

#print ContinuousLinearMap.opNorm_zero /-
/-- The norm of the `0` operator is `0`. -/
theorem opNorm_zero : ‖(0 : E →SL[σ₁₂] F)‖ = 0 :=
  le_antisymm
    (csInf_le bounds_bddBelow
      ⟨le_rfl, fun _ => le_of_eq (by rw [MulZeroClass.zero_mul]; exact norm_zero)⟩)
    (opNorm_nonneg _)
#align continuous_linear_map.op_norm_zero ContinuousLinearMap.opNorm_zero
-/

#print ContinuousLinearMap.norm_id_le /-
/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ‖id 𝕜 E‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp
#align continuous_linear_map.norm_id_le ContinuousLinearMap.norm_id_le
-/

#print ContinuousLinearMap.norm_id_of_nontrivial_seminorm /-
/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ‖x‖ ≠ 0) : ‖id 𝕜 E‖ = 1 :=
  le_antisymm norm_id_le <| by
    let ⟨x, hx⟩ := h
    have := (id 𝕜 E).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this
#align continuous_linear_map.norm_id_of_nontrivial_seminorm ContinuousLinearMap.norm_id_of_nontrivial_seminorm
-/

#print ContinuousLinearMap.opNorm_smul_le /-
theorem opNorm_smul_le {𝕜' : Type _} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
    (c : 𝕜') (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun _ =>
    by
    erw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
#align continuous_linear_map.op_norm_smul_le ContinuousLinearMap.opNorm_smul_le
-/

/-- Continuous linear maps themselves form a seminormed space with respect to
the operator norm. This is only a temporary definition because we want to replace the topology
with `continuous_linear_map.topological_space` to avoid diamond issues.
See Note [forgetful inheritance] -/
protected def tmpSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := norm
      map_zero' := opNorm_zero
      add_le' := opNorm_add_le
      neg' := opNorm_neg }
#align continuous_linear_map.tmp_seminormed_add_comm_group ContinuousLinearMap.tmpSeminormedAddCommGroup

/-- The `pseudo_metric_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmpPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpSeminormedAddCommGroup.toPseudoMetricSpace
#align continuous_linear_map.tmp_pseudo_metric_space ContinuousLinearMap.tmpPseudoMetricSpace

/-- The `uniform_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmpUniformSpace : UniformSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpPseudoMetricSpace.toUniformSpace
#align continuous_linear_map.tmp_uniform_space ContinuousLinearMap.tmpUniformSpace

/-- The `topological_space` structure on `E →SL[σ₁₂] F` coming from
`continuous_linear_map.tmp_seminormed_add_comm_group`.
See Note [forgetful inheritance] -/
protected def tmpTopologicalSpace : TopologicalSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpUniformSpace.toTopologicalSpace
#align continuous_linear_map.tmp_topological_space ContinuousLinearMap.tmpTopologicalSpace

section Tmp

attribute [-instance] ContinuousLinearMap.topologicalSpace

attribute [-instance] ContinuousLinearMap.uniformSpace

attribute [local instance] ContinuousLinearMap.tmpSeminormedAddCommGroup

protected theorem tmp_topologicalAddGroup : TopologicalAddGroup (E →SL[σ₁₂] F) :=
  inferInstance
#align continuous_linear_map.tmp_topological_add_group ContinuousLinearMap.tmp_topologicalAddGroup

protected theorem tmp_closedBall_div_subset {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closedBall (0 : E →SL[σ₁₂] F) (a / b) ⊆
      {f | ∀ x ∈ closedBall (0 : E) b, f x ∈ closedBall (0 : F) a} :=
  by
  intro f hf x hx
  rw [mem_closedBall_zero_iff] at hf hx ⊢
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
    _ ≤ a / b * b := (mul_le_mul hf hx (norm_nonneg _) (div_pos ha hb).le)
    _ = a := div_mul_cancel a hb.ne.symm
#align continuous_linear_map.tmp_closed_ball_div_subset ContinuousLinearMap.tmp_closedBall_div_subset

end Tmp

protected theorem tmp_topology_eq :
    (ContinuousLinearMap.tmpTopologicalSpace : TopologicalSpace (E →SL[σ₁₂] F)) =
      ContinuousLinearMap.topologicalSpace :=
  by
  refine'
    continuous_linear_map.tmp_topological_add_group.ext inferInstance
      ((@Metric.nhds_basis_closedBall _ ContinuousLinearMap.tmpPseudoMetricSpace 0).ext
        (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall) _ _)
  · rcases NormedField.exists_norm_lt_one 𝕜 with ⟨c, hc₀, hc₁⟩
    refine' fun ε hε =>
      ⟨⟨closed_ball 0 (1 / ‖c‖), ε⟩, ⟨NormedSpace.isVonNBounded_closedBall _ _ _, hε⟩, fun f hf =>
        _⟩
    change ∀ x, _ at hf
    simp_rw [mem_closedBall_zero_iff] at hf
    rw [@mem_closedBall_zero_iff _ SeminormedAddCommGroup.toSeminormedAddGroup]
    refine' op_norm_le_of_shell' (div_pos one_pos hc₀) hε.le hc₁ fun x hx₁ hxc => _
    rw [div_mul_cancel 1 hc₀.ne.symm] at hx₁
    exact (hf x hxc.le).trans (le_mul_of_one_le_right hε.le hx₁)
  · rintro ⟨S, ε⟩ ⟨hS, hε⟩
    rw [NormedSpace.isVonNBounded_iff, ← bounded_iff_is_bounded] at hS
    rcases hS.subset_ball_lt 0 0 with ⟨δ, hδ, hSδ⟩
    exact
      ⟨ε / δ, div_pos hε hδ,
        (ContinuousLinearMap.tmp_closedBall_div_subset hε hδ).trans fun f hf x hx => hf x <| hSδ hx⟩
#align continuous_linear_map.tmp_topology_eq ContinuousLinearMap.tmp_topology_eq

protected theorem tmpUniformSpace_eq :
    (ContinuousLinearMap.tmpUniformSpace : UniformSpace (E →SL[σ₁₂] F)) =
      ContinuousLinearMap.uniformSpace :=
  by
  rw [← @UniformAddGroup.toUniformSpace_eq _ ContinuousLinearMap.tmpUniformSpace, ←
    @UniformAddGroup.toUniformSpace_eq _ ContinuousLinearMap.uniformSpace]
  congr 1
  exact ContinuousLinearMap.tmp_topology_eq
#align continuous_linear_map.tmp_uniform_space_eq ContinuousLinearMap.tmpUniformSpace_eq

#print ContinuousLinearMap.toPseudoMetricSpace /-
instance toPseudoMetricSpace : PseudoMetricSpace (E →SL[σ₁₂] F) :=
  ContinuousLinearMap.tmpPseudoMetricSpace.replaceUniformity
    (congr_arg _ ContinuousLinearMap.tmpUniformSpace_eq.symm)
#align continuous_linear_map.to_pseudo_metric_space ContinuousLinearMap.toPseudoMetricSpace
-/

#print ContinuousLinearMap.toSeminormedAddCommGroup /-
/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (E →SL[σ₁₂] F)
    where dist_eq := ContinuousLinearMap.tmpSeminormedAddCommGroup.dist_eq
#align continuous_linear_map.to_seminormed_add_comm_group ContinuousLinearMap.toSeminormedAddCommGroup
-/

#print ContinuousLinearMap.nnnorm_def /-
theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf {c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊} :=
  by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_set_of_eq, Subtype.coe_mk,
    exists_prop]
#align continuous_linear_map.nnnorm_def ContinuousLinearMap.nnnorm_def
-/

#print ContinuousLinearMap.opNNNorm_le_bound /-
/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem opNNNorm_le_bound (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖f x‖₊ ≤ M * ‖x‖₊) : ‖f‖₊ ≤ M :=
  opNorm_le_bound f (zero_le M) hM
#align continuous_linear_map.op_nnnorm_le_bound ContinuousLinearMap.opNNNorm_le_bound
-/

#print ContinuousLinearMap.opNNNorm_le_bound' /-
/-- If one controls the norm of every `A x`, `‖x‖₊ ≠ 0`, then one controls the norm of `A`. -/
theorem opNNNorm_le_bound' (f : E →SL[σ₁₂] F) (M : ℝ≥0) (hM : ∀ x, ‖x‖₊ ≠ 0 → ‖f x‖₊ ≤ M * ‖x‖₊) :
    ‖f‖₊ ≤ M :=
  opNorm_le_bound' f (zero_le M) fun x hx => hM x <| by rwa [← NNReal.coe_ne_zero]
#align continuous_linear_map.op_nnnorm_le_bound' ContinuousLinearMap.opNNNorm_le_bound'
-/

#print ContinuousLinearMap.opNNNorm_le_of_unit_nnnorm /-
/-- For a continuous real linear map `f`, if one controls the norm of every `f x`, `‖x‖₊ = 1`, then
one controls the norm of `f`. -/
theorem opNNNorm_le_of_unit_nnnorm [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E →L[ℝ] F} {C : ℝ≥0}
    (hf : ∀ x, ‖x‖₊ = 1 → ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ C :=
  opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]
#align continuous_linear_map.op_nnnorm_le_of_unit_nnnorm ContinuousLinearMap.opNNNorm_le_of_unit_nnnorm
-/

#print ContinuousLinearMap.opNNNorm_le_of_lipschitz /-
theorem opNNNorm_le_of_lipschitz {f : E →SL[σ₁₂] F} {K : ℝ≥0} (hf : LipschitzWith K f) : ‖f‖₊ ≤ K :=
  opNorm_le_of_lipschitz hf
#align continuous_linear_map.op_nnnorm_le_of_lipschitz ContinuousLinearMap.opNNNorm_le_of_lipschitz
-/

#print ContinuousLinearMap.opNNNorm_eq_of_bounds /-
theorem opNNNorm_eq_of_bounds {φ : E →SL[σ₁₂] F} (M : ℝ≥0) (h_above : ∀ x, ‖φ x‖ ≤ M * ‖x‖)
    (h_below : ∀ N, (∀ x, ‖φ x‖₊ ≤ N * ‖x‖₊) → M ≤ N) : ‖φ‖₊ = M :=
  Subtype.ext <| opNorm_eq_of_bounds (zero_le M) h_above <| Subtype.forall'.mpr h_below
#align continuous_linear_map.op_nnnorm_eq_of_bounds ContinuousLinearMap.opNNNorm_eq_of_bounds
-/

#print ContinuousLinearMap.toNormedSpace /-
instance toNormedSpace {𝕜' : Type _} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    NormedSpace 𝕜' (E →SL[σ₁₂] F) :=
  ⟨opNorm_smul_le⟩
#align continuous_linear_map.to_normed_space ContinuousLinearMap.toNormedSpace
-/

#print ContinuousLinearMap.opNorm_comp_le /-
/-- The operator norm is submultiplicative. -/
theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
  csInf_le bounds_bddBelow
    ⟨mul_nonneg (opNorm_nonneg _) (opNorm_nonneg _), fun x => by rw [mul_assoc];
      exact h.le_op_norm_of_le (f.le_op_norm x)⟩
#align continuous_linear_map.op_norm_comp_le ContinuousLinearMap.opNorm_comp_le
-/

#print ContinuousLinearMap.opNNNorm_comp_le /-
theorem opNNNorm_comp_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) : ‖h.comp f‖₊ ≤ ‖h‖₊ * ‖f‖₊ :=
  opNorm_comp_le h f
#align continuous_linear_map.op_nnnorm_comp_le ContinuousLinearMap.opNNNorm_comp_le
-/

#print ContinuousLinearMap.toSemiNormedRing /-
/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance toSemiNormedRing : SeminormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toSeminormedAddCommGroup, ContinuousLinearMap.ring with
    norm_hMul := fun f g => opNorm_comp_le f g }
#align continuous_linear_map.to_semi_normed_ring ContinuousLinearMap.toSemiNormedRing
-/

#print ContinuousLinearMap.toNormedAlgebra /-
/-- For a normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance toNormedAlgebra : NormedAlgebra 𝕜 (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
#align continuous_linear_map.to_normed_algebra ContinuousLinearMap.toNormedAlgebra
-/

#print ContinuousLinearMap.le_opNNNorm /-
theorem le_opNNNorm : ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ :=
  f.le_opNorm x
#align continuous_linear_map.le_op_nnnorm ContinuousLinearMap.le_opNNNorm
-/

#print ContinuousLinearMap.nndist_le_opNNNorm /-
theorem nndist_le_opNNNorm (x y : E) : nndist (f x) (f y) ≤ ‖f‖₊ * nndist x y :=
  dist_le_opNorm f x y
#align continuous_linear_map.nndist_le_op_nnnorm ContinuousLinearMap.nndist_le_opNNNorm
-/

#print ContinuousLinearMap.lipschitz /-
/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ‖f‖₊ f :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm f _ f.le_opNNNorm
#align continuous_linear_map.lipschitz ContinuousLinearMap.lipschitz
-/

#print ContinuousLinearMap.lipschitz_apply /-
/-- Evaluation of a continuous linear map `f` at a point is Lipschitz continuous in `f`. -/
theorem lipschitz_apply (x : E) : LipschitzWith ‖x‖₊ fun f : E →SL[σ₁₂] F => f x :=
  lipschitzWith_iff_norm_sub_le.2 fun f g => ((f - g).le_opNorm x).trans_eq (mul_comm _ _)
#align continuous_linear_map.lipschitz_apply ContinuousLinearMap.lipschitz_apply
-/

end

section Sup

variable [RingHomIsometric σ₁₂]

#print ContinuousLinearMap.exists_mul_lt_apply_of_lt_opNNNorm /-
theorem exists_mul_lt_apply_of_lt_opNNNorm (f : E →SL[σ₁₂] F) {r : ℝ≥0} (hr : r < ‖f‖₊) :
    ∃ x, r * ‖x‖₊ < ‖f x‖₊ := by
  simpa only [Classical.not_forall, not_le, Set.mem_setOf] using
    not_mem_of_lt_csInf (nnnorm_def f ▸ hr : r < Inf {c : ℝ≥0 | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊})
      (OrderBot.bddBelow _)
#align continuous_linear_map.exists_mul_lt_apply_of_lt_op_nnnorm ContinuousLinearMap.exists_mul_lt_apply_of_lt_opNNNorm
-/

#print ContinuousLinearMap.exists_mul_lt_of_lt_opNorm /-
theorem exists_mul_lt_of_lt_opNorm (f : E →SL[σ₁₂] F) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < ‖f x‖ := by lift r to ℝ≥0 using hr₀;
  exact f.exists_mul_lt_apply_of_lt_op_nnnorm hr
#align continuous_linear_map.exists_mul_lt_of_lt_op_norm ContinuousLinearMap.exists_mul_lt_of_lt_opNorm
-/

#print ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm /-
theorem exists_lt_apply_of_lt_opNNNorm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ≥0}
    (hr : r < ‖f‖₊) : ∃ x : E, ‖x‖₊ < 1 ∧ r < ‖f x‖₊ :=
  by
  obtain ⟨y, hy⟩ := f.exists_mul_lt_apply_of_lt_op_nnnorm hr
  have hy' : ‖y‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.2 fun heq => by
      simpa only [HEq, nnnorm_zero, map_zero, not_lt_zero'] using hy
  have hfy : ‖f y‖₊ ≠ 0 := (zero_le'.trans_lt hy).ne'
  rw [← inv_inv ‖f y‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero hfy), mul_assoc, mul_comm ‖y‖₊, ←
    mul_assoc, ← NNReal.lt_inv_iff_mul_lt hy'] at hy
  obtain ⟨k, hk₁, hk₂⟩ := NormedField.exists_lt_nnnorm_lt 𝕜 hy
  refine' ⟨k • y, (nnnorm_smul k y).symm ▸ (NNReal.lt_inv_iff_mul_lt hy').1 hk₂, _⟩
  have : ‖σ₁₂ k‖₊ = ‖k‖₊ := Subtype.ext RingHomIsometric.is_iso
  rwa [map_smulₛₗ f, nnnorm_smul, ← NNReal.div_lt_iff hfy, div_eq_mul_inv, this]
#align continuous_linear_map.exists_lt_apply_of_lt_op_nnnorm ContinuousLinearMap.exists_lt_apply_of_lt_opNNNorm
-/

#print ContinuousLinearMap.exists_lt_apply_of_lt_opNorm /-
theorem exists_lt_apply_of_lt_opNorm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {r : ℝ}
    (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < ‖f x‖ :=
  by
  by_cases hr₀ : r < 0
  · exact ⟨0, by simpa using hr₀⟩
  · lift r to ℝ≥0 using not_lt.1 hr₀
    exact f.exists_lt_apply_of_lt_op_nnnorm hr
#align continuous_linear_map.exists_lt_apply_of_lt_op_norm ContinuousLinearMap.exists_lt_apply_of_lt_opNorm
-/

#print ContinuousLinearMap.sSup_unit_ball_eq_nnnorm /-
theorem sSup_unit_ball_eq_nnnorm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' ball 0 1) = ‖f‖₊ :=
  by
  refine'
    csSup_eq_of_forall_le_of_forall_lt_exists_gt ((nonempty_ball.mpr zero_lt_one).image _) _
      fun ub hub => _
  · rintro - ⟨x, hx, rfl⟩
    simpa only [mul_one] using f.le_op_norm_of_le (mem_ball_zero_iff.1 hx).le
  · obtain ⟨x, hx, hxf⟩ := f.exists_lt_apply_of_lt_op_nnnorm hub
    exact ⟨_, ⟨x, mem_ball_zero_iff.2 hx, rfl⟩, hxf⟩
#align continuous_linear_map.Sup_unit_ball_eq_nnnorm ContinuousLinearMap.sSup_unit_ball_eq_nnnorm
-/

#print ContinuousLinearMap.sSup_unit_ball_eq_norm /-
theorem sSup_unit_ball_eq_norm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' ball 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using NNReal.coe_inj.2 f.Sup_unit_ball_eq_nnnorm
#align continuous_linear_map.Sup_unit_ball_eq_norm ContinuousLinearMap.sSup_unit_ball_eq_norm
-/

#print ContinuousLinearMap.sSup_closed_unit_ball_eq_nnnorm /-
theorem sSup_closed_unit_ball_eq_nnnorm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊ :=
  by
  have hbdd : ∀ y ∈ (fun x => ‖f x‖₊) '' closed_ball 0 1, y ≤ ‖f‖₊ := by rintro - ⟨x, hx, rfl⟩;
    exact f.unit_le_op_norm x (mem_closedBall_zero_iff.1 hx)
  refine' le_antisymm (csSup_le ((nonempty_closed_ball.mpr zero_le_one).image _) hbdd) _
  rw [← Sup_unit_ball_eq_nnnorm]
  exact
    csSup_le_csSup ⟨‖f‖₊, hbdd⟩ ((nonempty_ball.2 zero_lt_one).image _)
      (Set.image_subset _ ball_subset_closed_ball)
#align continuous_linear_map.Sup_closed_unit_ball_eq_nnnorm ContinuousLinearMap.sSup_closed_unit_ball_eq_nnnorm
-/

#print ContinuousLinearMap.sSup_closed_unit_ball_eq_norm /-
theorem sSup_closed_unit_ball_eq_norm {𝕜 𝕜₂ E F : Type _} [NormedAddCommGroup E]
    [SeminormedAddCommGroup F] [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) :
    sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖ := by
  simpa only [NNReal.coe_sSup, Set.image_image] using
    NNReal.coe_inj.2 f.Sup_closed_unit_ball_eq_nnnorm
#align continuous_linear_map.Sup_closed_unit_ball_eq_norm ContinuousLinearMap.sSup_closed_unit_ball_eq_norm
-/

end Sup

section

#print ContinuousLinearMap.opNorm_ext /-
theorem opNorm_ext [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) (g : E →SL[σ₁₃] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  opNorm_eq_of_bounds (norm_nonneg _) (fun x => by rw [h x]; exact le_op_norm _ _) fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by rw [← h z]; exact h₂ z
#align continuous_linear_map.op_norm_ext ContinuousLinearMap.opNorm_ext
-/

variable [RingHomIsometric σ₂₃]

#print ContinuousLinearMap.opNorm_le_bound₂ /-
theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (mul_nonneg h0 (norm_nonneg _)) <| hC x
#align continuous_linear_map.op_norm_le_bound₂ ContinuousLinearMap.opNorm_le_bound₂
-/

#print ContinuousLinearMap.le_opNorm₂ /-
theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y
#align continuous_linear_map.le_op_norm₂ ContinuousLinearMap.le_opNorm₂
-/

end

#print ContinuousLinearMap.opNorm_prod /-
@[simp]
theorem opNorm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.Prod g‖ = ‖(f, g)‖ :=
  le_antisymm
      (opNorm_le_bound _ (norm_nonneg _) fun x => by
        simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, norm_nonneg] using
          max_le_max (le_op_norm f x) (le_op_norm g x)) <|
    max_le
      (opNorm_le_bound _ (norm_nonneg _) fun x => (le_max_left _ _).trans ((f.Prod g).le_opNorm x))
      (opNorm_le_bound _ (norm_nonneg _) fun x => (le_max_right _ _).trans ((f.Prod g).le_opNorm x))
#align continuous_linear_map.op_norm_prod ContinuousLinearMap.opNorm_prod
-/

#print ContinuousLinearMap.opNNNorm_prod /-
@[simp]
theorem opNNNorm_prod (f : E →L[𝕜] Fₗ) (g : E →L[𝕜] Gₗ) : ‖f.Prod g‖₊ = ‖(f, g)‖₊ :=
  Subtype.ext <| opNorm_prod f g
#align continuous_linear_map.op_nnnorm_prod ContinuousLinearMap.opNNNorm_prod
-/

#print ContinuousLinearMap.prodₗᵢ /-
/-- `continuous_linear_map.prod` as a `linear_isometry_equiv`. -/
def prodₗᵢ (R : Type _) [Semiring R] [Module R Fₗ] [Module R Gₗ] [ContinuousConstSMul R Fₗ]
    [ContinuousConstSMul R Gₗ] [SMulCommClass 𝕜 R Fₗ] [SMulCommClass 𝕜 R Gₗ] :
    (E →L[𝕜] Fₗ) × (E →L[𝕜] Gₗ) ≃ₗᵢ[R] E →L[𝕜] Fₗ × Gₗ :=
  ⟨prodₗ R, fun ⟨f, g⟩ => opNorm_prod f g⟩
#align continuous_linear_map.prodₗᵢ ContinuousLinearMap.prodₗᵢ
-/

variable [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F)

#print ContinuousLinearMap.opNorm_subsingleton /-
@[simp, nontriviality]
theorem opNorm_subsingleton [Subsingleton E] : ‖f‖ = 0 :=
  by
  refine' le_antisymm _ (norm_nonneg _)
  apply op_norm_le_bound _ rfl.ge
  intro x
  simp [Subsingleton.elim x 0]
#align continuous_linear_map.op_norm_subsingleton ContinuousLinearMap.opNorm_subsingleton
-/

end OpNorm

section IsO

variable [RingHomIsometric σ₁₂] (c : 𝕜) (f g : E →SL[σ₁₂] F) (h : F →SL[σ₂₃] G) (x y z : E)

open Asymptotics

#print ContinuousLinearMap.isBigOWith_id /-
theorem isBigOWith_id (l : Filter E) : IsBigOWith ‖f‖ l f fun x => x :=
  isBigOWith_of_le' _ f.le_opNorm
#align continuous_linear_map.is_O_with_id ContinuousLinearMap.isBigOWith_id
-/

#print ContinuousLinearMap.isBigO_id /-
theorem isBigO_id (l : Filter E) : f =O[l] fun x => x :=
  (f.isBigOWith_id l).IsBigO
#align continuous_linear_map.is_O_id ContinuousLinearMap.isBigO_id
-/

#print ContinuousLinearMap.isBigOWith_comp /-
theorem isBigOWith_comp [RingHomIsometric σ₂₃] {α : Type _} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : IsBigOWith ‖g‖ l (fun x' => g (f x')) f :=
  (g.isBigOWith_id ⊤).comp_tendsto le_top
#align continuous_linear_map.is_O_with_comp ContinuousLinearMap.isBigOWith_comp
-/

#print ContinuousLinearMap.isBigO_comp /-
theorem isBigO_comp [RingHomIsometric σ₂₃] {α : Type _} (g : F →SL[σ₂₃] G) (f : α → F)
    (l : Filter α) : (fun x' => g (f x')) =O[l] f :=
  (g.isBigOWith_comp f l).IsBigO
#align continuous_linear_map.is_O_comp ContinuousLinearMap.isBigO_comp
-/

#print ContinuousLinearMap.isBigOWith_sub /-
theorem isBigOWith_sub (f : E →SL[σ₁₂] F) (l : Filter E) (x : E) :
    IsBigOWith ‖f‖ l (fun x' => f (x' - x)) fun x' => x' - x :=
  f.isBigOWith_comp _ l
#align continuous_linear_map.is_O_with_sub ContinuousLinearMap.isBigOWith_sub
-/

#print ContinuousLinearMap.isBigO_sub /-
theorem isBigO_sub (f : E →SL[σ₁₂] F) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  f.isBigO_comp _ l
#align continuous_linear_map.is_O_sub ContinuousLinearMap.isBigO_sub
-/

end IsO

end ContinuousLinearMap

namespace LinearIsometry

#print LinearIsometry.norm_toContinuousLinearMap_le /-
theorem norm_toContinuousLinearMap_le (f : E →ₛₗᵢ[σ₁₂] F) : ‖f.toContinuousLinearMap‖ ≤ 1 :=
  f.toContinuousLinearMap.opNorm_le_bound zero_le_one fun x => by simp
#align linear_isometry.norm_to_continuous_linear_map_le LinearIsometry.norm_toContinuousLinearMap_le
-/

end LinearIsometry

namespace LinearMap

#print LinearMap.mkContinuous_norm_le /-
/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h
#align linear_map.mk_continuous_norm_le LinearMap.mkContinuous_norm_le
-/

#print LinearMap.mkContinuous_norm_le' /-
/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x =>
    (h x).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)
#align linear_map.mk_continuous_norm_le' LinearMap.mkContinuous_norm_le'
-/

variable [RingHomIsometric σ₂₃]

#print LinearMap.mkContinuous₂ /-
/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`linear_map.mk₂`. -/
def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) (hC x)
      map_add' := fun x y => by
        ext z
        rw [ContinuousLinearMap.add_apply, mk_continuous_apply, mk_continuous_apply,
          mk_continuous_apply, map_add, add_apply]
      map_smul' := fun c x => by
        ext z
        rw [ContinuousLinearMap.smul_apply, mk_continuous_apply, mk_continuous_apply, map_smulₛₗ,
          smul_apply] }
    (max C 0) fun x =>
    (mkContinuous_norm_le' _ _).trans_eq <| by
      rw [max_mul_of_nonneg _ _ (norm_nonneg x), MulZeroClass.zero_mul]
#align linear_map.mk_continuous₂ LinearMap.mkContinuous₂
-/

#print LinearMap.mkContinuous₂_apply /-
@[simp]
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl
#align linear_map.mk_continuous₂_apply LinearMap.mkContinuous₂_apply
-/

#print LinearMap.mkContinuous₂_norm_le' /-
theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) _
#align linear_map.mk_continuous₂_norm_le' LinearMap.mkContinuous₂_norm_le'
-/

#print LinearMap.mkContinuous₂_norm_le /-
theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0
#align linear_map.mk_continuous₂_norm_le LinearMap.mkContinuous₂_norm_le
-/

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

#print ContinuousLinearMap.flip /-
/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `linear_isometry_equiv`, see
`continuous_linear_map.flipL`. -/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by rw [f.map_add, add_apply]) fun c y x =>
      by rw [f.map_smulₛₗ, smul_apply])
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by rw [mul_right_comm]
#align continuous_linear_map.flip ContinuousLinearMap.flip
-/

private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  f.opNorm_le_bound₂ (norm_nonneg _) fun x y => by rw [mul_right_comm];
    exact (flip f).le_opNorm₂ y x

#print ContinuousLinearMap.flip_apply /-
@[simp]
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl
#align continuous_linear_map.flip_apply ContinuousLinearMap.flip_apply
-/

#print ContinuousLinearMap.flip_flip /-
@[simp]
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by ext; rfl
#align continuous_linear_map.flip_flip ContinuousLinearMap.flip_flip
-/

#print ContinuousLinearMap.opNorm_flip /-
@[simp]
theorem opNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)
#align continuous_linear_map.op_norm_flip ContinuousLinearMap.opNorm_flip
-/

#print ContinuousLinearMap.flip_add /-
@[simp]
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl
#align continuous_linear_map.flip_add ContinuousLinearMap.flip_add
-/

#print ContinuousLinearMap.flip_smul /-
@[simp]
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl
#align continuous_linear_map.flip_smul ContinuousLinearMap.flip_smul
-/

variable (E F G σ₁₃ σ₂₃)

#print ContinuousLinearMap.flipₗᵢ' /-
/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `linear_isometry_equiv`.
For an unbundled version see `continuous_linear_map.flip`. -/
def flipₗᵢ' : (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F →SL[σ₂₃] E →SL[σ₁₃] G
    where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
#align continuous_linear_map.flipₗᵢ' ContinuousLinearMap.flipₗᵢ'
-/

variable {E F G σ₁₃ σ₂₃}

#print ContinuousLinearMap.flipₗᵢ'_symm /-
@[simp]
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl
#align continuous_linear_map.flipₗᵢ'_symm ContinuousLinearMap.flipₗᵢ'_symm
-/

#print ContinuousLinearMap.coe_flipₗᵢ' /-
@[simp]
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ' ContinuousLinearMap.coe_flipₗᵢ'
-/

variable (𝕜 E Fₗ Gₗ)

#print ContinuousLinearMap.flipₗᵢ /-
/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `linear_isometry_equiv`.
For an unbundled version see `continuous_linear_map.flip`. -/
def flipₗᵢ : (E →L[𝕜] Fₗ →L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ →L[𝕜] E →L[𝕜] Gₗ
    where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
#align continuous_linear_map.flipₗᵢ ContinuousLinearMap.flipₗᵢ
-/

variable {𝕜 E Fₗ Gₗ}

#print ContinuousLinearMap.flipₗᵢ_symm /-
@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl
#align continuous_linear_map.flipₗᵢ_symm ContinuousLinearMap.flipₗᵢ_symm
-/

#print ContinuousLinearMap.coe_flipₗᵢ /-
@[simp]
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl
#align continuous_linear_map.coe_flipₗᵢ ContinuousLinearMap.coe_flipₗᵢ
-/

variable (F σ₁₂) [RingHomIsometric σ₁₂]

#print ContinuousLinearMap.apply' /-
/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `linear_map.applyₗ`. -/
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (id 𝕜₂ (E →SL[σ₁₂] F))
#align continuous_linear_map.apply' ContinuousLinearMap.apply'
-/

variable {F σ₁₂}

#print ContinuousLinearMap.apply_apply' /-
@[simp]
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply' ContinuousLinearMap.apply_apply'
-/

variable (𝕜 Fₗ)

#print ContinuousLinearMap.apply /-
/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `linear_map.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (id 𝕜 (E →L[𝕜] Fₗ))
#align continuous_linear_map.apply ContinuousLinearMap.apply
-/

variable {𝕜 Fₗ}

#print ContinuousLinearMap.apply_apply /-
@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl
#align continuous_linear_map.apply_apply ContinuousLinearMap.apply_apply
-/

variable (σ₁₂ σ₂₃ E F G)

#print ContinuousLinearMap.compSL /-
/-- Composition of continuous semilinear maps as a continuous semibilinear map. -/
def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by ext;
      simp only [ContinuousLinearMap.map_smulₛₗ, coe_smul', coe_comp', Function.comp_apply,
        Pi.smul_apply])
    1 fun f g => by simpa only [one_mul] using op_norm_comp_le f g
#align continuous_linear_map.compSL ContinuousLinearMap.compSL
-/

#print ContinuousLinearMap.norm_compSL_le /-
theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.norm_compSL_le ContinuousLinearMap.norm_compSL_le
-/

variable {𝕜 σ₁₂ σ₂₃ E F G}

#print ContinuousLinearMap.compSL_apply /-
@[simp]
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl
#align continuous_linear_map.compSL_apply ContinuousLinearMap.compSL_apply
-/

#print Continuous.const_clm_comp /-
theorem Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).Continuous.comp hf
#align continuous.const_clm_comp Continuous.const_clm_comp
-/

#print Continuous.clm_comp_const /-
-- Giving the implicit argument speeds up elaboration significantly
theorem Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
          (compSL E F G σ₁₂ σ₂₃) f).Continuous.comp
    hg
#align continuous.clm_comp_const Continuous.clm_comp_const
-/

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

#print ContinuousLinearMap.compL /-
/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)
#align continuous_linear_map.compL ContinuousLinearMap.compL
-/

#print ContinuousLinearMap.norm_compL_le /-
theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _
#align continuous_linear_map.norm_compL_le ContinuousLinearMap.norm_compL_le
-/

#print ContinuousLinearMap.compL_apply /-
@[simp]
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl
#align continuous_linear_map.compL_apply ContinuousLinearMap.compL_apply
-/

variable (Eₗ) {𝕜 E Fₗ Gₗ}

#print ContinuousLinearMap.precompR /-
/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps apply]
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (compL 𝕜 Eₗ Fₗ Gₗ).comp L
#align continuous_linear_map.precompR ContinuousLinearMap.precompR
-/

#print ContinuousLinearMap.precompL /-
/-- Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map -/
def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip
#align continuous_linear_map.precompL ContinuousLinearMap.precompL
-/

#print ContinuousLinearMap.norm_precompR_le /-
theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := (mul_le_mul_of_nonneg_right (norm_compL_le _ _ _ _) (norm_nonneg _))
    _ = ‖L‖ := by rw [one_mul]
#align continuous_linear_map.norm_precompR_le ContinuousLinearMap.norm_precompR_le
-/

#print ContinuousLinearMap.norm_precompL_le /-
theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, op_norm_flip, ← op_norm_flip L]; exact norm_precompR_le _ L.flip
#align continuous_linear_map.norm_precompL_le ContinuousLinearMap.norm_precompL_le
-/

section Prod

universe u₁ u₂ u₃ u₄

variable (M₁ : Type u₁) [SeminormedAddCommGroup M₁] [NormedSpace 𝕜 M₁] (M₂ : Type u₂)
  [SeminormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] (M₃ : Type u₃) [SeminormedAddCommGroup M₃]
  [NormedSpace 𝕜 M₃] (M₄ : Type u₄) [SeminormedAddCommGroup M₄] [NormedSpace 𝕜 M₄]

variable {Eₗ} (𝕜)

#print ContinuousLinearMap.prodMapL /-
/-- `continuous_linear_map.prod_map` as a continuous linear map. -/
def prodMapL : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ × M₃ →L[𝕜] M₂ × M₄ :=
  ContinuousLinearMap.copy
    (have Φ₁ : (M₁ →L[𝕜] M₂) →L[𝕜] M₁ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₁ M₂ (M₂ × M₄) (ContinuousLinearMap.inl 𝕜 M₂ M₄)
    have Φ₂ : (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₂ × M₄ :=
      ContinuousLinearMap.compL 𝕜 M₃ M₄ (M₂ × M₄) (ContinuousLinearMap.inr 𝕜 M₂ M₄)
    have Φ₁' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₁ (M₂ × M₄)).flip (ContinuousLinearMap.fst 𝕜 M₁ M₃)
    have Φ₂' :=
      (ContinuousLinearMap.compL 𝕜 (M₁ × M₃) M₃ (M₂ × M₄)).flip (ContinuousLinearMap.snd 𝕜 M₁ M₃)
    have Ψ₁ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₁ →L[𝕜] M₂ :=
      ContinuousLinearMap.fst 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    have Ψ₂ : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) →L[𝕜] M₃ →L[𝕜] M₄ :=
      ContinuousLinearMap.snd 𝕜 (M₁ →L[𝕜] M₂) (M₃ →L[𝕜] M₄)
    Φ₁' ∘L Φ₁ ∘L Ψ₁ + Φ₂' ∘L Φ₂ ∘L Ψ₂)
    (fun p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄) => p.1.Prod_map p.2)
    (by
      apply funext
      rintro ⟨φ, ψ⟩
      apply ContinuousLinearMap.ext fun x => _
      simp only [add_apply, coe_comp', coe_fst', Function.comp_apply, compL_apply, flip_apply,
        coe_snd', inl_apply, inr_apply, Prod.mk_add_mk, add_zero, zero_add, coe_prod_map', Prod_map,
        Prod.mk.inj_iff, eq_self_iff_true, and_self_iff]
      rfl)
#align continuous_linear_map.prod_mapL ContinuousLinearMap.prodMapL
-/

variable {M₁ M₂ M₃ M₄}

#print ContinuousLinearMap.prodMapL_apply /-
@[simp]
theorem prodMapL_apply (p : (M₁ →L[𝕜] M₂) × (M₃ →L[𝕜] M₄)) :
    ContinuousLinearMap.prodMapL 𝕜 M₁ M₂ M₃ M₄ p = p.1.Prod_map p.2 :=
  rfl
#align continuous_linear_map.prod_mapL_apply ContinuousLinearMap.prodMapL_apply
-/

variable {X : Type _} [TopologicalSpace X]

#print Continuous.prod_mapL /-
theorem Continuous.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).Prod_map (g x) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).Continuous.comp (hf.prod_mk hg)
#align continuous.prod_mapL Continuous.prod_mapL
-/

#print Continuous.prod_map_equivL /-
theorem Continuous.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄}
    (hf : Continuous fun x => (f x : M₁ →L[𝕜] M₂)) (hg : Continuous fun x => (g x : M₃ →L[𝕜] M₄)) :
    Continuous fun x => ((f x).Prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄) :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).Continuous.comp (hf.prod_mk hg)
#align continuous.prod_map_equivL Continuous.prod_map_equivL
-/

#print ContinuousOn.prod_mapL /-
theorem ContinuousOn.prod_mapL {f : X → M₁ →L[𝕜] M₂} {g : X → M₃ →L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).Prod_map (g x)) s :=
  ((prodMapL 𝕜 M₁ M₂ M₃ M₄).Continuous.comp_continuousOn (hf.Prod hg) : _)
#align continuous_on.prod_mapL ContinuousOn.prod_mapL
-/

#print ContinuousOn.prod_map_equivL /-
theorem ContinuousOn.prod_map_equivL {f : X → M₁ ≃L[𝕜] M₂} {g : X → M₃ ≃L[𝕜] M₄} {s : Set X}
    (hf : ContinuousOn (fun x => (f x : M₁ →L[𝕜] M₂)) s)
    (hg : ContinuousOn (fun x => (g x : M₃ →L[𝕜] M₄)) s) :
    ContinuousOn (fun x => ((f x).Prod (g x) : M₁ × M₃ →L[𝕜] M₂ × M₄)) s :=
  (prodMapL 𝕜 M₁ M₂ M₃ M₄).Continuous.comp_continuousOn (hf.Prod hg)
#align continuous_on.prod_map_equivL ContinuousOn.prod_map_equivL
-/

end Prod

variable {𝕜 E Fₗ Gₗ}

section MultiplicationLinear

section NonUnital

variable (𝕜) (𝕜' : Type _) [NonUnitalSeminormedRing 𝕜'] [NormedSpace 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' 𝕜']
  [SMulCommClass 𝕜 𝕜' 𝕜']

#print ContinuousLinearMap.mul /-
/-- Multiplication in a non-unital normed algebra as a continuous bilinear map. -/
def mul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (LinearMap.mul 𝕜 𝕜').mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y
#align continuous_linear_map.mul ContinuousLinearMap.mul
-/

#print ContinuousLinearMap.mul_apply' /-
@[simp]
theorem mul_apply' (x y : 𝕜') : mul 𝕜 𝕜' x y = x * y :=
  rfl
#align continuous_linear_map.mul_apply' ContinuousLinearMap.mul_apply'
-/

#print ContinuousLinearMap.opNorm_mul_apply_le /-
@[simp]
theorem opNorm_mul_apply_le (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)
#align continuous_linear_map.op_norm_mul_apply_le ContinuousLinearMap.opNorm_mul_apply_le
-/

#print ContinuousLinearMap.opNorm_mul_le /-
theorem opNorm_mul_le : ‖mul 𝕜 𝕜'‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
#align continuous_linear_map.op_norm_mul_le ContinuousLinearMap.opNorm_mul_le
-/

#print ContinuousLinearMap.mulLeftRight /-
/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `linear_map.mul_left_right`,
but there is a minor difference: `linear_map.mul_left_right` is uncurried. -/
def mulLeftRight : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (mul 𝕜 𝕜').flip).flip.comp (mul 𝕜 𝕜')
#align continuous_linear_map.mul_left_right ContinuousLinearMap.mulLeftRight
-/

#print ContinuousLinearMap.mulLeftRight_apply /-
@[simp]
theorem mulLeftRight_apply (x y z : 𝕜') : mulLeftRight 𝕜 𝕜' x y z = x * z * y :=
  rfl
#align continuous_linear_map.mul_left_right_apply ContinuousLinearMap.mulLeftRight_apply
-/

#print ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le /-
theorem opNorm_mulLeftRight_apply_apply_le (x y : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x y‖ ≤ ‖x‖ * ‖y‖ :=
  (opNorm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)
#align continuous_linear_map.op_norm_mul_left_right_apply_apply_le ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le
-/

#print ContinuousLinearMap.opNorm_mulLeftRight_apply_le /-
theorem opNorm_mulLeftRight_apply_le (x : 𝕜') : ‖mulLeftRight 𝕜 𝕜' x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 𝕜' x)
#align continuous_linear_map.op_norm_mul_left_right_apply_le ContinuousLinearMap.opNorm_mulLeftRight_apply_le
-/

#print ContinuousLinearMap.opNorm_mulLeftRight_le /-
theorem opNorm_mulLeftRight_le : ‖mulLeftRight 𝕜 𝕜'‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 𝕜' x
#align continuous_linear_map.op_norm_mul_left_right_le ContinuousLinearMap.opNorm_mulLeftRight_le
-/

end NonUnital

section Unital

variable (𝕜) (𝕜' : Type _) [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜']

/-- Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def mulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' where
  toLinearMap := mul 𝕜 𝕜'
  norm_map' x :=
    le_antisymm (opNorm_mul_apply_le _ _ _)
      (by
        convert ratio_le_op_norm _ (1 : 𝕜'); simp [norm_one]
        infer_instance)
#align continuous_linear_map.mulₗᵢ ContinuousLinearMap.mulₗᵢₓ

@[simp]
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 𝕜') = mul 𝕜 𝕜' :=
  rfl
#align continuous_linear_map.coe_mulₗᵢ ContinuousLinearMap.coe_mulₗᵢₓ

@[simp]
theorem opNorm_mul_apply (x : 𝕜') : ‖mul 𝕜 𝕜' x‖ = ‖x‖ :=
  (mulₗᵢ 𝕜 𝕜').norm_map x
#align continuous_linear_map.op_norm_mul_apply ContinuousLinearMap.opNorm_mul_applyₓ

end Unital

end MultiplicationLinear

section SmulLinear

variable (𝕜) (𝕜' : Type _) [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E]

#print ContinuousLinearMap.lsmul /-
/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using norm_smul_le c x
#align continuous_linear_map.lsmul ContinuousLinearMap.lsmul
-/

#print ContinuousLinearMap.lsmul_apply /-
@[simp]
theorem lsmul_apply (c : 𝕜') (x : E) : lsmul 𝕜 𝕜' c x = c • x :=
  rfl
#align continuous_linear_map.lsmul_apply ContinuousLinearMap.lsmul_apply
-/

variable {𝕜'}

#print ContinuousLinearMap.norm_toSpanSingleton /-
theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ :=
  by
  refine' op_norm_eq_of_bounds (norm_nonneg _) (fun x => _) fun N hN_nonneg h => _
  · rw [to_span_singleton_apply, norm_smul, mul_comm]
  · specialize h 1
    rw [to_span_singleton_apply, norm_smul, mul_comm] at h
    exact (mul_le_mul_right (by simp)).mp h
#align continuous_linear_map.norm_to_span_singleton ContinuousLinearMap.norm_toSpanSingleton
-/

variable {𝕜}

#print ContinuousLinearMap.opNorm_lsmul_apply_le /-
theorem opNorm_lsmul_apply_le (x : 𝕜') : ‖(lsmul 𝕜 𝕜' x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y
#align continuous_linear_map.op_norm_lsmul_apply_le ContinuousLinearMap.opNorm_lsmul_apply_le
-/

#print ContinuousLinearMap.opNorm_lsmul_le /-
/-- The norm of `lsmul` is at most 1 in any semi-normed group. -/
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ ≤ 1 :=
  by
  refine' ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => _
  simp_rw [one_mul]
  exact op_norm_lsmul_apply_le _
#align continuous_linear_map.op_norm_lsmul_le ContinuousLinearMap.opNorm_lsmul_le
-/

end SmulLinear

section RestrictScalars

variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]

variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

variable [NormedSpace 𝕜' Fₗ] [IsScalarTower 𝕜' 𝕜 Fₗ]

#print ContinuousLinearMap.norm_restrictScalars /-
@[simp]
theorem norm_restrictScalars (f : E →L[𝕜] Fₗ) : ‖f.restrictScalars 𝕜'‖ = ‖f‖ :=
  le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
    (opNorm_le_bound _ (norm_nonneg _) fun x => f.le_opNorm x)
#align continuous_linear_map.norm_restrict_scalars ContinuousLinearMap.norm_restrictScalars
-/

variable (𝕜 E Fₗ 𝕜') (𝕜'' : Type _) [Ring 𝕜''] [Module 𝕜'' Fₗ] [ContinuousConstSMul 𝕜'' Fₗ]
  [SMulCommClass 𝕜 𝕜'' Fₗ] [SMulCommClass 𝕜' 𝕜'' Fₗ]

#print ContinuousLinearMap.restrictScalarsIsometry /-
/-- `continuous_linear_map.restrict_scalars` as a `linear_isometry`. -/
def restrictScalarsIsometry : (E →L[𝕜] Fₗ) →ₗᵢ[𝕜''] E →L[𝕜'] Fₗ :=
  ⟨restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'', norm_restrictScalars⟩
#align continuous_linear_map.restrict_scalars_isometry ContinuousLinearMap.restrictScalarsIsometry
-/

variable {𝕜 E Fₗ 𝕜' 𝕜''}

#print ContinuousLinearMap.coe_restrictScalarsIsometry /-
@[simp]
theorem coe_restrictScalarsIsometry :
    ⇑(restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl
#align continuous_linear_map.coe_restrict_scalars_isometry ContinuousLinearMap.coe_restrictScalarsIsometry
-/

#print ContinuousLinearMap.restrictScalarsIsometry_toLinearMap /-
@[simp]
theorem restrictScalarsIsometry_toLinearMap :
    (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toLinearMap = restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl
#align continuous_linear_map.restrict_scalars_isometry_to_linear_map ContinuousLinearMap.restrictScalarsIsometry_toLinearMap
-/

variable (𝕜 E Fₗ 𝕜' 𝕜'')

#print ContinuousLinearMap.restrictScalarsL /-
/-- `continuous_linear_map.restrict_scalars` as a `continuous_linear_map`. -/
def restrictScalarsL : (E →L[𝕜] Fₗ) →L[𝕜''] E →L[𝕜'] Fₗ :=
  (restrictScalarsIsometry 𝕜 E Fₗ 𝕜' 𝕜'').toContinuousLinearMap
#align continuous_linear_map.restrict_scalarsL ContinuousLinearMap.restrictScalarsL
-/

variable {𝕜 E Fₗ 𝕜' 𝕜''}

#print ContinuousLinearMap.coe_restrictScalarsL /-
@[simp]
theorem coe_restrictScalarsL :
    (restrictScalarsL 𝕜 E Fₗ 𝕜' 𝕜'' : (E →L[𝕜] Fₗ) →ₗ[𝕜''] E →L[𝕜'] Fₗ) =
      restrictScalarsₗ 𝕜 E Fₗ 𝕜' 𝕜'' :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsL ContinuousLinearMap.coe_restrictScalarsL
-/

#print ContinuousLinearMap.coe_restrict_scalarsL' /-
@[simp]
theorem coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E Fₗ 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl
#align continuous_linear_map.coe_restrict_scalarsL' ContinuousLinearMap.coe_restrict_scalarsL'
-/

end RestrictScalars

end ContinuousLinearMap

namespace Submodule

#print Submodule.norm_subtypeL_le /-
theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ‖K.subtypeL‖ ≤ 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap_le
#align submodule.norm_subtypeL_le Submodule.norm_subtypeL_le
-/

end Submodule

namespace ContinuousLinearEquiv

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [RingHomIsometric σ₁₂]

variable (e : E ≃SL[σ₁₂] F)

#print ContinuousLinearEquiv.lipschitz /-
protected theorem lipschitz : LipschitzWith ‖(e : E →SL[σ₁₂] F)‖₊ e :=
  (e : E →SL[σ₁₂] F).lipschitz
#align continuous_linear_equiv.lipschitz ContinuousLinearEquiv.lipschitz
-/

#print ContinuousLinearEquiv.isBigO_comp /-
theorem isBigO_comp {α : Type _} (f : α → E) (l : Filter α) : (fun x' => e (f x')) =O[l] f :=
  (e : E →SL[σ₁₂] F).isBigO_comp f l
#align continuous_linear_equiv.is_O_comp ContinuousLinearEquiv.isBigO_comp
-/

#print ContinuousLinearEquiv.isBigO_sub /-
theorem isBigO_sub (l : Filter E) (x : E) : (fun x' => e (x' - x)) =O[l] fun x' => x' - x :=
  (e : E →SL[σ₁₂] F).isBigO_sub l x
#align continuous_linear_equiv.is_O_sub ContinuousLinearEquiv.isBigO_sub
-/

end

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

variable [RingHomIsometric σ₂₁] (e : E ≃SL[σ₁₂] F)

#print ContinuousLinearEquiv.isBigO_comp_rev /-
theorem isBigO_comp_rev {α : Type _} (f : α → E) (l : Filter α) : f =O[l] fun x' => e (f x') :=
  (e.symm.isBigO_comp _ l).congr_left fun _ => e.symm_apply_apply _
#align continuous_linear_equiv.is_O_comp_rev ContinuousLinearEquiv.isBigO_comp_rev
-/

#print ContinuousLinearEquiv.isBigO_sub_rev /-
theorem isBigO_sub_rev (l : Filter E) (x : E) : (fun x' => x' - x) =O[l] fun x' => e (x' - x) :=
  e.isBigO_comp_rev _ _
#align continuous_linear_equiv.is_O_sub_rev ContinuousLinearEquiv.isBigO_sub_rev
-/

end ContinuousLinearEquiv

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type _} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']

variable {𝕜₁' : Type _} {𝕜₂' : Type _} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

#print ContinuousLinearMap.bilinearComp /-
/-- Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`.  -/
def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip
#align continuous_linear_map.bilinear_comp ContinuousLinearMap.bilinearComp
-/

#print ContinuousLinearMap.bilinearComp_apply /-
@[simp]
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl
#align continuous_linear_map.bilinear_comp_apply ContinuousLinearMap.bilinearComp_apply
-/

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

#print ContinuousLinearMap.deriv₂ /-
/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)
#align continuous_linear_map.deriv₂ ContinuousLinearMap.deriv₂
-/

#print ContinuousLinearMap.coe_deriv₂ /-
@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl
#align continuous_linear_map.coe_deriv₂ ContinuousLinearMap.coe_deriv₂
-/

#print ContinuousLinearMap.map_add_add /-
theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
#align continuous_linear_map.map_add_add ContinuousLinearMap.map_add_add
-/

end ContinuousLinearMap

end SemiNormed

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

section

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f g : E →SL[σ₁₂] F) (x y z : E)

namespace LinearMap

#print LinearMap.bound_of_shell /-
theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact
    SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (ne_of_lt (norm_pos_iff.2 hx)).symm
#align linear_map.bound_of_shell LinearMap.bound_of_shell
-/

#print LinearMap.bound_of_ball_bound /-
/-- `linear_map.bound_of_ball_bound'` is a version of this lemma over a field satisfying `is_R_or_C`
that produces a concrete bound.
-/
theorem bound_of_ball_bound {r : ℝ} (r_pos : 0 < r) (c : ℝ) (f : E →ₗ[𝕜] Fₗ)
    (h : ∀ z ∈ Metric.ball (0 : E) r, ‖f z‖ ≤ c) : ∃ C, ∀ z : E, ‖f z‖ ≤ C * ‖z‖ :=
  by
  cases' @NontriviallyNormedField.non_trivial 𝕜 _ with k hk
  use c * (‖k‖ / r)
  intro z
  refine' bound_of_shell _ r_pos hk (fun x hko hxo => _) _
  calc
    ‖f x‖ ≤ c := h _ (mem_ball_zero_iff.mpr hxo)
    _ ≤ c * (‖x‖ * ‖k‖ / r) := (le_mul_of_one_le_right _ _)
    _ = _ := by ring
  · exact le_trans (norm_nonneg _) (h 0 (by simp [r_pos]))
  · rw [div_le_iff (zero_lt_one.trans hk)] at hko
    exact (one_le_div r_pos).mpr hko
#align linear_map.bound_of_ball_bound LinearMap.bound_of_ball_bound
-/

#print LinearMap.antilipschitz_of_comap_nhds_le /-
theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f :=
  by
  rcases((nhds_basis_ball.comap _).le_basis_iffₓ nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine' ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => _⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 :=
      Specializes.eq
        (specializes_iff_pure.2 <|
          ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ ≤ ‖c ^ n‖⁻¹ * 1 := (mul_le_mul_of_nonneg_left (hε _ hlt).le (inv_nonneg.2 (norm_nonneg _)))
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]
#align linear_map.antilipschitz_of_comap_nhds_le LinearMap.antilipschitz_of_comap_nhds_le
-/

end LinearMap

namespace ContinuousLinearMap

section OpNorm

open Set Real

#print ContinuousLinearMap.opNorm_zero_iff /-
/-- An operator is zero iff its norm vanishes. -/
theorem opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ContinuousLinearMap.ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
            _ = _ := by rw [hn, MulZeroClass.zero_mul]))
    (by rintro rfl; exact op_norm_zero)
#align continuous_linear_map.op_norm_zero_iff ContinuousLinearMap.opNorm_zero_iff
-/

#print ContinuousLinearMap.norm_id /-
/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem norm_id [Nontrivial E] : ‖id 𝕜 E‖ = 1 :=
  by
  refine' norm_id_of_nontrivial_seminorm _
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩
#align continuous_linear_map.norm_id ContinuousLinearMap.norm_id
-/

#print ContinuousLinearMap.normOneClass /-
instance normOneClass [Nontrivial E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩
#align continuous_linear_map.norm_one_class ContinuousLinearMap.normOneClass
-/

#print ContinuousLinearMap.toNormedAddCommGroup /-
/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance toNormedAddCommGroup [RingHomIsometric σ₁₂] : NormedAddCommGroup (E →SL[σ₁₂] F) :=
  NormedAddCommGroup.ofSeparation fun f => (opNorm_zero_iff f).mp
#align continuous_linear_map.to_normed_add_comm_group ContinuousLinearMap.toNormedAddCommGroup
-/

#print ContinuousLinearMap.toNormedRing /-
/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance toNormedRing : NormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedAddCommGroup, ContinuousLinearMap.toSemiNormedRing with }
#align continuous_linear_map.to_normed_ring ContinuousLinearMap.toNormedRing
-/

variable {f}

#print ContinuousLinearMap.homothety_norm /-
theorem homothety_norm [RingHomIsometric σ₁₂] [Nontrivial E] (f : E →SL[σ₁₂] F) {a : ℝ}
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : ‖f‖ = a :=
  by
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  rw [← norm_pos_iff] at hx
  have ha : 0 ≤ a := by simpa only [hf, hx, mul_nonneg_iff_of_pos_right] using norm_nonneg (f x)
  apply le_antisymm (f.op_norm_le_bound ha fun y => le_of_eq (hf y))
  simpa only [hf, hx, mul_le_mul_right] using f.le_op_norm x
#align continuous_linear_map.homothety_norm ContinuousLinearMap.homothety_norm
-/

variable (f)

#print ContinuousLinearMap.antilipschitz_of_embedding /-
/-- If a continuous linear map is a topology embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_embedding (f : E →L[𝕜] Fₗ) (hf : Embedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge
#align continuous_linear_map.antilipschitz_of_embedding ContinuousLinearMap.antilipschitz_of_embedding
-/

section Completeness

open scoped Topology

open Filter

variable {E' : Type _} [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [RingHomIsometric σ₁₂]

#print ContinuousLinearMap.ofMemClosureImageCoeBounded /-
/-- Construct a bundled continuous (semi)linear map from a map `f : E → F` and a proof of the fact
that it belongs to the closure of the image of a bounded set `s : set (E →SL[σ₁₂] F)` under coercion
to function. Coercion to function of the result is definitionally equal to `f`. -/
@[simps (config := { fullyApplied := false }) apply]
def ofMemClosureImageCoeBounded (f : E' → F) {s : Set (E' →SL[σ₁₂] F)} (hs : Bounded s)
    (hf : f ∈ closure ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s)) : E' →SL[σ₁₂] F :=
  by
  -- `f` is a linear map due to `linear_map_of_mem_closure_range_coe`
  refine' (linearMapOfMemClosureRangeCoe f _).mkContinuousOfExistsBound _
  · refine' closure_mono (image_subset_iff.2 fun g hg => _) hf; exact ⟨g, rfl⟩
  · -- We need to show that `f` has bounded norm. Choose `C` such that `‖g‖ ≤ C` for all `g ∈ s`.
    rcases isBounded_iff_forall_norm_le.1 hs with ⟨C, hC⟩
    -- Then `‖g x‖ ≤ C * ‖x‖` for all `g ∈ s`, `x : E`, hence `‖f x‖ ≤ C * ‖x‖` for all `x`.
    have : ∀ x, IsClosed {g : E' → F | ‖g x‖ ≤ C * ‖x‖} := fun x =>
      is_closed_Iic.preimage (@continuous_apply E' (fun _ => F) _ x).norm
    refine' ⟨C, fun x => (this x).closure_subset_iff.2 (image_subset_iff.2 fun g hg => _) hf⟩
    exact g.le_of_op_norm_le (hC _ hg) _
#align continuous_linear_map.of_mem_closure_image_coe_bounded ContinuousLinearMap.ofMemClosureImageCoeBounded
-/

#print ContinuousLinearMap.ofTendstoOfBoundedRange /-
/-- Let `f : E → F` be a map, let `g : α → E →SL[σ₁₂] F` be a family of continuous (semi)linear maps
that takes values in a bounded set and converges to `f` pointwise along a nontrivial filter. Then
`f` is a continuous (semi)linear map. -/
@[simps (config := { fullyApplied := false }) apply]
def ofTendstoOfBoundedRange {α : Type _} {l : Filter α} [l.ne_bot] (f : E' → F)
    (g : α → E' →SL[σ₁₂] F) (hf : Tendsto (fun a x => g a x) l (𝓝 f)) (hg : Bounded (Set.range g)) :
    E' →SL[σ₁₂] F :=
  ofMemClosureImageCoeBounded f hg <|
    mem_closure_of_tendsto hf <|
      eventually_of_forall fun a => mem_image_of_mem _ <| Set.mem_range_self _
#align continuous_linear_map.of_tendsto_of_bounded_range ContinuousLinearMap.ofTendstoOfBoundedRange
-/

#print ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq /-
/-- If a Cauchy sequence of continuous linear map converges to a continuous linear map pointwise,
then it converges to the same map in norm. This lemma is used to prove that the space of continuous
linear maps is complete provided that the codomain is a complete space. -/
theorem tendsto_of_tendsto_pointwise_of_cauchySeq {f : ℕ → E' →SL[σ₁₂] F} {g : E' →SL[σ₁₂] F}
    (hg : Tendsto (fun n x => f n x) atTop (𝓝 g)) (hf : CauchySeq f) : Tendsto f atTop (𝓝 g) :=
  by
  /- Since `f` is a Cauchy sequence, there exists `b → 0` such that `‖f n - f m‖ ≤ b N` for any
    `m, n ≥ N`. -/
  rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, hb₀, hfb, hb_lim⟩
  -- Since `b → 0`, it suffices to show that `‖f n x - g x‖ ≤ b n * ‖x‖` for all `n` and `x`.
  suffices : ∀ n x, ‖f n x - g x‖ ≤ b n * ‖x‖
  exact
    tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun n => norm_nonneg _) (fun n => op_norm_le_bound _ (hb₀ n) (this n)) hb_lim)
  intro n x
  -- Note that `f m x → g x`, hence `‖f n x - f m x‖ → ‖f n x - g x‖` as `m → ∞`
  have : tendsto (fun m => ‖f n x - f m x‖) at_top (𝓝 ‖f n x - g x‖) :=
    (tendsto_const_nhds.sub <| tendsto_pi_nhds.1 hg _).norm
  -- Thus it suffices to verify `‖f n x - f m x‖ ≤ b n * ‖x‖` for `m ≥ n`.
  refine' le_of_tendsto this (eventually_at_top.2 ⟨n, fun m hm => _⟩)
  -- This inequality follows from `‖f n - f m‖ ≤ b n`.
  exact (f n - f m).le_of_opNorm_le (hfb _ _ _ le_rfl hm) _
#align continuous_linear_map.tendsto_of_tendsto_pointwise_of_cauchy_seq ContinuousLinearMap.tendsto_of_tendsto_pointwise_of_cauchySeq
-/

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. This works also if the source space is seminormed. -/
instance [CompleteSpace F] : CompleteSpace (E' →SL[σ₁₂] F) :=
  by
  -- We show that every Cauchy sequence converges.
  refine' Metric.complete_of_cauchySeq_tendsto fun f hf => _
  -- The evaluation at any point `v : E` is Cauchy.
  have cau : ∀ v, CauchySeq fun n => f n v := fun v => hf.map (lipschitz_apply v).UniformContinuous
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `F` is complete)
  -- into a function which we call `G`.
  choose G hG using fun v => cauchySeq_tendsto_of_complete (cau v)
  -- Next, we show that this `G` is a continuous linear map.
  -- This is done in `continuous_linear_map.of_tendsto_of_bounded_range`.
  set Glin : E' →SL[σ₁₂] F :=
    of_tendsto_of_bounded_range _ _ (tendsto_pi_nhds.mpr hG) hf.bounded_range
  -- Finally, `f n` converges to `Glin` in norm because of
  -- `continuous_linear_map.tendsto_of_tendsto_pointwise_of_cauchy_seq`
  exact ⟨Glin, tendsto_of_tendsto_pointwise_of_cauchy_seq (tendsto_pi_nhds.2 hG) hf⟩

#print ContinuousLinearMap.isCompact_closure_image_coe_of_bounded /-
/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. Then `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is precompact: its closure is a compact set. -/
theorem isCompact_closure_image_coe_of_bounded [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : Bounded s) : IsCompact (closure ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s)) :=
  have : ∀ x, IsCompact (closure (apply' F σ₁₂ x '' s)) := fun x =>
    ((apply' F σ₁₂ x).lipschitz.isBounded_image hb).isCompact_closure
  IsCompact.closure_of_subset (isCompact_pi_infinite this)
    (image_subset_iff.2 fun g hg x => subset_closure <| mem_image_of_mem _ hg)
#align continuous_linear_map.is_compact_closure_image_coe_of_bounded ContinuousLinearMap.isCompact_closure_image_coe_of_bounded
-/

#print ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image /-
/-- Let `s` be a bounded set in the space of continuous (semi)linear maps `E →SL[σ] F` taking values
in a proper space. If `s` interpreted as a set in the space of maps `E → F` with topology of
pointwise convergence is closed, then it is compact.

TODO: reformulate this in terms of a type synonym with the right topology. -/
theorem isCompact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : Bounded s) (hc : IsClosed ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s)) :
    IsCompact ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  hc.closure_eq ▸ isCompact_closure_image_coe_of_bounded hb
#align continuous_linear_map.is_compact_image_coe_of_bounded_of_closed_image ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image
-/

#print ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed /-
/-- If a set `s` of semilinear functions is bounded and is closed in the weak-* topology, then its
image under coercion to functions `E → F` is a closed set. We don't have a name for `E →SL[σ] F`
with weak-* topology in `mathlib`, so we use an equivalent condition (see `is_closed_induced_iff'`).

TODO: reformulate this in terms of a type synonym with the right topology. -/
theorem isClosed_image_coe_of_bounded_of_weak_closed {s : Set (E' →SL[σ₁₂] F)} (hb : Bounded s)
    (hc : ∀ f, (⇑f : E' → F) ∈ closure ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsClosed ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isClosed_of_closure_subset fun f hf =>
    ⟨ofMemClosureImageCoeBounded f hb hf, hc (ofMemClosureImageCoeBounded f hb hf) hf, rfl⟩
#align continuous_linear_map.is_closed_image_coe_of_bounded_of_weak_closed ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed
-/

#print ContinuousLinearMap.isCompact_image_coe_of_bounded_of_weak_closed /-
/-- If a set `s` of semilinear functions is bounded and is closed in the weak-* topology, then its
image under coercion to functions `E → F` is a compact set. We don't have a name for `E →SL[σ] F`
with weak-* topology in `mathlib`, so we use an equivalent condition (see `is_closed_induced_iff'`).
-/
theorem isCompact_image_coe_of_bounded_of_weak_closed [ProperSpace F] {s : Set (E' →SL[σ₁₂] F)}
    (hb : Bounded s)
    (hc : ∀ f, (⇑f : E' → F) ∈ closure ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s) → f ∈ s) :
    IsCompact ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' s) :=
  isCompact_image_coe_of_bounded_of_closed_image hb <|
    isClosed_image_coe_of_bounded_of_weak_closed hb hc
#align continuous_linear_map.is_compact_image_coe_of_bounded_of_weak_closed ContinuousLinearMap.isCompact_image_coe_of_bounded_of_weak_closed
-/

#print ContinuousLinearMap.is_weak_closed_closedBall /-
/-- A closed ball is closed in the weak-* topology. We don't have a name for `E →SL[σ] F` with
weak-* topology in `mathlib`, so we use an equivalent condition (see `is_closed_induced_iff'`). -/
theorem is_weak_closed_closedBall (f₀ : E' →SL[σ₁₂] F) (r : ℝ) ⦃f : E' →SL[σ₁₂] F⦄
    (hf : ⇑f ∈ closure ((coeFn : (E' →SL[σ₁₂] F) → E' → F) '' closedBall f₀ r)) :
    f ∈ closedBall f₀ r :=
  by
  have hr : 0 ≤ r := nonempty_closed_ball.1 (nonempty_image_iff.1 (closure_nonempty_iff.1 ⟨_, hf⟩))
  refine' mem_closedBall_iff_norm.2 (op_norm_le_bound _ hr fun x => _)
  have : IsClosed {g : E' → F | ‖g x - f₀ x‖ ≤ r * ‖x‖} :=
    is_closed_Iic.preimage ((@continuous_apply E' (fun _ => F) _ x).sub continuous_const).norm
  refine' this.closure_subset_iff.2 (image_subset_iff.2 fun g hg => _) hf
  exact (g - f₀).le_of_opNorm_le (mem_closedBall_iff_norm.1 hg) _
#align continuous_linear_map.is_weak_closed_closed_ball ContinuousLinearMap.is_weak_closed_closedBall
-/

#print ContinuousLinearMap.isClosed_image_coe_closedBall /-
/-- The set of functions `f : E → F` that represent continuous linear maps `f : E →SL[σ₁₂] F`
at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is closed in the topology of pointwise convergence.
This is one of the key steps in the proof of the **Banach-Alaoglu** theorem. -/
theorem isClosed_image_coe_closedBall (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsClosed ((coeFn : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isClosed_image_coe_of_bounded_of_weak_closed isBounded_closedBall (is_weak_closed_closedBall f₀ r)
#align continuous_linear_map.is_closed_image_coe_closed_ball ContinuousLinearMap.isClosed_image_coe_closedBall
-/

#print ContinuousLinearMap.isCompact_image_coe_closedBall /-
/-- **Banach-Alaoglu** theorem. The set of functions `f : E → F` that represent continuous linear
maps `f : E →SL[σ₁₂] F` at distance `≤ r` from `f₀ : E →SL[σ₁₂] F` is compact in the topology of
pointwise convergence. Other versions of this theorem can be found in
`analysis.normed_space.weak_dual`. -/
theorem isCompact_image_coe_closedBall [ProperSpace F] (f₀ : E →SL[σ₁₂] F) (r : ℝ) :
    IsCompact ((coeFn : (E →SL[σ₁₂] F) → E → F) '' closedBall f₀ r) :=
  isCompact_image_coe_of_bounded_of_weak_closed isBounded_closedBall <|
    is_weak_closed_closedBall f₀ r
#align continuous_linear_map.is_compact_image_coe_closed_ball ContinuousLinearMap.isCompact_image_coe_closedBall
-/

end Completeness

section UniformlyExtend

variable [CompleteSpace F] (e : E →L[𝕜] Fₗ) (h_dense : DenseRange e)

section

variable (h_e : UniformInducing e)

#print ContinuousLinearMap.extend /-
/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] Fₗ`.  -/
def extend : Fₗ →SL[σ₁₂] F :=
  have cont :=
    (-- extension of `f` is continuous
        uniformContinuous_uniformly_extend
        h_e h_dense f.UniformContinuous).Continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h_e h_dense f.UniformContinuous
  { toFun := (h_e.DenseInducing h_dense).extend f
    map_add' := by
      refine' h_dense.induction_on₂ _ _
      ·
        exact
          isClosed_eq (cont.comp continuous_add)
            ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y; simp only [Eq, ← e.map_add]; exact f.map_add _ _
    map_smul' := fun k => by
      refine' fun b => h_dense.induction_on b _ _
      ·
        exact
          isClosed_eq (cont.comp (continuous_const_smul _)) ((continuous_const_smul _).comp Cont)
      · intro x; rw [← map_smul]; simp only [Eq]; exact ContinuousLinearMap.map_smulₛₗ _ _ _
    cont }
#align continuous_linear_map.extend ContinuousLinearMap.extend
-/

#print ContinuousLinearMap.extend_eq /-
@[simp]
theorem extend_eq (x : E) : extend f e h_dense h_e (e x) = f x :=
  DenseInducing.extend_eq _ f.cont _
#align continuous_linear_map.extend_eq ContinuousLinearMap.extend_eq
-/

#print ContinuousLinearMap.extend_unique /-
theorem extend_unique (g : Fₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.Continuous
#align continuous_linear_map.extend_unique ContinuousLinearMap.extend_unique
-/

#print ContinuousLinearMap.extend_zero /-
@[simp]
theorem extend_zero : extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)
#align continuous_linear_map.extend_zero ContinuousLinearMap.extend_zero
-/

end

section

variable {N : ℝ≥0} (h_e : ∀ x, ‖x‖ ≤ N * ‖e x‖) [RingHomIsometric σ₁₂]

local notation "ψ" => f.extend e h_dense (uniformEmbedding_of_bound _ h_e).to_uniformInducing

#print ContinuousLinearMap.opNorm_extend_le /-
/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ‖f‖`. -/
theorem opNorm_extend_le : ‖ψ‖ ≤ N * ‖f‖ :=
  by
  have uni : UniformInducing e := (uniform_embedding_of_bound _ h_e).to_uniformInducing
  have eq : ∀ x, ψ (e x) = f x := uniformly_extend_of_ind uni h_dense f.uniform_continuous
  by_cases N0 : 0 ≤ N
  · refine' op_norm_le_bound ψ _ (isClosed_property h_dense (isClosed_le _ _) _)
    · exact mul_nonneg N0 (norm_nonneg _)
    · exact continuous_norm.comp (Cont ψ)
    · exact continuous_const.mul continuous_norm
    · intro x
      rw [Eq]
      calc
        ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
        _ ≤ ‖f‖ * (N * ‖e x‖) := (mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _))
        _ ≤ N * ‖f‖ * ‖e x‖ := by rw [mul_comm ↑N ‖f‖, mul_assoc]
  · have he : ∀ x : E, x = 0 := by
      intro x
      have N0 : N ≤ 0 := le_of_lt (lt_of_not_ge N0)
      rw [← norm_le_zero_iff]
      exact le_trans (h_e x) (mul_nonpos_of_nonpos_of_nonneg N0 (norm_nonneg _))
    have hf : f = 0 := by ext; simp only [he x, zero_apply, map_zero]
    have hψ : ψ = 0 := by rw [hf]; apply extend_zero
    rw [hψ, hf, norm_zero, norm_zero, MulZeroClass.mul_zero]
#align continuous_linear_map.op_norm_extend_le ContinuousLinearMap.opNorm_extend_le
-/

end

end UniformlyExtend

end OpNorm

end ContinuousLinearMap

namespace LinearIsometry

#print LinearIsometry.norm_toContinuousLinearMap /-
@[simp]
theorem norm_toContinuousLinearMap [Nontrivial E] [RingHomIsometric σ₁₂] (f : E →ₛₗᵢ[σ₁₂] F) :
    ‖f.toContinuousLinearMap‖ = 1 :=
  f.toContinuousLinearMap.homothety_norm <| by simp
#align linear_isometry.norm_to_continuous_linear_map LinearIsometry.norm_toContinuousLinearMap
-/

variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

#print LinearIsometry.norm_toContinuousLinearMap_comp /-
/-- Postcomposition of a continuous linear map with a linear isometry preserves
the operator norm. -/
theorem norm_toContinuousLinearMap_comp [RingHomIsometric σ₁₂] (f : F →ₛₗᵢ[σ₂₃] G)
    {g : E →SL[σ₁₂] F} : ‖f.toContinuousLinearMap.comp g‖ = ‖g‖ :=
  opNorm_ext (f.toContinuousLinearMap.comp g) g fun x => by
    simp only [norm_map, coe_to_continuous_linear_map, coe_comp']
#align linear_isometry.norm_to_continuous_linear_map_comp LinearIsometry.norm_toContinuousLinearMap_comp
-/

end LinearIsometry

end

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ] (c : 𝕜)
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

variable {𝕜₂' : Type _} [NontriviallyNormedField 𝕜₂'] {F' : Type _} [NormedAddCommGroup F']
  [NormedSpace 𝕜₂' F'] {σ₂' : 𝕜₂' →+* 𝕜₂} {σ₂'' : 𝕜₂ →+* 𝕜₂'} {σ₂₃' : 𝕜₂' →+* 𝕜₃}
  [RingHomInvPair σ₂' σ₂''] [RingHomInvPair σ₂'' σ₂'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomCompTriple σ₂'' σ₂₃' σ₂₃] [RingHomIsometric σ₂₃] [RingHomIsometric σ₂']
  [RingHomIsometric σ₂''] [RingHomIsometric σ₂₃']

#print ContinuousLinearMap.opNorm_comp_linearIsometryEquiv /-
/-- Precomposition with a linear isometry preserves the operator norm. -/
theorem opNorm_comp_linearIsometryEquiv (f : F →SL[σ₂₃] G) (g : F' ≃ₛₗᵢ[σ₂'] F) :
    ‖f.comp g.toLinearIsometry.toContinuousLinearMap‖ = ‖f‖ :=
  by
  cases subsingleton_or_nontrivial F'
  · haveI := g.symm.to_linear_equiv.to_equiv.subsingleton
    simp
  refine' le_antisymm _ _
  · convert f.op_norm_comp_le g.to_linear_isometry.to_continuous_linear_map
    simp [g.to_linear_isometry.norm_to_continuous_linear_map]
  · convert
      (f.comp g.to_linear_isometry.to_continuous_linear_map).opNorm_comp_le
        g.symm.to_linear_isometry.to_continuous_linear_map
    · ext
      simp
    haveI := g.symm.surjective.nontrivial
    simp [g.symm.to_linear_isometry.norm_to_continuous_linear_map]
#align continuous_linear_map.op_norm_comp_linear_isometry_equiv ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
-/

#print ContinuousLinearMap.norm_smulRight_apply /-
/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
theorem norm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ :=
  by
  refine' le_antisymm _ _
  · apply op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => _
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := (mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _))
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · by_cases h : f = 0
    · simp [h]
    · have : 0 < ‖f‖ := norm_pos_iff.2 h
      rw [← le_div_iff this]
      apply op_norm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) fun x => _
      rw [div_mul_eq_mul_div, le_div_iff this]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smul_right c f x‖ := rfl
        _ ≤ ‖smul_right c f‖ * ‖x‖ := le_op_norm _ _
#align continuous_linear_map.norm_smul_right_apply ContinuousLinearMap.norm_smulRight_apply
-/

#print ContinuousLinearMap.nnnorm_smulRight_apply /-
/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
theorem nnnorm_smulRight_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f
#align continuous_linear_map.nnnorm_smul_right_apply ContinuousLinearMap.nnnorm_smulRight_apply
-/

variable (𝕜 E Fₗ)

#print ContinuousLinearMap.smulRightL /-
/-- `continuous_linear_map.smul_right` as a continuous trilinear map:
`smul_rightL (c : E →L[𝕜] 𝕜) (f : F) (x : E) = c x • f`. -/
def smulRightL : (E →L[𝕜] 𝕜) →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by ext x;
        simp only [add_smul, coe_smul_rightₗ, add_apply, smul_right_apply, LinearMap.add_apply]
      map_smul' := fun m c => by ext x;
        simp only [smul_smul, coe_smul_rightₗ, Algebra.id.smul_eq_mul, coe_smul', smul_right_apply,
          LinearMap.smul_apply, RingHom.id_apply, Pi.smul_apply] }
    1 fun c x => by simp only [coe_smul_rightₗ, one_mul, norm_smul_right_apply, LinearMap.coe_mk]
#align continuous_linear_map.smul_rightL ContinuousLinearMap.smulRightL
-/

variable {𝕜 E Fₗ}

#print ContinuousLinearMap.norm_smulRightL_apply /-
@[simp]
theorem norm_smulRightL_apply (c : E →L[𝕜] 𝕜) (f : Fₗ) : ‖smulRightL 𝕜 E Fₗ c f‖ = ‖c‖ * ‖f‖ :=
  norm_smulRight_apply c f
#align continuous_linear_map.norm_smul_rightL_apply ContinuousLinearMap.norm_smulRightL_apply
-/

#print ContinuousLinearMap.norm_smulRightL /-
@[simp]
theorem norm_smulRightL (c : E →L[𝕜] 𝕜) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply
#align continuous_linear_map.norm_smul_rightL ContinuousLinearMap.norm_smulRightL
-/

variable (𝕜) (𝕜' : Type _)

section

variable [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

@[simp]
theorem opNorm_mul [NormOneClass 𝕜'] : ‖mul 𝕜 𝕜'‖ = 1 :=
  haveI := NormOneClass.nontrivial 𝕜'
  (mulₗᵢ 𝕜 𝕜').norm_toContinuousLinearMap
#align continuous_linear_map.op_norm_mul ContinuousLinearMap.opNorm_mulₓ

end

#print ContinuousLinearMap.opNorm_lsmul /-
/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `continuous_linear_map.op_norm_lsmul_le` as an equality. -/
@[simp]
theorem opNorm_lsmul [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
    [Nontrivial E] : ‖(lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E)‖ = 1 :=
  by
  refine' ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => _) fun N hN h => _
  · rw [one_mul]
    exact op_norm_lsmul_apply_le _
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have := le_of_op_norm_le _ (h 1) y
  simp_rw [lsmul_apply, one_smul, norm_one, mul_one] at this
  refine' le_of_mul_le_mul_right _ (norm_pos_iff.mpr hy)
  simp_rw [one_mul, this]
#align continuous_linear_map.op_norm_lsmul ContinuousLinearMap.opNorm_lsmul
-/

end ContinuousLinearMap

namespace Submodule

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}

#print Submodule.norm_subtypeL /-
theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ‖K.subtypeL‖ = 1 :=
  K.subtypeₗᵢ.norm_toContinuousLinearMap
#align submodule.norm_subtypeL Submodule.norm_subtypeL
-/

end Submodule

namespace ContinuousLinearEquiv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂]

section

variable [RingHomIsometric σ₂₁]

#print ContinuousLinearEquiv.antilipschitz /-
protected theorem antilipschitz (e : E ≃SL[σ₁₂] F) :
    AntilipschitzWith ‖(e.symm : F →SL[σ₂₁] E)‖₊ e :=
  e.symm.lipschitz.to_rightInverse e.left_inv
#align continuous_linear_equiv.antilipschitz ContinuousLinearEquiv.antilipschitz
-/

#print ContinuousLinearEquiv.one_le_norm_mul_norm_symm /-
theorem one_le_norm_mul_norm_symm [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    1 ≤ ‖(e : E →SL[σ₁₂] F)‖ * ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  by
  rw [mul_comm]
  convert (e.symm : F →SL[σ₂₁] E).opNorm_comp_le (e : E →SL[σ₁₂] F)
  rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]
#align continuous_linear_equiv.one_le_norm_mul_norm_symm ContinuousLinearEquiv.one_le_norm_mul_norm_symm
-/

#print ContinuousLinearEquiv.norm_pos /-
theorem norm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e : E →SL[σ₁₂] F)‖ :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_pos ContinuousLinearEquiv.norm_pos
-/

#print ContinuousLinearEquiv.norm_symm_pos /-
theorem norm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  pos_of_mul_pos_right (zero_lt_one.trans_le e.one_le_norm_mul_norm_symm) (norm_nonneg _)
#align continuous_linear_equiv.norm_symm_pos ContinuousLinearEquiv.norm_symm_pos
-/

#print ContinuousLinearEquiv.nnnorm_symm_pos /-
theorem nnnorm_symm_pos [RingHomIsometric σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) :
    0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  e.norm_symm_pos
#align continuous_linear_equiv.nnnorm_symm_pos ContinuousLinearEquiv.nnnorm_symm_pos
-/

#print ContinuousLinearEquiv.subsingleton_or_norm_symm_pos /-
theorem subsingleton_or_norm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖ :=
  by
  rcases subsingleton_or_nontrivial E with (_i | _i) <;> skip
  · left; infer_instance
  · right; exact e.norm_symm_pos
#align continuous_linear_equiv.subsingleton_or_norm_symm_pos ContinuousLinearEquiv.subsingleton_or_norm_symm_pos
-/

#print ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos /-
theorem subsingleton_or_nnnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) :
    Subsingleton E ∨ 0 < ‖(e.symm : F →SL[σ₂₁] E)‖₊ :=
  subsingleton_or_norm_symm_pos e
#align continuous_linear_equiv.subsingleton_or_nnnorm_symm_pos ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos
-/

variable (𝕜)

#print ContinuousLinearEquiv.coord_norm /-
@[simp]
theorem coord_norm (x : E) (h : x ≠ 0) : ‖coord 𝕜 x h‖ = ‖x‖⁻¹ :=
  by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
  haveI : Nontrivial (𝕜 ∙ x) := Submodule.nontrivial_span_singleton h
  exact
    ContinuousLinearMap.homothety_norm _ fun y =>
      homothety_inverse _ hx _ (to_span_nonzero_singleton_homothety 𝕜 x h) _
#align continuous_linear_equiv.coord_norm ContinuousLinearEquiv.coord_norm
-/

end

end ContinuousLinearEquiv

end Normed

#print IsCoercive /-
/-- A bounded bilinear form `B` in a real normed space is *coercive*
if there is some positive constant C such that `C * ‖u‖ * ‖u‖ ≤ B u u`.
-/
def IsCoercive [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∃ C, 0 < C ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u
#align is_coercive IsCoercive
-/

