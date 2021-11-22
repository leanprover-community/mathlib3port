import Mathbin.Algebra.Algebra.Tower 
import Mathbin.Analysis.NormedSpace.LinearIsometry 
import Mathbin.Analysis.NormedSpace.RieszLemma

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory for `semi_normed_space` and we specialize to `normed_space` at the end.

## TODO

* Only the `normed_field` section applies to semilinear maps; the rest still only applies to
  plain linear maps.
-/


noncomputable theory

open_locale Classical Nnreal TopologicalSpace

variable{𝕜 𝕜₂ : Type _}{E : Type _}{F : Type _}{G : Type _}

section SemiNormed

variable[SemiNormedGroup E][SemiNormedGroup F][SemiNormedGroup G]

open Metric ContinuousLinearMap

section NormedField

/-! Most statements in this file require the field to be non-discrete,
as this is necessary to deduce an inequality `∥f x∥ ≤ C ∥x∥` from the continuity of f.
However, the other direction always holds.
In this section, we just assume that `𝕜` is a normed field.
In the remainder of the file, it will be non-discrete. -/


variable[NormedField 𝕜][NormedField 𝕜₂][SemiNormedSpace 𝕜 E][SemiNormedSpace 𝕜₂ F]

variable[SemiNormedSpace 𝕜 G]{σ : 𝕜 →+* 𝕜₂}(f : E →ₛₗ[σ] F)

theorem LinearMap.lipschitz_of_bound (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : LipschitzWith (Real.toNnreal C) f :=
  f.to_add_monoid_hom.lipschitz_of_bound C h

theorem LinearMap.lipschitz_of_bound_nnnorm (C :  ℝ≥0 ) (h : ∀ x, ∥f x∥₊ ≤ C*∥x∥₊) : LipschitzWith C f :=
  f.to_add_monoid_hom.lipschitz_of_bound_nnnorm C h

theorem LinearMap.antilipschitz_of_bound {K :  ℝ≥0 } (h : ∀ x, ∥x∥ ≤ K*∥f x∥) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist$
    fun x y =>
      by 
        simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem LinearMap.bound_of_antilipschitz {K :  ℝ≥0 } (h : AntilipschitzWith K f) x : ∥x∥ ≤ K*∥f x∥ :=
  by 
    simpa only [dist_zero_right, f.map_zero] using h.le_mul_dist x 0

theorem LinearMap.uniform_continuous_of_bound (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : UniformContinuous f :=
  (f.lipschitz_of_bound C h).UniformContinuous

theorem LinearMap.continuous_of_bound (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : Continuous f :=
  (f.lipschitz_of_bound C h).Continuous

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : E →SL[σ] F :=
  ⟨f, LinearMap.continuous_of_bound f C h⟩

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mk_continuous ∥f 1∥$
    fun x =>
      le_of_eqₓ$
        by 
          convLHS => rw [←mul_oneₓ x]
          rw [←smul_eq_mul, f.map_smul, norm_smul, mul_commₓ]

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ∥f x∥ ≤ C*∥x∥) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h 
    LinearMap.continuous_of_bound f C hC⟩

theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x+y) = f x+f y)
  (h_smul : ∀ c : 𝕜 x, f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ∥f x∥ ≤ C*∥x∥) : Continuous f :=
  let φ : E →ₛₗ[σ] F := { toFun := f, map_add' := h_add, map_smul' := h_smul }
  φ.continuous_of_bound C h_bound

theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x+y) = f x+f y)
  (h_smul : ∀ c : 𝕜 x, f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ∥f x∥ ≤ C*∥x∥) : Continuous f :=
  let φ : E →ₗ[𝕜] G := { toFun := f, map_add' := h_add, map_smul' := h_smul }
  φ.continuous_of_bound C h_bound

@[simp, normCast]
theorem LinearMap.mk_continuous_coe (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : (f.mk_continuous C h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
theorem LinearMap.mk_continuous_apply (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) (x : E) : f.mk_continuous C h x = f x :=
  rfl

@[simp, normCast]
theorem LinearMap.mk_continuous_of_exists_bound_coe (h : ∃ C, ∀ x, ∥f x∥ ≤ C*∥x∥) :
  (f.mk_continuous_of_exists_bound h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
theorem LinearMap.mk_continuous_of_exists_bound_apply (h : ∃ C, ∀ x, ∥f x∥ ≤ C*∥x∥) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x :=
  rfl

@[simp]
theorem LinearMap.to_continuous_linear_map₁_coe (f : 𝕜 →ₗ[𝕜] E) : (f.to_continuous_linear_map₁ : 𝕜 →ₗ[𝕜] E) = f :=
  rfl

@[simp]
theorem LinearMap.to_continuous_linear_map₁_apply (f : 𝕜 →ₗ[𝕜] E) x : f.to_continuous_linear_map₁ x = f x :=
  rfl

end NormedField

variable[NondiscreteNormedField
      𝕜][SemiNormedSpace 𝕜
      E][SemiNormedSpace 𝕜 F][SemiNormedSpace 𝕜 G](c : 𝕜)(f g : E →L[𝕜] F)(h : F →L[𝕜] G)(x y z : E)

include 𝕜

theorem LinearMap.bound_of_shell_semi_normed (f : E →ₗ[𝕜] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ∥c∥)
  (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C*∥x∥) {x : E} (hx : ∥x∥ ≠ 0) : ∥f x∥ ≤ C*∥x∥ :=
  by 
    rcases rescale_to_shell_semi_normed hc ε_pos hx with ⟨δ, hδ, δxle, leδx, δinv⟩
    simpa only [f.map_smul, norm_smul, mul_left_commₓ C, mul_le_mul_left (norm_pos_iff.2 hδ)] using hf (δ • x) leδx δxle

/-- If `∥x∥ = 0` and `f` is continuous then `∥f x∥ = 0`. -/
theorem norm_image_of_norm_zero {f : E →ₗ[𝕜] F} (hf : Continuous f) {x : E} (hx : ∥x∥ = 0) : ∥f x∥ = 0 :=
  by 
    refine' le_antisymmₓ (le_of_forall_pos_le_add fun ε hε => _) (norm_nonneg (f x))
    rcases NormedGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) ε hε with ⟨δ, δ_pos, hδ⟩
    replace hδ := hδ x 
    rw [sub_zero, hx] at hδ 
    replace hδ := le_of_ltₓ (hδ δ_pos)
    rw [LinearMap.map_zero, sub_zero] at hδ 
    rwa [zero_addₓ]

/-- A continuous linear map between seminormed spaces is bounded when the field is nondiscrete. The
continuity ensures boundedness on a ball of some radius `ε`. The nondiscreteness is then used to
rescale any element into an element of norm in `[ε/C, ε]`, whose image has a controlled norm. The
norm control for the original element follows by rescaling. -/
theorem LinearMap.bound_of_continuous (f : E →ₗ[𝕜] F) (hf : Continuous f) : ∃ C, 0 < C ∧ ∀ x : E, ∥f x∥ ≤ C*∥x∥ :=
  by 
    rcases NormedGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one with ⟨ε, ε_pos, hε⟩
    simp only [sub_zero, f.map_zero] at hε 
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    have  : 0 < ∥c∥ / ε 
    exact div_pos (zero_lt_one.trans hc) ε_pos 
    refine' ⟨∥c∥ / ε, this, fun x => _⟩
    byCases' hx : ∥x∥ = 0
    ·
      rw [hx, mul_zero]
      exact le_of_eqₓ (norm_image_of_norm_zero hf hx)
    refine' f.bound_of_shell_semi_normed ε_pos hc (fun x hle hlt => _) hx 
    refine' (hε _ hlt).le.trans _ 
    rwa [←div_le_iff' this, one_div_div]

namespace ContinuousLinearMap

theorem bound : ∃ C, 0 < C ∧ ∀ x : E, ∥f x∥ ≤ C*∥x∥ :=
  f.to_linear_map.bound_of_continuous f.2

section 

open Filter

/-- A linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def of_homothety (f : E →ₗ[𝕜] F) (a : ℝ) (hf : ∀ x, ∥f x∥ = a*∥x∥) : E →L[𝕜] F :=
  f.mk_continuous a fun x => le_of_eqₓ (hf x)

variable(𝕜)

theorem to_span_singleton_homothety (x : E) (c : 𝕜) : ∥LinearMap.toSpanSingleton 𝕜 E x c∥ = ∥x∥*∥c∥ :=
  by 
    rw [mul_commₓ]
    exact norm_smul _ _

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `E` to the span of `x`.-/
def to_span_singleton (x : E) : 𝕜 →L[𝕜] E :=
  of_homothety (LinearMap.toSpanSingleton 𝕜 E x) ∥x∥ (to_span_singleton_homothety 𝕜 x)

theorem to_span_singleton_apply (x : E) (r : 𝕜) : to_span_singleton 𝕜 x r = r • x :=
  by 
    simp [to_span_singleton, of_homothety, LinearMap.toSpanSingleton]

theorem to_span_singleton_add (x y : E) : to_span_singleton 𝕜 (x+y) = to_span_singleton 𝕜 x+to_span_singleton 𝕜 y :=
  by 
    ext1 
    simp [to_span_singleton_apply]

theorem to_span_singleton_smul' 𝕜' [NondiscreteNormedField 𝕜'] [SemiNormedSpace 𝕜' E] [SmulCommClass 𝕜 𝕜' E] (c : 𝕜')
  (x : E) : to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
  by 
    ext1 
    rw [to_span_singleton_apply, smul_apply, to_span_singleton_apply, smul_comm]

theorem to_span_singleton_smul (c : 𝕜) (x : E) : to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
  to_span_singleton_smul' 𝕜 𝕜 c x

end 

section OpNorm

open Set Real

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm :=
  Inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ }

instance has_op_norm : HasNorm (E →L[𝕜] F) :=
  ⟨op_norm⟩

theorem norm_def : ∥f∥ = Inf { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  rfl

theorem bounds_nonempty {f : E →L[𝕜] F} : ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_ltₓ hMp, hMb⟩

theorem bounds_bdd_below {f : E →L[𝕜] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c*∥x∥ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem op_norm_nonneg : 0 ≤ ∥f∥ :=
  le_cInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥*∥x∥ :=
  by 
    obtain ⟨C, Cpos, hC⟩ := f.bound 
    replace hC := hC x 
    byCases' h : ∥x∥ = 0
    ·
      rwa [h, mul_zero] at hC⊢
    have hlt : 0 < ∥x∥ := lt_of_le_of_neₓ (norm_nonneg x) (Ne.symm h)
    exact
      (div_le_iff hlt).mp
        (le_cInf bounds_nonempty
          fun c ⟨_, hc⟩ =>
            (div_le_iff hlt).mpr$
              by 
                apply hc)

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥*c :=
  le_transₓ (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : E) : ∥f x∥ ≤ c*∥x∥ :=
  (f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

theorem ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
  div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
  mul_oneₓ ∥f∥ ▸ f.le_op_norm_of_le

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M*∥x∥) : ∥f∥ ≤ M :=
  cInf_le bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_le_of_lipschitz {f : E →L[𝕜] F} {K :  ℝ≥0 } (hf : LipschitzWith K f) : ∥f∥ ≤ K :=
  f.op_norm_le_bound K.2$
    fun x =>
      by 
        simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

theorem op_norm_le_of_shell {f : E →L[𝕜] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜} (hc : 1 < ∥c∥)
  (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C*∥x∥) : ∥f∥ ≤ C :=
  by 
    refine' f.op_norm_le_bound hC fun x => _ 
    byCases' hx : ∥x∥ = 0
    ·
      rw [hx, mul_zero]
      exact le_of_eqₓ (norm_image_of_norm_zero f.2 hx)
    exact LinearMap.bound_of_shell_semi_normed f ε_pos hc hf hx

theorem op_norm_le_of_ball {f : E →L[𝕜] F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
  (hf : ∀ x _ : x ∈ ball (0 : E) ε, ∥f x∥ ≤ C*∥x∥) : ∥f∥ ≤ C :=
  by 
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    refine' op_norm_le_of_shell ε_pos hC hc fun x _ hx => hf x _ 
    rwa [ball_zero_eq]

theorem op_norm_le_of_nhds_zero {f : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ᶠx in 𝓝 (0 : E), ∥f x∥ ≤ C*∥x∥) : ∥f∥ ≤ C :=
  let ⟨ε, ε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 hf 
  op_norm_le_of_ball ε0 hC hε

theorem op_norm_le_of_shell' {f : E →L[𝕜] F} {ε C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜} (hc : ∥c∥ < 1)
  (hf : ∀ x, (ε*∥c∥) ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C*∥x∥) : ∥f∥ ≤ C :=
  by 
    byCases' h0 : c = 0
    ·
      refine' op_norm_le_of_ball ε_pos hC fun x hx => hf x _ _
      ·
        simp [h0]
      ·
        rwa [ball_zero_eq] at hx
    ·
      rw [←inv_inv₀ c, NormedField.norm_inv, inv_lt_one_iff_of_pos (norm_pos_iff.2$ inv_ne_zero h0)] at hc 
      refine' op_norm_le_of_shell ε_pos hC hc _ 
      rwa [NormedField.norm_inv, div_eq_mul_inv, inv_inv₀]

theorem op_norm_eq_of_bounds {φ : E →L[𝕜] F} {M : ℝ} (M_nonneg : 0 ≤ M) (h_above : ∀ x, ∥φ x∥ ≤ M*∥x∥)
  (h_below : ∀ N _ : N ≥ 0, (∀ x, ∥φ x∥ ≤ N*∥x∥) → M ≤ N) : ∥φ∥ = M :=
  le_antisymmₓ (φ.op_norm_le_bound M_nonneg h_above)
    ((le_cInf_iff ContinuousLinearMap.bounds_bdd_below ⟨M, M_nonneg, h_above⟩).mpr$
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f+g∥ ≤ ∥f∥+∥g∥ :=
  (f+g).op_norm_le_bound (add_nonneg f.op_norm_nonneg g.op_norm_nonneg)$
    fun x => (norm_add_le_of_le (f.le_op_norm x) (g.le_op_norm x)).trans_eq (add_mulₓ _ _ _).symm

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : E →L[𝕜] F)∥ = 0 :=
  le_antisymmₓ
    (cInf_le bounds_bdd_below
      ⟨ge_of_eq rfl,
        fun _ =>
          le_of_eqₓ
            (by 
              rw [zero_mul]
              exact norm_zero)⟩)
    (op_norm_nonneg _)

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le : ∥id 𝕜 E∥ ≤ 1 :=
  op_norm_le_bound _ zero_le_one
    fun x =>
      by 
        simp 

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
theorem norm_id_of_nontrivial_seminorm (h : ∃ x : E, ∥x∥ ≠ 0) : ∥id 𝕜 E∥ = 1 :=
  le_antisymmₓ norm_id_le$
    let ⟨x, hx⟩ := h 
    have  := (id 𝕜 E).ratio_le_op_norm x 
    by 
      rwa [id_apply, div_self hx] at this

theorem op_norm_smul_le {𝕜' : Type _} [NormedField 𝕜'] [SemiNormedSpace 𝕜' F] [SmulCommClass 𝕜 𝕜' F] (c : 𝕜')
  (f : E →L[𝕜] F) : ∥c • f∥ ≤ ∥c∥*∥f∥ :=
  (c • f).op_norm_le_bound (mul_nonneg (norm_nonneg _) (op_norm_nonneg _))
    fun _ =>
      by 
        erw [norm_smul, mul_assocₓ]
        exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)

theorem op_norm_neg : ∥-f∥ = ∥f∥ :=
  by 
    simp only [norm_def, neg_apply, norm_neg]

/-- Continuous linear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance to_semi_normed_group : SemiNormedGroup (E →L[𝕜] F) :=
  SemiNormedGroup.ofCore _ ⟨op_norm_zero, op_norm_add_le, op_norm_neg⟩

instance to_semi_normed_space {𝕜' : Type _} [NormedField 𝕜'] [SemiNormedSpace 𝕜' F] [SmulCommClass 𝕜 𝕜' F] :
  SemiNormedSpace 𝕜' (E →L[𝕜] F) :=
  ⟨op_norm_smul_le⟩

/-- The operator norm is submultiplicative. -/
theorem op_norm_comp_le (f : E →L[𝕜] F) : ∥h.comp f∥ ≤ ∥h∥*∥f∥ :=
  cInf_le bounds_bdd_below
    ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _),
      fun x =>
        by 
          rw [mul_assocₓ]
          exact h.le_op_norm_of_le (f.le_op_norm x)⟩

/-- Continuous linear maps form a seminormed ring with respect to the operator norm. -/
instance to_semi_normed_ring : SemiNormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toSemiNormedGroup with norm_mul := op_norm_comp_le }

theorem le_op_nnnorm : ∥f x∥₊ ≤ ∥f∥₊*∥x∥₊ :=
  f.le_op_norm x

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : LipschitzWith ∥f∥₊ f :=
  (f : E →ₗ[𝕜] F).lipschitz_of_bound_nnnorm _ f.le_op_nnnorm

theorem le_op_norm₂ (f : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) : ∥f x y∥ ≤ (∥f∥*∥x∥)*∥y∥ :=
  (f x).le_of_op_norm_le (f.le_op_norm x) y

theorem op_norm_le_bound₂ (f : E →L[𝕜] F →L[𝕜] G) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x y, ∥f x y∥ ≤ (C*∥x∥)*∥y∥) : ∥f∥ ≤ C :=
  f.op_norm_le_bound h0$ fun x => (f x).op_norm_le_bound (mul_nonneg h0 (norm_nonneg _))$ hC x

@[simp]
theorem op_norm_prod (f : E →L[𝕜] F) (g : E →L[𝕜] G) : ∥f.prod g∥ = ∥(f, g)∥ :=
  le_antisymmₓ
      (op_norm_le_bound _ (norm_nonneg _)$
        fun x =>
          by 
            simpa only [prod_apply, Prod.semi_norm_def, max_mul_of_nonneg, norm_nonneg] using
              max_le_max (le_op_norm f x) (le_op_norm g x))$
    max_leₓ (op_norm_le_bound _ (norm_nonneg _)$ fun x => (le_max_leftₓ _ _).trans ((f.prod g).le_op_norm x))
      (op_norm_le_bound _ (norm_nonneg _)$ fun x => (le_max_rightₓ _ _).trans ((f.prod g).le_op_norm x))

/-- `continuous_linear_map.prod` as a `linear_isometry_equiv`. -/
def prodₗᵢ (R : Type _) [Ringₓ R] [TopologicalSpace R] [Module R F] [Module R G] [HasContinuousSmul R F]
  [HasContinuousSmul R G] [SmulCommClass 𝕜 R F] [SmulCommClass 𝕜 R G] :
  (E →L[𝕜] F) × (E →L[𝕜] G) ≃ₗᵢ[R] E →L[𝕜] F × G :=
  ⟨prodₗ R, fun ⟨f, g⟩ => op_norm_prod f g⟩

/-- A continuous linear map is automatically uniformly continuous. -/
protected theorem UniformContinuous : UniformContinuous f :=
  f.lipschitz.uniform_continuous

@[simp, nontriviality]
theorem op_norm_subsingleton [Subsingleton E] : ∥f∥ = 0 :=
  by 
    refine' le_antisymmₓ _ (norm_nonneg _)
    apply op_norm_le_bound _ rfl.ge 
    intro x 
    simp [Subsingleton.elimₓ x 0]

/-- A continuous linear map is an isometry if and only if it preserves the norm.
(Note: Do you really want to use this lemma?  Try using the bundled structure `linear_isometry`
instead.) -/
theorem isometry_iff_norm : Isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ :=
  f.to_linear_map.to_add_monoid_hom.isometry_iff_norm

end OpNorm

section IsO

open Asymptotics

theorem is_O_with_id (l : Filter E) : is_O_with ∥f∥ f (fun x => x) l :=
  is_O_with_of_le' _ f.le_op_norm

theorem is_O_id (l : Filter E) : is_O f (fun x => x) l :=
  (f.is_O_with_id l).IsO

theorem is_O_with_comp {α : Type _} (g : F →L[𝕜] G) (f : α → F) (l : Filter α) :
  is_O_with ∥g∥ (fun x' => g (f x')) f l :=
  (g.is_O_with_id ⊤).comp_tendsto le_top

theorem is_O_comp {α : Type _} (g : F →L[𝕜] G) (f : α → F) (l : Filter α) : is_O (fun x' => g (f x')) f l :=
  (g.is_O_with_comp f l).IsO

theorem is_O_with_sub (f : E →L[𝕜] F) (l : Filter E) (x : E) :
  is_O_with ∥f∥ (fun x' => f (x' - x)) (fun x' => x' - x) l :=
  f.is_O_with_comp _ l

theorem is_O_sub (f : E →L[𝕜] F) (l : Filter E) (x : E) : is_O (fun x' => f (x' - x)) (fun x' => x' - x) l :=
  f.is_O_comp _ l

end IsO

end ContinuousLinearMap

namespace LinearIsometry

theorem norm_to_continuous_linear_map_le (f : E →ₗᵢ[𝕜] F) : ∥f.to_continuous_linear_map∥ ≤ 1 :=
  f.to_continuous_linear_map.op_norm_le_bound zero_le_one$
    fun x =>
      by 
        simp 

end LinearIsometry

namespace LinearMap

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mk_continuous_norm_le (f : E →ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ∥f x∥ ≤ C*∥x∥) :
  ∥f.mk_continuous C h∥ ≤ C :=
  ContinuousLinearMap.op_norm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mk_continuous_norm_le' (f : E →ₗ[𝕜] F) {C : ℝ} (h : ∀ x, ∥f x∥ ≤ C*∥x∥) : ∥f.mk_continuous C h∥ ≤ max C 0 :=
  ContinuousLinearMap.op_norm_le_bound _ (le_max_rightₓ _ _)$
    fun x => (h x).trans$ mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (norm_nonneg x)

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`linear_map.mk₂`. -/
def mk_continuous₂ (f : E →ₗ[𝕜] F →ₗ[𝕜] G) (C : ℝ) (hC : ∀ x y, ∥f x y∥ ≤ (C*∥x∥)*∥y∥) : E →L[𝕜] F →L[𝕜] G :=
  LinearMap.mkContinuous
      { toFun := fun x => (f x).mkContinuous (C*∥x∥) (hC x),
        map_add' :=
          fun x y =>
            by 
              ext z 
              simp ,
        map_smul' :=
          fun c x =>
            by 
              ext z 
              simp  }
      (max C 0)$
    fun x =>
      (mk_continuous_norm_le' _ _).trans_eq$
        by 
          rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

@[simp]
theorem mk_continuous₂_apply (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ} (hC : ∀ x y, ∥f x y∥ ≤ (C*∥x∥)*∥y∥) (x : E) (y : F) :
  f.mk_continuous₂ C hC x y = f x y :=
  rfl

theorem mk_continuous₂_norm_le' (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ} (hC : ∀ x y, ∥f x y∥ ≤ (C*∥x∥)*∥y∥) :
  ∥f.mk_continuous₂ C hC∥ ≤ max C 0 :=
  mk_continuous_norm_le _ (le_max_iff.2$ Or.inr le_rfl) _

theorem mk_continuous₂_norm_le (f : E →ₗ[𝕜] F →ₗ[𝕜] G) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x y, ∥f x y∥ ≤ (C*∥x∥)*∥y∥) :
  ∥f.mk_continuous₂ C hC∥ ≤ C :=
  (f.mk_continuous₂_norm_le' hC).trans_eq$ max_eq_leftₓ h0

end LinearMap

namespace ContinuousLinearMap

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `linear_isometry_equiv`, see
`continuous_linear_map.flipL`. -/
def flip (f : E →L[𝕜] F →L[𝕜] G) : F →L[𝕜] E →L[𝕜] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun y x => f x y) (fun x y z => (f z).map_add x y) (fun c y x => (f x).map_smul c y)
      (fun z x y =>
        by 
          rw [f.map_add, add_apply])
      fun c y x =>
        by 
          rw [map_smul, smul_apply])
    ∥f∥
    fun y x =>
      (f.le_op_norm₂ x y).trans_eq$
        by 
          rw [mul_right_commₓ]

private theorem le_norm_flip (f : E →L[𝕜] F →L[𝕜] G) : ∥f∥ ≤ ∥flip f∥ :=
  f.op_norm_le_bound₂ (norm_nonneg _)$
    fun x y =>
      by 
        rw [mul_right_commₓ]
        exact (flip f).le_op_norm₂ y x

@[simp]
theorem flip_apply (f : E →L[𝕜] F →L[𝕜] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl

@[simp]
theorem flip_flip (f : E →L[𝕜] F →L[𝕜] G) : f.flip.flip = f :=
  by 
    ext 
    rfl

@[simp]
theorem op_norm_flip (f : E →L[𝕜] F →L[𝕜] G) : ∥f.flip∥ = ∥f∥ :=
  le_antisymmₓ
    (by 
      simpa only [flip_flip] using le_norm_flip f.flip)
    (le_norm_flip f)

@[simp]
theorem flip_add (f g : E →L[𝕜] F →L[𝕜] G) : (f+g).flip = f.flip+g.flip :=
  rfl

@[simp]
theorem flip_smul (c : 𝕜) (f : E →L[𝕜] F →L[𝕜] G) : (c • f).flip = c • f.flip :=
  rfl

variable(𝕜 E F G)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `linear_isometry_equiv`.
For an unbundled version see `continuous_linear_map.flip`. -/
def flipₗᵢ : (E →L[𝕜] F →L[𝕜] G) ≃ₗᵢ[𝕜] F →L[𝕜] E →L[𝕜] G :=
  { toFun := flip, invFun := flip, map_add' := flip_add, map_smul' := flip_smul, left_inv := flip_flip,
    right_inv := flip_flip, norm_map' := op_norm_flip }

variable{𝕜 E F G}

@[simp]
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E F G).symm = flipₗᵢ 𝕜 F E G :=
  rfl

@[simp]
theorem coe_flipₗᵢ : «expr⇑ » (flipₗᵢ 𝕜 E F G) = flip :=
  rfl

variable(𝕜 F)

/-- The continuous linear map obtained by applying a continuous linear map at a given vector.

This is the continuous version of `linear_map.applyₗ`. -/
def apply : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F :=
  flip (id 𝕜 (E →L[𝕜] F))

variable{𝕜 F}

@[simp]
theorem apply_apply (v : E) (f : E →L[𝕜] F) : apply 𝕜 F v f = f v :=
  rfl

variable(𝕜 E F G)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
def compL : (F →L[𝕜] G) →L[𝕜] (E →L[𝕜] F) →L[𝕜] E →L[𝕜] G :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ _ comp add_comp smul_comp comp_add fun c f g => comp_smul _ _ _) 1$
    fun f g =>
      by 
        simpa only [one_mulₓ] using op_norm_comp_le f g

variable{𝕜 E F G}

@[simp]
theorem compL_apply (f : F →L[𝕜] G) (g : E →L[𝕜] F) : compL 𝕜 E F G f g = f.comp g :=
  rfl

section MultiplicationLinear

variable(𝕜)(𝕜' : Type _)[NormedRing 𝕜'][NormedAlgebra 𝕜 𝕜']

/-- Left multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
def lmulₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { toLinearMap :=
      (Algebra.lmul 𝕜 𝕜').toLinearMap.mkContinuous₂ 1$
        fun x y =>
          by 
            simpa using norm_mul_le x y,
    norm_map' :=
      fun x =>
        le_antisymmₓ (op_norm_le_bound _ (norm_nonneg x) (norm_mul_le x))
          (by 
            convert ratio_le_op_norm _ (1 : 𝕜')
            simp [NormedAlgebra.norm_one 𝕜 𝕜']) }

/-- Left multiplication in a normed algebra as a continuous bilinear map. -/
def lmul : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (lmulₗᵢ 𝕜 𝕜').toContinuousLinearMap

@[simp]
theorem lmul_apply (x y : 𝕜') : lmul 𝕜 𝕜' x y = x*y :=
  rfl

@[simp]
theorem coe_lmulₗᵢ : «expr⇑ » (lmulₗᵢ 𝕜 𝕜') = lmul 𝕜 𝕜' :=
  rfl

@[simp]
theorem op_norm_lmul_apply (x : 𝕜') : ∥lmul 𝕜 𝕜' x∥ = ∥x∥ :=
  (lmulₗᵢ 𝕜 𝕜').norm_map x

/-- Right-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_right : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  (lmul 𝕜 𝕜').flip

@[simp]
theorem lmul_right_apply (x y : 𝕜') : lmul_right 𝕜 𝕜' x y = y*x :=
  rfl

@[simp]
theorem op_norm_lmul_right_apply (x : 𝕜') : ∥lmul_right 𝕜 𝕜' x∥ = ∥x∥ :=
  le_antisymmₓ (op_norm_le_bound _ (norm_nonneg x) fun y => (norm_mul_le y x).trans_eq (mul_commₓ _ _))
    (by 
      convert ratio_le_op_norm _ (1 : 𝕜')
      simp [NormedAlgebra.norm_one 𝕜 𝕜'])

/-- Right-multiplication in a normed algebra, considered as a linear isometry to the space of
continuous linear maps. -/
def lmul_rightₗᵢ : 𝕜' →ₗᵢ[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  { toLinearMap := lmul_right 𝕜 𝕜', norm_map' := op_norm_lmul_right_apply 𝕜 𝕜' }

@[simp]
theorem coe_lmul_rightₗᵢ : «expr⇑ » (lmul_rightₗᵢ 𝕜 𝕜') = lmul_right 𝕜 𝕜' :=
  rfl

/-- Simultaneous left- and right-multiplication in a normed algebra, considered as a continuous
trilinear map. -/
def lmul_left_right : 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' →L[𝕜] 𝕜' :=
  ((compL 𝕜 𝕜' 𝕜' 𝕜').comp (lmul_right 𝕜 𝕜')).flip.comp (lmul 𝕜 𝕜')

@[simp]
theorem lmul_left_right_apply (x y z : 𝕜') : lmul_left_right 𝕜 𝕜' x y z = (x*z)*y :=
  rfl

theorem op_norm_lmul_left_right_apply_apply_le (x y : 𝕜') : ∥lmul_left_right 𝕜 𝕜' x y∥ ≤ ∥x∥*∥y∥ :=
  (op_norm_comp_le _ _).trans_eq$
    by 
      simp [mul_commₓ]

theorem op_norm_lmul_left_right_apply_le (x : 𝕜') : ∥lmul_left_right 𝕜 𝕜' x∥ ≤ ∥x∥ :=
  op_norm_le_bound _ (norm_nonneg x) (op_norm_lmul_left_right_apply_apply_le 𝕜 𝕜' x)

theorem op_norm_lmul_left_right_le : ∥lmul_left_right 𝕜 𝕜'∥ ≤ 1 :=
  op_norm_le_bound _ zero_le_one fun x => (one_mulₓ ∥x∥).symm ▸ op_norm_lmul_left_right_apply_le 𝕜 𝕜' x

end MultiplicationLinear

section SmulLinear

variable(𝕜)(𝕜' : Type _)[NormedField 𝕜'][NormedAlgebra 𝕜 𝕜'][SemiNormedSpace 𝕜' E][IsScalarTower 𝕜 𝕜' E]

/-- Scalar multiplication as a continuous bilinear map. -/
def lsmul : 𝕜' →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 E).toLinearMap : 𝕜' →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1$
    fun c x =>
      by 
        simpa only [one_mulₓ] using (norm_smul c x).le

@[simp]
theorem lsmul_apply (c : 𝕜') (x : E) : lsmul 𝕜 𝕜' c x = c • x :=
  rfl

variable{𝕜'}

theorem norm_to_span_singleton (x : E) : ∥to_span_singleton 𝕜 x∥ = ∥x∥ :=
  by 
    refine' op_norm_eq_of_bounds (norm_nonneg _) (fun x => _) fun N hN_nonneg h => _
    ·
      rw [to_span_singleton_apply, norm_smul, mul_commₓ]
    ·
      specialize h 1
      rw [to_span_singleton_apply, norm_smul, mul_commₓ] at h 
      exact
        (mul_le_mul_right
              (by 
                simp )).mp
          h

end SmulLinear

section RestrictScalars

variable{𝕜' : Type _}[NondiscreteNormedField 𝕜'][NormedAlgebra 𝕜' 𝕜]

variable[SemiNormedSpace 𝕜' E][IsScalarTower 𝕜' 𝕜 E]

variable[SemiNormedSpace 𝕜' F][IsScalarTower 𝕜' 𝕜 F]

@[simp]
theorem norm_restrict_scalars (f : E →L[𝕜] F) : ∥f.restrict_scalars 𝕜'∥ = ∥f∥ :=
  le_antisymmₓ (op_norm_le_bound _ (norm_nonneg _)$ fun x => f.le_op_norm x)
    (op_norm_le_bound _ (norm_nonneg _)$ fun x => f.le_op_norm x)

variable(𝕜 E F
    𝕜')(𝕜'' :
    Type
      _)[Ringₓ
      𝕜''][TopologicalSpace 𝕜''][Module 𝕜'' F][HasContinuousSmul 𝕜'' F][SmulCommClass 𝕜 𝕜'' F][SmulCommClass 𝕜' 𝕜'' F]

/-- `continuous_linear_map.restrict_scalars` as a `linear_isometry`. -/
def restrict_scalars_isometry : (E →L[𝕜] F) →ₗᵢ[𝕜''] E →L[𝕜'] F :=
  ⟨restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'', norm_restrict_scalars⟩

variable{𝕜 E F 𝕜' 𝕜''}

@[simp]
theorem coe_restrict_scalars_isometry : «expr⇑ » (restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'') = RestrictScalars 𝕜' :=
  rfl

@[simp]
theorem restrict_scalars_isometry_to_linear_map :
  (restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'').toLinearMap = restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

variable(𝕜 E F 𝕜' 𝕜'')

/-- `continuous_linear_map.restrict_scalars` as a `continuous_linear_map`. -/
def restrict_scalarsL : (E →L[𝕜] F) →L[𝕜''] E →L[𝕜'] F :=
  (restrict_scalars_isometry 𝕜 E F 𝕜' 𝕜'').toContinuousLinearMap

variable{𝕜 E F 𝕜' 𝕜''}

@[simp]
theorem coe_restrict_scalarsL :
  (restrict_scalarsL 𝕜 E F 𝕜' 𝕜'' : (E →L[𝕜] F) →ₗ[𝕜''] E →L[𝕜'] F) = restrict_scalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

@[simp]
theorem coe_restrict_scalarsL' : «expr⇑ » (restrict_scalarsL 𝕜 E F 𝕜' 𝕜'') = RestrictScalars 𝕜' :=
  rfl

end RestrictScalars

end ContinuousLinearMap

namespace Submodule

theorem norm_subtypeL_le (K : Submodule 𝕜 E) : ∥K.subtypeL∥ ≤ 1 :=
  K.subtypeₗᵢ.norm_to_continuous_linear_map_le

end Submodule

section HasSum

variable{ι R M M₂ :
    Type
      _}[Semiringₓ
      R][AddCommMonoidₓ M][Module R M][AddCommMonoidₓ M₂][Module R M₂][TopologicalSpace M][TopologicalSpace M₂]

omit 𝕜

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearMap.has_sum {f : ι → M} (φ : M →L[R] M₂) {x : M} (hf : HasSum f x) :
  HasSum (fun b : ι => φ (f b)) (φ x) :=
  by 
    simpa only using hf.map φ.to_linear_map.to_add_monoid_hom φ.continuous

alias ContinuousLinearMap.has_sum ← HasSum.mapL

protected theorem ContinuousLinearMap.summable {f : ι → M} (φ : M →L[R] M₂) (hf : Summable f) :
  Summable fun b : ι => φ (f b) :=
  (hf.has_sum.mapL φ).Summable

alias ContinuousLinearMap.summable ← Summable.mapL

protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] {f : ι → M} (φ : M →L[R] M₂) (hf : Summable f) :
  φ (∑'z, f z) = ∑'z, φ (f z) :=
  (hf.has_sum.mapL φ).tsum_eq.symm

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.has_sum {f : ι → M} (e : M ≃L[R] M₂) {y : M₂} :
  HasSum (fun b : ι => e (f b)) y ↔ HasSum f (e.symm y) :=
  ⟨fun h =>
      by 
        simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →L[R] M),
    fun h =>
      by 
        simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →L[R] M₂).HasSum h⟩

protected theorem ContinuousLinearEquiv.summable {f : ι → M} (e : M ≃L[R] M₂) :
  (Summable fun b : ι => e (f b)) ↔ Summable f :=
  ⟨fun hf => (e.has_sum.1 hf.has_sum).Summable, (e : M →L[R] M₂).Summable⟩

theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂] {f : ι → M} (e : M ≃L[R] M₂) {y : M₂} :
  (∑'z, e (f z)) = y ↔ (∑'z, f z) = e.symm y :=
  by 
    byCases' hf : Summable f
    ·
      exact
        ⟨fun h => (e.has_sum.mp ((e.summable.mpr hf).has_sum_iff.mpr h)).tsum_eq,
          fun h => (e.has_sum.mpr (hf.has_sum_iff.mpr h)).tsum_eq⟩
    ·
      have hf' : ¬Summable fun z => e (f z) := fun h => hf (e.summable.mp h)
      rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf']
      exact
        ⟨by 
            rintro rfl 
            simp ,
          fun H =>
            by 
              simpa using congr_argₓ (fun z => e z) H⟩

protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂] {f : ι → M} (e : M ≃L[R] M₂) :
  e (∑'z, f z) = ∑'z, e (f z) :=
  by 
    refine' symm (e.tsum_eq_iff.mpr _)
    rw [e.symm_apply_apply _]

end HasSum

namespace ContinuousLinearEquiv

variable(e : E ≃L[𝕜] F)

protected theorem lipschitz : LipschitzWith ∥(e : E →L[𝕜] F)∥₊ e :=
  (e : E →L[𝕜] F).lipschitz

theorem is_O_comp {α : Type _} (f : α → E) (l : Filter α) : Asymptotics.IsO (fun x' => e (f x')) f l :=
  (e : E →L[𝕜] F).is_O_comp f l

theorem is_O_sub (l : Filter E) (x : E) : Asymptotics.IsO (fun x' => e (x' - x)) (fun x' => x' - x) l :=
  (e : E →L[𝕜] F).is_O_sub l x

theorem is_O_comp_rev {α : Type _} (f : α → E) (l : Filter α) : Asymptotics.IsO f (fun x' => e (f x')) l :=
  (e.symm.is_O_comp _ l).congr_left$ fun _ => e.symm_apply_apply _

theorem is_O_sub_rev (l : Filter E) (x : E) : Asymptotics.IsO (fun x' => x' - x) (fun x' => e (x' - x)) l :=
  e.is_O_comp_rev _ _

theorem homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₗ[𝕜] F) :
  (∀ x : E, ∥f x∥ = a*∥x∥) → ∀ y : F, ∥f.symm y∥ = a⁻¹*∥y∥ :=
  by 
    intro hf y 
    calc ∥f.symm y∥ = a⁻¹*a*∥f.symm y∥ := _ _ = a⁻¹*∥f (f.symm y)∥ :=
      by 
        rw [hf]_ = a⁻¹*∥y∥ :=
      by 
        simp 
    rw [←mul_assocₓ, inv_mul_cancel (ne_of_ltₓ ha).symm, one_mulₓ]

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
def of_homothety (f : E ≃ₗ[𝕜] F) (a : ℝ) (ha : 0 < a) (hf : ∀ x, ∥f x∥ = a*∥x∥) : E ≃L[𝕜] F :=
  { toLinearEquiv := f, continuous_to_fun := f.to_linear_map.continuous_of_bound a fun x => le_of_eqₓ (hf x),
    continuous_inv_fun :=
      f.symm.to_linear_map.continuous_of_bound (a⁻¹) fun x => le_of_eqₓ (homothety_inverse a ha f hf x) }

variable(𝕜)

theorem to_span_nonzero_singleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
  ∥LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c∥ = ∥x∥*∥c∥ :=
  ContinuousLinearMap.to_span_singleton_homothety _ _ _

end ContinuousLinearEquiv

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₗ[𝕜] F) (C_to C_inv : ℝ) (h_to : ∀ x, ∥e x∥ ≤ C_to*∥x∥)
  (h_inv : ∀ x : F, ∥e.symm x∥ ≤ C_inv*∥x∥) : E ≃L[𝕜] F :=
  { toLinearEquiv := e, continuous_to_fun := e.to_linear_map.continuous_of_bound C_to h_to,
    continuous_inv_fun := e.symm.to_linear_map.continuous_of_bound C_inv h_inv }

namespace ContinuousLinearMap

variable(𝕜)(𝕜' : Type _)[NormedRing 𝕜'][NormedAlgebra 𝕜 𝕜']

variable{𝕜}

variable{E' F' : Type _}[SemiNormedGroup E'][SemiNormedGroup F'][SemiNormedSpace 𝕜 E'][SemiNormedSpace 𝕜 F']

/--
Compose a bilinear map `E →L[𝕜] F →L[𝕜] G` with two linear maps `E' →L[𝕜] E` and `F' →L[𝕜] F`.
-/
def bilinear_comp (f : E →L[𝕜] F →L[𝕜] G) (gE : E' →L[𝕜] E) (gF : F' →L[𝕜] F) : E' →L[𝕜] F' →L[𝕜] G :=
  ((f.comp gE).flip.comp gF).flip

@[simp]
theorem bilinear_comp_apply (f : E →L[𝕜] F →L[𝕜] G) (gE : E' →L[𝕜] E) (gF : F' →L[𝕜] F) (x : E') (y : F') :
  f.bilinear_comp gE gF x y = f (gE x) (gF y) :=
  rfl

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
def deriv₂ (f : E →L[𝕜] F →L[𝕜] G) : E × F →L[𝕜] E × F →L[𝕜] G :=
  f.bilinear_comp (fst _ _ _) (snd _ _ _)+f.flip.bilinear_comp (snd _ _ _) (fst _ _ _)

@[simp]
theorem coe_deriv₂ (f : E →L[𝕜] F →L[𝕜] G) (p : E × F) : «expr⇑ » (f.deriv₂ p) = fun q : E × F => f p.1 q.2+f q.1 p.2 :=
  rfl

theorem map_add₂ (f : E →L[𝕜] F →L[𝕜] G) (x x' : E) (y y' : F) :
  f (x+x') (y+y') = (f x y+f.deriv₂ (x, y) (x', y'))+f x' y' :=
  by 
    simp only [map_add, add_apply, coe_deriv₂, add_assocₓ]

end ContinuousLinearMap

end SemiNormed

section Normed

variable[NormedGroup E][NormedGroup F][NormedGroup G]

open Metric ContinuousLinearMap

section NormedField

variable[NormedField 𝕜][NormedSpace 𝕜 E][NormedSpace 𝕜 F](f : E →ₗ[𝕜] F)

theorem LinearMap.continuous_iff_is_closed_ker {f : E →ₗ[𝕜] 𝕜} : Continuous f ↔ IsClosed (f.ker : Set E) :=
  by 
    refine' ⟨fun h => (T1Space.t1 (0 : 𝕜)).Preimage h, fun h => _⟩
    byCases' hf : ∀ x, x ∈ f.ker
    ·
      have  : (f : E → 𝕜) = fun x => 0
      ·
        ·
          ext x 
          simpa using hf x 
      rw [this]
      exact continuous_const
    ·
      pushNeg  at hf 
      let r : ℝ := (2 : ℝ)⁻¹
      have  : 0 ≤ r
      ·
        normNum [r]
      have  : r < 1
      ·
        normNum [r]
      obtain ⟨x₀, x₀ker, h₀⟩ : ∃ x₀ : E, x₀ ∉ f.ker ∧ ∀ y _ : y ∈ LinearMap.ker f, (r*∥x₀∥) ≤ ∥x₀ - y∥
      exact riesz_lemma h hf this 
      have  : x₀ ≠ 0
      ·
        intro h 
        have  : x₀ ∈ f.ker
        ·
          ·
            rw [h]
            exact (LinearMap.ker f).zero_mem 
        exact x₀ker this 
      have rx₀_ne_zero : (r*∥x₀∥) ≠ 0
      ·
        ·
          simp [norm_eq_zero, this]
      have  : ∀ x, ∥f x∥ ≤ ((r*∥x₀∥)⁻¹*∥f x₀∥)*∥x∥
      ·
        intro x 
        byCases' hx : f x = 0
        ·
          rw [hx, norm_zero]
          applyRules [mul_nonneg, norm_nonneg, inv_nonneg.2]
        ·
          let y := x₀ - (f x₀*f x⁻¹) • x 
          have fy_zero : f y = 0
          ·
            calc f y = f x₀ - (f x₀*f x⁻¹)*f x :=
              by 
                simp [y]_ = 0 :=
              by 
                rw [mul_assocₓ, inv_mul_cancel hx, mul_oneₓ, sub_eq_zero_of_eq]
                rfl 
          have A : (r*∥x₀∥) ≤ (∥f x₀∥*∥f x∥⁻¹)*∥x∥
          exact
            calc (r*∥x₀∥) ≤ ∥x₀ - y∥ := h₀ _ (LinearMap.mem_ker.2 fy_zero)
              _ = ∥(f x₀*f x⁻¹) • x∥ :=
              by 
                dsimp [y]
                congr 
                abel 
              _ = (∥f x₀∥*∥f x∥⁻¹)*∥x∥ :=
              by 
                rw [norm_smul, NormedField.norm_mul, NormedField.norm_inv]
              
          calc ∥f x∥ = ((r*∥x₀∥)⁻¹*r*∥x₀∥)*∥f x∥ :=
            by 
              rwa [inv_mul_cancel, one_mulₓ]_ ≤ ((r*∥x₀∥)⁻¹*(∥f x₀∥*∥f x∥⁻¹)*∥x∥)*∥f x∥ :=
            by 
              apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left A _) (norm_nonneg _)
              exact
                inv_nonneg.2
                  (mul_nonneg
                    (by 
                      normNum)
                    (norm_nonneg _))_ = ((∥f x∥⁻¹*∥f x∥)*(r*∥x₀∥)⁻¹*∥f x₀∥)*∥x∥ :=
            by 
              ring _ = ((r*∥x₀∥)⁻¹*∥f x₀∥)*∥x∥ :=
            by 
              rw [inv_mul_cancel, one_mulₓ]
              simp [norm_eq_zero, hx]
      exact LinearMap.continuous_of_bound f _ this

end NormedField

variable[NondiscreteNormedField
      𝕜][NormedSpace 𝕜 E][NormedSpace 𝕜 F][NormedSpace 𝕜 G](c : 𝕜)(f g : E →L[𝕜] F)(h : F →L[𝕜] G)(x y z : E)

include 𝕜

theorem LinearMap.bound_of_shell (f : E →ₗ[𝕜] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ∥c∥)
  (hf : ∀ x, ε / ∥c∥ ≤ ∥x∥ → ∥x∥ < ε → ∥f x∥ ≤ C*∥x∥) (x : E) : ∥f x∥ ≤ C*∥x∥ :=
  by 
    byCases' hx : x = 0
    ·
      simp [hx]
    exact LinearMap.bound_of_shell_semi_normed f ε_pos hc hf (ne_of_ltₓ (norm_pos_iff.2 hx)).symm

namespace ContinuousLinearMap

section OpNorm

open Set Real

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ContinuousLinearMap.ext
        fun x =>
          norm_le_zero_iff.1
            (calc _ ≤ ∥f∥*∥x∥ := le_op_norm _ _ 
              _ = _ :=
              by 
                rw [hn, zero_mul]
              ))
    fun hf =>
      le_antisymmₓ
        (cInf_le bounds_bdd_below
          ⟨le_rfl,
            fun _ =>
              le_of_eqₓ
                (by 
                  rw [zero_mul, hf]
                  exact norm_zero)⟩)
        (op_norm_nonneg _)

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
theorem norm_id [Nontrivial E] : ∥id 𝕜 E∥ = 1 :=
  by 
    refine' norm_id_of_nontrivial_seminorm _ 
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨x, ne_of_gtₓ (norm_pos_iff.2 hx)⟩

instance NormOneClass [Nontrivial E] : NormOneClass (E →L[𝕜] E) :=
  ⟨norm_id⟩

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : NormedGroup (E →L[𝕜] F) :=
  NormedGroup.ofCore _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space {𝕜' : Type _} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SmulCommClass 𝕜 𝕜' F] :
  NormedSpace 𝕜' (E →L[𝕜] F) :=
  ⟨op_norm_smul_le⟩

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance to_normed_ring : NormedRing (E →L[𝕜] E) :=
  { ContinuousLinearMap.toNormedGroup with norm_mul := op_norm_comp_le }

/-- For a nonzero normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance to_normed_algebra [Nontrivial E] : NormedAlgebra 𝕜 (E →L[𝕜] E) :=
  { ContinuousLinearMap.algebra with
    norm_algebra_map_eq :=
      fun c =>
        show ∥c • id 𝕜 E∥ = ∥c∥by 
          rw [norm_smul, norm_id]
          simp  }

variable{f}

theorem homothety_norm [Nontrivial E] (f : E →L[𝕜] F) {a : ℝ} (hf : ∀ x, ∥f x∥ = a*∥x∥) : ∥f∥ = a :=
  by 
    obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
    rw [←norm_pos_iff] at hx 
    have ha : 0 ≤ a
    ·
      simpa only [hf, hx, zero_le_mul_right] using norm_nonneg (f x)
    apply le_antisymmₓ (f.op_norm_le_bound ha fun y => le_of_eqₓ (hf y))
    simpa only [hf, hx, mul_le_mul_right] using f.le_op_norm x

theorem to_span_singleton_norm (x : E) : ∥to_span_singleton 𝕜 x∥ = ∥x∥ :=
  homothety_norm _ (to_span_singleton_homothety 𝕜 x)

variable(f)

theorem uniform_embedding_of_bound {K :  ℝ≥0 } (hf : ∀ x, ∥x∥ ≤ K*∥f x∥) : UniformEmbedding f :=
  (f.to_linear_map.antilipschitz_of_bound hf).UniformEmbedding f.uniform_continuous

/-- If a continuous linear map is a uniform embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_uniform_embedding (hf : UniformEmbedding f) : ∃ K, AntilipschitzWith K f :=
  by 
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ)(H : ε > 0), ∀ {x y : E}, dist (f x) (f y) < ε → dist x y < 1 
    exact (uniform_embedding_iff.1 hf).2.2 1 zero_lt_one 
    let δ := ε / 2
    have δ_pos : δ > 0 := half_pos εpos 
    have H : ∀ {x}, ∥f x∥ ≤ δ → ∥x∥ ≤ 1
    ·
      intro x hx 
      have  : dist x 0 ≤ 1
      ·
        refine' (hε _).le 
        rw [f.map_zero, dist_zero_right]
        exact hx.trans_lt (half_lt_self εpos)
      simpa using this 
    rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
    refine' ⟨⟨δ⁻¹, _⟩*nnnorm c, f.to_linear_map.antilipschitz_of_bound$ fun x => _⟩
    exact inv_nonneg.2 (le_of_ltₓ δ_pos)
    byCases' hx : f x = 0
    ·
      have  : f x = f 0
      ·
        ·
          simp [hx]
      have  : x = 0 := (uniform_embedding_iff.1 hf).1 this 
      simp [this]
    ·
      rcases rescale_to_shell hc δ_pos hx with ⟨d, hd, dxlt, ledx, dinv⟩
      rw [←f.map_smul d] at dxlt 
      have  : ∥d • x∥ ≤ 1 := H dxlt.le 
      calc ∥x∥ = ∥d∥⁻¹*∥d • x∥ :=
        by 
          rwa [←NormedField.norm_inv, ←norm_smul, ←mul_smul, inv_mul_cancel, one_smul]_ ≤ ∥d∥⁻¹*1 :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 (norm_nonneg _))_ ≤ (δ⁻¹*∥c∥)*∥f x∥ :=
        by 
          rwa [mul_oneₓ]

section Completeness

open_locale TopologicalSpace

open Filter

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. This works also if the source space is seminormed. -/
instance  {E : Type _} [SemiNormedGroup E] [SemiNormedSpace 𝕜 E] [CompleteSpace F] : CompleteSpace (E →L[𝕜] F) :=
  by 
    refine' Metric.complete_of_cauchy_seq_tendsto fun f hf => _ 
    rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    clear hf 
    have cau : ∀ v, CauchySeq fun n => f n v
    ·
      intro v 
      apply cauchy_seq_iff_le_tendsto_0.2 ⟨fun n => b n*∥v∥, fun n => _, _, _⟩
      ·
        exact mul_nonneg (b0 n) (norm_nonneg _)
      ·
        intro n m N hn hm 
        rw [dist_eq_norm]
        apply le_transₓ ((f n - f m).le_op_norm v) _ 
        exact mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (norm_nonneg v)
      ·
        simpa using b_lim.mul tendsto_const_nhds 
    choose G hG using fun v => cauchy_seq_tendsto_of_complete (cau v)
    let Glin : E →ₗ[𝕜] F :=
      { toFun := G,
        map_add' :=
          fun v w =>
            by 
              have A := hG (v+w)
              have B := (hG v).add (hG w)
              simp only [map_add] at A B 
              exact tendsto_nhds_unique A B,
        map_smul' :=
          fun c v =>
            by 
              have A := hG (c • v)
              have B := Filter.Tendsto.smul (@tendsto_const_nhds _ ℕ _ c _) (hG v)
              simp only [map_smul] at A B 
              exact tendsto_nhds_unique A B }
    have Gnorm : ∀ v, ∥G v∥ ≤ (b 0+∥f 0∥)*∥v∥
    ·
      intro v 
      have A : ∀ n, ∥f n v∥ ≤ (b 0+∥f 0∥)*∥v∥
      ·
        intro n 
        apply le_transₓ ((f n).le_op_norm _) _ 
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        calc ∥f n∥ = ∥(f n - f 0)+f 0∥ :=
          by 
            congr 1
            abel _ ≤ ∥f n - f 0∥+∥f 0∥ :=
          norm_add_le _ _ _ ≤ b 0+∥f 0∥ :=
          by 
            apply add_le_add_right 
            simpa [dist_eq_norm] using b_bound n 0 0 (zero_le _) (zero_le _)
      exact le_of_tendsto (hG v).norm (eventually_of_forall A)
    let Gcont := Glin.mk_continuous _ Gnorm 
    use Gcont 
    have  : ∀ n, ∥f n - Gcont∥ ≤ b n
    ·
      intro n 
      apply op_norm_le_bound _ (b0 n) fun v => _ 
      have A : ∀ᶠm in at_top, ∥(f n - f m) v∥ ≤ b n*∥v∥
      ·
        refine' eventually_at_top.2 ⟨n, fun m hm => _⟩
        apply le_transₓ ((f n - f m).le_op_norm _) _ 
        exact mul_le_mul_of_nonneg_right (b_bound n m n (le_reflₓ _) hm) (norm_nonneg v)
      have B : tendsto (fun m => ∥(f n - f m) v∥) at_top (𝓝 ∥(f n - Gcont) v∥) :=
        tendsto.norm (tendsto_const_nhds.sub (hG v))
      exact le_of_tendsto B A 
    erw [tendsto_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) this b_lim

end Completeness

section UniformlyExtend

variable[CompleteSpace F](e : E →L[𝕜] G)(h_dense : DenseRange e)

section 

variable(h_e : UniformInducing e)

/-- Extension of a continuous linear map `f : E →L[𝕜] F`, with `E` a normed space and `F` a
complete normed space, along a uniform and dense embedding `e : E →L[𝕜] G`.  -/
def extend : G →L[𝕜] F :=
  have cont := (uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous).Continuous 
  have eq := uniformly_extend_of_ind h_e h_dense f.uniform_continuous
  { toFun := (h_e.dense_inducing h_dense).extend f,
    map_add' :=
      by 
        refine' h_dense.induction_on₂ _ _
        ·
          exact is_closed_eq (cont.comp continuous_add) ((cont.comp continuous_fst).add (cont.comp continuous_snd))
        ·
          intro x y 
          simp only [Eq, ←e.map_add]
          exact f.map_add _ _,
    map_smul' :=
      fun k =>
        by 
          refine' fun b => h_dense.induction_on b _ _
          ·
            exact
              is_closed_eq (cont.comp (continuous_const.smul continuous_id))
                ((continuous_const.smul continuous_id).comp cont)
          ·
            intro x 
            rw [←map_smul]
            simp only [Eq]
            exact map_smul _ _ _,
    cont }

theorem extend_unique (g : G →L[𝕜] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coe_fn_injective$
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp]
theorem extend_zero : extend (0 : E →L[𝕜] F) e h_dense h_e = 0 :=
  extend_unique _ _ _ _ _ (zero_comp _)

end 

section 

variable{N :  ℝ≥0 }(h_e : ∀ x, ∥x∥ ≤ N*∥e x∥)

local notation "ψ" => f.extend e h_dense (uniform_embedding_of_bound _ h_e).to_uniform_inducing

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the
norm of the extension of `f` along `e` is bounded by `N * ∥f∥`. -/
theorem op_norm_extend_le : ∥ψ∥ ≤ N*∥f∥ :=
  by 
    have uni : UniformInducing e := (uniform_embedding_of_bound _ h_e).to_uniform_inducing 
    have eq : ∀ x, ψ (e x) = f x := uniformly_extend_of_ind uni h_dense f.uniform_continuous 
    byCases' N0 : 0 ≤ N
    ·
      refine' op_norm_le_bound ψ _ (is_closed_property h_dense (is_closed_le _ _) _)
      ·
        exact mul_nonneg N0 (norm_nonneg _)
      ·
        exact continuous_norm.comp (cont ψ)
      ·
        exact continuous_const.mul continuous_norm
      ·
        intro x 
        rw [Eq]
        calc ∥f x∥ ≤ ∥f∥*∥x∥ := le_op_norm _ _ _ ≤ ∥f∥*N*∥e x∥ :=
          mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)_ ≤ (N*∥f∥)*∥e x∥ :=
          by 
            rw [mul_commₓ («expr↑ » N) ∥f∥, mul_assocₓ]
    ·
      have he : ∀ x : E, x = 0
      ·
        intro x 
        have N0 : N ≤ 0 := le_of_ltₓ (lt_of_not_geₓ N0)
        rw [←norm_le_zero_iff]
        exact le_transₓ (h_e x) (mul_nonpos_of_nonpos_of_nonneg N0 (norm_nonneg _))
      have hf : f = 0
      ·
        ext 
        simp only [he x, zero_apply, map_zero]
      have hψ : ψ = 0
      ·
        rw [hf]
        apply extend_zero 
      rw [hψ, hf, norm_zero, norm_zero, mul_zero]

end 

end UniformlyExtend

end OpNorm

end ContinuousLinearMap

namespace LinearIsometry

@[simp]
theorem norm_to_continuous_linear_map [Nontrivial E] (f : E →ₗᵢ[𝕜] F) : ∥f.to_continuous_linear_map∥ = 1 :=
  f.to_continuous_linear_map.homothety_norm$
    by 
      simp 

end LinearIsometry

namespace ContinuousLinearMap

/-- Precomposition with a linear isometry preserves the operator norm. -/
theorem op_norm_comp_linear_isometry_equiv {G : Type _} [SemiNormedGroup G] [SemiNormedSpace 𝕜 G] (f : F →L[𝕜] G)
  (g : E ≃ₗᵢ[𝕜] F) : ∥f.comp g.to_linear_isometry.to_continuous_linear_map∥ = ∥f∥ :=
  by 
    casesI subsingleton_or_nontrivial E
    ·
      haveI  := g.symm.to_linear_equiv.to_equiv.subsingleton 
      simp 
    refine' le_antisymmₓ _ _
    ·
      convert f.op_norm_comp_le g.to_linear_isometry.to_continuous_linear_map 
      simp [g.to_linear_isometry.norm_to_continuous_linear_map]
    ·
      convert
        (f.comp g.to_linear_isometry.to_continuous_linear_map).op_norm_comp_le
          g.symm.to_linear_isometry.to_continuous_linear_map
      ·
        ext 
        simp 
      haveI  := g.symm.surjective.nontrivial 
      simp [g.symm.to_linear_isometry.norm_to_continuous_linear_map]

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
theorem norm_smul_right_apply (c : E →L[𝕜] 𝕜) (f : F) : ∥smul_right c f∥ = ∥c∥*∥f∥ :=
  by 
    refine' le_antisymmₓ _ _
    ·
      apply op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => _ 
      calc ∥c x • f∥ = ∥c x∥*∥f∥ := norm_smul _ _ _ ≤ (∥c∥*∥x∥)*∥f∥ :=
        mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)_ = (∥c∥*∥f∥)*∥x∥ :=
        by 
          ring
    ·
      byCases' h : f = 0
      ·
        simp [h]
      ·
        have  : 0 < ∥f∥ := norm_pos_iff.2 h 
        rw [←le_div_iff this]
        apply op_norm_le_bound _ (div_nonneg (norm_nonneg _) (norm_nonneg f)) fun x => _ 
        rw [div_mul_eq_mul_div, le_div_iff this]
        calc (∥c x∥*∥f∥) = ∥c x • f∥ := (norm_smul _ _).symm _ = ∥smul_right c f x∥ := rfl _ ≤ ∥smul_right c f∥*∥x∥ :=
          le_op_norm _ _

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
theorem nnnorm_smul_right_apply (c : E →L[𝕜] 𝕜) (f : F) : ∥smul_right c f∥₊ = ∥c∥₊*∥f∥₊ :=
  Nnreal.eq$ c.norm_smul_right_apply f

variable(𝕜 E F)

/-- `continuous_linear_map.smul_right` as a continuous trilinear map:
`smul_rightL (c : E →L[𝕜] 𝕜) (f : F) (x : E) = c x • f`. -/
def smul_rightL : (E →L[𝕜] 𝕜) →L[𝕜] F →L[𝕜] E →L[𝕜] F :=
  LinearMap.mkContinuous₂
      { toFun := smul_rightₗ,
        map_add' :=
          fun c₁ c₂ =>
            by 
              ext x 
              simp [add_smul],
        map_smul' :=
          fun m c =>
            by 
              ext x 
              simp [smul_smul] }
      1$
    fun c x =>
      by 
        simp 

variable{𝕜 E F}

@[simp]
theorem norm_smul_rightL_apply (c : E →L[𝕜] 𝕜) (f : F) : ∥smul_rightL 𝕜 E F c f∥ = ∥c∥*∥f∥ :=
  norm_smul_right_apply c f

@[simp]
theorem norm_smul_rightL (c : E →L[𝕜] 𝕜) [Nontrivial F] : ∥smul_rightL 𝕜 E F c∥ = ∥c∥ :=
  ContinuousLinearMap.homothety_norm _ c.norm_smul_right_apply

variable(𝕜)(𝕜' : Type _)[NormedRing 𝕜'][NormedAlgebra 𝕜 𝕜']

@[simp]
theorem op_norm_lmul : ∥lmul 𝕜 𝕜'∥ = 1 :=
  by 
    haveI  := NormedAlgebra.nontrivial 𝕜 𝕜' <;> exact (lmulₗᵢ 𝕜 𝕜').norm_to_continuous_linear_map

@[simp]
theorem op_norm_lmul_right : ∥lmul_right 𝕜 𝕜'∥ = 1 :=
  (op_norm_flip (@lmul 𝕜 _ 𝕜' _ _)).trans (op_norm_lmul _ _)

end ContinuousLinearMap

namespace Submodule

theorem norm_subtypeL (K : Submodule 𝕜 E) [Nontrivial K] : ∥K.subtypeL∥ = 1 :=
  K.subtypeₗᵢ.norm_to_continuous_linear_map

end Submodule

namespace ContinuousLinearEquiv

variable(e : E ≃L[𝕜] F)

protected theorem antilipschitz : AntilipschitzWith (nnnorm (e.symm : F →L[𝕜] E)) e :=
  e.symm.lipschitz.to_right_inverse e.left_inv

/-- A continuous linear equiv is a uniform embedding. -/
theorem UniformEmbedding : UniformEmbedding e :=
  e.antilipschitz.uniform_embedding e.lipschitz.uniform_continuous

theorem one_le_norm_mul_norm_symm [Nontrivial E] : 1 ≤ ∥(e : E →L[𝕜] F)∥*∥(e.symm : F →L[𝕜] E)∥ :=
  by 
    rw [mul_commₓ]
    convert (e.symm : F →L[𝕜] E).op_norm_comp_le (e : E →L[𝕜] F)
    rw [e.coe_symm_comp_coe, ContinuousLinearMap.norm_id]

theorem norm_pos [Nontrivial E] : 0 < ∥(e : E →L[𝕜] F)∥ :=
  pos_of_mul_pos_right (lt_of_lt_of_leₓ zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

theorem norm_symm_pos [Nontrivial E] : 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
  pos_of_mul_pos_left (lt_of_lt_of_leₓ zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

theorem nnnorm_symm_pos [Nontrivial E] : 0 < nnnorm (e.symm : F →L[𝕜] E) :=
  e.norm_symm_pos

theorem subsingleton_or_norm_symm_pos : Subsingleton E ∨ 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
  by 
    rcases subsingleton_or_nontrivial E with (_i | _i) <;> resetI
    ·
      left 
      infer_instance
    ·
      right 
      exact e.norm_symm_pos

theorem subsingleton_or_nnnorm_symm_pos : Subsingleton E ∨ 0 < (nnnorm$ (e.symm : F →L[𝕜] E)) :=
  subsingleton_or_norm_symm_pos e

variable(𝕜)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
def to_span_nonzero_singleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜∙x :=
  of_homothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ∥x∥ (norm_pos_iff.mpr h)
    (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
def coord (x : E) (h : x ≠ 0) : (𝕜∙x) →L[𝕜] 𝕜 :=
  (to_span_nonzero_singleton 𝕜 x h).symm

@[simp]
theorem coe_to_span_nonzero_singleton_symm {x : E} (h : x ≠ 0) :
  «expr⇑ » (to_span_nonzero_singleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl

@[simp]
theorem coord_to_span_nonzero_singleton {x : E} (h : x ≠ 0) (c : 𝕜) :
  coord 𝕜 x h (to_span_nonzero_singleton 𝕜 x h c) = c :=
  (to_span_nonzero_singleton 𝕜 x h).symm_apply_apply c

@[simp]
theorem to_span_nonzero_singleton_coord {x : E} (h : x ≠ 0) (y : 𝕜∙x) :
  to_span_nonzero_singleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (to_span_nonzero_singleton 𝕜 x h).apply_symm_apply y

@[simp]
theorem coord_norm (x : E) (h : x ≠ 0) : ∥coord 𝕜 x h∥ = ∥x∥⁻¹ :=
  by 
    have hx : 0 < ∥x∥ := norm_pos_iff.mpr h 
    haveI  : Nontrivial (𝕜∙x) := Submodule.nontrivial_span_singleton h 
    exact
      ContinuousLinearMap.homothety_norm _
        fun y => homothety_inverse _ hx _ (to_span_nonzero_singleton_homothety 𝕜 x h) _

@[simp]
theorem coord_self (x : E) (h : x ≠ 0) : (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜∙x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h

end ContinuousLinearEquiv

theorem LinearEquiv.uniform_embedding (e : E ≃ₗ[𝕜] F) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
  UniformEmbedding e :=
  ContinuousLinearEquiv.uniform_embedding { e with continuous_to_fun := h₁, continuous_inv_fun := h₂ }

end Normed

