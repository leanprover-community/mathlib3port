import Mathbin.Analysis.NormedSpace.HahnBanach 
import Mathbin.Analysis.NormedSpace.IsROrC

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_space` and we specialize to `normed_space` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals `x'` for which
  `∥x' z∥ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/


noncomputable section 

open_locale Classical

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type _) [NondiscreteNormedField 𝕜]

variable (E : Type _) [SemiNormedGroup E] [SemiNormedSpace 𝕜 E]

variable (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F]

-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler inhabited
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler semi_normed_group
-- ././Mathport/Syntax/Translate/Basic.lean:748:9: unsupported derive handler semi_normed_space 𝕜
/-- The topological dual of a seminormed space `E`. -/
def dual :=
  E →L[𝕜] 𝕜 deriving [anonymous], [anonymous], [anonymous]

instance : AddMonoidHomClass (dual 𝕜 E) E 𝕜 :=
  ContinuousLinearMap.addMonoidHomClass

instance : CoeFun (dual 𝕜 E) fun _ => E → 𝕜 :=
  ContinuousLinearMap.toFun

instance : NormedGroup (dual 𝕜 F) :=
  ContinuousLinearMap.toNormedGroup

instance : NormedSpace 𝕜 (dual 𝕜 F) :=
  ContinuousLinearMap.toNormedSpace

instance [FiniteDimensional 𝕜 E] : FiniteDimensional 𝕜 (dual 𝕜 E) :=
  ContinuousLinearMap.finite_dimensional

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusion_in_double_dual : E →L[𝕜] dual 𝕜 (dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : dual 𝕜 E) : inclusion_in_double_dual 𝕜 E x f = f x :=
  rfl

theorem inclusion_in_double_dual_norm_eq : ∥inclusion_in_double_dual 𝕜 E∥ = ∥ContinuousLinearMap.id 𝕜 (dual 𝕜 E)∥ :=
  ContinuousLinearMap.op_norm_flip _

theorem inclusion_in_double_dual_norm_le : ∥inclusion_in_double_dual 𝕜 E∥ ≤ 1 :=
  by 
    rw [inclusion_in_double_dual_norm_eq]
    exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ∥(inclusion_in_double_dual 𝕜 E) x∥ ≤ ∥x∥ :=
  by 
    simpa using ContinuousLinearMap.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le 𝕜 E) x

end General

section BidualIsometry

variable (𝕜 : Type v) [IsROrC 𝕜] {E : Type u} [NormedGroup E] [NormedSpace 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ f : dual 𝕜 E, ∥f x∥ ≤ M*∥f∥) : ∥x∥ ≤ M :=
  by 
    classical 
    byCases' h : x = 0
    ·
      simp only [h, hMp, norm_zero]
    ·
      obtain ⟨f, hf⟩ : ∃ g : E →L[𝕜] 𝕜, _ := exists_dual_vector 𝕜 x h 
      calc ∥x∥ = ∥(∥x∥ : 𝕜)∥ := is_R_or_C.norm_coe_norm.symm _ = ∥f x∥ :=
        by 
          rw [hf.2]_ ≤ M*∥f∥ :=
        hM f _ = M :=
        by 
          rw [hf.1, mul_oneₓ]

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_eq_zero.mp
    (le_antisymmₓ
      (norm_le_dual_bound 𝕜 x le_rfl
        fun f =>
          by 
            simp [h f])
      (norm_nonneg _))

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : dual 𝕜 E, g x = 0 :=
  ⟨fun hx =>
      by 
        simp [hx],
    fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : dual 𝕜 E, g x = g y :=
  by 
    rw [←sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
    simp [sub_eq_zero]

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusion_in_double_dual_li : E →ₗᵢ[𝕜] dual 𝕜 (dual 𝕜 E) :=
  { inclusion_in_double_dual 𝕜 E with
    norm_map' :=
      by 
        intro x 
        apply le_antisymmₓ
        ·
          exact double_dual_bound 𝕜 E x 
        rw [ContinuousLinearMap.norm_def]
        refine' le_cInf ContinuousLinearMap.bounds_nonempty _ 
        rintro c ⟨hc1, hc2⟩
        exact norm_le_dual_bound 𝕜 x hc1 hc2 }

end BidualIsometry

end NormedSpace

section PolarSets

open Metric Set NormedSpace

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (z «expr ∈ » s)
/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def Polar (𝕜 : Type _) [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] (s : Set E) :
  Set (dual 𝕜 E) :=
  { x' : dual 𝕜 E | ∀ z _ : z ∈ s, ∥x' z∥ ≤ 1 }

open Metric Set NormedSpace

open_locale TopologicalSpace

variable (𝕜 : Type _) [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : dual 𝕜 E) ∈ Polar 𝕜 s :=
  fun _ _ =>
    by 
      simp only [zero_le_one, ContinuousLinearMap.zero_apply, norm_zero]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (z «expr ∈ » s)
theorem polar_eq_Inter (s : Set E) : Polar 𝕜 s = ⋂ (z : _)(_ : z ∈ s), { x' : dual 𝕜 E | ∥x' z∥ ≤ 1 } :=
  by 
    ext 
    simp only [Polar, mem_bInter_iff, mem_set_of_eq]

@[simp]
theorem polar_empty : Polar 𝕜 (∅ : Set E) = univ :=
  by 
    simp only [Polar, forall_false_left, mem_empty_eq, forall_const, set_of_true]

variable {𝕜}

/-- If `x'` is a dual element such that the norms `∥x' z∥` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
theorem smul_mem_polar {s : Set E} {x' : dual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ∥x' z∥ ≤ ∥c∥) : c⁻¹ • x' ∈ Polar 𝕜 s :=
  by 
    byCases' c_zero : c = 0
    ·
      simp [c_zero]
    have eq : ∀ z, ∥c⁻¹ • x' z∥ = ∥c⁻¹∥*∥x' z∥ := fun z => norm_smul (c⁻¹) _ 
    have le : ∀ z, z ∈ s → ∥c⁻¹ • x' z∥ ≤ ∥c⁻¹∥*∥c∥
    ·
      intro z hzs 
      rw [Eq z]
      apply mul_le_mul (le_of_eqₓ rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
    have cancel : (∥c⁻¹∥*∥c∥) = 1
    ·
      simp only [c_zero, norm_eq_zero, Ne.def, not_false_iff, inv_mul_cancel, NormedField.norm_inv]
    rwa [cancel] at le

variable (𝕜)

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closed_ball {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {r : ℝ} (hr : 0 < r) :
  Polar 𝕜 (closed_ball (0 : E) r) = closed_ball (0 : dual 𝕜 E) (1 / r) :=
  by 
    ext x' 
    simp only [mem_closed_ball, mem_set_of_eq, dist_zero_right]
    constructor
    ·
      intro h 
      apply ContinuousLinearMap.op_norm_le_of_ball hr (one_div_nonneg.mpr hr.le)
      ·
        exact fun z hz => LinearMap.bound_of_ball_bound hr 1 x'.to_linear_map h z
      ·
        exact RingHomIsometric.ids
    ·
      intro h z hz 
      simp only [mem_closed_ball, dist_zero_right] at hz 
      have key :=
        (ContinuousLinearMap.le_op_norm x' z).trans (mul_le_mul h hz (norm_nonneg _) (one_div_nonneg.mpr hr.le))
      rwa [one_div_mul_cancel hr.ne.symm] at key

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x' «expr ∈ » polar 𝕜 s)
/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
theorem polar_bounded_of_nhds_zero {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) : ∃ c : ℝ, ∀ x' _ : x' ∈ Polar 𝕜 s, ∥x'∥ ≤ c :=
  by 
    obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ∥a∥ := NormedField.exists_one_lt_norm 𝕜 
    obtain ⟨r, r_pos, r_ball⟩ : ∃ (r : ℝ)(hr : 0 < r), ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhd 
    refine' ⟨∥a∥ / r, fun x' hx' => _⟩
    have I : 0 ≤ ∥a∥ / r := div_nonneg (norm_nonneg _) r_pos.le 
    refine' ContinuousLinearMap.op_norm_le_of_shell r_pos I ha fun x hx h'x => _ 
    have x_mem : x ∈ ball (0 : E) r
    ·
      simpa only [mem_ball_zero_iff] using h'x 
    calc ∥x' x∥ ≤ 1 := hx' x (r_ball x_mem)_ = (∥a∥ / r)*r / ∥a∥ :=
      by 
        fieldSimp [r_pos.ne', (zero_lt_one.trans ha).ne']_ ≤ (∥a∥ / r)*∥x∥ :=
      mul_le_mul_of_nonneg_left hx I

end PolarSets

