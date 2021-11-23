import Mathbin.Analysis.NormedSpace.HahnBanach

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

## Tags

dual
-/


noncomputable theory

open_locale Classical

universe u v

namespace NormedSpace

section General

variable(𝕜 : Type _)[NondiscreteNormedField 𝕜]

variable(E : Type _)[SemiNormedGroup E][SemiNormedSpace 𝕜 E]

variable(F : Type _)[NormedGroup F][NormedSpace 𝕜 F]

-- error in Analysis.NormedSpace.Dual: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
/-- The topological dual of a seminormed space `E`. -/
@[derive #["[", expr inhabited, ",", expr semi_normed_group, ",", expr semi_normed_space 𝕜, "]"]]
def dual :=
«expr →L[ ] »(E, 𝕜, 𝕜)

instance  : CoeFun (dual 𝕜 E) fun _ => E → 𝕜 :=
  ContinuousLinearMap.toFun

instance  : NormedGroup (dual 𝕜 F) :=
  ContinuousLinearMap.toNormedGroup

instance  : NormedSpace 𝕜 (dual 𝕜 F) :=
  ContinuousLinearMap.toNormedSpace

instance  [FiniteDimensional 𝕜 E] : FiniteDimensional 𝕜 (dual 𝕜 E) :=
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

variable(𝕜 : Type v)[IsROrC 𝕜]{E : Type u}[NormedGroup E][NormedSpace 𝕜 E]

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
      calc ∥x∥ = ∥norm' 𝕜 x∥ := (norm_norm' _ _ _).symm _ = ∥f x∥ :=
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
        apply le_cInf ContinuousLinearMap.bounds_nonempty 
        rintro c ⟨hc1, hc2⟩
        exact norm_le_dual_bound 𝕜 x hc1 hc2 }

end BidualIsometry

end NormedSpace

