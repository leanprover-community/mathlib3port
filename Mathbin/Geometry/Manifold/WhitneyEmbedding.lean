import Mathbin.Geometry.Manifold.Diffeomorph 
import Mathbin.Geometry.Manifold.Instances.Real 
import Mathbin.Geometry.Manifold.PartitionOfUnity

/-!
# Whitney embedding theorem

In this file we prove a version of the Whitney embedding theorem: for any compact real manifold `M`,
for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

## Tags

partition of unity, smooth bump function, whitney theorem
-/


universe uι uE uH uM

variable {ι : Type uι} {E : Type uE} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type uH}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

open Function Filter FiniteDimensional Set

open_locale TopologicalSpace Manifold Classical Filter BigOperators

noncomputable section 

namespace SmoothBumpCovering

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/


variable [T2Space M] [Fintype ι] {s : Set M} (f : SmoothBumpCovering ι I M s)

/-- Smooth embedding of `M` into `(E × ℝ) ^ ι`. -/
def embedding_pi_tangent : C^∞⟮I, M; 𝓘(ℝ, ι → E × ℝ), ι → E × ℝ⟯ :=
  { toFun := fun x i => (f i x • extChartAt I (f.c i) x, f i x),
    times_cont_mdiff_to_fun :=
      times_cont_mdiff_pi_space.2$
        fun i => ((f i).smooth_smul times_cont_mdiff_on_ext_chart_at).prod_mk_space (f i).Smooth }

@[local simp]
theorem embedding_pi_tangent_coe : ⇑f.embedding_pi_tangent = fun x i => (f i x • extChartAt I (f.c i) x, f i x) :=
  rfl

theorem embedding_pi_tangent_inj_on : inj_on f.embedding_pi_tangent s :=
  by 
    intro x hx y hy h 
    simp only [embedding_pi_tangent_coe, funext_iff] at h 
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj_iffₓ.1 (h (f.ind x hx))
    rw [f.apply_ind x hx] at h₂ 
    rw [←h₂, f.apply_ind x hx, one_smul, one_smul] at h₁ 
    have  := f.mem_ext_chart_at_source_of_eq_one h₂.symm 
    exact (extChartAt I (f.c _)).InjOn (f.mem_ext_chart_at_ind_source x hx) this h₁

theorem embedding_pi_tangent_injective (f : SmoothBumpCovering ι I M) : injective f.embedding_pi_tangent :=
  injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

theorem comp_embedding_pi_tangent_mfderiv (x : M) (hx : x ∈ s) :
  ((ContinuousLinearMap.fst ℝ E ℝ).comp
          (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance) (f.ind x hx))).comp
      (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embedding_pi_tangent x) =
    mfderiv I I (chart_at H (f.c (f.ind x hx))) x :=
  by 
    set L :=
      (ContinuousLinearMap.fst ℝ E ℝ).comp
        (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance) (f.ind x hx))
    have  := L.has_mfderiv_at.comp x f.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at 
    convert has_mfderiv_at_unique this _ 
    refine' (has_mfderiv_at_ext_chart_at I (f.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _ 
    refine' (f.eventually_eq_one x hx).mono fun y hy => _ 
    simp only [embedding_pi_tangent_coe, ContinuousLinearMap.coe_comp', · ∘ ·, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply]
    rw [hy, Pi.one_apply, one_smul]

theorem embedding_pi_tangent_ker_mfderiv (x : M) (hx : x ∈ s) :
  (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embedding_pi_tangent x).ker = ⊥ :=
  by 
    apply bot_unique 
    rw [←(mdifferentiable_chart I (f.c (f.ind x hx))).ker_mfderiv_eq_bot (f.mem_chart_at_ind_source x hx),
      ←comp_embedding_pi_tangent_mfderiv]
    exact LinearMap.ker_le_ker_comp _ _

theorem embedding_pi_tangent_injective_mfderiv (x : M) (hx : x ∈ s) :
  injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embedding_pi_tangent x) :=
  LinearMap.ker_eq_bot.1 (f.embedding_pi_tangent_ker_mfderiv x hx)

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
theorem exists_immersion_euclidean (f : SmoothBumpCovering ι I M) :
  ∃ (n : ℕ)(e : M → EuclideanSpace ℝ (Finₓ n)),
    Smooth I (𝓡 n) e ∧ injective e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
  by 
    set F := EuclideanSpace ℝ (Finₓ$ finrank ℝ (ι → E × ℝ))
    let this' : IsNoetherian ℝ (E × ℝ) := IsNoetherian.iff_fg.2 inferInstance 
    let this' : FiniteDimensional ℝ (ι → E × ℝ) := IsNoetherian.iff_fg.1 inferInstance 
    set eEF : (ι → E × ℝ) ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq finrank_euclidean_space_fin.symm 
    refine'
      ⟨_, eEF ∘ f.embedding_pi_tangent, eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth,
        eEF.injective.comp f.embedding_pi_tangent_injective, fun x => _⟩
    rw [mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at f.embedding_pi_tangent.mdifferentiable_at,
      eEF.mfderiv_eq]
    exact eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivialₓ)

end SmoothBumpCovering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
theorem exists_embedding_euclidean_of_compact [T2Space M] [CompactSpace M] :
  ∃ (n : ℕ)(e : M → EuclideanSpace ℝ (Finₓ n)),
    Smooth I (𝓡 n) e ∧ ClosedEmbedding e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
  by 
    rcases SmoothBumpCovering.exists_is_subordinate I is_closed_univ fun x : M _ => univ_mem with ⟨ι, f, -⟩
    have  := f.fintype 
    rcases f.exists_immersion_euclidean with ⟨n, e, hsmooth, hinj, hinj_mfderiv⟩
    exact ⟨n, e, hsmooth, hsmooth.continuous.closed_embedding hinj, hinj_mfderiv⟩

