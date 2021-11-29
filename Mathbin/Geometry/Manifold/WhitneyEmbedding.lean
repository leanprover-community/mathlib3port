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

noncomputable theory

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
theorem embedding_pi_tangent_coe :
  «expr⇑ » f.embedding_pi_tangent = fun x i => (f i x • extChartAt I (f.c i) x, f i x) :=
  rfl

-- error in Geometry.Manifold.WhitneyEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem embedding_pi_tangent_inj_on : inj_on f.embedding_pi_tangent s :=
begin
  intros [ident x, ident hx, ident y, ident hy, ident h],
  simp [] [] ["only"] ["[", expr embedding_pi_tangent_coe, ",", expr funext_iff, "]"] [] ["at", ident h],
  obtain ["⟨", ident h₁, ",", ident h₂, "⟩", ":=", expr prod.mk.inj_iff.1 (h (f.ind x hx))],
  rw ["[", expr f.apply_ind x hx, "]"] ["at", ident h₂],
  rw ["[", "<-", expr h₂, ",", expr f.apply_ind x hx, ",", expr one_smul, ",", expr one_smul, "]"] ["at", ident h₁],
  have [] [] [":=", expr f.mem_ext_chart_at_source_of_eq_one h₂.symm],
  exact [expr (ext_chart_at I (f.c _)).inj_on (f.mem_ext_chart_at_ind_source x hx) this h₁]
end

theorem embedding_pi_tangent_injective (f : SmoothBumpCovering ι I M) : injective f.embedding_pi_tangent :=
  injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

-- error in Geometry.Manifold.WhitneyEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_embedding_pi_tangent_mfderiv
(x : M)
(hx : «expr ∈ »(x, s)) : «expr = »(((continuous_linear_map.fst exprℝ() E exprℝ()).comp (@continuous_linear_map.proj exprℝ() _ ι (λ
    _, «expr × »(E, exprℝ())) _ _ (λ
    _, infer_instance) (f.ind x hx))).comp (mfderiv I «expr𝓘( , )»(exprℝ(), ι → «expr × »(E, exprℝ())) f.embedding_pi_tangent x), mfderiv I I (chart_at H (f.c (f.ind x hx))) x) :=
begin
  set [] [ident L] [] [":="] [expr (continuous_linear_map.fst exprℝ() E exprℝ()).comp (@continuous_linear_map.proj exprℝ() _ ι (λ
     _, «expr × »(E, exprℝ())) _ _ (λ _, infer_instance) (f.ind x hx))] [],
  have [] [] [":=", expr L.has_mfderiv_at.comp x f.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at],
  convert [] [expr has_mfderiv_at_unique this _] [],
  refine [expr (has_mfderiv_at_ext_chart_at I (f.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _],
  refine [expr (f.eventually_eq_one x hx).mono (λ y hy, _)],
  simp [] [] ["only"] ["[", expr embedding_pi_tangent_coe, ",", expr continuous_linear_map.coe_comp', ",", expr («expr ∘ »), ",", expr continuous_linear_map.coe_fst', ",", expr continuous_linear_map.proj_apply, "]"] [] [],
  rw ["[", expr hy, ",", expr pi.one_apply, ",", expr one_smul, "]"] []
end

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

-- error in Geometry.Manifold.WhitneyEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
theorem exists_immersion_euclidean
(f : smooth_bump_covering ι I M) : «expr∃ , »((n : exprℕ())
 (e : M → euclidean_space exprℝ() (fin n)), «expr ∧ »(smooth I «expr𝓡 »(n) e, «expr ∧ »(injective e, ∀
   x : M, injective (mfderiv I «expr𝓡 »(n) e x)))) :=
begin
  set [] [ident F] [] [":="] [expr euclidean_space exprℝ() «expr $ »(fin, finrank exprℝ() (ι → «expr × »(E, exprℝ())))] [],
  letI [] [":", expr is_noetherian exprℝ() «expr × »(E, exprℝ())] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  letI [] [":", expr finite_dimensional exprℝ() (ι → «expr × »(E, exprℝ()))] [":=", expr is_noetherian.iff_fg.1 infer_instance],
  set [] [ident eEF] [":", expr «expr ≃L[ ] »(ι → «expr × »(E, exprℝ()), exprℝ(), F)] [":="] [expr continuous_linear_equiv.of_finrank_eq finrank_euclidean_space_fin.symm] [],
  refine [expr ⟨_, «expr ∘ »(eEF, f.embedding_pi_tangent), eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth, eEF.injective.comp f.embedding_pi_tangent_injective, λ
    x, _⟩],
  rw ["[", expr mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at f.embedding_pi_tangent.mdifferentiable_at, ",", expr eEF.mfderiv_eq, "]"] [],
  exact [expr eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivial)]
end

end SmoothBumpCovering

-- error in Geometry.Manifold.WhitneyEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
theorem exists_embedding_euclidean_of_compact
[t2_space M]
[compact_space M] : «expr∃ , »((n : exprℕ())
 (e : M → euclidean_space exprℝ() (fin n)), «expr ∧ »(smooth I «expr𝓡 »(n) e, «expr ∧ »(closed_embedding e, ∀
   x : M, injective (mfderiv I «expr𝓡 »(n) e x)))) :=
begin
  rcases [expr smooth_bump_covering.exists_is_subordinate I is_closed_univ (λ
    (x : M)
    (_), univ_mem), "with", "⟨", ident ι, ",", ident f, ",", "-", "⟩"],
  haveI [] [] [":=", expr f.fintype],
  rcases [expr f.exists_immersion_euclidean, "with", "⟨", ident n, ",", ident e, ",", ident hsmooth, ",", ident hinj, ",", ident hinj_mfderiv, "⟩"],
  exact [expr ⟨n, e, hsmooth, hsmooth.continuous.closed_embedding hinj, hinj_mfderiv⟩]
end

