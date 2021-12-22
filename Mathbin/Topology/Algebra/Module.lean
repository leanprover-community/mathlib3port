import Mathbin.Topology.Algebra.Ring
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Algebra.Algebra.Basic
import Mathbin.LinearAlgebra.Projection
import Mathbin.LinearAlgebra.Pi

/-!
# Theory of topological modules and continuous linear maps.

We use the class `has_continuous_smul` for topological (semi) modules and topological vector spaces.

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `ring_hom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.

The corresponding notation for equivalences is `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/


open Filter

open_locale TopologicalSpace BigOperators Filter

universe u v w u'

section

variable {R : Type _} {M : Type _} [Ringₓ R] [TopologicalSpace R] [TopologicalSpace M] [AddCommGroupₓ M] [Module R M]

theorem HasContinuousSmul.of_nhds_zero [TopologicalRing R] [TopologicalAddGroup M]
    (hmul : tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ᶠ 𝓝 0) (𝓝 0))
    (hmulleft : ∀ m : M, tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : ∀ a : R, tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : HasContinuousSmul R M :=
  ⟨by
    rw [continuous_iff_continuous_at]
    rintro ⟨a₀, m₀⟩
    have key : ∀ p : R × M, p.1 • p.2 = (a₀ • m₀)+(((p.1 - a₀) • m₀)+a₀ • (p.2 - m₀))+(p.1 - a₀) • (p.2 - m₀) := by
      rintro ⟨a, m⟩
      simp [sub_smul, smul_sub]
      abel
    rw [funext key]
    clear key
    refine' tendsto_const_nhds.add (tendsto.add (tendsto.add _ _) _)
    ·
      rw [sub_self, zero_smul]
      apply (hmulleft m₀).comp
      rw
        [show (fun p : R × M => p.1 - a₀) = ((fun a => a - a₀) ∘ Prod.fst)by
          ext
          rfl,
        nhds_prod_eq]
      have : tendsto (fun a => a - a₀) (𝓝 a₀) (𝓝 0) := by
        rw [← sub_self a₀]
        exact tendsto_id.sub tendsto_const_nhds
      exact this.comp tendsto_fst
    ·
      rw [sub_self, smul_zero]
      apply (hmulright a₀).comp
      rw
        [show (fun p : R × M => p.2 - m₀) = ((fun m => m - m₀) ∘ Prod.snd)by
          ext
          rfl,
        nhds_prod_eq]
      have : tendsto (fun m => m - m₀) (𝓝 m₀) (𝓝 0) := by
        rw [← sub_self m₀]
        exact tendsto_id.sub tendsto_const_nhds
      exact this.comp tendsto_snd
    ·
      rw [sub_self, zero_smul, nhds_prod_eq,
        show
          (fun p : R × M => (p.fst - a₀) • (p.snd - m₀)) =
            ((fun p : R × M => p.1 • p.2) ∘ Prod.map (fun a => a - a₀) fun m => m - m₀)by
          ext
          rfl]
      apply hmul.comp (tendsto.prod_map _ _) <;>
        ·
          rw [← sub_self]
          exact tendsto_id.sub tendsto_const_nhds⟩

end

section

variable {R : Type _} {M : Type _} [Ringₓ R] [TopologicalSpace R] [TopologicalSpace M] [AddCommGroupₓ M]
  [HasContinuousAdd M] [Module R M] [HasContinuousSmul R M]

/--  If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nondiscrete normed field. -/
theorem Submodule.eq_top_of_nonempty_interior' [ne_bot (𝓝[{ x : R | IsUnit x }] 0)] (s : Submodule R M)
    (hs : (Interior (s : Set M)).Nonempty) : s = ⊤ := by
  rcases hs with ⟨y, hy⟩
  refine' Submodule.eq_top_iff'.2 $ fun x => _
  rw [mem_interior_iff_mem_nhds] at hy
  have : tendsto (fun c : R => y+c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y+(0 : R) • x))
  exact tendsto_const_nhds.add ((tendsto_nhds_within_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds)
  rw [zero_smul, add_zeroₓ] at this
  obtain ⟨_, hu : (y+_ • _) ∈ s, u, rfl⟩ := nonempty_of_mem (inter_mem (mem_map.1 (this hy)) self_mem_nhds_within)
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

variable (R M)

/--  Let `R` be a topological ring such that zero is not an isolated point (e.g., a nondiscrete
normed field, see `normed_field.punctured_nhds_ne_bot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `ne_bot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[has_continuous_smul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `real.punctured_nhds_module_ne_bot`.
One can also use `haveI := module.punctured_nhds_ne_bot R M` in a proof.
-/
theorem Module.punctured_nhds_ne_bot [Nontrivial M] [ne_bot (𝓝[≠] (0 : R))] [NoZeroSmulDivisors R M] (x : M) :
    ne_bot (𝓝[≠] x) := by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices : tendsto (fun c : R => x+c • y) (𝓝[≠] 0) (𝓝[≠] x)
  exact this.ne_bot
  refine' tendsto.inf _ (tendsto_principal_principal.2 $ _)
  ·
    convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y)
    rw [zero_smul, add_zeroₓ]
  ·
    intro c hc
    simpa [hy] using hc

end

namespace Submodule

variable {α β : Type _} [TopologicalSpace β]

instance [TopologicalSpace α] [Semiringₓ α] [AddCommMonoidₓ β] [Module α β] [HasContinuousSmul α β]
    (S : Submodule α β) : HasContinuousSmul α S where
  continuous_smul := by
    rw [embedding_subtype_coe.to_inducing.continuous_iff]
    exact continuous_fst.smul (continuous_subtype_coe.comp continuous_snd)

instance [Ringₓ α] [AddCommGroupₓ β] [Module α β] [TopologicalAddGroup β] (S : Submodule α β) : TopologicalAddGroup S :=
  S.to_add_subgroup.topological_add_group

end Submodule

section Closure

variable {R : Type u} {M : Type v} [Semiringₓ R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoidₓ M]
  [Module R M] [HasContinuousSmul R M]

theorem Submodule.closure_smul_self_subset (s : Submodule R M) :
    (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) ⊆ Closure (s : Set M) :=
  calc
    (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) =
      (fun p : R × M => p.1 • p.2) '' Closure ((Set.Univ : Set R).Prod s) :=
    by
    simp [closure_prod_eq]
    _ ⊆ Closure ((fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod s) :=
    image_closure_subset_closure_image continuous_smul
    _ = Closure s := by
    congr
    ext x
    refine' ⟨_, fun hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩⟩
    rintro ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩
    simp [s.smul_mem c hy]
    

theorem Submodule.closure_smul_self_eq (s : Submodule R M) :
    (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) = Closure (s : Set M) :=
  Set.Subset.antisymm s.closure_smul_self_subset fun x hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩

variable [HasContinuousAdd M]

/--  The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
a submodule. -/
def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  { s.to_add_submonoid.topological_closure with Carrier := Closure (s : Set M),
    smul_mem' := fun c x hx => s.closure_smul_self_subset ⟨⟨c, x⟩, ⟨Set.mem_univ _, hx⟩, rfl⟩ }

@[simp]
theorem Submodule.topological_closure_coe (s : Submodule R M) : (s.topological_closure : Set M) = Closure (s : Set M) :=
  rfl

instance Submodule.topological_closure_has_continuous_smul (s : Submodule R M) :
    HasContinuousSmul R s.topological_closure :=
  { s.to_add_submonoid.topological_closure_has_continuous_add with
    continuous_smul := by
      apply continuous_induced_rng
      change Continuous fun p : R × s.topological_closure => p.1 • (p.2 : M)
      continuity }

theorem Submodule.submodule_topological_closure (s : Submodule R M) : s ≤ s.topological_closure :=
  subset_closure

theorem Submodule.is_closed_topological_closure (s : Submodule R M) : IsClosed (s.topological_closure : Set M) := by
  convert is_closed_closure

theorem Submodule.topological_closure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topological_closure ≤ t :=
  closure_minimal h ht

theorem Submodule.topological_closure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
    s.topological_closure ≤ t.topological_closure :=
  s.topological_closure_minimal (h.trans t.submodule_topological_closure) t.is_closed_topological_closure

end Closure

/--  Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure ContinuousLinearMap {R : Type _} {S : Type _} [Semiringₓ R] [Semiringₓ S] (σ : R →+* S) (M : Type _)
  [TopologicalSpace M] [AddCommMonoidₓ M] (M₂ : Type _) [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module R M]
  [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'

notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (@starRingAut R _ _ : R →+* R) M M₂

/--  Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological ring `R`. -/
@[nolint has_inhabited_instance]
structure ContinuousLinearEquiv {R : Type _} {S : Type _} [Semiringₓ R] [Semiringₓ S] (σ : R →+* S) {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type _) [TopologicalSpace M] [AddCommMonoidₓ M] (M₂ : Type _)
  [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module R M] [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_to_fun : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'
  continuous_inv_fun : Continuous inv_fun := by
    run_tac
      tactic.interactive.continuity'

notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (@starRingAut R _ _ : R →+* R) M M₂

section PointwiseLimits

variable {M₁ M₂ α R S : Type _} [TopologicalSpace M₂] [T2Space M₂] [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M₁]
  [AddCommMonoidₓ M₂] [Module R M₁] [Module S M₂] [TopologicalSpace S] [HasContinuousSmul S M₂] [HasContinuousAdd M₂]
  {σ : R →+* S} {l : Filter α} {f : M₁ → M₂}

/--  Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps]
def linearMapOfTendsto (g : α → M₁ →ₛₗ[σ] M₂) [l.ne_bot] (h : tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
  { addMonoidHomOfTendsto (fun a => (g a).toAddMonoidHom) h with toFun := f,
    map_smul' := fun r x => by
      rw [tendsto_pi_nhds] at h
      refine' tendsto_nhds_unique (h (r • x)) _
      simpa only [LinearMap.map_smulₛₗ] using tendsto.smul tendsto_const_nhds (h x) }

end PointwiseLimits

namespace ContinuousLinearMap

section Semiringₓ

/-!
### Properties that hold for non-necessarily commutative semirings.
-/


variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ : Type _} [TopologicalSpace M₁] [AddCommMonoidₓ M₁] {M'₁ : Type _} [TopologicalSpace M'₁]
  [AddCommMonoidₓ M'₁] {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoidₓ M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoidₓ M₃] {M₄ : Type _} [TopologicalSpace M₄] [AddCommMonoidₓ M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

/--  Coerce continuous linear maps to linear maps. -/
instance : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) :=
  ⟨to_linear_map⟩

@[simp]
theorem to_linear_map_eq_coe (f : M₁ →SL[σ₁₂] M₂) : f.to_linear_map = f :=
  rfl

theorem coe_injective : Function.Injective (coeₓ : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) := by
  intro f g H
  cases f
  cases g
  congr

-- failed to format: format: uncaught backtrack exception
instance
  : AddMonoidHomClass ( M₁ →SL[ σ₁₂ ] M₂ ) M₁ M₂
  where
    coe f := f.to_fun
      coe_injective' f g h := coe_injective ( FunLike.coe_injective h )
      map_add f := map_add f.to_linear_map
      map_zero f := LinearMap.map_zero f

/--  Coerce continuous linear maps to functions. -/
instance to_fun : CoeFun (M₁ →SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) h : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) h : (mk f h : M₁ → M₂) = f :=
  rfl

@[continuity]
protected theorem Continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2

@[simp, norm_cast]
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff

theorem coe_fn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) coeFn :=
  FunLike.coe_injective

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/--  See Note [custom simps projection]. -/
def simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (to_linear_map_to_fun → apply, toLinearMap → coe)

@[ext]
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

theorem ext_iff {f g : M₁ →SL[σ₁₂] M₂} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

variable (f g : M₁ →SL[σ₁₂] M₂) (c : R₁) (h : M₂ →SL[σ₂₃] M₃) (x y z : M₁) (fₗ : M₁ →L[R₁] M'₁)

protected theorem map_zero : f (0 : M₁) = 0 :=
  map_zero f

protected theorem map_add : f (x+y) = f x+f y :=
  map_add f x y

@[simp]
theorem map_smulₛₗ : f (c • x) = σ₁₂ c • f x :=
  (to_linear_map _).map_smulₛₗ _ _

@[simp]
theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) : f (c • x) = c • f x := by
  simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
theorem map_smul_of_tower {R S : Type _} [Semiringₓ S] [HasScalar R M₁] [Module S M₁] [HasScalar R M₂] [Module S M₂]
    [LinearMap.CompatibleSmul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) : f (c • x) = c • f x :=
  LinearMap.CompatibleSmul.map_smul f c x

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `map_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`s] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder "(" [`g] [":" (Term.arrow `ι "→" `M₁)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `f
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        " in "
        `s
        ", "
        (Term.app `g [`i]))])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `f [(Term.app `g [`i])])))))
  (Command.declValSimple ":=" `f.to_linear_map.map_sum [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f.to_linear_map.map_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `f
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      " in "
      `s
      ", "
      (Term.app `g [`i]))])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
    " in "
    `s
    ", "
    (Term.app `f [(Term.app `g [`i])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   " in "
   `s
   ", "
   (Term.app `f [(Term.app `g [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [(Term.app `g [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `g [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    map_sum
    { ι : Type _ } ( s : Finset ι ) ( g : ι → M₁ ) : f ∑ i in s , g i = ∑ i in s , f g i
    := f.to_linear_map.map_sum

@[simp, norm_cast]
theorem coe_coe : ((f : M₁ →ₛₗ[σ₁₂] M₂) : M₁ → M₂) = (f : M₁ → M₂) :=
  rfl

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 $ LinearMap.ext_ring h

theorem ext_ring_iff [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩

/--  If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `submodule.span` of this set. -/
theorem eq_on_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (Closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eq_on_span' h).closure f.continuous g.continuous

/--  If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁)) {f g : M₁ →SL[σ₁₂] M₂}
    (h : Set.EqOn f g s) : f = g :=
  ext $ fun x => eq_on_closure_span h (hs x)

/--  Under a continuous linear map, the image of the `topological_closure` of a submodule is
contained in the `topological_closure` of its image. -/
theorem _root_.submodule.topological_closure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁] [TopologicalSpace R₂]
    [HasContinuousSmul R₁ M₁] [HasContinuousAdd M₁] [HasContinuousSmul R₂ M₂] [HasContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂)
    (s : Submodule R₁ M₁) :
    s.topological_closure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤ (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/--  Under a dense continuous linear map, a submodule whose `topological_closure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.dense_range.topological_closure_map_submodule [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [HasContinuousSmul R₁ M₁] [HasContinuousAdd M₁] [HasContinuousSmul R₂ M₂]
    [HasContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f) {s : Submodule R₁ M₁}
    (hs : s.topological_closure = ⊤) : (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs⊢
  simp only [Submodule.topological_closure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs⊢
  exact hf'.dense_image f.continuous hs

/--  The continuous map that is constantly zero. -/
instance : HasZero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

instance : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : default (M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp]
theorem zero_apply : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

@[norm_cast]
theorem coe_zero' : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = 0 :=
  rfl

instance unique_of_left [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

instance unique_of_right [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

section

variable (R₁ M₁)

/--  the identity map as a continuous linear map. -/
def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end

instance : HasOne (M₁ →L[R₁] M₁) :=
  ⟨id R₁ M₁⟩

theorem one_def : (1 : M₁ →L[R₁] M₁) = id R₁ M₁ :=
  rfl

theorem id_apply : id R₁ M₁ x = x :=
  rfl

@[simp, norm_cast]
theorem coe_id : (id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, norm_cast]
theorem coe_id' : (id R₁ M₁ : M₁ → M₁) = _root_.id :=
  rfl

@[simp, norm_cast]
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = id _ _ := by
  rw [← coe_id, coe_inj]

@[simp]
theorem one_apply : (1 : M₁ →L[R₁] M₁) x = x :=
  rfl

section Add

variable [HasContinuousAdd M₂]

instance : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f+g, f.2.add g.2⟩⟩

theorem continuous_nsmul (n : ℕ) : Continuous fun x : M₂ => n • x := by
  induction' n with n ih
  ·
    simp [continuous_const]
  ·
    simp [Nat.succ_eq_add_one, add_smul]
    exact ih.add continuous_id

@[continuity]
theorem continuous.nsmul {α : Type _} [TopologicalSpace α] {n : ℕ} {f : α → M₂} (hf : Continuous f) :
    Continuous fun x : α => n • f x :=
  (continuous_nsmul n).comp hf

@[simp]
theorem add_apply : (f+g) x = f x+g x :=
  rfl

@[simp, norm_cast]
theorem coe_add : ((f+g : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = f+g :=
  rfl

@[norm_cast]
theorem coe_add' : ((f+g : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = (f : M₁ → M₂)+g :=
  rfl

-- failed to format: format: uncaught backtrack exception
instance
  : AddCommMonoidₓ ( M₁ →SL[ σ₁₂ ] M₂ )
  where
    zero := ( 0 : M₁ →SL[ σ₁₂ ] M₂ )
      add := · + ·
      zero_add := by intros <;> ext <;> apply_rules [ zero_addₓ , add_assocₓ , add_zeroₓ , add_left_negₓ , add_commₓ ]
      add_zero := by intros <;> ext <;> apply_rules [ zero_addₓ , add_assocₓ , add_zeroₓ , add_left_negₓ , add_commₓ ]
      add_comm := by intros <;> ext <;> apply_rules [ zero_addₓ , add_assocₓ , add_zeroₓ , add_left_negₓ , add_commₓ ]
      add_assoc := by intros <;> ext <;> apply_rules [ zero_addₓ , add_assocₓ , add_zeroₓ , add_left_negₓ , add_commₓ ]
      nsmul n f := { toFun := fun x => n • f x , map_add' := by simp , map_smul' := by simp [ smul_comm n ] }
      nsmul_zero' f := by ext simp
      nsmul_succ' n f := by ext simp [ Nat.succ_eq_one_add , add_smul ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.normCast "norm_cast" []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `coe_sum [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`t] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow `ι "→" (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Init.Coe.«term↑_»
      "↑"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       `t
       ", "
       (Term.app `f [`d])))
     "="
     (Term.paren
      "("
      [(Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
        " in "
        `t
        ", "
        (Term.app `f [`d]))
       [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂))]]
      ")"))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj
     (Term.app
      `AddMonoidHom.mk
      [(Term.paren
        "("
        [`coeₓ
         [(Term.typeAscription
           ":"
           (Term.arrow
            (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
            "→"
            (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
        ")")
       `rfl
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))])
     "."
     `map_sum)
    [(Term.hole "_") (Term.hole "_")])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `AddMonoidHom.mk
     [(Term.paren
       "("
       [`coeₓ
        [(Term.typeAscription
          ":"
          (Term.arrow
           (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
           "→"
           (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
       ")")
      `rfl
      (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))])
    "."
    `map_sum)
   [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    `AddMonoidHom.mk
    [(Term.paren
      "("
      [`coeₓ
       [(Term.typeAscription
         ":"
         (Term.arrow
          (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
          "→"
          (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
      ")")
     `rfl
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))])
   "."
   `map_sum)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `AddMonoidHom.mk
   [(Term.paren
     "("
     [`coeₓ
      [(Term.typeAscription
        ":"
        (Term.arrow
         (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
         "→"
         (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
     ")")
    `rfl
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [`coeₓ
    [(Term.typeAscription
      ":"
      (Term.arrow
       (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
       "→"
       (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
   "→"
   (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Module.LinearMap.«term_→ₛₗ[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `M₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Algebra.Module.«term_→SL[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `M₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `coeₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AddMonoidHom.mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `AddMonoidHom.mk
   [(Term.paren
     "("
     [`coeₓ
      [(Term.typeAscription
        ":"
        (Term.arrow
         (Term.paren "(" [(Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂) []] ")")
         "→"
         (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)))]]
     ")")
    `rfl
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Init.Coe.«term↑_»
    "↑"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
     " in "
     `t
     ", "
     (Term.app `f [`d])))
   "="
   (Term.paren
    "("
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
      " in "
      `t
      ", "
      (Term.app `f [`d]))
     [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂))]]
    ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
     " in "
     `t
     ", "
     (Term.app `f [`d]))
    [(Term.typeAscription ":" (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Module.LinearMap.«term_→ₛₗ[_]_» `M₁ " →ₛₗ[" `σ₁₂ "] " `M₂)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Module.LinearMap.«term_→ₛₗ[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `M₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `σ₁₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `M₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
   " in "
   `t
   ", "
   (Term.app `f [`d]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ]
  theorem
    coe_sum
    { ι : Type _ } ( t : Finset ι ) ( f : ι → M₁ →SL[ σ₁₂ ] M₂ )
      : ↑ ∑ d in t , f d = ( ∑ d in t , f d : M₁ →ₛₗ[ σ₁₂ ] M₂ )
    := AddMonoidHom.mk ( coeₓ : M₁ →SL[ σ₁₂ ] M₂ → M₁ →ₛₗ[ σ₁₂ ] M₂ ) rfl fun _ _ => rfl . map_sum _ _

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes
    "@["
    [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
     ","
     (Term.attrInstance (Term.attrKind []) (Attr.normCast "norm_cast" []))]
    "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `coe_sum' [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`t] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow `ι "→" (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Init.Coe.«term⇑_»
      "⇑"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       `t
       ", "
       (Term.app `f [`d])))
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
      " in "
      `t
      ", "
      (Term.app `f [`d])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] ["←"] `coe_coe)
           ","
           (Tactic.simpLemma [] [] `coe_sum)
           ","
           (Tactic.simpLemma [] [] `LinearMap.coe_fn_sum)]
          "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] ["←"] `coe_coe)
          ","
          (Tactic.simpLemma [] [] `coe_sum)
          ","
          (Tactic.simpLemma [] [] `LinearMap.coe_fn_sum)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] ["←"] `coe_coe)
     ","
     (Tactic.simpLemma [] [] `coe_sum)
     ","
     (Tactic.simpLemma [] [] `LinearMap.coe_fn_sum)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.coe_fn_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Init.Coe.«term⇑_»
    "⇑"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
     " in "
     `t
     ", "
     (Term.app `f [`d])))
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
    " in "
    `t
    ", "
    (Term.app `f [`d])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
   " in "
   `t
   ", "
   (Term.app `f [`d]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`d])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ]
  theorem
    coe_sum'
    { ι : Type _ } ( t : Finset ι ) ( f : ι → M₁ →SL[ σ₁₂ ] M₂ ) : ⇑ ∑ d in t , f d = ∑ d in t , f d
    := by simp only [ ← coe_coe , coe_sum , LinearMap.coe_fn_sum ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `sum_apply [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [":" (Term.type "Type" [(Level.hole "_")])] "}")
    (Term.explicitBinder "(" [`t] [":" (Term.app `Finset [`ι])] [] ")")
    (Term.explicitBinder
     "("
     [`f]
     [":" (Term.arrow `ι "→" (Topology.Algebra.Module.«term_→SL[_]_» `M₁ " →SL[" `σ₁₂ "] " `M₂))]
     []
     ")")
    (Term.explicitBinder "(" [`b] [":" `M₁] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       `t
       ", "
       (Term.app `f [`d]))
      [`b])
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
      " in "
      `t
      ", "
      (Term.app `f [`d `b])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `coe_sum') "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `coe_sum') "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `coe_sum') "," (Tactic.simpLemma [] [] `Finset.sum_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `coe_sum'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
     " in "
     `t
     ", "
     (Term.app `f [`d]))
    [`b])
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
    " in "
    `t
    ", "
    (Term.app `f [`d `b])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
   " in "
   `t
   ", "
   (Term.app `f [`d `b]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`d `b])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  sum_apply
  { ι : Type _ } ( t : Finset ι ) ( f : ι → M₁ →SL[ σ₁₂ ] M₂ ) ( b : M₁ ) : ∑ d in t , f d b = ∑ d in t , f d b
  := by simp only [ coe_sum' , Finset.sum_apply ]

end Add

variable {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/--  Composition of bounded linear maps. -/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp (↑f), g.2.comp f.2⟩

infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _)
    RingHomCompTriple.ids

@[simp, norm_cast]
theorem coe_comp : (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

include σ₁₃

@[simp, norm_cast]
theorem coe_comp' : (h.comp f : M₁ → M₃) = ((h : M₂ → M₃) ∘ f) :=
  rfl

theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl

omit σ₁₃

@[simp]
theorem comp_id : f.comp (id R₁ M₁) = f :=
  ext $ fun x => rfl

@[simp]
theorem id_comp : (id R₂ M₂).comp f = f :=
  ext $ fun x => rfl

include σ₁₃

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 := by
  ext
  simp

@[simp]
theorem comp_add [HasContinuousAdd M₂] [HasContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M₁ →SL[σ₁₂] M₂) :
    g.comp (f₁+f₂) = g.comp f₁+g.comp f₂ := by
  ext
  simp

@[simp]
theorem add_comp [HasContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁+g₂).comp f = g₁.comp f+g₂.comp f := by
  ext
  simp

omit σ₁₃

theorem comp_assoc {R₄ : Type _} [Semiringₓ R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₃₄ : R₃ →+* R₄}
    [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄)
    (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩

theorem mul_def (f g : M₁ →L[R₁] M₁) : (f*g) = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : (⇑f*g) = (f ∘ g) :=
  rfl

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f*g) x = f (g x) :=
  rfl

/--  The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def Prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) : M₁ →L[R₁] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R₁] M₂).Prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section

variable (R₁ M₁ M₂)

/--  The left injection into a product is a continuous linear map. -/
def inl [Module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ :=
  (id R₁ M₁).Prod 0

/--  The right injection into a product is a continuous linear map. -/
def inr [Module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ :=
  (0 : M₂ →L[R₁] M₁).Prod (id R₁ M₂)

end

@[simp]
theorem inl_apply [Module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
theorem inr_apply [Module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) :=
  rfl

@[simp, norm_cast]
theorem coe_inl [Module R₁ M₂] : (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = LinearMap.inl R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_inr [Module R₁ M₂] : (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = LinearMap.inr R₁ M₁ M₂ :=
  rfl

/--  Kernel of a continuous linear map. -/
def ker (f : M₁ →SL[σ₁₂] M₂) : Submodule R₁ M₁ :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker

@[norm_cast]
theorem ker_coe : (f : M₁ →ₛₗ[σ₁₂] M₂).ker = f.ker :=
  rfl

@[simp]
theorem mem_ker {f : M₁ →SL[σ₁₂] M₂} {x} : x ∈ f.ker ↔ f x = 0 :=
  LinearMap.mem_ker

theorem is_closed_ker [T1Space M₂] : IsClosed (f.ker : Set M₁) :=
  continuous_iff_is_closed.1 f.cont _ is_closed_singleton

@[simp]
theorem apply_ker (x : f.ker) : f x = 0 :=
  mem_ker.1 x.2

theorem is_complete_ker {M' : Type _} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoidₓ M'] [Module R₁ M']
    [T1Space M₂] (f : M' →SL[σ₁₂] M₂) : IsComplete (f.ker : Set M') :=
  f.is_closed_ker.is_complete

instance complete_space_ker {M' : Type _} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoidₓ M'] [Module R₁ M']
    [T1Space M₂] (f : M' →SL[σ₁₂] M₂) : CompleteSpace f.ker :=
  f.is_closed_ker.complete_space_coe

@[simp]
theorem ker_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) : ker (f.prod g) = ker f⊓ker g :=
  LinearMap.ker_prod f g

/--  Range of a continuous linear map. -/
def range [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) : Submodule R₂ M₂ :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).range

theorem range_coe [RingHomSurjective σ₁₂] : (f.range : Set M₂) = Set.Range f :=
  LinearMap.range_coe _

theorem mem_range [RingHomSurjective σ₁₂] {f : M₁ →SL[σ₁₂] M₂} {y} : y ∈ f.range ↔ ∃ x, f x = y :=
  LinearMap.mem_range

theorem mem_range_self [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

theorem range_prod_le [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    range (f.prod g) ≤ (range f).Prod (range g) :=
  (f : M₁ →ₗ[R₁] M₂).range_prod_le g

/--  Restrict codomain of a continuous linear map. -/
def cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) : M₁ →SL[σ₁₂] p :=
  { cont := continuous_subtype_mk h f.continuous, toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h }

@[norm_cast]
theorem coe_cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.cod_restrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h :=
  rfl

@[simp]
theorem coe_cod_restrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) x :
    (f.cod_restrict p h x : M₂) = f x :=
  rfl

@[simp]
theorem ker_cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.cod_restrict p h) = ker f :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker_cod_restrict p h

/--  Embedding of a submodule into the ambient space as a continuous linear map. -/
def subtype_val (p : Submodule R₁ M₁) : p →L[R₁] M₁ :=
  { cont := continuous_subtype_val, toLinearMap := p.subtype }

@[simp, norm_cast]
theorem coe_subtype_val (p : Submodule R₁ M₁) : (subtype_val p : p →ₗ[R₁] M₁) = p.subtype :=
  rfl

@[simp, norm_cast]
theorem subtype_val_apply (p : Submodule R₁ M₁) (x : p) : (subtype_val p : p → M₁) x = x :=
  rfl

variable (R₁ M₁ M₂)

/--  `prod.fst` as a `continuous_linear_map`. -/
def fst [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₁ :=
  { cont := continuous_fst, toLinearMap := LinearMap.fst R₁ M₁ M₂ }

/--  `prod.snd` as a `continuous_linear_map`. -/
def snd [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₂ :=
  { cont := continuous_snd, toLinearMap := LinearMap.snd R₁ M₁ M₂ }

variable {R₁ M₁ M₂}

@[simp, norm_cast]
theorem coe_fst [Module R₁ M₂] : (fst R₁ M₁ M₂ : M₁ × M₂ →ₗ[R₁] M₁) = LinearMap.fst R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_fst' [Module R₁ M₂] : (fst R₁ M₁ M₂ : M₁ × M₂ → M₁) = Prod.fst :=
  rfl

@[simp, norm_cast]
theorem coe_snd [Module R₁ M₂] : (snd R₁ M₁ M₂ : M₁ × M₂ →ₗ[R₁] M₂) = LinearMap.snd R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_snd' [Module R₁ M₂] : (snd R₁ M₁ M₂ : M₁ × M₂ → M₂) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd [Module R₁ M₂] : (fst R₁ M₁ M₂).Prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext $ fun ⟨x, y⟩ => rfl

@[simp]
theorem fst_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (fst R₁ M₂ M₃).comp (f.prod g) = f :=
  ext $ fun x => rfl

@[simp]
theorem snd_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (snd R₁ M₂ M₃).comp (f.prod g) = g :=
  ext $ fun x => rfl

/--  `prod.map` of two continuous linear maps. -/
def prod_mapₓ [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    M₁ × M₃ →L[R₁] M₂ × M₄ :=
  (f₁.comp (fst R₁ M₁ M₃)).Prod (f₂.comp (snd R₁ M₁ M₃))

@[simp, norm_cast]
theorem coe_prod_map [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    (f₁.prod_map f₂ : M₁ × M₃ →ₗ[R₁] M₂ × M₄) = (f₁ : M₁ →ₗ[R₁] M₂).prod_map (f₂ : M₃ →ₗ[R₁] M₄) :=
  rfl

@[simp, norm_cast]
theorem coe_prod_map' [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    ⇑f₁.prod_map f₂ = Prod.map f₁ f₂ :=
  rfl

/--  The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [Module R₁ M₂] [Module R₁ M₃] [HasContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) :
    M₁ × M₂ →L[R₁] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[norm_cast, simp]
theorem coe_coprod [Module R₁ M₂] [Module R₁ M₃] [HasContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) :
    (f₁.coprod f₂ : M₁ × M₂ →ₗ[R₁] M₃) = LinearMap.coprod f₁ f₂ :=
  rfl

@[simp]
theorem coprod_apply [Module R₁ M₂] [Module R₁ M₃] [HasContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) x :
    f₁.coprod f₂ x = f₁ x.1+f₂ x.2 :=
  rfl

theorem range_coprod [Module R₁ M₂] [Module R₁ M₃] [HasContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) :
    (f₁.coprod f₂).range = f₁.range⊔f₂.range :=
  LinearMap.range_coprod _ _

section

variable {R S : Type _} [Semiringₓ R] [Semiringₓ S] [Module R M₁] [Module R M₂] [Module R S] [Module S M₂]
  [IsScalarTower R S M₂] [TopologicalSpace S] [HasContinuousSmul S M₂]

/--  The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `continuous_linear_map.smul_rightₗ` and `continuous_linear_map.smul_rightL`. -/
def smul_right (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.to_linear_map.smul_right f with cont := c.2.smul continuous_const }

@[simp]
theorem smul_right_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} : (smul_right c f : M₁ → M₂) x = c x • f :=
  rfl

end

section Pointwise

open_locale Pointwise

@[simp]
theorem image_smul_setₛₗ (c : R₁) (s : Set M₁) : f '' (c • s) = σ₁₂ c • f '' s :=
  f.to_linear_map.image_smul_setₛₗ c s

theorem image_smul_set (c : R₁) (s : Set M₁) : fₗ '' (c • s) = c • fₗ '' s :=
  fₗ.to_linear_map.image_smul_set c s

theorem preimage_smul_setₛₗ {c : R₁} (hc : IsUnit c) (s : Set M₂) : f ⁻¹' (σ₁₂ c • s) = c • f ⁻¹' s :=
  f.to_linear_map.preimage_smul_setₛₗ hc s

theorem preimage_smul_set {c : R₁} (hc : IsUnit c) (s : Set M'₁) : fₗ ⁻¹' (c • s) = c • fₗ ⁻¹' s :=
  fₗ.to_linear_map.preimage_smul_set hc s

end Pointwise

variable [Module R₁ M₂] [TopologicalSpace R₁] [HasContinuousSmul R₁ M₂]

@[simp]
theorem smul_right_one_one (c : R₁ →L[R₁] M₂) : smul_right (1 : R₁ →L[R₁] R₁) (c 1) = c := by
  ext <;> simp [← ContinuousLinearMap.map_smul_of_tower]

@[simp]
theorem smul_right_one_eq_iff {f f' : M₂} :
    smul_right (1 : R₁ →L[R₁] R₁) f = smul_right (1 : R₁ →L[R₁] R₁) f' ↔ f = f' := by
  simp only [ext_ring_iff, smul_right_apply, one_apply, one_smul]

theorem smul_right_comp [HasContinuousMul R₁] {x : M₂} {c : R₁} :
    (smul_right (1 : R₁ →L[R₁] R₁) x).comp (smul_right (1 : R₁ →L[R₁] R₁) c) = smul_right (1 : R₁ →L[R₁] R₁) (c • x) :=
  by
  ext
  simp [mul_smul]

end Semiringₓ

section Pi

variable {R : Type _} [Semiringₓ R] {M : Type _} [TopologicalSpace M] [AddCommMonoidₓ M] [Module R M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module R M₂] {ι : Type _} {φ : ι → Type _} [∀ i, TopologicalSpace (φ i)]
  [∀ i, AddCommMonoidₓ (φ i)] [∀ i, Module R (φ i)]

/--  `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).Continuous⟩

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑pi f = fun c i => f i c :=
  rfl

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [ext_iff, pi_apply, Function.funext_iffₓ]
  exact forall_swap

theorem pi_zero : pi (fun i => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext $ fun _ => rfl

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) : (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/--  The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext $ fun c => rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `infi_ker_proj [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.paren
      "("
      [(Order.CompleteLattice.«term⨅_,_»
        "⨅"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
        ", "
        (Term.app `ker [(Term.app `proj [`i])]))
       [(Term.typeAscription
         ":"
         (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
      ")")
     "="
     (Order.BoundedOrder.«term⊥» "⊥"))))
  (Command.declValSimple ":=" `LinearMap.infi_ker_proj [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `LinearMap.infi_ker_proj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Order.CompleteLattice.«term⨅_,_»
      "⨅"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
      ", "
      (Term.app `ker [(Term.app `proj [`i])]))
     [(Term.typeAscription
       ":"
       (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
    ")")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren
   "("
   [(Order.CompleteLattice.«term⨅_,_»
     "⨅"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
     ", "
     (Term.app `ker [(Term.app `proj [`i])]))
    [(Term.typeAscription
      ":"
      (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `φ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i])) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Submodule
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.CompleteLattice.«term⨅_,_»
   "⨅"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
   ", "
   (Term.app `ker [(Term.app `proj [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ker [(Term.app `proj [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `proj [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `proj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `proj [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ker
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem infi_ker_proj : ( ⨅ i , ker proj i : Submodule R ∀ i , φ i ) = ⊥ := LinearMap.infi_ker_proj

variable (R φ)

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (i «expr ∈ » J)
-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (i «expr ∈ » J)
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections\nof `φ` is linearly equivalent to the product over `I`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `infi_ker_proj_equiv [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`I `J] [":" (Term.app `Set [`ι])] "}")
    (Term.instBinder
     "["
     []
     (Term.app
      `DecidablePred
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Init.Core.«term_∈_» `i " ∈ " `I)))])
     "]")
    (Term.explicitBinder "(" [`hd] [":" (Term.app `Disjoint [`I `J])] [] ")")
    (Term.explicitBinder
     "("
     [`hu]
     [":" (Init.Core.«term_⊆_» `Set.Univ " ⊆ " (Init.Core.«term_∪_» `I " ∪ " `J))]
     []
     ")")]
   [(Term.typeSpec
     ":"
     (Topology.Algebra.Module.«term_≃L[_]_»
      (Term.paren
       "("
       [(Order.CompleteLattice.«term⨅_,_»
         "⨅"
         (Lean.explicitBinders
          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
           (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
         ", "
         (Term.app `ker [(Term.app `proj [`i])]))
        [(Term.typeAscription
          ":"
          (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
       ")")
      " ≃L["
      `R
      "] "
      (Term.forall "∀" [(Term.simpleBinder [`i] [(Term.typeSpec ":" `I)])] "," (Term.app `φ [`i]))))])
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(Term.app `LinearMap.infiKerProjEquiv [`R `φ `hd `hu])
     ","
     (Term.app
      `continuous_pi
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`i] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 []
                 ":="
                 (Term.app
                  (Term.explicit "@" `continuous_subtype_coe)
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x] [])]
                     "=>"
                     (Init.Core.«term_∈_»
                      `x
                      " ∈ "
                      (Term.paren
                       "("
                       [(Order.CompleteLattice.«term⨅_,_»
                         "⨅"
                         (Lean.explicitBinders
                          [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                           (Lean.bracketedExplicitBinders
                            "("
                            [(Lean.binderIdent "_")]
                            ":"
                            (Init.Core.«term_∈_» `i " ∈ " `J)
                            ")")])
                         ", "
                         (Term.app `ker [(Term.app `proj [`i])]))
                        [(Term.typeAscription
                          ":"
                          (Term.app
                           `Submodule
                           [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
                       ")"))))]))))
              [])
             (group
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 []
                 ":="
                 (Term.app
                  `Continuous.comp
                  [(Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
                   `this]))))
              [])
             (group (Tactic.exact "exact" `this) [])])))))])
     ","
     (Term.app
      `continuous_subtype_mk
      [(Term.hole "_")
       (Term.app
        `continuous_pi
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`i] [])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
               (group
                (Tactic.«tactic_<;>[_]»
                 (Tactic.splitIfs "split_ifs" [] [])
                 "<;>"
                 "["
                 [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
                 "]")
                [])])))))])])]
    "⟩")
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `LinearMap.infiKerProjEquiv [`R `φ `hd `hu])
    ","
    (Term.app
     `continuous_pi
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`i] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 (Term.explicit "@" `continuous_subtype_coe)
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [])]
                    "=>"
                    (Init.Core.«term_∈_»
                     `x
                     " ∈ "
                     (Term.paren
                      "("
                      [(Order.CompleteLattice.«term⨅_,_»
                        "⨅"
                        (Lean.explicitBinders
                         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                          (Lean.bracketedExplicitBinders
                           "("
                           [(Lean.binderIdent "_")]
                           ":"
                           (Init.Core.«term_∈_» `i " ∈ " `J)
                           ")")])
                        ", "
                        (Term.app `ker [(Term.app `proj [`i])]))
                       [(Term.typeAscription
                         ":"
                         (Term.app
                          `Submodule
                          [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
                      ")"))))]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 `Continuous.comp
                 [(Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
                  `this]))))
             [])
            (group (Tactic.exact "exact" `this) [])])))))])
    ","
    (Term.app
     `continuous_subtype_mk
     [(Term.hole "_")
      (Term.app
       `continuous_pi
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
              (group
               (Tactic.«tactic_<;>[_]»
                (Tactic.splitIfs "split_ifs" [] [])
                "<;>"
                "["
                [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
                "]")
               [])])))))])])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `continuous_subtype_mk
   [(Term.hole "_")
    (Term.app
     `continuous_pi
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`i] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
            (group
             (Tactic.«tactic_<;>[_]»
              (Tactic.splitIfs "split_ifs" [] [])
              "<;>"
              "["
              [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
              "]")
             [])])))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `continuous_pi
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
          (group
           (Tactic.«tactic_<;>[_]»
            (Tactic.splitIfs "split_ifs" [] [])
            "<;>"
            "["
            [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
            "]")
           [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
        (group
         (Tactic.«tactic_<;>[_]»
          (Tactic.splitIfs "split_ifs" [] [])
          "<;>"
          "["
          [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
          "]")
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.«tactic_<;>[_]»
        (Tactic.splitIfs "split_ifs" [] [])
        "<;>"
        "["
        [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
        "]")
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>[_]»
   (Tactic.splitIfs "split_ifs" [] [])
   "<;>"
   "["
   [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
   "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>[_]»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `continuous_zero)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" `continuous_apply)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `continuous_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.splitIfs', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_pi
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `continuous_pi
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
          (group
           (Tactic.«tactic_<;>[_]»
            (Tactic.splitIfs "split_ifs" [] [])
            "<;>"
            "["
            [(Tactic.apply "apply" `continuous_apply) "," (Tactic.exact "exact" `continuous_zero)]
            "]")
           [])])))))])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_subtype_mk
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `continuous_pi
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               (Term.explicit "@" `continuous_subtype_coe)
               [(Term.hole "_")
                (Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`x] [])]
                  "=>"
                  (Init.Core.«term_∈_»
                   `x
                   " ∈ "
                   (Term.paren
                    "("
                    [(Order.CompleteLattice.«term⨅_,_»
                      "⨅"
                      (Lean.explicitBinders
                       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                        (Lean.bracketedExplicitBinders
                         "("
                         [(Lean.binderIdent "_")]
                         ":"
                         (Init.Core.«term_∈_» `i " ∈ " `J)
                         ")")])
                      ", "
                      (Term.app `ker [(Term.app `proj [`i])]))
                     [(Term.typeAscription
                       ":"
                       (Term.app
                        `Submodule
                        [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
                    ")"))))]))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `Continuous.comp
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
                `this]))))
           [])
          (group (Tactic.exact "exact" `this) [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            []
            ":="
            (Term.app
             (Term.explicit "@" `continuous_subtype_coe)
             [(Term.hole "_")
              (Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x] [])]
                "=>"
                (Init.Core.«term_∈_»
                 `x
                 " ∈ "
                 (Term.paren
                  "("
                  [(Order.CompleteLattice.«term⨅_,_»
                    "⨅"
                    (Lean.explicitBinders
                     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                      (Lean.bracketedExplicitBinders
                       "("
                       [(Lean.binderIdent "_")]
                       ":"
                       (Init.Core.«term_∈_» `i " ∈ " `J)
                       ")")])
                    ", "
                    (Term.app `ker [(Term.app `proj [`i])]))
                   [(Term.typeAscription
                     ":"
                     (Term.app
                      `Submodule
                      [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
                  ")"))))]))))
         [])
        (group
         (Tactic.tacticHave_
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            []
            ":="
            (Term.app
             `Continuous.comp
             [(Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
              `this]))))
         [])
        (group (Tactic.exact "exact" `this) [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           (Term.explicit "@" `continuous_subtype_coe)
           [(Term.hole "_")
            (Term.hole "_")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x] [])]
              "=>"
              (Init.Core.«term_∈_»
               `x
               " ∈ "
               (Term.paren
                "("
                [(Order.CompleteLattice.«term⨅_,_»
                  "⨅"
                  (Lean.explicitBinders
                   [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
                    (Lean.bracketedExplicitBinders
                     "("
                     [(Lean.binderIdent "_")]
                     ":"
                     (Init.Core.«term_∈_» `i " ∈ " `J)
                     ")")])
                  ", "
                  (Term.app `ker [(Term.app `proj [`i])]))
                 [(Term.typeAscription
                   ":"
                   (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
                ")"))))]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           `Continuous.comp
           [(Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
            `this]))))
       [])
      (group (Tactic.exact "exact" `this) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `this)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      `Continuous.comp
      [(Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
       `this]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Continuous.comp
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
    `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `continuous_apply [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `continuous_apply [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `continuous_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.exact "exact" (Term.app `continuous_apply [`i])) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Continuous.comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      (Term.explicit "@" `continuous_subtype_coe)
      [(Term.hole "_")
       (Term.hole "_")
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x] [])]
         "=>"
         (Init.Core.«term_∈_»
          `x
          " ∈ "
          (Term.paren
           "("
           [(Order.CompleteLattice.«term⨅_,_»
             "⨅"
             (Lean.explicitBinders
              [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
               (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
             ", "
             (Term.app `ker [(Term.app `proj [`i])]))
            [(Term.typeAscription
              ":"
              (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
           ")"))))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `continuous_subtype_coe)
   [(Term.hole "_")
    (Term.hole "_")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Init.Core.«term_∈_»
       `x
       " ∈ "
       (Term.paren
        "("
        [(Order.CompleteLattice.«term⨅_,_»
          "⨅"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
          ", "
          (Term.app `ker [(Term.app `proj [`i])]))
         [(Term.typeAscription
           ":"
           (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
        ")"))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Init.Core.«term_∈_»
     `x
     " ∈ "
     (Term.paren
      "("
      [(Order.CompleteLattice.«term⨅_,_»
        "⨅"
        (Lean.explicitBinders
         [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
          (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
        ", "
        (Term.app `ker [(Term.app `proj [`i])]))
       [(Term.typeAscription
         ":"
         (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
      ")"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_»
   `x
   " ∈ "
   (Term.paren
    "("
    [(Order.CompleteLattice.«term⨅_,_»
      "⨅"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
      ", "
      (Term.app `ker [(Term.app `proj [`i])]))
     [(Term.typeAscription
       ":"
       (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
    ")"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Order.CompleteLattice.«term⨅_,_»
     "⨅"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
     ", "
     (Term.app `ker [(Term.app `proj [`i])]))
    [(Term.typeAscription
      ":"
      (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Submodule [`R (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `φ [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `φ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.forall "∀" [(Term.simpleBinder [`i] [])] "," (Term.app `φ [`i])) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `R
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Submodule
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.CompleteLattice.«term⨅_,_»
   "⨅"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `i)] ":" (Term.hole "_") ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Init.Core.«term_∈_» `i " ∈ " `J) ")")])
   ", "
   (Term.app `ker [(Term.app `proj [`i])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.CompleteLattice.«term⨅_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ker [(Term.app `proj [`i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `proj [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `proj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `proj [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ker
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
    of `φ` is linearly equivalent to the product over `I`. -/
  def
    infi_ker_proj_equiv
    { I J : Set ι } [ DecidablePred fun i => i ∈ I ] ( hd : Disjoint I J ) ( hu : Set.Univ ⊆ I ∪ J )
      : ( ⨅ ( i : _ ) ( _ : i ∈ J ) , ker proj i : Submodule R ∀ i , φ i ) ≃L[ R ] ∀ i : I , φ i
    :=
      ⟨
        LinearMap.infiKerProjEquiv R φ hd hu
          ,
          continuous_pi
            fun
              i
                =>
                by
                  have
                      :=
                        @ continuous_subtype_coe
                          _ _ fun x => x ∈ ( ⨅ ( i : _ ) ( _ : i ∈ J ) , ker proj i : Submodule R ∀ i , φ i )
                    have := Continuous.comp by exact continuous_apply i this
                    exact this
          ,
          continuous_subtype_mk
            _ continuous_pi fun i => by dsimp split_ifs <;> [ apply continuous_apply , exact continuous_zero ]
        ⟩

end Pi

section Ringₓ

variable {R : Type _} [Ringₓ R] {R₂ : Type _} [Ringₓ R₂] {M : Type _} [TopologicalSpace M] [AddCommGroupₓ M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroupₓ M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroupₓ M₃]
  {M₄ : Type _} [TopologicalSpace M₄] [AddCommGroupₓ M₄] [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂}

section

variable (f g : M →SL[σ₁₂] M₂) (x y : M)

protected theorem map_neg : f (-x) = -f x :=
  (to_linear_map _).map_neg _

protected theorem map_sub : f (x - y) = f x - f y :=
  (to_linear_map _).map_sub _ _

@[simp]
theorem sub_apply' (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end

section

variable [Module R M₂] [Module R M₃] [Module R M₄]

variable (c : R) (f g : M →L[R] M₂) (h : M₂ →L[R] M₃) (x y z : M)

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f⊔ker g = ⊤) :
    range (f.prod g) = (range f).Prod (range g) :=
  LinearMap.range_prod_eq h

theorem ker_prod_ker_le_ker_coprod [HasContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (ker f).Prod (ker g) ≤ ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.to_linear_map g.to_linear_map

theorem ker_coprod_of_disjoint_range [HasContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃)
    (hd : Disjoint f.range g.range) : ker (f.coprod g) = (ker f).Prod (ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.to_linear_map g.to_linear_map hd

end

section

variable [TopologicalAddGroup M₂]

variable (f g : M →SL[σ₁₂] M₂) (x y : M)

instance : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp]
theorem neg_apply : (-f) x = -f x :=
  rfl

@[simp, norm_cast]
theorem coe_neg : ((-f : M →SL[σ₁₂] M₂) : M →ₛₗ[σ₁₂] M₂) = -(f : M →ₛₗ[σ₁₂] M₂) :=
  rfl

@[norm_cast]
theorem coe_neg' : ((-f : M →SL[σ₁₂] M₂) : M → M₂) = -(f : M → M₂) :=
  rfl

instance : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

theorem continuous_zsmul : ∀ n : ℤ, Continuous fun x : M₂ => n • x
  | (n : ℕ) => by
    simp only [coe_nat_zsmul]
    exact continuous_nsmul _
  | -[1+ n] => by
    simp only [zsmul_neg_succ_of_nat]
    exact (continuous_nsmul _).neg

@[continuity]
theorem continuous.zsmul {α : Type _} [TopologicalSpace α] {n : ℤ} {f : α → M₂} (hf : Continuous f) :
    Continuous fun x : α => n • f x :=
  (continuous_zsmul n).comp hf

instance : AddCommGroupₓ (M →SL[σ₁₂] M₂) := by
  refine'
      { ContinuousLinearMap.addCommMonoid with zero := 0, add := ·+·, neg := Neg.neg, sub := Sub.sub,
        sub_eq_add_neg := _,
        nsmul := fun n f =>
          { toFun := fun x => n • f x,
            map_add' := by
              simp ,
            map_smul' := by
              simp [smul_comm n] },
        zsmul := fun n f =>
          { toFun := fun x => n • f x,
            map_add' := by
              simp ,
            map_smul' := by
              simp [smul_comm n] },
        zsmul_zero' := fun f => by
          ext
          simp ,
        zsmul_succ' := fun n f => by
          ext
          simp [add_smul, add_commₓ],
        zsmul_neg' := fun n f => by
          ext
          simp [Nat.succ_eq_add_one, add_smul],
        .. } <;>
    intros <;> ext <;> apply_rules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ, sub_eq_add_neg]

theorem sub_apply (x : M) : (f - g) x = f x - g x :=
  rfl

@[simp, norm_cast]
theorem coe_sub : ((f - g : M →SL[σ₁₂] M₂) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[simp, norm_cast]
theorem coe_sub' : ((f - g : M →SL[σ₁₂] M₂) : M → M₂) = (f : M → M₂) - g :=
  rfl

end

instance [TopologicalAddGroup M] : Ringₓ (M →L[R] M) :=
  { ContinuousLinearMap.addCommGroup with mul := ·*·, one := 1, mul_one := fun _ => ext $ fun _ => rfl,
    one_mul := fun _ => ext $ fun _ => rfl, mul_assoc := fun _ _ _ => ext $ fun _ => rfl,
    left_distrib := fun f g h => ext $ fun x => map_add f (g x) (h x),
    right_distrib := fun _ _ _ => ext $ fun _ => LinearMap.add_apply _ _ _ }

theorem smul_right_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
    smul_right (1 : R →L[R] R) c ^ n = smul_right (1 : R →L[R] R) (c ^ n) := by
  induction' n with n ihn
  ·
    ext
    simp
  ·
    rw [pow_succₓ, ihn, mul_def, smul_right_comp, smul_eq_mul, pow_succ'ₓ]

section

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]

/--  Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def proj_ker_of_right_inverse [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →L[R] f₁.ker :=
  (id R M - f₂.comp f₁).codRestrict f₁.ker $ fun x => by
    simp [h (f₁ x)]

@[simp]
theorem coe_proj_ker_of_right_inverse_apply [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (f₁.proj_ker_of_right_inverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem proj_ker_of_right_inverse_apply_idem [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) (x : f₁.ker) : f₁.proj_ker_of_right_inverse f₂ h x = x :=
  Subtype.ext_iff_val.2 $ by
    simp

@[simp]
theorem proj_ker_of_right_inverse_comp_inv [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂) : f₁.proj_ker_of_right_inverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff_val.2 $ by
    simp [h y]

end

end Ringₓ

section SmulMonoid

variable {R R₂ R₃ S S₃ : Type _} [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Monoidₓ S] [Monoidₓ S₃]
  [TopologicalSpace S] [TopologicalSpace S₃] {M : Type _} [TopologicalSpace M] [AddCommMonoidₓ M] [Module R M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module R₂ M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoidₓ M₃] [Module R₃ M₃] {N₂ : Type _} [TopologicalSpace N₂] [AddCommMonoidₓ N₂] [Module R N₂] {N₃ : Type _}
  [TopologicalSpace N₃] [AddCommMonoidₓ N₃] [Module R N₃] [DistribMulAction S₃ M₃] [SmulCommClass R₃ S₃ M₃]
  [HasContinuousSmul S₃ M₃] [DistribMulAction S N₃] [SmulCommClass R S N₃] [HasContinuousSmul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

-- failed to format: format: uncaught backtrack exception
instance
  : MulAction S₃ ( M →SL[ σ₁₃ ] M₃ )
  where
    smul c f := ⟨ c • f , ( continuous_const . smul f . 2 : Continuous fun x => c • f x ) ⟩
      one_smul f := ext $ fun x => one_smul _ _
      mul_smul a b f := ext $ fun x => mul_smul _ _ _

variable (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f g : M →SL[σ₁₂] M₂) (x y z : M)

variable (hₗ : N₂ →L[R] N₃) (fₗ gₗ : M →L[R] N₂)

include σ₁₃

@[simp]
theorem smul_comp : (c • h).comp f = c • h.comp f :=
  rfl

omit σ₁₃

variable [DistribMulAction S₃ M₂] [HasContinuousSmul S₃ M₂] [SmulCommClass R₂ S₃ M₂]

variable [DistribMulAction S N₂] [HasContinuousSmul S N₂] [SmulCommClass R S N₂]

theorem smul_apply : (c • f) x = c • f x :=
  rfl

@[simp, norm_cast]
theorem coe_smul : ((c • f : M →SL[σ₁₂] M₂) : M →ₛₗ[σ₁₂] M₂) = c • f :=
  rfl

@[simp, norm_cast]
theorem coe_smul' : ((c • f : M →SL[σ₁₂] M₂) : M → M₂) = c • f :=
  rfl

@[simp]
theorem comp_smul [LinearMap.CompatibleSmul N₂ N₃ S R] (c : S) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

instance {T : Type _} [Monoidₓ T] [TopologicalSpace T] [DistribMulAction T M₂] [HasContinuousSmul T M₂]
    [SmulCommClass R₂ T M₂] [HasScalar S₃ T] [IsScalarTower S₃ T M₂] : IsScalarTower S₃ T (M →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext $ fun x => smul_assoc a b (f x)⟩

instance {T : Type _} [Monoidₓ T] [TopologicalSpace T] [DistribMulAction T M₂] [HasContinuousSmul T M₂]
    [SmulCommClass R₂ T M₂] [SmulCommClass S₃ T M₂] : SmulCommClass S₃ T (M →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext $ fun x => smul_comm a b (f x)⟩

-- failed to format: format: uncaught backtrack exception
instance
  [ HasContinuousAdd M₂ ] : DistribMulAction S₃ ( M →SL[ σ₁₂ ] M₂ )
  where smul_add a f g := ext $ fun x => smul_add a ( f x ) ( g x ) smul_zero a := ext $ fun x => smul_zero _

end SmulMonoid

section Smul

variable {R R₂ R₃ S S₃ : Type _} [Semiringₓ R] [Semiringₓ R₂] [Semiringₓ R₃] [Semiringₓ S] [Semiringₓ S₃]
  [TopologicalSpace S] [TopologicalSpace S₃] {M : Type _} [TopologicalSpace M] [AddCommMonoidₓ M] [Module R M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoidₓ M₂] [Module R₂ M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoidₓ M₃] [Module R₃ M₃] {N₂ : Type _} [TopologicalSpace N₂] [AddCommMonoidₓ N₂] [Module R N₂] {N₃ : Type _}
  [TopologicalSpace N₃] [AddCommMonoidₓ N₃] [Module R N₃] [Module S₃ M₃] [SmulCommClass R₃ S₃ M₃]
  [HasContinuousSmul S₃ M₃] [Module S N₂] [HasContinuousSmul S N₂] [SmulCommClass R S N₂] [Module S N₃]
  [SmulCommClass R S N₃] [HasContinuousSmul S N₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S) (h : M₂ →SL[σ₂₃] M₃) (f g : M →SL[σ₁₂] M₂) (x y z : M)

/--  `continuous_linear_map.prod` as an `equiv`. -/
@[simps apply]
def prod_equiv : (M →L[R] N₂) × (M →L[R] N₃) ≃ (M →L[R] N₂ × N₃) :=
  { toFun := fun f => f.1.Prod f.2, invFun := fun f => ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩,
    left_inv := fun f => by
      ext <;> rfl,
    right_inv := fun f => by
      ext <;> rfl }

theorem prod_ext_iff {f g : M × N₂ →L[R] N₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]
theorem prod_ext {f g : M × N₂ →L[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable [HasContinuousAdd M₂] [HasContinuousAdd M₃] [HasContinuousAdd N₂]

-- failed to format: format: uncaught backtrack exception
instance
  : Module S₃ ( M →SL[ σ₁₃ ] M₃ )
  where zero_smul _ := ext $ fun _ => zero_smul _ _ add_smul _ _ _ := ext $ fun _ => add_smul _ _ _

variable (S) [HasContinuousAdd N₃]

/--  `continuous_linear_map.prod` as a `linear_equiv`. -/
@[simps apply]
def prodₗ : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ₗ[S] M →L[R] N₂ × N₃ :=
  { prod_equiv with map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

/--  The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coe_lm : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃ :=
  { toFun := coeₓ, map_add' := fun f g => coe_add f g, map_smul' := fun c f => coe_smul c f }

variable {S} (σ₁₃)

/--  The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
def coe_lmₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃ :=
  { toFun := coeₓ, map_add' := fun f g => coe_add f g, map_smul' := fun c f => coe_smul c f }

variable {σ₁₃}

end Smul

section SmulRightₗ

variable {R S T M M₂ : Type _} [Ringₓ R] [Ringₓ S] [Ringₓ T] [Module R S] [AddCommGroupₓ M₂] [Module R M₂] [Module S M₂]
  [IsScalarTower R S M₂] [TopologicalSpace S] [TopologicalSpace M₂] [HasContinuousSmul S M₂] [TopologicalSpace M]
  [AddCommGroupₓ M] [Module R M] [TopologicalAddGroup M₂] [TopologicalSpace T] [Module T M₂] [HasContinuousSmul T M₂]
  [SmulCommClass R T M₂] [SmulCommClass S T M₂]

/--  Given `c : E →L[𝕜] 𝕜`, `c.smul_rightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. See also `continuous_linear_map.smul_rightL`. -/
def smul_rightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ :=
  { toFun := c.smul_right,
    map_add' := fun x y => by
      ext e
      apply smul_add,
    map_smul' := fun a x => by
      ext e
      dsimp
      apply smul_comm }

@[simp]
theorem coe_smul_rightₗ (c : M →L[R] S) : ⇑(smul_rightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smul_right :=
  rfl

end SmulRightₗ

section CommRingₓ

variable {R : Type _} [CommRingₓ R] [TopologicalSpace R] {M : Type _} [TopologicalSpace M] [AddCommGroupₓ M]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroupₓ M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroupₓ M₃]
  [Module R M] [Module R M₂] [Module R M₃] [HasContinuousSmul R M₃]

variable [TopologicalAddGroup M₂] [HasContinuousSmul R M₂]

instance : Algebra R (M₂ →L[R] M₂) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

end CommRingₓ

section RestrictScalars

variable {A M M₂ : Type _} [Ringₓ A] [AddCommGroupₓ M] [AddCommGroupₓ M₂] [Module A M] [Module A M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] (R : Type _) [Ringₓ R] [Module R M] [Module R M₂]
  [LinearMap.CompatibleSmul M M₂ R A]

/--  If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `linear_map.compatible_smul M M₂ R A` to match assumptions of
`linear_map.map_smul_of_tower`. -/
def restrict_scalars (f : M →L[A] M₂) : M →L[R] M₂ :=
  ⟨(f : M →ₗ[A] M₂).restrictScalars R, f.continuous⟩

variable {R}

@[simp, norm_cast]
theorem coe_restrict_scalars (f : M →L[A] M₂) :
    (f.restrict_scalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrictScalars R :=
  rfl

@[simp]
theorem coe_restrict_scalars' (f : M →L[A] M₂) : ⇑f.restrict_scalars R = f :=
  rfl

@[simp]
theorem restrict_scalars_zero : (0 : M →L[A] M₂).restrictScalars R = 0 :=
  rfl

section

variable [TopologicalAddGroup M₂]

@[simp]
theorem restrict_scalars_add (f g : M →L[A] M₂) : (f+g).restrictScalars R = f.restrict_scalars R+g.restrict_scalars R :=
  rfl

@[simp]
theorem restrict_scalars_neg (f : M →L[A] M₂) : (-f).restrictScalars R = -f.restrict_scalars R :=
  rfl

end

variable {S : Type _} [Ringₓ S] [TopologicalSpace S] [Module S M₂] [HasContinuousSmul S M₂] [SmulCommClass A S M₂]
  [SmulCommClass R S M₂]

@[simp]
theorem restrict_scalars_smul (c : S) (f : M →L[A] M₂) : (c • f).restrictScalars R = c • f.restrict_scalars R :=
  rfl

variable (A M M₂ R S) [TopologicalAddGroup M₂]

/--  `continuous_linear_map.restrict_scalars` as a `linear_map`. See also
`continuous_linear_map.restrict_scalarsL`. -/
def restrict_scalarsₗ : (M →L[A] M₂) →ₗ[S] M →L[R] M₂ :=
  { toFun := restrict_scalars R, map_add' := restrict_scalars_add, map_smul' := restrict_scalars_smul }

variable {A M M₂ R S}

@[simp]
theorem coe_restrict_scalarsₗ : ⇑restrict_scalarsₗ A M M₂ R S = restrict_scalars R :=
  rfl

end RestrictScalars

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoidₓ

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} [Semiringₓ R₁] [Semiringₓ R₂] [Semiringₓ R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
  [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃] {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁]
  [RingHomInvPair σ₃₁ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type _}
  [TopologicalSpace M₁] [AddCommMonoidₓ M₁] {M'₁ : Type _} [TopologicalSpace M'₁] [AddCommMonoidₓ M'₁] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommMonoidₓ M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommMonoidₓ M₃] {M₄ : Type _}
  [TopologicalSpace M₄] [AddCommMonoidₓ M₄] [Module R₁ M₁] [Module R₁ M'₁] [Module R₂ M₂] [Module R₃ M₃]

include σ₂₁

/--  A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.to_linear_equiv.to_linear_map with cont := e.continuous_to_fun }

/--  Coerce continuous linear equivs to continuous linear maps. -/
instance : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨to_continuous_linear_map⟩

/--  Coerce continuous linear equivs to maps. -/
instance : CoeFun (M₁ ≃SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f⟩

@[simp]
theorem coe_def_rev (e : M₁ ≃SL[σ₁₂] M₂) : e.to_continuous_linear_map = e :=
  rfl

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
theorem coe_to_linear_equiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.to_linear_equiv = f :=
  rfl

@[simp, norm_cast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ((e : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = e :=
  rfl

theorem to_linear_equiv_injective : Function.Injective (to_linear_equiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂)
  | ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  to_linear_equiv_injective $ LinearEquiv.ext $ congr_funₓ h

theorem coe_injective : Function.Injective (coeₓ : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) := fun e e' h =>
  ext $ funext $ ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/--  A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.to_linear_equiv.to_equiv }

@[simp]
theorem coe_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.to_homeomorph = e :=
  rfl

theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' Closure s = Closure (e '' s) :=
  e.to_homeomorph.image_closure s

theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' Closure s = Closure (e ⁻¹' s) :=
  e.to_homeomorph.preimage_closure s

@[simp]
theorem is_closed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.to_homeomorph.is_closed_image

theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.to_homeomorph.map_nhds_eq x

@[simp]
theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero

@[simp]
theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x+y) = e x+e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y

@[simp]
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x

omit σ₂₁

@[simp]
theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x

include σ₂₁

@[simp]
theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.to_linear_equiv.map_eq_zero_iff

attribute [continuity] ContinuousLinearEquiv.continuous_to_fun ContinuousLinearEquiv.continuous_inv_fun

@[continuity]
protected theorem Continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_to_fun

protected theorem ContinuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.continuous.continuous_on

protected theorem ContinuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.continuous.continuous_at

protected theorem ContinuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.continuous.continuous_within_at

theorem comp_continuous_on_iff {α : Type _} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} {s : Set α} :
    ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.to_homeomorph.comp_continuous_on_iff _ _

theorem comp_continuous_iff {α : Type _} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.to_homeomorph.comp_continuous_iff

omit σ₂₁

/--  An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext $
    funext $ fun x =>
      mul_oneₓ x ▸ by
        rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable (R₁ M₁)

/--  The identity map as a continuous linear equivalence. -/
@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id }

end

@[simp, norm_cast]
theorem coe_refl : (ContinuousLinearEquiv.refl R₁ M₁ : M₁ →L[R₁] M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
theorem coe_refl' : (ContinuousLinearEquiv.refl R₁ M₁ : M₁ → M₁) = id :=
  rfl

/--  The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.to_linear_equiv.symm with continuous_to_fun := e.continuous_inv_fun, continuous_inv_fun := e.continuous_to_fun }

include σ₂₁

@[simp]
theorem symm_to_linear_equiv (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.to_linear_equiv = e.to_linear_equiv.symm := by
  ext
  rfl

@[simp]
theorem symm_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : e.to_homeomorph.symm = e.symm.to_homeomorph :=
  rfl

/--  See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/--  See Note [custom simps projection] -/
def simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (to_linear_equiv_to_fun → apply, to_linear_equiv_inv_fun → symmApply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.to_homeomorph.symm_map_nhds_eq x

omit σ₂₁

include σ₂₁ σ₃₂ σ₃₁

/--  The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  { e₁.to_linear_equiv.trans e₂.to_linear_equiv with
    continuous_to_fun := e₂.continuous_to_fun.comp e₁.continuous_to_fun,
    continuous_inv_fun := e₁.continuous_inv_fun.comp e₂.continuous_inv_fun }

include σ₁₃

@[simp]
theorem trans_to_linear_equiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv := by
  ext
  rfl

omit σ₁₃ σ₂₁ σ₃₂ σ₃₁

/--  Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def Prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  { e.to_linear_equiv.prod e'.to_linear_equiv with
    continuous_to_fun := e.continuous_to_fun.prod_map e'.continuous_to_fun,
    continuous_inv_fun := e.continuous_inv_fun.prod_map e'.continuous_inv_fun }

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) x :
    e.prod e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (e.prod e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prod_map (e' : M₃ →L[R₁] M₄) :=
  rfl

include σ₂₁

theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.to_linear_equiv.to_equiv.bijective

theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.to_linear_equiv.to_equiv.injective

theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.to_linear_equiv.to_equiv.surjective

include σ₃₂ σ₃₁ σ₁₃

@[simp]
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) : (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

omit σ₃₂ σ₃₁ σ₁₃

@[simp]
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b

include σ₁₂ σ₂₃ σ₁₃ σ₃₁

@[simp]
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

omit σ₁₂ σ₂₃ σ₁₃ σ₃₁

@[simp]
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' (e '' s) = s :=
  e.to_linear_equiv.to_equiv.symm_image_image s

@[simp]
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

include σ₃₂ σ₃₁

@[simp, norm_cast]
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl

omit σ₃₂ σ₃₁ σ₂₁

@[simp]
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

@[simp]
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

include σ₂₁

@[simp]
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : ((e.symm : M₂ → M₁) ∘ (e : M₁ → M₂)) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : ((e : M₁ → M₂) ∘ (e.symm : M₂ → M₁)) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := by
  ext x
  rfl

omit σ₂₁

@[simp]
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl

include σ₂₁

theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.to_linear_equiv.symm_apply_eq

theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.to_linear_equiv.eq_symm_apply

protected theorem image_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.to_linear_equiv.to_equiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e.symm '' s = e ⁻¹' s := by
  rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.to_linear_equiv.to_equiv.symm_preimage_preimage s

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.symm.symm_preimage_preimage s

omit σ₂₁

/--  Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
inverse of each other. -/
def equiv_of_inverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with toFun := f₁, continuous_to_fun := f₁.continuous, invFun := f₂, continuous_inv_fun := f₂.continuous,
    left_inv := h₁, right_inv := h₂ }

include σ₂₁

@[simp]
theorem equiv_of_inverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) f₂ h₁ h₂ x : equiv_of_inverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
theorem symm_equiv_of_inverse (f₁ : M₁ →SL[σ₁₂] M₂) f₂ h₁ h₂ :
    (equiv_of_inverse f₁ f₂ h₁ h₂).symm = equiv_of_inverse f₂ f₁ h₂ h₁ :=
  rfl

omit σ₂₁

section Pointwise

open_locale Pointwise

include σ₂₁

@[simp]
theorem image_smul_setₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (s : Set M₁) : e '' (c • s) = σ₁₂ c • e '' s :=
  e.to_linear_equiv.image_smul_setₛₗ c s

@[simp]
theorem preimage_smul_setₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₂) (s : Set M₂) : e ⁻¹' (c • s) = σ₂₁ c • e ⁻¹' s :=
  e.to_linear_equiv.preimage_smul_setₛₗ c s

omit σ₂₁

@[simp]
theorem image_smul_set (e : M₁ ≃L[R₁] M'₁) (c : R₁) (s : Set M₁) : e '' (c • s) = c • e '' s :=
  e.to_linear_equiv.image_smul_set c s

@[simp]
theorem preimage_smul_set (e : M₁ ≃L[R₁] M'₁) (c : R₁) (s : Set M'₁) : e ⁻¹' (c • s) = c • e ⁻¹' s :=
  e.to_linear_equiv.preimage_smul_set c s

end Pointwise

variable (M₁)

-- failed to format: format: uncaught backtrack exception
/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
  instance
    automorphism_group
    : Groupₓ ( M₁ ≃L[ R₁ ] M₁ )
    where
      mul f g := g.trans f
        one := ContinuousLinearEquiv.refl R₁ M₁
        inv f := f.symm
        mul_assoc f g h := by ext rfl
        mul_one f := by ext rfl
        one_mul f := by ext rfl
        mul_left_inv f := by ext exact f.left_inv x

variable {M₁} {R₄ : Type _} [Semiringₓ R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₃₄ σ₄₃]
  [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄} [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄]
  [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

include σ₂₁ σ₃₄ σ₂₃ σ₂₄ σ₁₃

/--  A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. -/
@[simps]
def arrow_congr_equiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) : (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) :=
  { toFun := fun f => (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁)),
    invFun := fun f => (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂)),
    left_inv := fun f =>
      ContinuousLinearMap.ext $ fun x => by
        simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe],
    right_inv := fun f =>
      ContinuousLinearMap.ext $ fun x => by
        simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe] }

end AddCommMonoidₓ

section AddCommGroupₓ

variable {R : Type _} [Semiringₓ R] {M : Type _} [TopologicalSpace M] [AddCommGroupₓ M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommGroupₓ M₂] {M₃ : Type _} [TopologicalSpace M₃] [AddCommGroupₓ M₃] {M₄ : Type _}
  [TopologicalSpace M₄] [AddCommGroupₓ M₄] [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

variable [TopologicalAddGroup M₄]

/--  Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skew_prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  { e.to_linear_equiv.skew_prod e'.to_linear_equiv (↑f) with
    continuous_to_fun :=
      (e.continuous_to_fun.comp continuous_fst).prod_mk
        ((e'.continuous_to_fun.comp continuous_snd).add $ f.continuous.comp continuous_fst),
    continuous_inv_fun :=
      (e.continuous_inv_fun.comp continuous_fst).prod_mk
        (e'.continuous_inv_fun.comp $
          continuous_snd.sub $ f.continuous.comp $ e.continuous_inv_fun.comp continuous_fst) }

@[simp]
theorem skew_prod_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) x :
    e.skew_prod e' f x = (e x.1, e' x.2+f x.1) :=
  rfl

@[simp]
theorem skew_prod_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) x :
    (e.skew_prod e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

end AddCommGroupₓ

section Ringₓ

variable {R : Type _} [Ringₓ R] {R₂ : Type _} [Ringₓ R₂] {M : Type _} [TopologicalSpace M] [AddCommGroupₓ M]
  [Module R M] {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroupₓ M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

include σ₂₁

@[simp]
theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y

@[simp]
theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x

omit σ₂₁

section

/-! The next theorems cover the identification between `M ≃L[𝕜] M`and the group of units of the ring
`M →L[R] M`. -/


variable [TopologicalAddGroup M]

/--  An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def of_unit (f : Units (M →L[R] M)) : M ≃L[R] M :=
  { toLinearEquiv :=
      { toFun := f.val,
        map_add' := by
          simp ,
        map_smul' := by
          simp ,
        invFun := f.inv,
        left_inv := fun x =>
          show (f.inv*f.val) x = x by
            rw [f.inv_val]
            simp ,
        right_inv := fun x =>
          show (f.val*f.inv) x = x by
            rw [f.val_inv]
            simp },
    continuous_to_fun := f.val.continuous, continuous_inv_fun := f.inv.continuous }

/--  A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def to_unit (f : M ≃L[R] M) : Units (M →L[R] M) :=
  { val := f, inv := f.symm,
    val_inv := by
      ext
      simp ,
    inv_val := by
      ext
      simp }

variable (R M)

/--  The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def units_equiv : Units (M →L[R] M) ≃* M ≃L[R] M :=
  { toFun := of_unit, invFun := to_unit,
    left_inv := fun f => by
      ext
      rfl,
    right_inv := fun f => by
      ext
      rfl,
    map_mul' := fun x y => by
      ext
      rfl }

@[simp]
theorem units_equiv_apply (f : Units (M →L[R] M)) (x : M) : units_equiv R M f x = f x :=
  rfl

end

section

variable (R) [TopologicalSpace R] [HasContinuousMul R]

/--  Continuous linear equivalences `R ≃L[R] R` are enumerated by `units R`. -/
def units_equiv_aut : Units R ≃ R ≃L[R] R :=
  { toFun := fun u =>
      equiv_of_inverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) (↑u))
        (ContinuousLinearMap.smulRight (1 : R →L[R] R) (↑u⁻¹))
        (fun x => by
          simp )
        fun x => by
        simp ,
    invFun := fun e =>
      ⟨e 1, e.symm 1, by
        rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_oneₓ, symm_apply_apply], by
        rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_oneₓ, apply_symm_apply]⟩,
    left_inv := fun u =>
      Units.ext $ by
        simp ,
    right_inv := fun e =>
      ext₁ $ by
        simp }

variable {R}

@[simp]
theorem units_equiv_aut_apply (u : Units R) (x : R) : units_equiv_aut R u x = x*u :=
  rfl

@[simp]
theorem units_equiv_aut_apply_symm (u : Units R) (x : R) : (units_equiv_aut R u).symm x = x*↑u⁻¹ :=
  rfl

@[simp]
theorem units_equiv_aut_symm_apply (e : R ≃L[R] R) : ↑(units_equiv_aut R).symm e = e 1 :=
  rfl

end

variable [Module R M₂] [TopologicalAddGroup M]

open _root_.continuous_linear_map (id fst snd subtypeVal mem_ker)

/--  A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × f₁.ker :=
  equiv_of_inverse (f₁.prod (f₁.proj_ker_of_right_inverse f₂ h)) (f₂.coprod (subtype_val f₁.ker))
    (fun x => by
      simp )
    fun ⟨x, y⟩ => by
    simp [h x]

@[simp]
theorem fst_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (equiv_of_right_inverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
theorem snd_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equiv_of_right_inverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem equiv_of_right_inverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁)
    (y : M₂ × f₁.ker) : (equiv_of_right_inverse f₁ f₂ h).symm y = f₂ y.1+y.2 :=
  rfl

end Ringₓ

section

variable (ι R M : Type _) [Unique ι] [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [TopologicalSpace M]

/--  If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def fun_unique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
theorem coe_fun_unique : ⇑fun_unique ι R M = Function.eval (default ι) :=
  rfl

@[simp]
theorem coe_fun_unique_symm : ⇑(fun_unique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

/--  Continuous linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config := { fullyApplied := ff })]
def pi_fin_two (M : Finₓ 2 → Type _) [∀ i, AddCommMonoidₓ (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] :
    (∀ i, M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/--  Continuous linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config := { fullyApplied := ff })]
def fin_two_arrow : (Finₓ 2 → M) ≃L[R] M × M :=
  { pi_fin_two R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

end

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open_locale Classical

variable {R : Type _} {M : Type _} {M₂ : Type _} [TopologicalSpace M] [TopologicalSpace M₂]

section

variable [Semiringₓ R]

variable [AddCommMonoidₓ M₂] [Module R M₂]

variable [AddCommMonoidₓ M] [Module R M]

/--  Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : ∃ e : M ≃L[R] M₂, (e : M →L[R] M₂) = f then ((Classical.some h).symm : M₂ →L[R] M) else 0

/--  By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  have h : ∃ e' : M ≃L[R] M₂, (e' : M →L[R] M₂) = ↑e := ⟨e, rfl⟩
  simp only [inverse, dif_pos h]
  congr
  exact_mod_cast Classical.some_spec h

/--  By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp]
theorem inverse_non_equiv (f : M →L[R] M₂) (h : ¬∃ e' : M ≃L[R] M₂, ↑e' = f) : inverse f = 0 :=
  dif_neg h

end

section

variable [Ringₓ R]

variable [AddCommGroupₓ M] [TopologicalAddGroup M] [Module R M]

variable [AddCommGroupₓ M₂] [Module R M₂]

@[simp]
theorem ring_inverse_equiv (e : M ≃L[R] M) : Ring.inverse (↑e) = inverse (e : M →L[R] M) := by
  suffices Ring.inverse ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M) = inverse (↑e)by
    convert this
  simp
  rfl

/--  The function `continuous_linear_equiv.inverse` can be written in terms of `ring.inverse` for the
ring of self-maps of the domain. -/
theorem to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = Ring.inverse ((e.symm : M₂ →L[R] M).comp f) ∘L ↑e.symm := by
  by_cases' h₁ : ∃ e' : M ≃L[R] M₂, ↑e' = f
  ·
    obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = Ring.inverse (↑e'.trans e.symm) ∘L ↑e.symm
    ext
    simp
  ·
    suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f)by
      simp [this, h₁]
    contrapose! h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [coe_fn_coe_base' F, hF]
    simp

theorem ring_inverse_eq_map_inverse : Ring.inverse = @inverse R M M _ _ _ _ _ _ _ := by
  ext
  simp [to_ring_inverse (ContinuousLinearEquiv.refl R M)]

end

end ContinuousLinearMap

namespace Submodule

variable {R : Type _} [Ringₓ R] {M : Type _} [TopologicalSpace M] [AddCommGroupₓ M] [Module R M] {M₂ : Type _}
  [TopologicalSpace M₂] [AddCommGroupₓ M₂] [Module R M₂]

open ContinuousLinearMap

/--  A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def closed_complemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

theorem closed_complemented.has_closed_complement {p : Submodule R M} [T1Space p] (h : closed_complemented p) :
    ∃ (q : Submodule R M)(hq : IsClosed (q : Set M)), IsCompl p q :=
  Exists.elim h $ fun f hf => ⟨f.ker, f.is_closed_ker, LinearMap.is_compl_of_proj hf⟩

protected theorem closed_complemented.is_closed [TopologicalAddGroup M] [T1Space M] {p : Submodule R M}
    (h : closed_complemented p) : IsClosed (p : Set M) := by
  rcases h with ⟨f, hf⟩
  have : ker (id R M - (subtype_val p).comp f) = p := LinearMap.ker_id_sub_eq_of_proj hf
  exact this ▸ is_closed_ker _

@[simp]
theorem closed_complemented_bot : closed_complemented (⊥ : Submodule R M) :=
  ⟨0, fun x => by
    simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp]
theorem closed_complemented_top : closed_complemented (⊤ : Submodule R M) :=
  ⟨(id R M).codRestrict ⊤ fun x => trivialₓ, fun x =>
    Subtype.ext_iff_val.2 $ by
      simp ⟩

end Submodule

theorem ContinuousLinearMap.closed_complemented_ker_of_right_inverse {R : Type _} [Ringₓ R] {M : Type _}
    [TopologicalSpace M] [AddCommGroupₓ M] {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroupₓ M₂] [Module R M]
    [Module R M₂] [TopologicalAddGroup M] (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    f₁.ker.closed_complemented :=
  ⟨f₁.proj_ker_of_right_inverse f₂ h, f₁.proj_ker_of_right_inverse_apply_idem f₂ h⟩

