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

variable{R : Type _}{M : Type _}[Ringₓ R][TopologicalSpace R][TopologicalSpace M][AddCommGroupₓ M][Module R M]

-- error in Topology.Algebra.Module: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_continuous_smul.of_nhds_zero
[topological_ring R]
[topological_add_group M]
(hmul : tendsto (λ p : «expr × »(R, M), «expr • »(p.1, p.2)) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0) (expr𝓝() 0))
(hmulleft : ∀ m : M, tendsto (λ a : R, «expr • »(a, m)) (expr𝓝() 0) (expr𝓝() 0))
(hmulright : ∀ a : R, tendsto (λ m : M, «expr • »(a, m)) (expr𝓝() 0) (expr𝓝() 0)) : has_continuous_smul R M :=
⟨begin
   rw [expr continuous_iff_continuous_at] [],
   rintros ["⟨", ident a₀, ",", ident m₀, "⟩"],
   have [ident key] [":", expr ∀
    p : «expr × »(R, M), «expr = »(«expr • »(p.1, p.2), «expr + »(«expr • »(a₀, m₀), «expr + »(«expr + »(«expr • »(«expr - »(p.1, a₀), m₀), «expr • »(a₀, «expr - »(p.2, m₀))), «expr • »(«expr - »(p.1, a₀), «expr - »(p.2, m₀)))))] [],
   { rintro ["⟨", ident a, ",", ident m, "⟩"],
     simp [] [] [] ["[", expr sub_smul, ",", expr smul_sub, "]"] [] [],
     abel [] [] [] },
   rw [expr funext key] [],
   clear [ident key],
   refine [expr tendsto_const_nhds.add (tendsto.add (tendsto.add _ _) _)],
   { rw ["[", expr sub_self, ",", expr zero_smul, "]"] [],
     apply [expr (hmulleft m₀).comp],
     rw ["[", expr show «expr = »(λ
       p : «expr × »(R, M), «expr - »(p.1, a₀), «expr ∘ »(λ a, «expr - »(a, a₀), prod.fst)), by { ext [] [] [],
        refl }, ",", expr nhds_prod_eq, "]"] [],
     have [] [":", expr tendsto (λ a, «expr - »(a, a₀)) (expr𝓝() a₀) (expr𝓝() 0)] [],
     { rw ["<-", expr sub_self a₀] [],
       exact [expr tendsto_id.sub tendsto_const_nhds] },
     exact [expr this.comp tendsto_fst] },
   { rw ["[", expr sub_self, ",", expr smul_zero, "]"] [],
     apply [expr (hmulright a₀).comp],
     rw ["[", expr show «expr = »(λ
       p : «expr × »(R, M), «expr - »(p.2, m₀), «expr ∘ »(λ m, «expr - »(m, m₀), prod.snd)), by { ext [] [] [],
        refl }, ",", expr nhds_prod_eq, "]"] [],
     have [] [":", expr tendsto (λ m, «expr - »(m, m₀)) (expr𝓝() m₀) (expr𝓝() 0)] [],
     { rw ["<-", expr sub_self m₀] [],
       exact [expr tendsto_id.sub tendsto_const_nhds] },
     exact [expr this.comp tendsto_snd] },
   { rw ["[", expr sub_self, ",", expr zero_smul, ",", expr nhds_prod_eq, ",", expr show «expr = »(λ
       p : «expr × »(R, M), «expr • »(«expr - »(p.fst, a₀), «expr - »(p.snd, m₀)), «expr ∘ »(λ
        p : «expr × »(R, M), «expr • »(p.1, p.2), prod.map (λ
         a, «expr - »(a, a₀)) (λ m, «expr - »(m, m₀)))), by { ext [] [] [],
        refl }, "]"] [],
     apply [expr hmul.comp (tendsto.prod_map _ _)]; { rw ["<-", expr sub_self] [],
       exact [expr tendsto_id.sub tendsto_const_nhds] } }
 end⟩

end 

section 

variable{R :
    Type
      _}{M :
    Type
      _}[Ringₓ
      R][TopologicalSpace R][TopologicalSpace M][AddCommGroupₓ M][HasContinuousAdd M][Module R M][HasContinuousSmul R M]

-- error in Topology.Algebra.Module: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nondiscrete normed field. -/
theorem submodule.eq_top_of_nonempty_interior'
[ne_bot «expr𝓝[ ] »({x : R | is_unit x}, 0)]
(s : submodule R M)
(hs : (interior (s : set M)).nonempty) : «expr = »(s, «expr⊤»()) :=
begin
  rcases [expr hs, "with", "⟨", ident y, ",", ident hy, "⟩"],
  refine [expr «expr $ »(submodule.eq_top_iff'.2, λ x, _)],
  rw ["[", expr mem_interior_iff_mem_nhds, "]"] ["at", ident hy],
  have [] [":", expr tendsto (λ
    c : R, «expr + »(y, «expr • »(c, x))) «expr𝓝[ ] »({x : R | is_unit x}, 0) (expr𝓝() «expr + »(y, «expr • »((0 : R), x)))] [],
  from [expr tendsto_const_nhds.add ((tendsto_nhds_within_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds)],
  rw ["[", expr zero_smul, ",", expr add_zero, "]"] ["at", ident this],
  obtain ["⟨", "_", ",", ident hu, ":", expr «expr ∈ »(«expr + »(y, «expr • »(_, _)), s), ",", ident u, ",", ident rfl, "⟩", ":=", expr nonempty_of_mem (inter_mem (mem_map.1 (this hy)) self_mem_nhds_within)],
  have [ident hy'] [":", expr «expr ∈ »(y, «expr↑ »(s))] [":=", expr mem_of_mem_nhds hy],
  rwa ["[", expr s.add_mem_iff_right hy', ",", "<-", expr units.smul_def, ",", expr s.smul_mem_iff' u, "]"] ["at", ident hu]
end

variable(R M)

/-- Let `R` be a topological ring such that zero is not an isolated point (e.g., a nondiscrete
normed field, see `normed_field.punctured_nhds_ne_bot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `ne_bot (𝓝[{x}ᶜ] x)`.

This lemma is not an instance because Lean would need to find `[has_continuous_smul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `real.punctured_nhds_module_ne_bot`.
One can also use `haveI := module.punctured_nhds_ne_bot R M` in a proof.
-/
theorem Module.punctured_nhds_ne_bot [Nontrivial M] [ne_bot (𝓝[«expr ᶜ» {0}] (0 : R))] [NoZeroSmulDivisors R M]
  (x : M) : ne_bot (𝓝[«expr ᶜ» {x}] x) :=
  by 
    rcases exists_ne (0 : M) with ⟨y, hy⟩
    suffices  : tendsto (fun c : R => x+c • y) (𝓝[«expr ᶜ» {0}] 0) (𝓝[«expr ᶜ» {x}] x)
    exact this.ne_bot 
    refine' tendsto.inf _ (tendsto_principal_principal.2$ _)
    ·
      convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y)
      rw [zero_smul, add_zeroₓ]
    ·
      intro c hc 
      simpa [hy] using hc

end 

section Closure

variable{R :
    Type
      u}{M :
    Type v}[Semiringₓ R][TopologicalSpace R][TopologicalSpace M][AddCommMonoidₓ M][Module R M][HasContinuousSmul R M]

theorem Submodule.closure_smul_self_subset (s : Submodule R M) :
  (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) ⊆ Closure (s : Set M) :=
  calc
    (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) =
      (fun p : R × M => p.1 • p.2) '' Closure ((Set.Univ : Set R).Prod s) :=
    by 
      simp [closure_prod_eq]
    _ ⊆ Closure ((fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod s) :=
    image_closure_subset_closure_image continuous_smul 
    _ = Closure s :=
    by 
      congr 
      ext x 
      refine' ⟨_, fun hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩⟩
      rintro ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩
      simp [s.smul_mem c hy]
    

theorem Submodule.closure_smul_self_eq (s : Submodule R M) :
  (fun p : R × M => p.1 • p.2) '' (Set.Univ : Set R).Prod (Closure (s : Set M)) = Closure (s : Set M) :=
  Set.Subset.antisymm s.closure_smul_self_subset fun x hx => ⟨⟨1, x⟩, ⟨Set.mem_univ _, hx⟩, one_smul R _⟩

variable[HasContinuousAdd M]

/-- The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
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
    continuous_smul :=
      by 
        apply continuous_induced_rng 
        change Continuous fun p : R × s.topological_closure => p.1 • (p.2 : M)
        continuity }

theorem Submodule.submodule_topological_closure (s : Submodule R M) : s ≤ s.topological_closure :=
  subset_closure

theorem Submodule.is_closed_topological_closure (s : Submodule R M) : IsClosed (s.topological_closure : Set M) :=
  by 
    convert is_closed_closure

theorem Submodule.topological_closure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
  (ht : IsClosed (t : Set M)) : s.topological_closure ≤ t :=
  closure_minimal h ht

theorem Submodule.topological_closure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
  s.topological_closure ≤ t.topological_closure :=
  s.topological_closure_minimal (h.trans t.submodule_topological_closure) t.is_closed_topological_closure

end Closure

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure
  ContinuousLinearMap{R :
    Type
      _}{S :
    Type
      _}[Semiringₓ
      R][Semiringₓ
      S](σ :
    R →+*
      S)(M :
    Type
      _)[TopologicalSpace
      M][AddCommMonoidₓ M](M₂ : Type _)[TopologicalSpace M₂][AddCommMonoidₓ M₂][Module R M][Module S M₂] extends
  M →ₛₗ[σ] M₂ where 
  cont : Continuous to_fun :=  by 
  runTac 
    tactic.interactive.continuity'

notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (@starRingAut R _ _ : R →+* R) M M₂

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological ring `R`. -/
@[nolint has_inhabited_instance]
structure
  ContinuousLinearEquiv{R :
    Type
      _}{S :
    Type
      _}[Semiringₓ
      R][Semiringₓ
      S](σ :
    R →+*
      S){σ' :
    S →+*
      R}[RingHomInvPair σ
      σ'][RingHomInvPair σ'
      σ](M :
    Type
      _)[TopologicalSpace
      M][AddCommMonoidₓ M](M₂ : Type _)[TopologicalSpace M₂][AddCommMonoidₓ M₂][Module R M][Module S M₂] extends
  M ≃ₛₗ[σ] M₂ where 
  continuous_to_fun : Continuous to_fun :=  by 
  runTac 
    tactic.interactive.continuity' 
  continuous_inv_fun : Continuous inv_fun :=  by 
  runTac 
    tactic.interactive.continuity'

notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (@starRingAut R _ _ : R →+* R) M M₂

namespace ContinuousLinearMap

section Semiringₓ

/-!
### Properties that hold for non-necessarily commutative semirings.
-/


variable{R₁ :
    Type
      _}{R₂ :
    Type
      _}{R₃ :
    Type
      _}[Semiringₓ
      R₁][Semiringₓ
      R₂][Semiringₓ
      R₃]{σ₁₂ :
    R₁ →+*
      R₂}{σ₂₃ :
    R₂ →+*
      R₃}{M₁ :
    Type
      _}[TopologicalSpace
      M₁][AddCommMonoidₓ
      M₁]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommMonoidₓ
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommMonoidₓ
      M₃]{M₄ : Type _}[TopologicalSpace M₄][AddCommMonoidₓ M₄][Module R₁ M₁][Module R₂ M₂][Module R₃ M₃]

/-- Coerce continuous linear maps to linear maps. -/
instance  : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) :=
  ⟨to_linear_map⟩

@[simp]
theorem to_linear_map_eq_coe (f : M₁ →SL[σ₁₂] M₂) : f.to_linear_map = f :=
  rfl

/-- Coerce continuous linear maps to functions. -/
instance to_fun : CoeFun (M₁ →SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f⟩

@[simp]
theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) h : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) h : (mk f h : M₁ → M₂) = f :=
  rfl

@[continuity]
protected theorem Continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2

theorem coe_injective : Function.Injective (coeₓ : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) :=
  by 
    intro f g H 
    cases f 
    cases g 
    congr

@[simp, normCast]
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff

theorem coe_fn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) coeFn :=
  LinearMap.coe_injective.comp coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection]. -/
def simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (to_linear_map_to_fun → apply, toLinearMap → coe)

@[ext]
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  coe_fn_injective$ funext h

theorem ext_iff {f g : M₁ →SL[σ₁₂] M₂} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x =>
      by 
        rw [h],
    by 
      ext⟩

variable(f g : M₁ →SL[σ₁₂] M₂)(c : R₁)(h : M₂ →SL[σ₂₃] M₃)(x y z : M₁)

@[simp]
theorem map_zero : f (0 : M₁) = 0 :=
  (to_linear_map _).map_zero

@[simp]
theorem map_add : f (x+y) = f x+f y :=
  (to_linear_map _).map_add _ _

@[simp]
theorem map_smulₛₗ : f (c • x) = σ₁₂ c • f x :=
  (to_linear_map _).map_smulₛₗ _ _

@[simp]
theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) : f (c • x) = c • f x :=
  by 
    simp only [RingHom.id_apply, map_smulₛₗ]

@[simp]
theorem map_smul_of_tower {R S : Type _} [Semiringₓ S] [HasScalar R M₁] [Module S M₁] [HasScalar R M₂] [Module S M₂]
  [LinearMap.CompatibleSmul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) : f (c • x) = c • f x :=
  LinearMap.CompatibleSmul.map_smul f c x

theorem map_sum {ι : Type _} (s : Finset ι) (g : ι → M₁) : f (∑i in s, g i) = ∑i in s, f (g i) :=
  f.to_linear_map.map_sum

@[simp, normCast]
theorem coe_coe : ((f : M₁ →ₛₗ[σ₁₂] M₂) : M₁ → M₂) = (f : M₁ → M₂) :=
  rfl

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1$ LinearMap.ext_ring h

theorem ext_ring_iff [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `submodule.span` of this set. -/
theorem eq_on_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
  Set.EqOn f g (Closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eq_on_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁)) {f g : M₁ →SL[σ₁₂] M₂}
  (h : Set.EqOn f g s) : f = g :=
  ext$ fun x => eq_on_closure_span h (hs x)

/-- Under a continuous linear map, the image of the `topological_closure` of a submodule is
contained in the `topological_closure` of its image. -/
theorem _root_.submodule.topological_closure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁] [TopologicalSpace R₂]
  [HasContinuousSmul R₁ M₁] [HasContinuousAdd M₁] [HasContinuousSmul R₂ M₂] [HasContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂)
  (s : Submodule R₁ M₁) :
  s.topological_closure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤ (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/-- Under a dense continuous linear map, a submodule whose `topological_closure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
theorem _root_.dense_range.topological_closure_map_submodule [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
  [TopologicalSpace R₂] [HasContinuousSmul R₁ M₁] [HasContinuousAdd M₁] [HasContinuousSmul R₂ M₂] [HasContinuousAdd M₂]
  {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f) {s : Submodule R₁ M₁} (hs : s.topological_closure = ⊤) :
  (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ :=
  by 
    rw [SetLike.ext'_iff] at hs⊢
    simp only [Submodule.topological_closure_coe, Submodule.top_coe, ←dense_iff_closure_eq] at hs⊢
    exact hf'.dense_image f.continuous hs

/-- The continuous map that is constantly zero. -/
instance  : HasZero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

instance  : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : default (M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp]
theorem zero_apply : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
  rfl

@[simp, normCast]
theorem coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

@[normCast]
theorem coe_zero' : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = 0 :=
  rfl

instance unique_of_left [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

instance unique_of_right [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

section 

variable(R₁ M₁)

/-- the identity map as a continuous linear map. -/
def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end 

instance  : HasOne (M₁ →L[R₁] M₁) :=
  ⟨id R₁ M₁⟩

theorem one_def : (1 : M₁ →L[R₁] M₁) = id R₁ M₁ :=
  rfl

theorem id_apply : id R₁ M₁ x = x :=
  rfl

@[simp, normCast]
theorem coe_id : (id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, normCast]
theorem coe_id' : (id R₁ M₁ : M₁ → M₁) = _root_.id :=
  rfl

@[simp, normCast]
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = id _ _ :=
  by 
    rw [←coe_id, coe_inj]

@[simp]
theorem one_apply : (1 : M₁ →L[R₁] M₁) x = x :=
  rfl

section Add

variable[HasContinuousAdd M₂]

instance  : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f+g, f.2.add g.2⟩⟩

theorem continuous_nsmul (n : ℕ) : Continuous fun x : M₂ => n • x :=
  by 
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

@[simp, normCast]
theorem coe_add : ((f+g : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = f+g :=
  rfl

@[normCast]
theorem coe_add' : ((f+g : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = (f : M₁ → M₂)+g :=
  rfl

instance  : AddCommMonoidₓ (M₁ →SL[σ₁₂] M₂) :=
  { zero := (0 : M₁ →SL[σ₁₂] M₂), add := ·+·,
    zero_add :=
      by 
        intros  <;> ext <;> applyRules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ],
    add_zero :=
      by 
        intros  <;> ext <;> applyRules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ],
    add_comm :=
      by 
        intros  <;> ext <;> applyRules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ],
    add_assoc :=
      by 
        intros  <;> ext <;> applyRules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ],
    nsmul :=
      fun n f =>
        { toFun := fun x => n • f x,
          map_add' :=
            by 
              simp ,
          map_smul' :=
            by 
              simp [smul_comm n] },
    nsmul_zero' :=
      fun f =>
        by 
          ext 
          simp ,
    nsmul_succ' :=
      fun n f =>
        by 
          ext 
          simp [Nat.succ_eq_one_add, add_smul] }

@[simp, normCast]
theorem coe_sum {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
  «expr↑ » (∑d in t, f d) = (∑d in t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
  (AddMonoidHom.mk (coeₓ : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) rfl fun _ _ => rfl).map_sum _ _

@[simp, normCast]
theorem coe_sum' {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) : «expr⇑ » (∑d in t, f d) = ∑d in t, f d :=
  by 
    simp only [←coe_coe, coe_sum, LinearMap.coe_fn_sum]

theorem sum_apply {ι : Type _} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) (b : M₁) : (∑d in t, f d) b = ∑d in t, f d b :=
  by 
    simp only [coe_sum', Finset.sum_apply]

end Add

variable{σ₁₃ : R₁ →+* R₃}[RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp («expr↑ » f), g.2.comp f.2⟩

infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _)
    RingHomCompTriple.ids

@[simp, normCast]
theorem coe_comp : (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

include σ₁₃

@[simp, normCast]
theorem coe_comp' : (h.comp f : M₁ → M₃) = ((h : M₂ → M₃) ∘ f) :=
  rfl

theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl

omit σ₁₃

@[simp]
theorem comp_id : f.comp (id R₁ M₁) = f :=
  ext$ fun x => rfl

@[simp]
theorem id_comp : (id R₂ M₂).comp f = f :=
  ext$ fun x => rfl

include σ₁₃

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem zero_comp : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem comp_add [HasContinuousAdd M₂] [HasContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M₁ →SL[σ₁₂] M₂) :
  g.comp (f₁+f₂) = g.comp f₁+g.comp f₂ :=
  by 
    ext 
    simp 

@[simp]
theorem add_comp [HasContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
  (g₁+g₂).comp f = g₁.comp f+g₂.comp f :=
  by 
    ext 
    simp 

omit σ₁₃

theorem comp_assoc {R₄ : Type _} [Semiringₓ R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄} {σ₃₄ : R₃ →+* R₄}
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄)
  (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance  : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩

theorem mul_def (f g : M₁ →L[R₁] M₁) : (f*g) = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : «expr⇑ » (f*g) = (f ∘ g) :=
  rfl

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f*g) x = f (g x) :=
  rfl

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def Prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) : M₁ →L[R₁] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R₁] M₂).Prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, normCast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
  (f₁.prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, normCast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
  f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section 

variable(R₁ M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
def inl [Module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ :=
  (id R₁ M₁).Prod 0

/-- The right injection into a product is a continuous linear map. -/
def inr [Module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ :=
  (0 : M₂ →L[R₁] M₁).Prod (id R₁ M₂)

end 

@[simp]
theorem inl_apply [Module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
theorem inr_apply [Module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) :=
  rfl

@[simp, normCast]
theorem coe_inl [Module R₁ M₂] : (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = LinearMap.inl R₁ M₁ M₂ :=
  rfl

@[simp, normCast]
theorem coe_inr [Module R₁ M₂] : (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = LinearMap.inr R₁ M₁ M₂ :=
  rfl

/-- Kernel of a continuous linear map. -/
def ker (f : M₁ →SL[σ₁₂] M₂) : Submodule R₁ M₁ :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker

@[normCast]
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

/-- Range of a continuous linear map. -/
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

/-- Restrict codomain of a continuous linear map. -/
def cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) : M₁ →SL[σ₁₂] p :=
  { cont := continuous_subtype_mk h f.continuous, toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h }

@[normCast]
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

/-- Embedding of a submodule into the ambient space as a continuous linear map. -/
def subtype_val (p : Submodule R₁ M₁) : p →L[R₁] M₁ :=
  { cont := continuous_subtype_val, toLinearMap := p.subtype }

@[simp, normCast]
theorem coe_subtype_val (p : Submodule R₁ M₁) : (subtype_val p : p →ₗ[R₁] M₁) = p.subtype :=
  rfl

@[simp, normCast]
theorem subtype_val_apply (p : Submodule R₁ M₁) (x : p) : (subtype_val p : p → M₁) x = x :=
  rfl

variable(R₁ M₁ M₂)

/-- `prod.fst` as a `continuous_linear_map`. -/
def fst [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₁ :=
  { cont := continuous_fst, toLinearMap := LinearMap.fst R₁ M₁ M₂ }

/-- `prod.snd` as a `continuous_linear_map`. -/
def snd [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₂ :=
  { cont := continuous_snd, toLinearMap := LinearMap.snd R₁ M₁ M₂ }

variable{R₁ M₁ M₂}

@[simp, normCast]
theorem coe_fst [Module R₁ M₂] : (fst R₁ M₁ M₂ : M₁ × M₂ →ₗ[R₁] M₁) = LinearMap.fst R₁ M₁ M₂ :=
  rfl

@[simp, normCast]
theorem coe_fst' [Module R₁ M₂] : (fst R₁ M₁ M₂ : M₁ × M₂ → M₁) = Prod.fst :=
  rfl

@[simp, normCast]
theorem coe_snd [Module R₁ M₂] : (snd R₁ M₁ M₂ : M₁ × M₂ →ₗ[R₁] M₂) = LinearMap.snd R₁ M₁ M₂ :=
  rfl

@[simp, normCast]
theorem coe_snd' [Module R₁ M₂] : (snd R₁ M₁ M₂ : M₁ × M₂ → M₂) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd [Module R₁ M₂] : (fst R₁ M₁ M₂).Prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext$ fun ⟨x, y⟩ => rfl

@[simp]
theorem fst_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  (fst R₁ M₂ M₃).comp (f.prod g) = f :=
  ext$ fun x => rfl

@[simp]
theorem snd_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  (snd R₁ M₂ M₃).comp (f.prod g) = g :=
  ext$ fun x => rfl

/-- `prod.map` of two continuous linear maps. -/
def prod_mapₓ [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  M₁ × M₃ →L[R₁] M₂ × M₄ :=
  (f₁.comp (fst R₁ M₁ M₃)).Prod (f₂.comp (snd R₁ M₁ M₃))

@[simp, normCast]
theorem coe_prod_map [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  (f₁.prod_map f₂ : M₁ × M₃ →ₗ[R₁] M₂ × M₄) = (f₁ : M₁ →ₗ[R₁] M₂).prod_map (f₂ : M₃ →ₗ[R₁] M₄) :=
  rfl

@[simp, normCast]
theorem coe_prod_map' [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  «expr⇑ » (f₁.prod_map f₂) = Prod.mapₓ f₁ f₂ :=
  rfl

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [Module R₁ M₂] [Module R₁ M₃] [HasContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) :
  M₁ × M₂ →L[R₁] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[normCast, simp]
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

variable{R S :
    Type
      _}[Semiringₓ
      R][Semiringₓ
      S][Module R
      M₁][Module R M₂][Module R S][Module S M₂][IsScalarTower R S M₂][TopologicalSpace S][HasContinuousSmul S M₂]

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `continuous_linear_map.smul_rightₗ` and `continuous_linear_map.smul_rightL`. -/
def smul_right (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.to_linear_map.smul_right f with cont := c.2.smul continuous_const }

@[simp]
theorem smul_right_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} : (smul_right c f : M₁ → M₂) x = c x • f :=
  rfl

end 

variable[Module R₁ M₂][TopologicalSpace R₁][HasContinuousSmul R₁ M₂]

@[simp]
theorem smul_right_one_one (c : R₁ →L[R₁] M₂) : smul_right (1 : R₁ →L[R₁] R₁) (c 1) = c :=
  by 
    ext <;> simp [←ContinuousLinearMap.map_smul_of_tower]

@[simp]
theorem smul_right_one_eq_iff {f f' : M₂} :
  smul_right (1 : R₁ →L[R₁] R₁) f = smul_right (1 : R₁ →L[R₁] R₁) f' ↔ f = f' :=
  by 
    simp only [ext_ring_iff, smul_right_apply, one_apply, one_smul]

theorem smul_right_comp [HasContinuousMul R₁] {x : M₂} {c : R₁} :
  (smul_right (1 : R₁ →L[R₁] R₁) x).comp (smul_right (1 : R₁ →L[R₁] R₁) c) = smul_right (1 : R₁ →L[R₁] R₁) (c • x) :=
  by 
    ext 
    simp [mul_smul]

end Semiringₓ

section Pi

variable{R :
    Type
      _}[Semiringₓ
      R]{M :
    Type
      _}[TopologicalSpace
      M][AddCommMonoidₓ
      M][Module R
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommMonoidₓ
      M₂][Module R
      M₂]{ι : Type _}{φ : ι → Type _}[∀ i, TopologicalSpace (φ i)][∀ i, AddCommMonoidₓ (φ i)][∀ i, Module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).Continuous⟩

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : «expr⇑ » (pi f) = fun c i => f i c :=
  rfl

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 :=
  by 
    simp only [ext_iff, pi_apply, Function.funext_iffₓ]
    exact forall_swap

theorem pi_zero : pi (fun i => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext$ fun _ => rfl

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) : (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext$ fun c => rfl

theorem infi_ker_proj : (⨅i, ker (proj i) : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.infi_ker_proj

variable(R φ)

-- error in Topology.Algebra.Module: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv
{I J : set ι}
[decidable_pred (λ i, «expr ∈ »(i, I))]
(hd : disjoint I J)
(hu : «expr ⊆ »(set.univ, «expr ∪ »(I, J))) : «expr ≃L[ ] »((«expr⨅ , »((i «expr ∈ » J), ker (proj i)) : submodule R (∀
  i, φ i)), R, ∀ i : I, φ i) :=
⟨linear_map.infi_ker_proj_equiv R φ hd hu, continuous_pi (λ i, begin
    have [] [] [":=", expr @continuous_subtype_coe _ _ (λ
      x, «expr ∈ »(x, («expr⨅ , »((i «expr ∈ » J), ker (proj i)) : submodule R (∀ i, φ i))))],
    have [] [] [":=", expr continuous.comp (by exact [expr continuous_apply i]) this],
    exact [expr this]
  end), continuous_subtype_mk _ (continuous_pi (λ i, begin
     dsimp [] [] [] [],
     split_ifs [] []; [apply [expr continuous_apply], exact [expr continuous_zero]]
   end))⟩

end Pi

section Ringₓ

variable{R :
    Type
      _}[Ringₓ
      R]{R₂ :
    Type
      _}[Ringₓ
      R₂]{M :
    Type
      _}[TopologicalSpace
      M][AddCommGroupₓ
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommGroupₓ
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommGroupₓ
      M₃]{M₄ : Type _}[TopologicalSpace M₄][AddCommGroupₓ M₄][Module R M][Module R₂ M₂]{σ₁₂ : R →+* R₂}

section 

variable(f g : M →SL[σ₁₂] M₂)(x y : M)

@[simp]
theorem map_neg : f (-x) = -f x :=
  (to_linear_map _).map_neg _

@[simp]
theorem map_sub : f (x - y) = f x - f y :=
  (to_linear_map _).map_sub _ _

@[simp]
theorem sub_apply' (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end 

section 

variable[Module R M₂][Module R M₃][Module R M₄]

variable(c : R)(f g : M →L[R] M₂)(h : M₂ →L[R] M₃)(x y z : M)

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

variable[TopologicalAddGroup M₂]

variable(f g : M →SL[σ₁₂] M₂)(x y : M)

instance  : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp]
theorem neg_apply : (-f) x = -f x :=
  rfl

@[simp, normCast]
theorem coe_neg : ((-f : M →SL[σ₁₂] M₂) : M →ₛₗ[σ₁₂] M₂) = -(f : M →ₛₗ[σ₁₂] M₂) :=
  rfl

@[normCast]
theorem coe_neg' : ((-f : M →SL[σ₁₂] M₂) : M → M₂) = -(f : M → M₂) :=
  rfl

instance  : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

theorem continuous_zsmul : ∀ n : ℤ, Continuous fun x : M₂ => n • x
| (n : ℕ) =>
  by 
    simp only [coe_nat_zsmul]
    exact continuous_nsmul _
| -[1+ n] =>
  by 
    simp only [zsmul_neg_succ_of_nat]
    exact (continuous_nsmul _).neg

@[continuity]
theorem continuous.zsmul {α : Type _} [TopologicalSpace α] {n : ℤ} {f : α → M₂} (hf : Continuous f) :
  Continuous fun x : α => n • f x :=
  (continuous_zsmul n).comp hf

instance  : AddCommGroupₓ (M →SL[σ₁₂] M₂) :=
  by 
    refine'
        { ContinuousLinearMap.addCommMonoid with zero := 0, add := ·+·, neg := Neg.neg, sub := Sub.sub,
          sub_eq_add_neg := _,
          nsmul :=
            fun n f =>
              { toFun := fun x => n • f x,
                map_add' :=
                  by 
                    simp ,
                map_smul' :=
                  by 
                    simp [smul_comm n] },
          zsmul :=
            fun n f =>
              { toFun := fun x => n • f x,
                map_add' :=
                  by 
                    simp ,
                map_smul' :=
                  by 
                    simp [smul_comm n] },
          zsmul_zero' :=
            fun f =>
              by 
                ext 
                simp ,
          zsmul_succ' :=
            fun n f =>
              by 
                ext 
                simp [add_smul, add_commₓ],
          zsmul_neg' :=
            fun n f =>
              by 
                ext 
                simp [Nat.succ_eq_add_one, add_smul],
          .. } <;>
      intros  <;> ext <;> applyRules [zero_addₓ, add_assocₓ, add_zeroₓ, add_left_negₓ, add_commₓ, sub_eq_add_neg]

theorem sub_apply (x : M) : (f - g) x = f x - g x :=
  rfl

@[simp, normCast]
theorem coe_sub : ((f - g : M →SL[σ₁₂] M₂) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[simp, normCast]
theorem coe_sub' : ((f - g : M →SL[σ₁₂] M₂) : M → M₂) = (f : M → M₂) - g :=
  rfl

end 

instance  [TopologicalAddGroup M] : Ringₓ (M →L[R] M) :=
  { ContinuousLinearMap.addCommGroup with mul := ·*·, one := 1, mul_one := fun _ => ext$ fun _ => rfl,
    one_mul := fun _ => ext$ fun _ => rfl, mul_assoc := fun _ _ _ => ext$ fun _ => rfl,
    left_distrib := fun _ _ _ => ext$ fun _ => map_add _ _ _,
    right_distrib := fun _ _ _ => ext$ fun _ => LinearMap.add_apply _ _ _ }

theorem smul_right_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
  smul_right (1 : R →L[R] R) c ^ n = smul_right (1 : R →L[R] R) (c ^ n) :=
  by 
    induction' n with n ihn
    ·
      ext 
      simp 
    ·
      rw [pow_succₓ, ihn, mul_def, smul_right_comp, smul_eq_mul, pow_succ'ₓ]

section 

variable{σ₂₁ : R₂ →+* R}[RingHomInvPair σ₁₂ σ₂₁]

/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def proj_ker_of_right_inverse [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
  (h : Function.RightInverse f₂ f₁) : M →L[R] f₁.ker :=
  (id R M - f₂.comp f₁).codRestrict f₁.ker$
    fun x =>
      by 
        simp [h (f₁ x)]

@[simp]
theorem coe_proj_ker_of_right_inverse_apply [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
  (h : Function.RightInverse f₂ f₁) (x : M) : (f₁.proj_ker_of_right_inverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem proj_ker_of_right_inverse_apply_idem [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
  (h : Function.RightInverse f₂ f₁) (x : f₁.ker) : f₁.proj_ker_of_right_inverse f₂ h x = x :=
  Subtype.ext_iff_val.2$
    by 
      simp 

@[simp]
theorem proj_ker_of_right_inverse_comp_inv [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
  (h : Function.RightInverse f₂ f₁) (y : M₂) : f₁.proj_ker_of_right_inverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff_val.2$
    by 
      simp [h y]

end 

end Ringₓ

section SmulMonoid

variable{R S :
    Type
      _}[Semiringₓ
      R][Monoidₓ
      S][TopologicalSpace
      S]{M :
    Type
      _}[TopologicalSpace
      M][AddCommMonoidₓ
      M][Module R
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommMonoidₓ
      M₂][Module R
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommMonoidₓ M₃][Module R M₃][DistribMulAction S M₃][SmulCommClass R S M₃][HasContinuousSmul S M₃]

instance  : MulAction S (M →L[R] M₃) :=
  { smul := fun c f => ⟨c • f, (continuous_const.smul f.2 : Continuous fun x => c • f x)⟩,
    one_smul := fun f => ext$ fun x => one_smul _ _, mul_smul := fun a b f => ext$ fun x => mul_smul _ _ _ }

variable(c : S)(h : M₂ →L[R] M₃)(f g : M →L[R] M₂)(x y z : M)

@[simp]
theorem smul_comp : (c • h).comp f = c • h.comp f :=
  rfl

variable[DistribMulAction S M₂][HasContinuousSmul S M₂][SmulCommClass R S M₂]

theorem smul_apply : (c • f) x = c • f x :=
  rfl

@[simp, normCast]
theorem coe_smul : ((c • f : M →L[R] M₂) : M →ₗ[R] M₂) = c • f :=
  rfl

@[simp, normCast]
theorem coe_smul' : ((c • f : M →L[R] M₂) : M → M₂) = c • f :=
  rfl

@[simp]
theorem comp_smul [LinearMap.CompatibleSmul M₂ M₃ S R] : h.comp (c • f) = c • h.comp f :=
  by 
    ext x 
    exact h.map_smul_of_tower c (f x)

instance  {T : Type _} [Monoidₓ T] [TopologicalSpace T] [DistribMulAction T M₂] [HasContinuousSmul T M₂]
  [SmulCommClass R T M₂] [HasScalar S T] [IsScalarTower S T M₂] : IsScalarTower S T (M →L[R] M₂) :=
  ⟨fun a b f => ext$ fun x => smul_assoc a b (f x)⟩

instance  {T : Type _} [Monoidₓ T] [TopologicalSpace T] [DistribMulAction T M₂] [HasContinuousSmul T M₂]
  [SmulCommClass R T M₂] [SmulCommClass S T M₂] : SmulCommClass S T (M →L[R] M₂) :=
  ⟨fun a b f => ext$ fun x => smul_comm a b (f x)⟩

instance  [HasContinuousAdd M₂] : DistribMulAction S (M →L[R] M₂) :=
  { smul_add := fun a f g => ext$ fun x => smul_add a (f x) (g x), smul_zero := fun a => ext$ fun x => smul_zero _ }

end SmulMonoid

section Smul

variable{R S :
    Type
      _}[Semiringₓ
      R][Semiringₓ
      S][TopologicalSpace
      S]{M :
    Type
      _}[TopologicalSpace
      M][AddCommMonoidₓ
      M][Module R
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommMonoidₓ
      M₂][Module R
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommMonoidₓ
      M₃][Module R
      M₃][Module S
      M₃][HasContinuousSmul S
      M₃][SmulCommClass R S
      M₃][Module S
      M₂][HasContinuousSmul S M₂][SmulCommClass R S M₂](c : S)(h : M₂ →L[R] M₃)(f g : M →L[R] M₂)(x y z : M)

/-- `continuous_linear_map.prod` as an `equiv`. -/
@[simps apply]
def prod_equiv : (M →L[R] M₂) × (M →L[R] M₃) ≃ (M →L[R] M₂ × M₃) :=
  { toFun := fun f => f.1.Prod f.2, invFun := fun f => ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩,
    left_inv :=
      fun f =>
        by 
          ext <;> rfl,
    right_inv :=
      fun f =>
        by 
          ext <;> rfl }

theorem prod_ext_iff {f g : M × M₂ →L[R] M₃} :
  f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  by 
    simp only [←coe_inj, LinearMap.prod_ext_iff]
    rfl

@[ext]
theorem prod_ext {f g : M × M₂ →L[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable[HasContinuousAdd M₂]

instance  : Module S (M →L[R] M₂) :=
  { zero_smul := fun _ => ext$ fun _ => zero_smul _ _, add_smul := fun _ _ _ => ext$ fun _ => add_smul _ _ _ }

variable(S)[HasContinuousAdd M₃]

/-- `continuous_linear_map.prod` as a `linear_equiv`. -/
@[simps apply]
def prodₗ : ((M →L[R] M₂) × (M →L[R] M₃)) ≃ₗ[S] M →L[R] M₂ × M₃ :=
  { prod_equiv with map_add' := fun f g => rfl, map_smul' := fun c f => rfl }

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coe_lm : (M →L[R] M₂) →ₗ[S] M →ₗ[R] M₂ :=
  { toFun := coeₓ, map_add' := fun f g => coe_add f g, map_smul' := fun c f => coe_smul c f }

end Smul

section SmulRightₗ

variable{R S T M M₂ :
    Type
      _}[Ringₓ
      R][Ringₓ
      S][Ringₓ
      T][Module R
      S][AddCommGroupₓ
      M₂][Module R
      M₂][Module S
      M₂][IsScalarTower R S
      M₂][TopologicalSpace
      S][TopologicalSpace
      M₂][HasContinuousSmul S
      M₂][TopologicalSpace
      M][AddCommGroupₓ
      M][Module R
      M][TopologicalAddGroup
      M₂][TopologicalSpace T][Module T M₂][HasContinuousSmul T M₂][SmulCommClass R T M₂][SmulCommClass S T M₂]

/-- Given `c : E →L[𝕜] 𝕜`, `c.smul_rightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. See also `continuous_linear_map.smul_rightL`. -/
def smul_rightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ :=
  { toFun := c.smul_right,
    map_add' :=
      fun x y =>
        by 
          ext e 
          apply smul_add,
    map_smul' :=
      fun a x =>
        by 
          ext e 
          dsimp 
          apply smul_comm }

@[simp]
theorem coe_smul_rightₗ (c : M →L[R] S) : «expr⇑ » (smul_rightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smul_right :=
  rfl

end SmulRightₗ

section CommRingₓ

variable{R :
    Type
      _}[CommRingₓ
      R][TopologicalSpace
      R]{M :
    Type
      _}[TopologicalSpace
      M][AddCommGroupₓ
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommGroupₓ
      M₂]{M₃ :
    Type _}[TopologicalSpace M₃][AddCommGroupₓ M₃][Module R M][Module R M₂][Module R M₃][HasContinuousSmul R M₃]

variable[TopologicalAddGroup M₂][HasContinuousSmul R M₂]

instance  : Algebra R (M₂ →L[R] M₂) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

end CommRingₓ

section RestrictScalars

variable{A M M₂ :
    Type
      _}[Ringₓ
      A][AddCommGroupₓ
      M][AddCommGroupₓ
      M₂][Module A
      M][Module A
      M₂][TopologicalSpace
      M][TopologicalSpace M₂](R : Type _)[Ringₓ R][Module R M][Module R M₂][LinearMap.CompatibleSmul M M₂ R A]

/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `linear_map.compatible_smul M M₂ R A` to match assumptions of
`linear_map.map_smul_of_tower`. -/
def restrict_scalars (f : M →L[A] M₂) : M →L[R] M₂ :=
  ⟨(f : M →ₗ[A] M₂).restrictScalars R, f.continuous⟩

variable{R}

@[simp, normCast]
theorem coe_restrict_scalars (f : M →L[A] M₂) :
  (f.restrict_scalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrictScalars R :=
  rfl

@[simp]
theorem coe_restrict_scalars' (f : M →L[A] M₂) : «expr⇑ » (f.restrict_scalars R) = f :=
  rfl

@[simp]
theorem restrict_scalars_zero : (0 : M →L[A] M₂).restrictScalars R = 0 :=
  rfl

section 

variable[TopologicalAddGroup M₂]

@[simp]
theorem restrict_scalars_add (f g : M →L[A] M₂) : (f+g).restrictScalars R = f.restrict_scalars R+g.restrict_scalars R :=
  rfl

@[simp]
theorem restrict_scalars_neg (f : M →L[A] M₂) : (-f).restrictScalars R = -f.restrict_scalars R :=
  rfl

end 

variable{S :
    Type
      _}[Ringₓ S][TopologicalSpace S][Module S M₂][HasContinuousSmul S M₂][SmulCommClass A S M₂][SmulCommClass R S M₂]

@[simp]
theorem restrict_scalars_smul (c : S) (f : M →L[A] M₂) : (c • f).restrictScalars R = c • f.restrict_scalars R :=
  rfl

variable(A M M₂ R S)[TopologicalAddGroup M₂]

/-- `continuous_linear_map.restrict_scalars` as a `linear_map`. See also
`continuous_linear_map.restrict_scalarsL`. -/
def restrict_scalarsₗ : (M →L[A] M₂) →ₗ[S] M →L[R] M₂ :=
  { toFun := restrict_scalars R, map_add' := restrict_scalars_add, map_smul' := restrict_scalars_smul }

variable{A M M₂ R S}

@[simp]
theorem coe_restrict_scalarsₗ : «expr⇑ » (restrict_scalarsₗ A M M₂ R S) = restrict_scalars R :=
  rfl

end RestrictScalars

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoidₓ

variable{R₁ :
    Type
      _}{R₂ :
    Type
      _}{R₃ :
    Type
      _}[Semiringₓ
      R₁][Semiringₓ
      R₂][Semiringₓ
      R₃]{σ₁₂ :
    R₁ →+*
      R₂}{σ₂₁ :
    R₂ →+*
      R₁}[RingHomInvPair σ₁₂
      σ₂₁][RingHomInvPair σ₂₁
      σ₁₂]{σ₂₃ :
    R₂ →+*
      R₃}{σ₃₂ :
    R₃ →+*
      R₂}[RingHomInvPair σ₂₃
      σ₃₂][RingHomInvPair σ₃₂
      σ₂₃]{σ₁₃ :
    R₁ →+*
      R₃}{σ₃₁ :
    R₃ →+*
      R₁}[RingHomInvPair σ₁₃
      σ₃₁][RingHomInvPair σ₃₁
      σ₁₃][RingHomCompTriple σ₁₂ σ₂₃
      σ₁₃][RingHomCompTriple σ₃₂ σ₂₁
      σ₃₁]{M₁ :
    Type
      _}[TopologicalSpace
      M₁][AddCommMonoidₓ
      M₁]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommMonoidₓ
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommMonoidₓ
      M₃]{M₄ : Type _}[TopologicalSpace M₄][AddCommMonoidₓ M₄][Module R₁ M₁][Module R₂ M₂][Module R₃ M₃]

include σ₂₁

/-- A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.to_linear_equiv.to_linear_map with cont := e.continuous_to_fun }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance  : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨to_continuous_linear_map⟩

/-- Coerce continuous linear equivs to maps. -/
instance  : CoeFun (M₁ ≃SL[σ₁₂] M₂) fun _ => M₁ → M₂ :=
  ⟨fun f => f⟩

@[simp]
theorem coe_def_rev (e : M₁ ≃SL[σ₁₂] M₂) : e.to_continuous_linear_map = e :=
  rfl

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
theorem coe_to_linear_equiv (f : M₁ ≃SL[σ₁₂] M₂) : «expr⇑ » f.to_linear_equiv = f :=
  rfl

@[simp, normCast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ((e : M₁ →SL[σ₁₂] M₂) : M₁ → M₂) = e :=
  rfl

theorem to_linear_equiv_injective : Function.Injective (to_linear_equiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂)
| ⟨e, _, _⟩, ⟨e', _, _⟩, rfl => rfl

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  to_linear_equiv_injective$ LinearEquiv.ext$ congr_funₓ h

theorem coe_injective : Function.Injective (coeₓ : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun e e' h => ext$ funext$ ContinuousLinearMap.ext_iff.1 h

@[simp, normCast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

/-- A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.to_linear_equiv.to_equiv }

@[simp]
theorem coe_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : «expr⇑ » e.to_homeomorph = e :=
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

/-- An extensionality lemma for `R ≃L[R] M`. -/
theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext$
    funext$
      fun x =>
        mul_oneₓ x ▸
          by 
            rw [←smul_eq_mul, map_smul, h, map_smul]

section 

variable(R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with continuous_to_fun := continuous_id, continuous_inv_fun := continuous_id }

end 

@[simp, normCast]
theorem coe_refl : (ContinuousLinearEquiv.refl R₁ M₁ : M₁ →L[R₁] M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, normCast]
theorem coe_refl' : (ContinuousLinearEquiv.refl R₁ M₁ : M₁ → M₁) = id :=
  rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.to_linear_equiv.symm with continuous_to_fun := e.continuous_inv_fun, continuous_inv_fun := e.continuous_to_fun }

include σ₂₁

@[simp]
theorem symm_to_linear_equiv (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.to_linear_equiv = e.to_linear_equiv.symm :=
  by 
    ext 
    rfl

@[simp]
theorem symm_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : e.to_homeomorph.symm = e.symm.to_homeomorph :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

/-- See Note [custom simps projection] -/
def simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (to_linear_equiv_to_fun → apply, to_linear_equiv_inv_fun → symmApply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.to_homeomorph.symm_map_nhds_eq x

omit σ₂₁

include σ₂₁ σ₃₂ σ₃₁

/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  { e₁.to_linear_equiv.trans e₂.to_linear_equiv with
    continuous_to_fun := e₂.continuous_to_fun.comp e₁.continuous_to_fun,
    continuous_inv_fun := e₁.continuous_inv_fun.comp e₂.continuous_inv_fun }

include σ₁₃

@[simp]
theorem trans_to_linear_equiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
  (e₁.trans e₂).toLinearEquiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv :=
  by 
    ext 
    rfl

omit σ₁₃ σ₂₁ σ₃₂ σ₃₁

/-- Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def Prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
  (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  { e.to_linear_equiv.prod e'.to_linear_equiv with
    continuous_to_fun := e.continuous_to_fun.prod_map e'.continuous_to_fun,
    continuous_inv_fun := e.continuous_inv_fun.prod_map e'.continuous_inv_fun }

@[simp, normCast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) x :
  e.prod e' x = (e x.1, e' x.2) :=
  rfl

@[simp, normCast]
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

@[simp, normCast]
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
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : ((e.symm : M₂ → M₁) ∘ (e : M₁ → M₂)) = id :=
  by 
    ext x 
    exact symm_apply_apply e x

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : ((e : M₁ → M₂) ∘ (e.symm : M₂ → M₁)) = id :=
  by 
    ext x 
    exact apply_symm_apply e x

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e :=
  by 
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

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  by 
    rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.to_linear_equiv.to_equiv.symm_preimage_preimage s

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.symm.symm_preimage_preimage s

omit σ₂₁

/-- Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
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

variable(M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
instance automorphism_group : Groupₓ (M₁ ≃L[R₁] M₁) :=
  { mul := fun f g => g.trans f, one := ContinuousLinearEquiv.refl R₁ M₁, inv := fun f => f.symm,
    mul_assoc :=
      fun f g h =>
        by 
          ext 
          rfl,
    mul_one :=
      fun f =>
        by 
          ext 
          rfl,
    one_mul :=
      fun f =>
        by 
          ext 
          rfl,
    mul_left_inv :=
      fun f =>
        by 
          ext 
          exact f.left_inv x }

variable{M₁}{R₄ :
    Type
      _}[Semiringₓ
      R₄][Module R₄
      M₄]{σ₃₄ :
    R₃ →+*
      R₄}{σ₄₃ :
    R₄ →+*
      R₃}[RingHomInvPair σ₃₄
      σ₄₃][RingHomInvPair σ₄₃
      σ₃₄]{σ₂₄ :
    R₂ →+*
      R₄}{σ₁₄ : R₁ →+* R₄}[RingHomCompTriple σ₂₁ σ₁₄ σ₂₄][RingHomCompTriple σ₂₄ σ₄₃ σ₂₃][RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

include σ₂₁ σ₃₄ σ₂₃ σ₂₄ σ₁₃

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. -/
@[simps]
def arrow_congr_equiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) : (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) :=
  { toFun := fun f => (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁)),
    invFun := fun f => (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂)),
    left_inv :=
      fun f =>
        ContinuousLinearMap.ext$
          fun x =>
            by 
              simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe],
    right_inv :=
      fun f =>
        ContinuousLinearMap.ext$
          fun x =>
            by 
              simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe] }

end AddCommMonoidₓ

section AddCommGroupₓ

variable{R :
    Type
      _}[Semiringₓ
      R]{M :
    Type
      _}[TopologicalSpace
      M][AddCommGroupₓ
      M]{M₂ :
    Type
      _}[TopologicalSpace
      M₂][AddCommGroupₓ
      M₂]{M₃ :
    Type
      _}[TopologicalSpace
      M₃][AddCommGroupₓ
      M₃]{M₄ : Type _}[TopologicalSpace M₄][AddCommGroupₓ M₄][Module R M][Module R M₂][Module R M₃][Module R M₄]

variable[TopologicalAddGroup M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skew_prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  { e.to_linear_equiv.skew_prod e'.to_linear_equiv («expr↑ » f) with
    continuous_to_fun :=
      (e.continuous_to_fun.comp continuous_fst).prod_mk
        ((e'.continuous_to_fun.comp continuous_snd).add$ f.continuous.comp continuous_fst),
    continuous_inv_fun :=
      (e.continuous_inv_fun.comp continuous_fst).prod_mk
        (e'.continuous_inv_fun.comp$ continuous_snd.sub$ f.continuous.comp$ e.continuous_inv_fun.comp continuous_fst) }

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

variable{R :
    Type
      _}[Ringₓ
      R]{R₂ :
    Type
      _}[Ringₓ
      R₂]{M :
    Type
      _}[TopologicalSpace
      M][AddCommGroupₓ M][Module R M]{M₂ : Type _}[TopologicalSpace M₂][AddCommGroupₓ M₂][Module R₂ M₂]

variable{σ₁₂ : R →+* R₂}{σ₂₁ : R₂ →+* R}[RingHomInvPair σ₁₂ σ₂₁][RingHomInvPair σ₂₁ σ₁₂]

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


variable[TopologicalAddGroup M]

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def of_unit (f : Units (M →L[R] M)) : M ≃L[R] M :=
  { toLinearEquiv :=
      { toFun := f.val,
        map_add' :=
          by 
            simp ,
        map_smul' :=
          by 
            simp ,
        invFun := f.inv,
        left_inv :=
          fun x =>
            show (f.inv*f.val) x = x by 
              rw [f.inv_val]
              simp ,
        right_inv :=
          fun x =>
            show (f.val*f.inv) x = x by 
              rw [f.val_inv]
              simp  },
    continuous_to_fun := f.val.continuous, continuous_inv_fun := f.inv.continuous }

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def to_unit (f : M ≃L[R] M) : Units (M →L[R] M) :=
  { val := f, inv := f.symm,
    val_inv :=
      by 
        ext 
        simp ,
    inv_val :=
      by 
        ext 
        simp  }

variable(R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def units_equiv : Units (M →L[R] M) ≃* M ≃L[R] M :=
  { toFun := of_unit, invFun := to_unit,
    left_inv :=
      fun f =>
        by 
          ext 
          rfl,
    right_inv :=
      fun f =>
        by 
          ext 
          rfl,
    map_mul' :=
      fun x y =>
        by 
          ext 
          rfl }

@[simp]
theorem units_equiv_apply (f : Units (M →L[R] M)) (x : M) : units_equiv R M f x = f x :=
  rfl

end 

section 

variable(R)[TopologicalSpace R][HasContinuousMul R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `units R`. -/
def units_equiv_aut : Units R ≃ R ≃L[R] R :=
  { toFun :=
      fun u =>
        equiv_of_inverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) («expr↑ » u))
          (ContinuousLinearMap.smulRight (1 : R →L[R] R) («expr↑ » (u⁻¹)))
          (fun x =>
            by 
              simp )
          fun x =>
            by 
              simp ,
    invFun :=
      fun e =>
        ⟨e 1, e.symm 1,
          by 
            rw [←smul_eq_mul, ←map_smul, smul_eq_mul, mul_oneₓ, symm_apply_apply],
          by 
            rw [←smul_eq_mul, ←map_smul, smul_eq_mul, mul_oneₓ, apply_symm_apply]⟩,
    left_inv :=
      fun u =>
        Units.ext$
          by 
            simp ,
    right_inv :=
      fun e =>
        ext₁$
          by 
            simp  }

variable{R}

@[simp]
theorem units_equiv_aut_apply (u : Units R) (x : R) : units_equiv_aut R u x = x*u :=
  rfl

@[simp]
theorem units_equiv_aut_apply_symm (u : Units R) (x : R) : (units_equiv_aut R u).symm x = x*«expr↑ » (u⁻¹) :=
  rfl

@[simp]
theorem units_equiv_aut_symm_apply (e : R ≃L[R] R) : «expr↑ » ((units_equiv_aut R).symm e) = e 1 :=
  rfl

end 

variable[Module R M₂][TopologicalAddGroup M]

open _root_.continuous_linear_map(id fst snd subtypeVal mem_ker)

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
  M ≃L[R] M₂ × f₁.ker :=
  equiv_of_inverse (f₁.prod (f₁.proj_ker_of_right_inverse f₂ h)) (f₂.coprod (subtype_val f₁.ker))
    (fun x =>
      by 
        simp )
    fun ⟨x, y⟩ =>
      by 
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

variable(ι R M : Type _)[Unique ι][Semiringₓ R][AddCommMonoidₓ M][Module R M][TopologicalSpace M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def fun_unique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable{ι R M}

@[simp]
theorem coe_fun_unique : «expr⇑ » (fun_unique ι R M) = Function.eval (default ι) :=
  rfl

@[simp]
theorem coe_fun_unique_symm : «expr⇑ » (fun_unique ι R M).symm = Function.const ι :=
  rfl

variable(R M)

/-- Continuous linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps (config := { fullyApplied := ff })]
def pi_fin_two (M : Finₓ 2 → Type _) [∀ i, AddCommMonoidₓ (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] :
  (∀ i, M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

/-- Continuous linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps (config := { fullyApplied := ff })]
def fin_two_arrow : (Finₓ 2 → M) ≃L[R] M × M :=
  { pi_fin_two R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

end 

end ContinuousLinearEquiv

namespace ContinuousLinearMap

open_locale Classical

variable{R : Type _}{M : Type _}{M₂ : Type _}[TopologicalSpace M][TopologicalSpace M₂]

section 

variable[Semiringₓ R]

variable[AddCommMonoidₓ M₂][Module R M₂]

variable[AddCommMonoidₓ M][Module R M]

/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M :=
  fun f => if h : ∃ e : M ≃L[R] M₂, (e : M →L[R] M₂) = f then ((Classical.some h).symm : M₂ →L[R] M) else 0

-- error in Topology.Algebra.Module: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp]
theorem inverse_equiv (e : «expr ≃L[ ] »(M, R, M₂)) : «expr = »(inverse (e : «expr →L[ ] »(M, R, M₂)), e.symm) :=
begin
  have [ident h] [":", expr «expr∃ , »((e' : «expr ≃L[ ] »(M, R, M₂)), «expr = »((e' : «expr →L[ ] »(M, R, M₂)), «expr↑ »(e)))] [":=", expr ⟨e, rfl⟩],
  simp [] [] ["only"] ["[", expr inverse, ",", expr dif_pos h, "]"] [] [],
  congr,
  exact_mod_cast [expr classical.some_spec h]
end

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp]
theorem inverse_non_equiv (f : M →L[R] M₂) (h : ¬∃ e' : M ≃L[R] M₂, «expr↑ » e' = f) : inverse f = 0 :=
  dif_neg h

end 

section 

variable[Ringₓ R]

variable[AddCommGroupₓ M][TopologicalAddGroup M][Module R M]

variable[AddCommGroupₓ M₂][Module R M₂]

@[simp]
theorem ring_inverse_equiv (e : M ≃L[R] M) : Ring.inverse («expr↑ » e) = inverse (e : M →L[R] M) :=
  by 
    suffices  : Ring.inverse ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M) = inverse («expr↑ » e)
    ·
      convert this 
    simp 
    rfl

/-- The function `continuous_linear_equiv.inverse` can be written in terms of `ring.inverse` for the
ring of self-maps of the domain. -/
theorem to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
  inverse f = Ring.inverse ((e.symm : M₂ →L[R] M).comp f) ∘L «expr↑ » e.symm :=
  by 
    byCases' h₁ : ∃ e' : M ≃L[R] M₂, «expr↑ » e' = f
    ·
      obtain ⟨e', he'⟩ := h₁ 
      rw [←he']
      change _ = Ring.inverse («expr↑ » (e'.trans e.symm)) ∘L «expr↑ » e.symm 
      ext 
      simp 
    ·
      suffices  : ¬IsUnit ((e.symm : M₂ →L[R] M).comp f)
      ·
        simp [this, h₁]
      contrapose! h₁ 
      rcases h₁ with ⟨F, hF⟩
      use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e 
      ext 
      dsimp 
      rw [coe_fn_coe_base' F, hF]
      simp 

theorem ring_inverse_eq_map_inverse : Ring.inverse = @inverse R M M _ _ _ _ _ _ _ :=
  by 
    ext 
    simp [to_ring_inverse (ContinuousLinearEquiv.refl R M)]

end 

end ContinuousLinearMap

namespace Submodule

variable{R :
    Type
      _}[Ringₓ
      R]{M :
    Type
      _}[TopologicalSpace
      M][AddCommGroupₓ M][Module R M]{M₂ : Type _}[TopologicalSpace M₂][AddCommGroupₓ M₂][Module R M₂]

open ContinuousLinearMap

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def closed_complemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

theorem closed_complemented.has_closed_complement {p : Submodule R M} [T1Space p] (h : closed_complemented p) :
  ∃ (q : Submodule R M)(hq : IsClosed (q : Set M)), IsCompl p q :=
  Exists.elim h$ fun f hf => ⟨f.ker, f.is_closed_ker, LinearMap.is_compl_of_proj hf⟩

-- error in Topology.Algebra.Module: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem closed_complemented.is_closed
[topological_add_group M]
[t1_space M]
{p : submodule R M}
(h : closed_complemented p) : is_closed (p : set M) :=
begin
  rcases [expr h, "with", "⟨", ident f, ",", ident hf, "⟩"],
  have [] [":", expr «expr = »(ker «expr - »(id R M, (subtype_val p).comp f), p)] [":=", expr linear_map.ker_id_sub_eq_of_proj hf],
  exact [expr «expr ▸ »(this, is_closed_ker _)]
end

@[simp]
theorem closed_complemented_bot : closed_complemented (⊥ : Submodule R M) :=
  ⟨0,
    fun x =>
      by 
        simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp]
theorem closed_complemented_top : closed_complemented (⊤ : Submodule R M) :=
  ⟨(id R M).codRestrict ⊤ fun x => trivialₓ,
    fun x =>
      Subtype.ext_iff_val.2$
        by 
          simp ⟩

end Submodule

theorem ContinuousLinearMap.closed_complemented_ker_of_right_inverse {R : Type _} [Ringₓ R] {M : Type _}
  [TopologicalSpace M] [AddCommGroupₓ M] {M₂ : Type _} [TopologicalSpace M₂] [AddCommGroupₓ M₂] [Module R M]
  [Module R M₂] [TopologicalAddGroup M] (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
  f₁.ker.closed_complemented :=
  ⟨f₁.proj_ker_of_right_inverse f₂ h, f₁.proj_ker_of_right_inverse_apply_idem f₂ h⟩

