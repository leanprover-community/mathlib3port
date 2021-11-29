import Mathbin.Topology.UniformSpace.AbstractCompletion

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `completion α` and a morphism
(ie. uniformly continuous map) `coe : α → completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`completion.extension f : completion α → β` such that `f = completion.extension f ∘ coe`.
Actually `completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `coe` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `completion.map f : completion α → completion β`
such that
  `coe ∘ f = (completion.map f) ∘ coe`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `Cauchy α` the uniform completion of the uniform space `α` (using Cauchy filters). These are not
  minimal filters.

* `completion α := quotient (separation_setoid (Cauchy α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in topology.uniform_space.basic.
-/


noncomputable theory

open Filter Set

universe u v w x

open_locale uniformity Classical TopologicalSpace Filter

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchyₓ (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }

namespace Cauchyₓ

section 

parameter {α : Type u}[UniformSpace α]

variable{β : Type v}{γ : Type w}

variable[UniformSpace β][UniformSpace γ]

def gen (s : Set (α × α)) : Set (Cauchyₓ α × Cauchyₓ α) :=
  { p | s ∈ p.1.val ×ᶠ p.2.val }

theorem monotone_gen : Monotone gen :=
  monotone_set_of$ fun p => @monotone_mem (α × α) (p.1.val ×ᶠ p.2.val)

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
private theorem symm_gen : «expr ≤ »(map prod.swap ((expr𝓤() α).lift' gen), (expr𝓤() α).lift' gen) :=
calc
  «expr = »(map prod.swap ((expr𝓤() α).lift' gen), (expr𝓤() α).lift' (λ
    s : set «expr × »(α, α), {p | «expr ∈ »(s, «expr ×ᶠ »(p.2.val, p.1.val))})) : begin
    delta [ident gen] [],
    simp [] [] [] ["[", expr map_lift'_eq, ",", expr monotone_set_of, ",", expr monotone_mem, ",", expr function.comp, ",", expr image_swap_eq_preimage_swap, ",", "-", ident subtype.val_eq_coe, "]"] [] []
  end
  «expr ≤ »(..., (expr𝓤() α).lift' gen) : uniformity_lift_le_swap (monotone_principal.comp «expr $ »(monotone_set_of, assume
    p, @monotone_mem «expr × »(α, α) «expr ×ᶠ »(p.2.val, p.1.val))) (begin
     have [ident h] [] [":=", expr λ p : «expr × »(Cauchy α, Cauchy α), @filter.prod_comm _ _ p.2.val p.1.val],
     simp [] [] [] ["[", expr function.comp, ",", expr h, ",", "-", ident subtype.val_eq_coe, ",", expr mem_map', "]"] [] [],
     exact [expr le_refl _]
   end)

private theorem comp_rel_gen_gen_subset_gen_comp_rel {s t : Set (α × α)} :
  CompRel (gen s) (gen t) ⊆ (gen (CompRel s t) : Set (Cauchyₓ α × Cauchyₓ α)) :=
  fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
    let ⟨t₁, (ht₁ : t₁ ∈ f.val), t₂, (ht₂ : t₂ ∈ h.val), (h₁ : Set.Prod t₁ t₂ ⊆ s)⟩ := mem_prod_iff.mp h₁ 
    let ⟨t₃, (ht₃ : t₃ ∈ h.val), t₄, (ht₄ : t₄ ∈ g.val), (h₂ : Set.Prod t₃ t₄ ⊆ t)⟩ := mem_prod_iff.mp h₂ 
    have  : t₂ ∩ t₃ ∈ h.val := inter_mem ht₂ ht₃ 
    let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
    (f.val ×ᶠ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
      fun ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩ =>
        ⟨x, h₁ (show (a, x) ∈ Set.Prod t₁ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) ∈ Set.Prod t₃ t₄ from ⟨xt₃, hb⟩)⟩

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
private theorem comp_gen : «expr ≤ »(((expr𝓤() α).lift' gen).lift' (λ s, comp_rel s s), (expr𝓤() α).lift' gen) :=
calc
  «expr = »(((expr𝓤() α).lift' gen).lift' (λ
    s, comp_rel s s), (expr𝓤() α).lift' (λ s, comp_rel (gen s) (gen s))) : begin
    rw ["[", expr lift'_lift'_assoc, "]"] [],
    exact [expr monotone_gen],
    exact [expr monotone_comp_rel monotone_id monotone_id]
  end
  «expr ≤ »(..., (expr𝓤() α).lift' (λ
    s, «expr $ »(gen, comp_rel s s))) : «expr $ »(lift'_mono', assume s hs, comp_rel_gen_gen_subset_gen_comp_rel)
  «expr = »(..., «expr $ »((expr𝓤() α).lift', λ s : set «expr × »(α, α), comp_rel s s).lift' gen) : begin
    rw ["[", expr lift'_lift'_assoc, "]"] [],
    exact [expr monotone_comp_rel monotone_id monotone_id],
    exact [expr monotone_gen]
  end
  «expr ≤ »(..., (expr𝓤() α).lift' gen) : lift'_mono comp_le_uniformity (le_refl _)

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance : uniform_space (Cauchy α) :=
uniform_space.of_core { uniformity := (expr𝓤() α).lift' gen,
  refl := «expr $ »(principal_le_lift', assume
   (s hs)
   ⟨a, b⟩
   (a_eq_b : «expr = »(a, b)), «expr ▸ »(a_eq_b, a.property.right hs)),
  symm := symm_gen,
  comp := comp_gen }

theorem mem_uniformity {s : Set (Cauchyₓ α × Cauchyₓ α)} : s ∈ 𝓤 (Cauchyₓ α) ↔ ∃ (t : _)(_ : t ∈ 𝓤 α), gen t ⊆ s :=
  mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : Set (Cauchyₓ α × Cauchyₓ α)} :
  s ∈ 𝓤 (Cauchyₓ α) ↔ ∃ (t : _)(_ : t ∈ 𝓤 α), ∀ (f g : Cauchyₓ α), t ∈ f.1 ×ᶠ g.1 → (f, g) ∈ s :=
  mem_uniformity.trans$ bex_congr$ fun t h => Prod.forall

/-- Embedding of `α` into its completion `Cauchy α` -/
def pure_cauchy (a : α) : Cauchyₓ α :=
  ⟨pure a, cauchy_pure⟩

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_inducing_pure_cauchy : uniform_inducing (pure_cauchy : α → Cauchy α) :=
⟨have «expr = »(«expr ∘ »(preimage (λ
    x : «expr × »(α, α), (pure_cauchy x.fst, pure_cauchy x.snd)), gen), id), from «expr $ »(funext, assume
  s, «expr $ »(set.ext, assume
   ⟨a₁, a₂⟩, by simp [] [] [] ["[", expr preimage, ",", expr gen, ",", expr pure_cauchy, ",", expr prod_principal_principal, "]"] [] [])),
 calc
   «expr = »(comap (λ
     x : «expr × »(α, α), (pure_cauchy x.fst, pure_cauchy x.snd)) ((expr𝓤() α).lift' gen), (expr𝓤() α).lift' «expr ∘ »(preimage (λ
      x : «expr × »(α, α), (pure_cauchy x.fst, pure_cauchy x.snd)), gen)) : comap_lift'_eq monotone_gen
   «expr = »(..., expr𝓤() α) : by simp [] [] [] ["[", expr this, "]"] [] []⟩

theorem uniform_embedding_pure_cauchy : UniformEmbedding (pure_cauchy : α → Cauchyₓ α) :=
  { uniform_inducing_pure_cauchy with inj := fun a₁ a₂ h => pure_injective$ Subtype.ext_iff_val.1 h }

theorem dense_range_pure_cauchy : DenseRange pure_cauchy :=
  fun f =>
    have h_ex : ∀ s (_ : s ∈ 𝓤 (Cauchyₓ α)), ∃ y : α, (f, pure_cauchy y) ∈ s :=
      fun s hs =>
        let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs 
        let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁ 
        have  : t' ∈ f.val ×ᶠ f.val := f.property.right ht'₁ 
        let ⟨t, ht, (h : Set.Prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this 
        let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht 
        have  : t'' ∈ f.val ×ᶠ pure x :=
          mem_prod_iff.mpr
            ⟨t, ht, { y:α | (x, y) ∈ t' }, h$ mk_mem_prod hx hx,
              fun ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩ => ht'₂$ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩
        ⟨x,
          ht''₂$
            by 
              dsimp [gen] <;> exact this⟩
    by 
      simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
        Set.inter_comm _ (range pure_cauchy), mem_set_of_eq]
      exact
        (lift'_ne_bot_iff$ monotone_inter monotone_const monotone_preimage).mpr
          fun s hs =>
            let ⟨y, hy⟩ := h_ex s hs 
            have  : pure_cauchy y ∈ range pure_cauchy ∩ { y:Cauchyₓ α | (f, y) ∈ s } := ⟨mem_range_self y, hy⟩
            ⟨_, this⟩

theorem dense_inducing_pure_cauchy : DenseInducing pure_cauchy :=
  uniform_inducing_pure_cauchy.dense_inducing dense_range_pure_cauchy

theorem dense_embedding_pure_cauchy : DenseEmbedding pure_cauchy :=
  uniform_embedding_pure_cauchy.dense_embedding dense_range_pure_cauchy

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nonempty_Cauchy_iff : «expr ↔ »(nonempty (Cauchy α), nonempty α) :=
begin
  split; rintro ["⟨", ident c, "⟩"],
  { have [] [] [":=", expr eq_univ_iff_forall.1 dense_embedding_pure_cauchy.to_dense_inducing.closure_range c],
    obtain ["⟨", "_", ",", "⟨", "_", ",", ident a, ",", "_", "⟩", "⟩", ":=", expr mem_closure_iff.1 this _ is_open_univ trivial],
    exact [expr ⟨a⟩] },
  { exact [expr ⟨pure_cauchy c⟩] }
end

section 

set_option eqn_compiler.zeta true

instance  : CompleteSpace (Cauchyₓ α) :=
  complete_space_extension uniform_inducing_pure_cauchy dense_range_pure_cauchy$
    fun f hf =>
      let f' : Cauchyₓ α := ⟨f, hf⟩
      have  : map pure_cauchy f ≤ (𝓤$ Cauchyₓ α).lift' (preimage (Prod.mk f')) :=
        le_lift'$
          fun s hs =>
            let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs 
            let ⟨t', ht', (h : Set.Prod t' t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
            have  : t' ⊆ { y:α | (f', pure_cauchy y) ∈ gen t } :=
              fun x hx => (f ×ᶠ pure x).sets_of_superset (prod_mem_prod ht' hx) h 
            f.sets_of_superset ht'$ subset.trans this (preimage_mono ht₂)
      ⟨f',
        by 
          simp [nhds_eq_uniformity] <;> assumption⟩

end 

instance  [Inhabited α] : Inhabited (Cauchyₓ α) :=
  ⟨pure_cauchy$ default α⟩

instance  [h : Nonempty α] : Nonempty (Cauchyₓ α) :=
  h.rec_on$ fun a => Nonempty.intro$ Cauchyₓ.pureCauchy a

section Extend

def extend (f : α → β) : Cauchyₓ α → β :=
  if UniformContinuous f then dense_inducing_pure_cauchy.extend f else
    fun x => f (Classical.inhabitedOfNonempty$ nonempty_Cauchy_iff.1 ⟨x⟩).default

variable[SeparatedSpace β]

theorem extend_pure_cauchy {f : α → β} (hf : UniformContinuous f) (a : α) : extend f (pure_cauchy a) = f a :=
  by 
    rw [extend, if_pos hf]
    exact uniformly_extend_of_ind uniform_inducing_pure_cauchy dense_range_pure_cauchy hf _

variable[_root_.complete_space β]

theorem uniform_continuous_extend {f : α → β} : UniformContinuous (extend f) :=
  by 
    byCases' hf : UniformContinuous f
    ·
      rw [extend, if_pos hf]
      exact uniform_continuous_uniformly_extend uniform_inducing_pure_cauchy dense_range_pure_cauchy hf
    ·
      rw [extend, if_neg hf]
      exact
        uniform_continuous_of_const
          fun a b =>
            by 
              congr

end Extend

end 

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Cauchy_eq
{α : Type*}
[inhabited α]
[uniform_space α]
[complete_space α]
[separated_space α]
{f g : Cauchy α} : «expr ↔ »(«expr = »(Lim f.1, Lim g.1), «expr ∈ »((f, g), separation_rel (Cauchy α))) :=
begin
  split,
  { intros [ident e, ident s, ident hs],
    rcases [expr Cauchy.mem_uniformity'.1 hs, "with", "⟨", ident t, ",", ident tu, ",", ident ts, "⟩"],
    apply [expr ts],
    rcases [expr comp_mem_uniformity_sets tu, "with", "⟨", ident d, ",", ident du, ",", ident dt, "⟩"],
    refine [expr mem_prod_iff.2 ⟨_, f.2.le_nhds_Lim (mem_nhds_right (Lim f.1) du), _, g.2.le_nhds_Lim (mem_nhds_left (Lim g.1) du), λ
      x h, _⟩],
    cases [expr x] ["with", ident a, ident b],
    cases [expr h] ["with", ident h₁, ident h₂],
    rw ["<-", expr e] ["at", ident h₂],
    exact [expr dt ⟨_, h₁, h₂⟩] },
  { intros [ident H],
    refine [expr separated_def.1 (by apply_instance) _ _ (λ t tu, _)],
    rcases [expr mem_uniformity_is_closed tu, "with", "⟨", ident d, ",", ident du, ",", ident dc, ",", ident dt, "⟩"],
    refine [expr H {p | «expr ∈ »((Lim p.1.1, Lim p.2.1), t)} (Cauchy.mem_uniformity'.2 ⟨d, du, λ f g h, _⟩)],
    rcases [expr mem_prod_iff.1 h, "with", "⟨", ident x, ",", ident xf, ",", ident y, ",", ident yg, ",", ident h, "⟩"],
    have [ident limc] [":", expr ∀ (f : Cauchy α) (x «expr ∈ » f.1), «expr ∈ »(Lim f.1, closure x)] [],
    { intros [ident f, ident x, ident xf],
      rw [expr closure_eq_cluster_pts] [],
      exact [expr f.2.1.mono (le_inf f.2.le_nhds_Lim (le_principal_iff.2 xf))] },
    have [] [] [":=", expr dc.closure_subset_iff.2 h],
    rw [expr closure_prod_eq] ["at", ident this],
    refine [expr dt (this ⟨_, _⟩)]; dsimp [] [] [] []; apply [expr limc]; assumption }
end

section 

attribute [local instance] UniformSpace.separationSetoid

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem separated_pure_cauchy_injective
{α : Type*}
[uniform_space α]
[s : separated_space α] : function.injective (λ a : α, «expr⟦ ⟧»(pure_cauchy a))
| a, b, h := «expr $ »(separated_def.1 s _ _, assume
 s
 hs, let ⟨t, ht, hts⟩ := by rw ["[", "<-", expr (@uniform_embedding_pure_cauchy α _).comap_uniformity, ",", expr filter.mem_comap, "]"] ["at", ident hs]; exact [expr hs] in
 have «expr ∈ »((pure_cauchy a, pure_cauchy b), t), from quotient.exact h t ht,
 @hts (a, b) this)

end 

end Cauchyₓ

attribute [local instance] UniformSpace.separationSetoid

open Cauchyₓ Set

namespace UniformSpace

variable(α : Type _)[UniformSpace α]

variable{β : Type _}[UniformSpace β]

variable{γ : Type _}[UniformSpace γ]

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance complete_space_separation [h : complete_space α] : complete_space (quotient (separation_setoid α)) :=
⟨assume
 f, assume
 hf : cauchy f, have cauchy (f.comap (λ
   x, «expr⟦ ⟧»(x))), from «expr $ »(hf.comap' comap_quotient_le_uniformity, hf.left.comap_of_surj (surjective_quotient_mk _)),
 let ⟨x, (hx : «expr ≤ »(f.comap (λ x, «expr⟦ ⟧»(x)), expr𝓝() x))⟩ := complete_space.complete this in
 ⟨«expr⟦ ⟧»(x), «expr $ »(comap_le_comap_iff, by simp [] [] [] [] [] []).1 «expr $ »(hx.trans, map_le_iff_le_comap.1 continuous_quotient_mk.continuous_at)⟩⟩

/-- Hausdorff completion of `α` -/
def completion :=
  Quotientₓ (separation_setoid$ Cauchyₓ α)

namespace Completion

instance  [Inhabited α] : Inhabited (completion α) :=
  by 
    unfold completion <;> infer_instance

instance (priority := 50) : UniformSpace (completion α) :=
  by 
    dunfold completion <;> infer_instance

instance  : CompleteSpace (completion α) :=
  by 
    dunfold completion <;> infer_instance

instance  : SeparatedSpace (completion α) :=
  by 
    dunfold completion <;> infer_instance

instance  : RegularSpace (completion α) :=
  separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance  : CoeTₓ α (completion α) :=
  ⟨Quotientₓ.mk ∘ pure_cauchy⟩

protected theorem coe_eq : (coeₓ : α → completion α) = (Quotientₓ.mk ∘ pure_cauchy) :=
  rfl

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comap_coe_eq_uniformity : «expr = »((expr𝓤() _).comap (λ
  p : «expr × »(α, α), ((p.1 : completion α), (p.2 : completion α))), expr𝓤() α) :=
begin
  have [] [":", expr «expr = »(λ
    x : «expr × »(α, α), ((x.1 : completion α), (x.2 : completion α)), «expr ∘ »(λ
     x : «expr × »(Cauchy α, Cauchy α), («expr⟦ ⟧»(x.1), «expr⟦ ⟧»(x.2)), λ
     x : «expr × »(α, α), (pure_cauchy x.1, pure_cauchy x.2)))] [],
  { ext [] ["⟨", ident a, ",", ident b, "⟩"] []; simp [] [] [] [] [] []; refl },
  rw ["[", expr this, ",", "<-", expr filter.comap_comap, "]"] [],
  change [expr «expr = »(filter.comap _ (filter.comap _ «expr $ »(expr𝓤(), «expr $ »(quotient, «expr $ »(separation_setoid, Cauchy α)))), expr𝓤() α)] [] [],
  rw ["[", expr comap_quotient_eq_uniformity, ",", expr uniform_embedding_pure_cauchy.comap_uniformity, "]"] []
end

theorem uniform_inducing_coe : UniformInducing (coeₓ : α → completion α) :=
  ⟨comap_coe_eq_uniformity α⟩

variable{α}

theorem dense_range_coe : DenseRange (coeₓ : α → completion α) :=
  dense_range_pure_cauchy.Quotient

variable(α)

def cpkg {α : Type _} [UniformSpace α] : AbstractCompletion α :=
  { Space := completion α, coe := coeₓ,
    uniformStruct :=
      by 
        infer_instance,
    complete :=
      by 
        infer_instance,
    separation :=
      by 
        infer_instance,
    UniformInducing := completion.uniform_inducing_coe α, dense := completion.dense_range_coe }

instance abstract_completion.inhabited : Inhabited (AbstractCompletion α) :=
  ⟨cpkg⟩

attribute [local instance] AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

theorem nonempty_completion_iff : Nonempty (completion α) ↔ Nonempty α :=
  cpkg.dense.nonempty_iff.symm

theorem uniform_continuous_coe : UniformContinuous (coeₓ : α → completion α) :=
  cpkg.uniform_continuous_coe

theorem continuous_coe : Continuous (coeₓ : α → completion α) :=
  cpkg.continuous_coe

theorem uniform_embedding_coe [SeparatedSpace α] : UniformEmbedding (coeₓ : α → completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α, inj := separated_pure_cauchy_injective }

variable{α}

theorem dense_inducing_coe : DenseInducing (coeₓ : α → completion α) :=
  { (uniform_inducing_coe α).Inducing with dense := dense_range_coe }

open TopologicalSpace

instance separable_space_completion [separable_space α] : separable_space (completion α) :=
  completion.dense_inducing_coe.SeparableSpace

theorem dense_embedding_coe [SeparatedSpace α] : DenseEmbedding (coeₓ : α → completion α) :=
  { dense_inducing_coe with inj := separated_pure_cauchy_injective }

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dense_range_coe₂ : dense_range (λ x : «expr × »(α, β), ((x.1 : completion α), (x.2 : completion β))) :=
dense_range_coe.prod_map dense_range_coe

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem dense_range_coe₃ : dense_range (λ
 x : «expr × »(α, «expr × »(β, γ)), ((x.1 : completion α), ((x.2.1 : completion β), (x.2.2 : completion γ)))) :=
dense_range_coe.prod_map dense_range_coe₂

@[elab_as_eliminator]
theorem induction_on {p : completion α → Prop} (a : completion α) (hp : IsClosed { a | p a }) (ih : ∀ (a : α), p a) :
  p a :=
  is_closed_property dense_range_coe hp ih a

@[elab_as_eliminator]
theorem induction_on₂ {p : completion α → completion β → Prop} (a : completion α) (b : completion β)
  (hp : IsClosed { x:completion α × completion β | p x.1 x.2 }) (ih : ∀ (a : α) (b : β), p a b) : p a b :=
  have  : ∀ (x : completion α × completion β), p x.1 x.2 :=
    is_closed_property dense_range_coe₂ hp$ fun ⟨a, b⟩ => ih a b 
  this (a, b)

@[elab_as_eliminator]
theorem induction_on₃ {p : completion α → completion β → completion γ → Prop} (a : completion α) (b : completion β)
  (c : completion γ) (hp : IsClosed { x:completion α × completion β × completion γ | p x.1 x.2.1 x.2.2 })
  (ih : ∀ (a : α) (b : β) (c : γ), p a b c) : p a b c :=
  have  : ∀ (x : completion α × completion β × completion γ), p x.1 x.2.1 x.2.2 :=
    is_closed_property dense_range_coe₃ hp$ fun ⟨a, b, c⟩ => ih a b c 
  this (a, b, c)

theorem ext [T2Space β] {f g : completion α → β} (hf : Continuous f) (hg : Continuous g) (h : ∀ (a : α), f a = g a) :
  f = g :=
  cpkg.funext hf hg h

section Extension

variable{f : α → β}

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : completion α → β :=
  cpkg.extend f

variable[SeparatedSpace β]

@[simp]
theorem extension_coe (hf : UniformContinuous f) (a : α) : (completion.extension f) a = f a :=
  cpkg.extend_coe hf a

variable[CompleteSpace β]

theorem uniform_continuous_extension : UniformContinuous (completion.extension f) :=
  cpkg.uniform_continuous_extend

theorem continuous_extension : Continuous (completion.extension f) :=
  cpkg.continuous_extend

theorem extension_unique (hf : UniformContinuous f) {g : completion α → β} (hg : UniformContinuous g)
  (h : ∀ (a : α), f a = g (a : completion α)) : completion.extension f = g :=
  cpkg.extend_unique hf hg h

@[simp]
theorem extension_comp_coe {f : completion α → β} (hf : UniformContinuous f) : completion.extension (f ∘ coeₓ) = f :=
  cpkg.extend_comp_coe hf

end Extension

section Map

variable{f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : completion α → completion β :=
  cpkg.map cpkg f

theorem uniform_continuous_map : UniformContinuous (completion.map f) :=
  cpkg.uniform_continuous_map cpkg f

theorem continuous_map : Continuous (completion.map f) :=
  cpkg.continuous_map cpkg f

@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : (completion.map f) a = f a :=
  cpkg.map_coe cpkg hf a

theorem map_unique {f : α → β} {g : completion α → completion β} (hg : UniformContinuous g)
  (h : ∀ (a : α), «expr↑ » (f a) = g a) : completion.map f = g :=
  cpkg.map_unique cpkg hg h

@[simp]
theorem map_id : completion.map (@id α) = id :=
  cpkg.map_id

theorem extension_map [CompleteSpace γ] [SeparatedSpace γ] {f : β → γ} {g : α → β} (hf : UniformContinuous f)
  (hg : UniformContinuous g) : (completion.extension f ∘ completion.map g) = completion.extension (f ∘ g) :=
  completion.ext (continuous_extension.comp continuous_map) continuous_extension$
    by 
      intro a <;> simp only [hg, hf, hf.comp hg, · ∘ ·, map_coe, extension_coe]

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
  (completion.map g ∘ completion.map f) = completion.map (g ∘ f) :=
  extension_map ((uniform_continuous_coe _).comp hg) hf

end Map

section SeparationQuotientCompletion

def completion_separation_quotient_equiv (α : Type u) [UniformSpace α] :
  completion (separation_quotient α) ≃ completion α :=
  by 
    refine'
      ⟨completion.extension (separation_quotient.lift (coeₓ : α → completion α)), completion.map Quotientₓ.mk, _, _⟩
    ·
      intro a 
      refine' induction_on a (is_closed_eq (continuous_map.comp continuous_extension) continuous_id) _ 
      rintro ⟨a⟩
      show
        completion.map Quotientₓ.mk (completion.extension (separation_quotient.lift coeₓ) («expr↑ » («expr⟦ ⟧» a))) =
          «expr↑ » («expr⟦ ⟧» a)
      rw [extension_coe (separation_quotient.uniform_continuous_lift _),
          separation_quotient.lift_mk (uniform_continuous_coe α), completion.map_coe uniform_continuous_quotient_mk] <;>
        infer_instance
    ·
      intro a 
      refine'
        completion.induction_on a (is_closed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => _ 
      rw [map_coe uniform_continuous_quotient_mk, extension_coe (separation_quotient.uniform_continuous_lift _),
          separation_quotient.lift_mk (uniform_continuous_coe α) _] <;>
        infer_instance

theorem uniform_continuous_completion_separation_quotient_equiv :
  UniformContinuous («expr⇑ » (completion_separation_quotient_equiv α)) :=
  uniform_continuous_extension

theorem uniform_continuous_completion_separation_quotient_equiv_symm :
  UniformContinuous («expr⇑ » (completion_separation_quotient_equiv α).symm) :=
  uniform_continuous_map

end SeparationQuotientCompletion

section Extension₂

variable(f : α → β → γ)

open Function

protected def extension₂ (f : α → β → γ) : completion α → completion β → γ :=
  cpkg.extend₂ cpkg f

variable[SeparatedSpace γ]{f}

@[simp]
theorem extension₂_coe_coe (hf : UniformContinuous₂ f) (a : α) (b : β) : completion.extension₂ f a b = f a b :=
  cpkg.extension₂_coe_coe cpkg hf a b

variable[CompleteSpace γ](f)

theorem uniform_continuous_extension₂ : UniformContinuous₂ (completion.extension₂ f) :=
  cpkg.uniform_continuous_extension₂ cpkg f

end Extension₂

section Map₂

open Function

protected def map₂ (f : α → β → γ) : completion α → completion β → completion γ :=
  cpkg.map₂ cpkg cpkg f

theorem uniform_continuous_map₂ (f : α → β → γ) : UniformContinuous₂ (completion.map₂ f) :=
  cpkg.uniform_continuous_map₂ cpkg cpkg f

-- error in Topology.UniformSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem continuous_map₂
{δ}
[topological_space δ]
{f : α → β → γ}
{a : δ → completion α}
{b : δ → completion β}
(ha : continuous a)
(hb : continuous b) : continuous (λ d : δ, completion.map₂ f (a d) (b d)) :=
cpkg.continuous_map₂ cpkg cpkg ha hb

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
  completion.map₂ f (a : completion α) (b : completion β) = f a b :=
  cpkg.map₂_coe_coe cpkg cpkg a b f hf

end Map₂

end Completion

end UniformSpace

