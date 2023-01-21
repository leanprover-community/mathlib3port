/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.uniform_space.completion
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
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


noncomputable section

open Filter Set

universe u v w x

open uniformity Classical TopologicalSpace Filter

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def CauchyCat (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }
#align Cauchy CauchyCat

namespace CauchyCat

section

parameter {α : Type u}[UniformSpace α]

variable {β : Type v} {γ : Type w}

variable [UniformSpace β] [UniformSpace γ]

/-- The pairs of Cauchy filters generated by a set. -/
def gen (s : Set (α × α)) : Set (CauchyCat α × CauchyCat α) :=
  { p | s ∈ p.1.val ×ᶠ p.2.val }
#align Cauchy.gen CauchyCat.gen

theorem monotone_gen : Monotone gen :=
  monotone_set_of fun p => @Filter.monotone_mem _ (p.1.val ×ᶠ p.2.val)
#align Cauchy.monotone_gen CauchyCat.monotone_gen

private theorem symm_gen : map Prod.swap ((𝓤 α).lift' gen) ≤ (𝓤 α).lift' gen :=
  calc
    map Prod.swap ((𝓤 α).lift' gen) =
        (𝓤 α).lift' fun s : Set (α × α) => { p | s ∈ p.2.val ×ᶠ p.1.val } :=
      by
      delta gen
      simp [map_lift'_eq, monotone_set_of, Filter.monotone_mem, Function.comp,
        image_swap_eq_preimage_swap, -Subtype.val_eq_coe]
    _ ≤ (𝓤 α).lift' gen :=
      uniformity_lift_le_swap
        (monotone_principal.comp
          (monotone_set_of fun p => @Filter.monotone_mem _ (p.2.val ×ᶠ p.1.val)))
        (by
          have h := fun p : CauchyCat α × CauchyCat α => @Filter.prod_comm _ _ p.2.val p.1.val
          simp [Function.comp, h, -Subtype.val_eq_coe, mem_map']
          exact le_rfl)
    
#align Cauchy.symm_gen Cauchy.symm_gen

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem comp_rel_gen_gen_subset_gen_comp_rel {s t : Set (α × α)} :
    compRel (gen s) (gen t) ⊆ (gen (compRel s t) : Set (CauchyCat α × CauchyCat α)) :=
  fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ ∈ f), t₂, (ht₂ : t₂ ∈ h), (h₁ : t₁ ×ˢ t₂ ⊆ s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ ∈ h), t₄, (ht₄ : t₄ ∈ g), (h₂ : t₃ ×ˢ t₄ ⊆ t)⟩ := mem_prod_iff.mp h₂
  have : t₂ ∩ t₃ ∈ h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ᶠ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
    fun ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩ =>
    ⟨x, h₁ (show (a, x) ∈ t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) ∈ t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩
#align Cauchy.comp_rel_gen_gen_subset_gen_comp_rel Cauchy.comp_rel_gen_gen_subset_gen_comp_rel

private theorem comp_gen : (((𝓤 α).lift' gen).lift' fun s => compRel s s) ≤ (𝓤 α).lift' gen :=
  calc
    (((𝓤 α).lift' gen).lift' fun s => compRel s s) = (𝓤 α).lift' fun s => compRel (gen s) (gen s) :=
      by
      rw [lift'_lift'_assoc]
      exact monotone_gen
      exact monotone_compRel monotone_id monotone_id
    _ ≤ (𝓤 α).lift' fun s => gen <| compRel s s :=
      lift'_mono' fun s hs => comp_rel_gen_gen_subset_gen_comp_rel
    _ = ((𝓤 α).lift' fun s : Set (α × α) => compRel s s).lift' gen :=
      by
      rw [lift'_lift'_assoc]
      exact monotone_compRel monotone_id monotone_id
      exact monotone_gen
    _ ≤ (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl
    
#align Cauchy.comp_gen Cauchy.comp_gen

instance : UniformSpace (CauchyCat α) :=
  UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen
      refl := principal_le_lift'.2 fun s hs ⟨a, b⟩ (a_eq_b : a = b) => a_eq_b ▸ a.property.right hs
      symm := symm_gen
      comp := comp_gen }

theorem mem_uniformity {s : Set (CauchyCat α × CauchyCat α)} :
    s ∈ 𝓤 (CauchyCat α) ↔ ∃ t ∈ 𝓤 α, gen t ⊆ s :=
  mem_lift'_sets monotone_gen
#align Cauchy.mem_uniformity CauchyCat.mem_uniformity

theorem mem_uniformity' {s : Set (CauchyCat α × CauchyCat α)} :
    s ∈ 𝓤 (CauchyCat α) ↔ ∃ t ∈ 𝓤 α, ∀ f g : CauchyCat α, t ∈ f.1 ×ᶠ g.1 → (f, g) ∈ s :=
  mem_uniformity.trans <| bex_congr fun t h => Prod.forall
#align Cauchy.mem_uniformity' CauchyCat.mem_uniformity'

/-- Embedding of `α` into its completion `Cauchy α` -/
def pureCauchy (a : α) : CauchyCat α :=
  ⟨pure a, cauchy_pure⟩
#align Cauchy.pure_cauchy CauchyCat.pureCauchy

theorem uniformInducing_pureCauchy : UniformInducing (pure_cauchy : α → CauchyCat α) :=
  ⟨have : (preimage fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pure_cauchy, prod_principal_principal]
    calc
      comap (fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩
#align Cauchy.uniform_inducing_pure_cauchy CauchyCat.uniformInducing_pureCauchy

theorem uniformEmbedding_pureCauchy : UniformEmbedding (pure_cauchy : α → CauchyCat α) :=
  { uniform_inducing_pure_cauchy with
    inj := fun a₁ a₂ h => pure_injective <| Subtype.ext_iff_val.1 h }
#align Cauchy.uniform_embedding_pure_cauchy CauchyCat.uniformEmbedding_pureCauchy

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem denseRange_pureCauchy : DenseRange pure_cauchy := fun f =>
  by
  have h_ex : ∀ s ∈ 𝓤 (CauchyCat α), ∃ y : α, (f, pure_cauchy y) ∈ s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' ∈ f.val ×ᶠ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t ⊆ t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' ∈ f.val ×ᶠ pure x :=
      mem_prod_iff.mpr
        ⟨t, ht, { y : α | (x, y) ∈ t' }, h <| mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩ =>
          ht'₂ <| prod_mk_mem_compRel (@h (a, x) ⟨h₁, hx⟩) h₂⟩
    ⟨x, ht''₂ <| by dsimp [gen] <;> exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pure_cauchy), mem_set_of_eq]
  exact
    (lift'_ne_bot_iff <| monotone_const.inter monotone_preimage).mpr fun s hs =>
      let ⟨y, hy⟩ := h_ex s hs
      have : pure_cauchy y ∈ range pure_cauchy ∩ { y : CauchyCat α | (f, y) ∈ s } :=
        ⟨mem_range_self y, hy⟩
      ⟨_, this⟩
#align Cauchy.dense_range_pure_cauchy CauchyCat.denseRange_pureCauchy

theorem denseInducing_pureCauchy : DenseInducing pure_cauchy :=
  uniform_inducing_pure_cauchy.DenseInducing dense_range_pure_cauchy
#align Cauchy.dense_inducing_pure_cauchy CauchyCat.denseInducing_pureCauchy

theorem denseEmbedding_pureCauchy : DenseEmbedding pure_cauchy :=
  uniform_embedding_pure_cauchy.DenseEmbedding dense_range_pure_cauchy
#align Cauchy.dense_embedding_pure_cauchy CauchyCat.denseEmbedding_pureCauchy

theorem nonempty_cauchyCat_iff : Nonempty (CauchyCat α) ↔ Nonempty α :=
  by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 dense_embedding_pure_cauchy.to_dense_inducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pure_cauchy c⟩
#align Cauchy.nonempty_Cauchy_iff CauchyCat.nonempty_cauchyCat_iff

section

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance : CompleteSpace (CauchyCat α) :=
  completeSpace_extension uniform_inducing_pure_cauchy dense_range_pure_cauchy fun f hf =>
    let f' : CauchyCat α := ⟨f, hf⟩
    have : map pure_cauchy f ≤ (𝓤 <| CauchyCat α).lift' (preimage (Prod.mk f')) :=
      le_lift'.2 fun s hs =>
        let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t } := fun x hx =>
          (f ×ᶠ pure x).sets_of_superset (prod_mem_prod ht' hx) h
        f.sets_of_superset ht' <| Subset.trans this (preimage_mono ht₂)
    ⟨f', by simp [nhds_eq_uniformity] <;> assumption⟩

end

instance [Inhabited α] : Inhabited (CauchyCat α) :=
  ⟨pure_cauchy default⟩

instance [h : Nonempty α] : Nonempty (CauchyCat α) :=
  h.recOn fun a => Nonempty.intro <| CauchyCat.pureCauchy a

section Extend

/-- Extend a uniformly continuous function `α → β` to a function `Cauchy α → β`. Outputs junk when
`f` is not uniformly continuous. -/
def extend (f : α → β) : CauchyCat α → β :=
  if UniformContinuous f then dense_inducing_pure_cauchy.extend f
  else fun x => f (nonempty_Cauchy_iff.1 ⟨x⟩).some
#align Cauchy.extend CauchyCat.extend

section SeparatedSpace

variable [SeparatedSpace β]

theorem extend_pureCauchy {f : α → β} (hf : UniformContinuous f) (a : α) :
    extend f (pure_cauchy a) = f a := by
  rw [extend, if_pos hf]
  exact uniformly_extend_of_ind uniform_inducing_pure_cauchy dense_range_pure_cauchy hf _
#align Cauchy.extend_pure_cauchy CauchyCat.extend_pureCauchy

end SeparatedSpace

variable [CompleteSpace β]

theorem uniformContinuous_extend {f : α → β} : UniformContinuous (extend f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend uniform_inducing_pure_cauchy dense_range_pure_cauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr
#align Cauchy.uniform_continuous_extend CauchyCat.uniformContinuous_extend

end Extend

end

theorem cauchyCat_eq {α : Type _} [Inhabited α] [UniformSpace α] [CompleteSpace α]
    [SeparatedSpace α] {f g : CauchyCat α} :
    lim f.1 = lim g.1 ↔ (f, g) ∈ separationRel (CauchyCat α) :=
  by
  constructor
  · intro e s hs
    rcases CauchyCat.mem_uniformity'.1 hs with ⟨t, tu, ts⟩
    apply ts
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩
    refine'
      mem_prod_iff.2
        ⟨_, f.2.le_nhds_Lim (mem_nhds_right (lim f.1) du), _,
          g.2.le_nhds_Lim (mem_nhds_left (lim g.1) du), fun x h => _⟩
    cases' x with a b
    cases' h with h₁ h₂
    rw [← e] at h₂
    exact dt ⟨_, h₁, h₂⟩
  · intro H
    refine' separated_def.1 (by infer_instance) _ _ fun t tu => _
    rcases mem_uniformity_isClosed tu with ⟨d, du, dc, dt⟩
    refine'
      H { p | (lim p.1.1, lim p.2.1) ∈ t } (CauchyCat.mem_uniformity'.2 ⟨d, du, fun f g h => _⟩)
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩
    have limc : ∀ (f : CauchyCat α), ∀ x ∈ f.1, lim f.1 ∈ closure x :=
      by
      intro f x xf
      rw [closure_eq_cluster_pts]
      exact f.2.1.mono (le_inf f.2.le_nhds_Lim (le_principal_iff.2 xf))
    have := dc.closure_subset_iff.2 h
    rw [closure_prod_eq] at this
    refine' dt (this ⟨_, _⟩) <;> dsimp <;> apply limc <;> assumption
#align Cauchy.Cauchy_eq CauchyCat.cauchyCat_eq

section

attribute [local instance] UniformSpace.separationSetoid

theorem separated_pureCauchy_injective {α : Type _} [UniformSpace α] [s : SeparatedSpace α] :
    Function.Injective fun a : α => ⟦pureCauchy a⟧
  | a, b, h =>
    separated_def.1 s _ _ fun s hs =>
      let ⟨t, ht, hts⟩ := by
        rw [← (@uniform_embedding_pure_cauchy α _).comap_uniformity, Filter.mem_comap] at hs <;>
          exact hs
      have : (pureCauchy a, pureCauchy b) ∈ t := Quotient.exact h t ht
      @hts (a, b) this
#align Cauchy.separated_pure_cauchy_injective CauchyCat.separated_pureCauchy_injective

end

end CauchyCat

attribute [local instance] UniformSpace.separationSetoid

open CauchyCat Set

namespace UniformSpace

variable (α : Type _) [UniformSpace α]

variable {β : Type _} [UniformSpace β]

variable {γ : Type _} [UniformSpace γ]

instance completeSpace_separation [h : CompleteSpace α] :
    CompleteSpace (Quotient (separationSetoid α)) :=
  ⟨fun f => fun hf : Cauchy f =>
    have : Cauchy (f.comap fun x => ⟦x⟧) :=
      hf.comap' comap_quotient_le_uniformity <| hf.left.comap_of_surj (surjective_quotient_mk'' _)
    let ⟨x, (hx : (f fun x => ⟦x⟧) ≤ 𝓝 x)⟩ := CompleteSpace.complete this
    ⟨⟦x⟧,
      (comap_le_comap_iff <| by simp).1
        (hx.trans <| map_le_iff_le_comap.1 continuous_quotient_mk''.ContinuousAt)⟩⟩
#align uniform_space.complete_space_separation UniformSpace.completeSpace_separation

/-- Hausdorff completion of `α` -/
def Completion :=
  Quotient (separation_setoid <| CauchyCat α)
#align uniform_space.completion UniformSpace.Completion

namespace Completion

instance [Inhabited α] : Inhabited (Completion α) :=
  Quotient.inhabited (separationSetoid (CauchyCat α))

instance (priority := 50) : UniformSpace (Completion α) :=
  separation_setoid.uniform_space

instance : CompleteSpace (Completion α) :=
  UniformSpace.completeSpace_separation (CauchyCat α)

instance : SeparatedSpace (Completion α) :=
  UniformSpace.separated_separation

instance : T3Space (Completion α) :=
  separatedT3

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : CoeTC α (Completion α) :=
  ⟨Quotient.mk'' ∘ pure_cauchy⟩

-- note [use has_coe_t]
protected theorem coe_eq : (coe : α → Completion α) = Quotient.mk'' ∘ pure_cauchy :=
  rfl
#align uniform_space.completion.coe_eq UniformSpace.Completion.coe_eq

theorem comap_coe_eq_uniformity :
    ((𝓤 _).comap fun p : α × α => ((p.1 : Completion α), (p.2 : Completion α))) = 𝓤 α :=
  by
  have :
    (fun x : α × α => ((x.1 : completion α), (x.2 : completion α))) =
      (fun x : CauchyCat α × CauchyCat α => (⟦x.1⟧, ⟦x.2⟧)) ∘ fun x : α × α =>
        (pure_cauchy x.1, pure_cauchy x.2) :=
    by ext ⟨a, b⟩ <;> simp <;> rfl
  rw [this, ← Filter.comap_comap]
  change Filter.comap _ (Filter.comap _ (𝓤 <| Quotient <| separation_setoid <| CauchyCat α)) = 𝓤 α
  rw [comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.comap_uniformity]
#align uniform_space.completion.comap_coe_eq_uniformity UniformSpace.Completion.comap_coe_eq_uniformity

theorem uniformInducing_coe : UniformInducing (coe : α → Completion α) :=
  ⟨comap_coe_eq_uniformity α⟩
#align uniform_space.completion.uniform_inducing_coe UniformSpace.Completion.uniformInducing_coe

variable {α}

theorem denseRange_coe : DenseRange (coe : α → Completion α) :=
  denseRange_pureCauchy.Quotient
#align uniform_space.completion.dense_range_coe UniformSpace.Completion.denseRange_coe

variable (α)

/-- The Haudorff completion as an abstract completion. -/
def cpkg {α : Type _} [UniformSpace α] : AbstractCompletion α
    where
  Space := Completion α
  coe := coe
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  UniformInducing := Completion.uniformInducing_coe α
  dense := Completion.denseRange_coe
#align uniform_space.completion.cpkg UniformSpace.Completion.cpkg

instance AbstractCompletion.inhabited : Inhabited (AbstractCompletion α) :=
  ⟨cpkg⟩
#align uniform_space.completion.abstract_completion.inhabited UniformSpace.Completion.AbstractCompletion.inhabited

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

theorem nonempty_completion_iff : Nonempty (Completion α) ↔ Nonempty α :=
  cpkg.dense.nonempty_iff.symm
#align uniform_space.completion.nonempty_completion_iff UniformSpace.Completion.nonempty_completion_iff

theorem uniformContinuous_coe : UniformContinuous (coe : α → Completion α) :=
  cpkg.uniform_continuous_coe
#align uniform_space.completion.uniform_continuous_coe UniformSpace.Completion.uniformContinuous_coe

theorem continuous_coe : Continuous (coe : α → Completion α) :=
  cpkg.continuous_coe
#align uniform_space.completion.continuous_coe UniformSpace.Completion.continuous_coe

theorem uniformEmbedding_coe [SeparatedSpace α] : UniformEmbedding (coe : α → Completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α
    inj := separated_pureCauchy_injective }
#align uniform_space.completion.uniform_embedding_coe UniformSpace.Completion.uniformEmbedding_coe

theorem coe_injective [SeparatedSpace α] : Function.Injective (coe : α → Completion α) :=
  UniformEmbedding.inj (uniformEmbedding_coe _)
#align uniform_space.completion.coe_injective UniformSpace.Completion.coe_injective

variable {α}

theorem denseInducing_coe : DenseInducing (coe : α → Completion α) :=
  { (uniformInducing_coe α).Inducing with dense := denseRange_coe }
#align uniform_space.completion.dense_inducing_coe UniformSpace.Completion.denseInducing_coe

/-- The uniform bijection between a complete space and its uniform completion. -/
def UniformCompletion.completeEquivSelf [CompleteSpace α] [SeparatedSpace α] : Completion α ≃ᵤ α :=
  AbstractCompletion.compareEquiv Completion.cpkg AbstractCompletion.ofComplete
#align uniform_space.completion.uniform_completion.complete_equiv_self UniformSpace.Completion.UniformCompletion.completeEquivSelf

open TopologicalSpace

instance separableSpace_completion [SeparableSpace α] : SeparableSpace (Completion α) :=
  Completion.denseInducing_coe.SeparableSpace
#align uniform_space.completion.separable_space_completion UniformSpace.Completion.separableSpace_completion

theorem denseEmbedding_coe [SeparatedSpace α] : DenseEmbedding (coe : α → Completion α) :=
  { denseInducing_coe with inj := separated_pureCauchy_injective }
#align uniform_space.completion.dense_embedding_coe UniformSpace.Completion.denseEmbedding_coe

theorem denseRange_coe₂ :
    DenseRange fun x : α × β => ((x.1 : Completion α), (x.2 : Completion β)) :=
  denseRange_coe.prod_map denseRange_coe
#align uniform_space.completion.dense_range_coe₂ UniformSpace.Completion.denseRange_coe₂

theorem denseRange_coe₃ :
    DenseRange fun x : α × β × γ =>
      ((x.1 : Completion α), ((x.2.1 : Completion β), (x.2.2 : Completion γ))) :=
  denseRange_coe.prod_map denseRange_coe₂
#align uniform_space.completion.dense_range_coe₃ UniformSpace.Completion.denseRange_coe₃

@[elab_as_elim]
theorem induction_on {p : Completion α → Prop} (a : Completion α) (hp : IsClosed { a | p a })
    (ih : ∀ a : α, p a) : p a :=
  isClosed_property denseRange_coe hp ih a
#align uniform_space.completion.induction_on UniformSpace.Completion.induction_on

@[elab_as_elim]
theorem induction_on₂ {p : Completion α → Completion β → Prop} (a : Completion α) (b : Completion β)
    (hp : IsClosed { x : Completion α × Completion β | p x.1 x.2 })
    (ih : ∀ (a : α) (b : β), p a b) : p a b :=
  have : ∀ x : Completion α × Completion β, p x.1 x.2 :=
    isClosed_property denseRange_coe₂ hp fun ⟨a, b⟩ => ih a b
  this (a, b)
#align uniform_space.completion.induction_on₂ UniformSpace.Completion.induction_on₂

@[elab_as_elim]
theorem induction_on₃ {p : Completion α → Completion β → Completion γ → Prop} (a : Completion α)
    (b : Completion β) (c : Completion γ)
    (hp : IsClosed { x : Completion α × Completion β × Completion γ | p x.1 x.2.1 x.2.2 })
    (ih : ∀ (a : α) (b : β) (c : γ), p a b c) : p a b c :=
  have : ∀ x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    isClosed_property denseRange_coe₃ hp fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)
#align uniform_space.completion.induction_on₃ UniformSpace.Completion.induction_on₃

theorem ext {Y : Type _} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : α, f a = g a) : f = g :=
  cpkg.funext hf hg h
#align uniform_space.completion.ext UniformSpace.Completion.ext

theorem ext' {Y : Type _} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : α, f a = g a) (a : Completion α) :
    f a = g a :=
  congr_fun (ext hf hg h) a
#align uniform_space.completion.ext' UniformSpace.Completion.ext'

section Extension

variable {f : α → β}

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : Completion α → β :=
  cpkg.extend f
#align uniform_space.completion.extension UniformSpace.Completion.extension

section CompleteSpace

variable [CompleteSpace β]

theorem uniformContinuous_extension : UniformContinuous (Completion.extension f) :=
  cpkg.uniform_continuous_extend
#align uniform_space.completion.uniform_continuous_extension UniformSpace.Completion.uniformContinuous_extension

theorem continuous_extension : Continuous (Completion.extension f) :=
  cpkg.continuous_extend
#align uniform_space.completion.continuous_extension UniformSpace.Completion.continuous_extension

end CompleteSpace

@[simp]
theorem extension_coe [SeparatedSpace β] (hf : UniformContinuous f) (a : α) :
    (Completion.extension f) a = f a :=
  cpkg.extend_coe hf a
#align uniform_space.completion.extension_coe UniformSpace.Completion.extension_coe

variable [SeparatedSpace β] [CompleteSpace β]

theorem extension_unique (hf : UniformContinuous f) {g : Completion α → β}
    (hg : UniformContinuous g) (h : ∀ a : α, f a = g (a : Completion α)) :
    Completion.extension f = g :=
  cpkg.extend_unique hf hg h
#align uniform_space.completion.extension_unique UniformSpace.Completion.extension_unique

@[simp]
theorem extension_comp_coe {f : Completion α → β} (hf : UniformContinuous f) :
    Completion.extension (f ∘ coe) = f :=
  cpkg.extend_comp_coe hf
#align uniform_space.completion.extension_comp_coe UniformSpace.Completion.extension_comp_coe

end Extension

section Map

variable {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : Completion α → Completion β :=
  cpkg.map cpkg f
#align uniform_space.completion.map UniformSpace.Completion.map

theorem uniformContinuous_map : UniformContinuous (Completion.map f) :=
  cpkg.uniform_continuous_map cpkg f
#align uniform_space.completion.uniform_continuous_map UniformSpace.Completion.uniformContinuous_map

theorem continuous_map : Continuous (Completion.map f) :=
  cpkg.continuous_map cpkg f
#align uniform_space.completion.continuous_map UniformSpace.Completion.continuous_map

@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : (Completion.map f) a = f a :=
  cpkg.map_coe cpkg hf a
#align uniform_space.completion.map_coe UniformSpace.Completion.map_coe

theorem map_unique {f : α → β} {g : Completion α → Completion β} (hg : UniformContinuous g)
    (h : ∀ a : α, ↑(f a) = g a) : Completion.map f = g :=
  cpkg.map_unique cpkg hg h
#align uniform_space.completion.map_unique UniformSpace.Completion.map_unique

@[simp]
theorem map_id : Completion.map (@id α) = id :=
  cpkg.map_id
#align uniform_space.completion.map_id UniformSpace.Completion.map_id

theorem extension_map [CompleteSpace γ] [SeparatedSpace γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    Completion.extension f ∘ Completion.map g = Completion.extension (f ∘ g) :=
  Completion.ext (continuous_extension.comp continuous_map) continuous_extension <| by
    intro a <;> simp only [hg, hf, hf.comp hg, (· ∘ ·), map_coe, extension_coe]
#align uniform_space.completion.extension_map UniformSpace.Completion.extension_map

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    Completion.map g ∘ Completion.map f = Completion.map (g ∘ f) :=
  extension_map ((uniformContinuous_coe _).comp hg) hf
#align uniform_space.completion.map_comp UniformSpace.Completion.map_comp

end Map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section SeparationQuotientCompletion

/-- The isomorphism between the completion of a uniform space and the completion of its separation
quotient. -/
def completionSeparationQuotientEquiv (α : Type u) [UniformSpace α] :
    Completion (SeparationQuotient α) ≃ Completion α :=
  by
  refine'
    ⟨completion.extension (SeparationQuotient.lift (coe : α → completion α)),
      completion.map Quotient.mk'', _, _⟩
  · intro a
    refine' induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) _
    rintro ⟨a⟩
    show
      completion.map Quotient.mk'' (completion.extension (SeparationQuotient.lift coe) ↑(⟦a⟧)) =
        ↑(⟦a⟧)
    rw [extension_coe (separation_quotient.uniform_continuous_lift _),
        SeparationQuotient.lift_mk (uniform_continuous_coe α),
        completion.map_coe uniform_continuous_quotient_mk] <;>
      infer_instance
  · intro a
    refine'
      completion.induction_on a
        (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => _
    rw [map_coe uniform_continuous_quotient_mk,
        extension_coe (separation_quotient.uniform_continuous_lift _),
        SeparationQuotient.lift_mk (uniform_continuous_coe α) _] <;>
      infer_instance
#align uniform_space.completion.completion_separation_quotient_equiv UniformSpace.Completion.completionSeparationQuotientEquiv

theorem uniformContinuous_completionSeparationQuotientEquiv :
    UniformContinuous ⇑(completionSeparationQuotientEquiv α) :=
  uniform_continuous_extension
#align uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv UniformSpace.Completion.uniformContinuous_completionSeparationQuotientEquiv

theorem uniformContinuous_completionSeparationQuotientEquiv_symm :
    UniformContinuous ⇑(completionSeparationQuotientEquiv α).symm :=
  uniform_continuous_map
#align uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv_symm UniformSpace.Completion.uniformContinuous_completionSeparationQuotientEquiv_symm

end SeparationQuotientCompletion

section Extension₂

variable (f : α → β → γ)

open Function

/-- Extend a two variable map to the Hausdorff completions. -/
protected def extension₂ (f : α → β → γ) : Completion α → Completion β → γ :=
  cpkg.extend₂ cpkg f
#align uniform_space.completion.extension₂ UniformSpace.Completion.extension₂

section SeparatedSpace

variable [SeparatedSpace γ] {f}

@[simp]
theorem extension₂_coe_coe (hf : UniformContinuous₂ f) (a : α) (b : β) :
    Completion.extension₂ f a b = f a b :=
  cpkg.extension₂_coe_coe cpkg hf a b
#align uniform_space.completion.extension₂_coe_coe UniformSpace.Completion.extension₂_coe_coe

end SeparatedSpace

variable [CompleteSpace γ] (f)

theorem uniform_continuous_extension₂ : UniformContinuous₂ (Completion.extension₂ f) :=
  cpkg.uniform_continuous_extension₂ cpkg f
#align uniform_space.completion.uniform_continuous_extension₂ UniformSpace.Completion.uniform_continuous_extension₂

end Extension₂

section Map₂

open Function

/-- Lift a two variable map to the Hausdorff completions. -/
protected def map₂ (f : α → β → γ) : Completion α → Completion β → Completion γ :=
  cpkg.map₂ cpkg cpkg f
#align uniform_space.completion.map₂ UniformSpace.Completion.map₂

theorem uniform_continuous_map₂ (f : α → β → γ) : UniformContinuous₂ (Completion.map₂ f) :=
  cpkg.uniform_continuous_map₂ cpkg cpkg f
#align uniform_space.completion.uniform_continuous_map₂ UniformSpace.Completion.uniform_continuous_map₂

theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → Completion α}
    {b : δ → Completion β} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => Completion.map₂ f (a d) (b d) :=
  cpkg.continuous_map₂ cpkg cpkg ha hb
#align uniform_space.completion.continuous_map₂ UniformSpace.Completion.continuous_map₂

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    Completion.map₂ f (a : Completion α) (b : Completion β) = f a b :=
  cpkg.map₂_coe_coe cpkg cpkg a b f hf
#align uniform_space.completion.map₂_coe_coe UniformSpace.Completion.map₂_coe_coe

end Map₂

end Completion

end UniformSpace

