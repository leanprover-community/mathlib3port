/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
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
def Cauchyₓ (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }

namespace Cauchyₓ

section

parameter {α : Type u}[UniformSpace α]

variable {β : Type v} {γ : Type w}

variable [UniformSpace β] [UniformSpace γ]

def Gen (s : Set (α × α)) : Set (Cauchyₓ α × Cauchyₓ α) :=
  { p | s ∈ p.1.val ×ᶠ p.2.val }

theorem monotone_gen : Monotone gen :=
  monotone_set_of fun p => @monotone_mem (α × α) (p.1.val ×ᶠ p.2.val)

private theorem symm_gen : map Prod.swap ((𝓤 α).lift' gen) ≤ (𝓤 α).lift' gen :=
  calc
    map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' fun s : Set (α × α) => { p | s ∈ p.2.val ×ᶠ p.1.val } := by
      delta' gen
      simp [map_lift'_eq, monotone_set_of, monotone_mem, Function.comp, image_swap_eq_preimage_swap,
        -Subtype.val_eq_coe]
    _ ≤ (𝓤 α).lift' gen :=
      uniformity_lift_le_swap
        (monotone_principal.comp (monotone_set_of fun p => @monotone_mem (α × α) (p.2.val ×ᶠ p.1.val)))
        (by
          have h := fun p : Cauchyₓ α × Cauchyₓ α => @Filter.prod_comm _ _ p.2.val p.1.val
          simp [Function.comp, h, -Subtype.val_eq_coe, mem_map']
          exact le_rfl)
    

private theorem comp_rel_gen_gen_subset_gen_comp_rel {s t : Set (α × α)} :
    CompRel (gen s) (gen t) ⊆ (gen (CompRel s t) : Set (Cauchyₓ α × Cauchyₓ α)) := fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ ∈ f), t₂, (ht₂ : t₂ ∈ h), (h₁ : t₁ ×ˢ t₂ ⊆ s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ ∈ h), t₄, (ht₄ : t₄ ∈ g), (h₂ : t₃ ×ˢ t₄ ⊆ t)⟩ := mem_prod_iff.mp h₂
  have : t₂ ∩ t₃ ∈ h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ᶠ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄) fun ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩ =>
    ⟨x, h₁ (show (a, x) ∈ t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) ∈ t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩

private theorem comp_gen : (((𝓤 α).lift' gen).lift' fun s => CompRel s s) ≤ (𝓤 α).lift' gen :=
  calc
    (((𝓤 α).lift' gen).lift' fun s => CompRel s s) = (𝓤 α).lift' fun s => CompRel (gen s) (gen s) := by
      rw [lift'_lift'_assoc]
      exact monotone_gen
      exact monotone_comp_rel monotone_id monotone_id
    _ ≤ (𝓤 α).lift' fun s => gen <| CompRel s s := lift'_mono' fun s hs => comp_rel_gen_gen_subset_gen_comp_rel
    _ = ((𝓤 α).lift' fun s : Set (α × α) => CompRel s s).lift' gen := by
      rw [lift'_lift'_assoc]
      exact monotone_comp_rel monotone_id monotone_id
      exact monotone_gen
    _ ≤ (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl
    

instance : UniformSpace (Cauchyₓ α) :=
  UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen, refl := principal_le_lift' fun a_eq_b : a = b => a_eq_b ▸ a.property.right hs,
      symm := symm_gen, comp := comp_gen }

theorem mem_uniformity {s : Set (Cauchyₓ α × Cauchyₓ α)} : s ∈ 𝓤 (Cauchyₓ α) ↔ ∃ t ∈ 𝓤 α, gen t ⊆ s :=
  mem_lift'_sets monotone_gen

theorem mem_uniformity' {s : Set (Cauchyₓ α × Cauchyₓ α)} :
    s ∈ 𝓤 (Cauchyₓ α) ↔ ∃ t ∈ 𝓤 α, ∀ f g : Cauchyₓ α, t ∈ f.1 ×ᶠ g.1 → (f, g) ∈ s :=
  mem_uniformity.trans <| bex_congr fun t h => Prod.forall

/-- Embedding of `α` into its completion `Cauchy α` -/
def pureCauchy (a : α) : Cauchyₓ α :=
  ⟨pure a, cauchy_pure⟩

theorem uniform_inducing_pure_cauchy : UniformInducing (pure_cauchy : α → Cauchyₓ α) :=
  ⟨have : (Preimage fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by
          simp [preimage, gen, pure_cauchy, prod_principal_principal]
    calc
      comap (fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((Preimage fun x : α × α => (pure_cauchy x.fst, pure_cauchy x.snd)) ∘ gen) :=
        comap_lift'_eq monotone_gen
      _ = 𝓤 α := by
        simp [this]
      ⟩

theorem uniform_embedding_pure_cauchy : UniformEmbedding (pure_cauchy : α → Cauchyₓ α) :=
  { uniform_inducing_pure_cauchy with inj := fun a₁ a₂ h => pure_injective <| Subtype.ext_iff_val.1 h }

theorem dense_range_pure_cauchy : DenseRange pure_cauchy := fun f => by
  have h_ex : ∀, ∀ s ∈ 𝓤 (Cauchyₓ α), ∀, ∃ y : α, (f, pure_cauchy y) ∈ s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' ∈ f.val ×ᶠ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t ⊆ t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' ∈ f.val ×ᶠ pure x :=
      mem_prod_iff.mpr
        ⟨t, ht, { y : α | (x, y) ∈ t' }, h <| mk_mem_prod hx hx, fun ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩ =>
          ht'₂ <| prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩
    ⟨x,
      ht''₂ <| by
        dsimp [gen] <;> exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pure_cauchy), mem_set_of_eq]
  exact
    (lift'_ne_bot_iff <| monotone_const.inter monotone_preimage).mpr fun s hs =>
      let ⟨y, hy⟩ := h_ex s hs
      have : pure_cauchy y ∈ range pure_cauchy ∩ { y : Cauchyₓ α | (f, y) ∈ s } := ⟨mem_range_self y, hy⟩
      ⟨_, this⟩

theorem dense_inducing_pure_cauchy : DenseInducing pure_cauchy :=
  uniform_inducing_pure_cauchy.DenseInducing dense_range_pure_cauchy

theorem dense_embedding_pure_cauchy : DenseEmbedding pure_cauchy :=
  uniform_embedding_pure_cauchy.DenseEmbedding dense_range_pure_cauchy

theorem nonempty_Cauchy_iff : Nonempty (Cauchyₓ α) ↔ Nonempty α := by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 dense_embedding_pure_cauchy.to_dense_inducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ is_open_univ trivialₓ
    exact ⟨a⟩
    
  · exact ⟨pure_cauchy c⟩
    

section

-- ././Mathport/Syntax/Translate/Basic.lean:210:40: warning: unsupported option eqn_compiler.zeta
set_option eqn_compiler.zeta true

instance : CompleteSpace (Cauchyₓ α) :=
  (complete_space_extension uniform_inducing_pure_cauchy dense_range_pure_cauchy) fun f hf =>
    let f' : Cauchyₓ α := ⟨f, hf⟩
    have : map pure_cauchy f ≤ (𝓤 <| Cauchyₓ α).lift' (Preimage (Prod.mk f')) :=
      le_lift' fun s hs =>
        let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' ⊆ { y : α | (f', pure_cauchy y) ∈ gen t } := fun x hx =>
          (f ×ᶠ pure x).sets_of_superset (prod_mem_prod ht' hx) h
        f.sets_of_superset ht' <| Subset.trans this (preimage_mono ht₂)
    ⟨f', by
      simp [nhds_eq_uniformity] <;> assumption⟩

end

instance [Inhabited α] : Inhabited (Cauchyₓ α) :=
  ⟨pure_cauchy default⟩

instance [h : Nonempty α] : Nonempty (Cauchyₓ α) :=
  h.recOn fun a => Nonempty.intro <| Cauchyₓ.pureCauchy a

section Extend

def extend (f : α → β) : Cauchyₓ α → β :=
  if UniformContinuous f then dense_inducing_pure_cauchy.extend f
  else fun x => f (Classical.inhabitedOfNonempty <| nonempty_Cauchy_iff.1 ⟨x⟩).default

section SeparatedSpace

variable [SeparatedSpace β]

theorem extend_pure_cauchy {f : α → β} (hf : UniformContinuous f) (a : α) : extend f (pure_cauchy a) = f a := by
  rw [extend, if_pos hf]
  exact uniformly_extend_of_ind uniform_inducing_pure_cauchy dense_range_pure_cauchy hf _

end SeparatedSpace

variable [CompleteSpace β]

theorem uniform_continuous_extend {f : α → β} : UniformContinuous (extend f) := by
  by_cases' hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniform_continuous_uniformly_extend uniform_inducing_pure_cauchy dense_range_pure_cauchy hf
    
  · rw [extend, if_neg hf]
    exact
      uniform_continuous_of_const fun a b => by
        congr
    

end Extend

end

theorem Cauchy_eq {α : Type _} [Inhabited α] [UniformSpace α] [CompleteSpace α] [SeparatedSpace α] {f g : Cauchyₓ α} :
    lim f.1 = lim g.1 ↔ (f, g) ∈ SeparationRel (Cauchyₓ α) := by
  constructor
  · intro e s hs
    rcases Cauchyₓ.mem_uniformity'.1 hs with ⟨t, tu, ts⟩
    apply ts
    rcases comp_mem_uniformity_sets tu with ⟨d, du, dt⟩
    refine'
      mem_prod_iff.2
        ⟨_, f.2.le_nhds_Lim (mem_nhds_right (lim f.1) du), _, g.2.le_nhds_Lim (mem_nhds_left (lim g.1) du), fun x h =>
          _⟩
    cases' x with a b
    cases' h with h₁ h₂
    rw [← e] at h₂
    exact dt ⟨_, h₁, h₂⟩
    
  · intro H
    refine'
      separated_def.1
        (by
          infer_instance)
        _ _ fun t tu => _
    rcases mem_uniformity_is_closed tu with ⟨d, du, dc, dt⟩
    refine' H { p | (lim p.1.1, lim p.2.1) ∈ t } (Cauchyₓ.mem_uniformity'.2 ⟨d, du, fun f g h => _⟩)
    rcases mem_prod_iff.1 h with ⟨x, xf, y, yg, h⟩
    have limc : ∀ f : Cauchyₓ α, ∀ x ∈ f.1, ∀, lim f.1 ∈ Closure x := by
      intro f x xf
      rw [closure_eq_cluster_pts]
      exact f.2.1.mono (le_inf f.2.le_nhds_Lim (le_principal_iff.2 xf))
    have := dc.closure_subset_iff.2 h
    rw [closure_prod_eq] at this
    refine' dt (this ⟨_, _⟩) <;> dsimp <;> apply limc <;> assumption
    

section

attribute [local instance] UniformSpace.separationSetoid

theorem separated_pure_cauchy_injective {α : Type _} [UniformSpace α] [s : SeparatedSpace α] :
    Function.Injective fun a : α => ⟦pureCauchy a⟧
  | a, b, h =>
    (separated_def.1 s _ _) fun s hs =>
      let ⟨t, ht, hts⟩ := by
        rw [← (@uniform_embedding_pure_cauchy α _).comap_uniformity, Filter.mem_comap] at hs <;> exact hs
      have : (pureCauchy a, pureCauchy b) ∈ t := Quotientₓ.exact h t ht
      @hts (a, b) this

end

end Cauchyₓ

attribute [local instance] UniformSpace.separationSetoid

open Cauchyₓ Set

namespace UniformSpace

variable (α : Type _) [UniformSpace α]

variable {β : Type _} [UniformSpace β]

variable {γ : Type _} [UniformSpace γ]

instance complete_space_separation [h : CompleteSpace α] : CompleteSpace (Quotientₓ (separationSetoid α)) :=
  ⟨fun f => fun hf : Cauchy f =>
    have : Cauchy (f.comap fun x => ⟦x⟧) :=
      hf.comap' comap_quotient_le_uniformity <| hf.left.comap_of_surj (surjective_quotient_mk _)
    let ⟨x, (hx : (f fun x => ⟦x⟧) ≤ 𝓝 x)⟩ := CompleteSpace.complete this
    ⟨⟦x⟧,
      (comap_le_comap_iff <| by
            simp ).1
        (hx.trans <| map_le_iff_le_comap.1 continuous_quotient_mk.ContinuousAt)⟩⟩

/-- Hausdorff completion of `α` -/
def Completion :=
  Quotientₓ (separation_setoid <| Cauchyₓ α)

namespace Completion

instance [Inhabited α] : Inhabited (Completion α) :=
  Quotientₓ.inhabited (separationSetoid (Cauchyₓ α))

instance (priority := 50) : UniformSpace (Completion α) :=
  separation_setoid.uniform_space

instance : CompleteSpace (Completion α) :=
  UniformSpace.complete_space_separation (Cauchyₓ α)

instance : SeparatedSpace (Completion α) :=
  UniformSpace.separated_separation

instance : RegularSpace (Completion α) :=
  separated_regular

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : CoeTₓ α (Completion α) :=
  ⟨Quotientₓ.mk ∘ pure_cauchy⟩

-- note [use has_coe_t]
protected theorem coe_eq : (coe : α → Completion α) = Quotientₓ.mk ∘ pure_cauchy :=
  rfl

theorem comap_coe_eq_uniformity : ((𝓤 _).comap fun p : α × α => ((p.1 : Completion α), (p.2 : Completion α))) = 𝓤 α :=
  by
  have :
    (fun x : α × α => ((x.1 : completion α), (x.2 : completion α))) =
      (fun x : Cauchyₓ α × Cauchyₓ α => (⟦x.1⟧, ⟦x.2⟧)) ∘ fun x : α × α => (pure_cauchy x.1, pure_cauchy x.2) :=
    by
    ext ⟨a, b⟩ <;> simp <;> rfl
  rw [this, ← Filter.comap_comap]
  change Filter.comap _ (Filter.comap _ (𝓤 <| Quotientₓ <| separation_setoid <| Cauchyₓ α)) = 𝓤 α
  rw [comap_quotient_eq_uniformity, uniform_embedding_pure_cauchy.comap_uniformity]

theorem uniform_inducing_coe : UniformInducing (coe : α → Completion α) :=
  ⟨comap_coe_eq_uniformity α⟩

variable {α}

theorem dense_range_coe : DenseRange (coe : α → Completion α) :=
  dense_range_pure_cauchy.Quotient

variable (α)

def cpkg {α : Type _} [UniformSpace α] : AbstractCompletion α where
  Space := Completion α
  coe := coe
  uniformStruct := by
    infer_instance
  complete := by
    infer_instance
  separation := by
    infer_instance
  UniformInducing := Completion.uniform_inducing_coe α
  dense := Completion.dense_range_coe

instance AbstractCompletion.inhabited : Inhabited (AbstractCompletion α) :=
  ⟨cpkg⟩

attribute [local instance] AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

theorem nonempty_completion_iff : Nonempty (Completion α) ↔ Nonempty α :=
  cpkg.dense.nonempty_iff.symm

theorem uniform_continuous_coe : UniformContinuous (coe : α → Completion α) :=
  cpkg.uniform_continuous_coe

theorem continuous_coe : Continuous (coe : α → Completion α) :=
  cpkg.continuous_coe

theorem uniform_embedding_coe [SeparatedSpace α] : UniformEmbedding (coe : α → Completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α, inj := separated_pure_cauchy_injective }

theorem coe_injective [SeparatedSpace α] : Function.Injective (coe : α → Completion α) :=
  UniformEmbedding.inj (uniform_embedding_coe _)

variable {α}

theorem dense_inducing_coe : DenseInducing (coe : α → Completion α) :=
  { (uniform_inducing_coe α).Inducing with dense := dense_range_coe }

open TopologicalSpace

instance separable_space_completion [SeparableSpace α] : SeparableSpace (Completion α) :=
  Completion.dense_inducing_coe.SeparableSpace

theorem dense_embedding_coe [SeparatedSpace α] : DenseEmbedding (coe : α → Completion α) :=
  { dense_inducing_coe with inj := separated_pure_cauchy_injective }

theorem dense_range_coe₂ : DenseRange fun x : α × β => ((x.1 : Completion α), (x.2 : Completion β)) :=
  dense_range_coe.prod_map dense_range_coe

theorem dense_range_coe₃ :
    DenseRange fun x : α × β × γ => ((x.1 : Completion α), ((x.2.1 : Completion β), (x.2.2 : Completion γ))) :=
  dense_range_coe.prod_map dense_range_coe₂

@[elab_as_eliminator]
theorem induction_on {p : Completion α → Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : ∀ a : α, p a) :
    p a :=
  is_closed_property dense_range_coe hp ih a

@[elab_as_eliminator]
theorem induction_on₂ {p : Completion α → Completion β → Prop} (a : Completion α) (b : Completion β)
    (hp : IsClosed { x : Completion α × Completion β | p x.1 x.2 }) (ih : ∀ a : α b : β, p a b) : p a b :=
  have : ∀ x : Completion α × Completion β, p x.1 x.2 := (is_closed_property dense_range_coe₂ hp) fun ⟨a, b⟩ => ih a b
  this (a, b)

@[elab_as_eliminator]
theorem induction_on₃ {p : Completion α → Completion β → Completion γ → Prop} (a : Completion α) (b : Completion β)
    (c : Completion γ) (hp : IsClosed { x : Completion α × Completion β × Completion γ | p x.1 x.2.1 x.2.2 })
    (ih : ∀ a : α b : β c : γ, p a b c) : p a b c :=
  have : ∀ x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    (is_closed_property dense_range_coe₃ hp) fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)

theorem ext {Y : Type _} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a : α, f a = g a) : f = g :=
  cpkg.funext hf hg h

theorem ext' {Y : Type _} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a : α, f a = g a) (a : Completion α) : f a = g a :=
  congr_funₓ (ext hf hg h) a

section Extension

variable {f : α → β}

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : Completion α → β :=
  cpkg.extend f

section CompleteSpace

variable [CompleteSpace β]

theorem uniform_continuous_extension : UniformContinuous (Completion.extension f) :=
  cpkg.uniform_continuous_extend

theorem continuous_extension : Continuous (Completion.extension f) :=
  cpkg.continuous_extend

end CompleteSpace

@[simp]
theorem extension_coe [SeparatedSpace β] (hf : UniformContinuous f) (a : α) : (Completion.extension f) a = f a :=
  cpkg.extend_coe hf a

variable [SeparatedSpace β] [CompleteSpace β]

theorem extension_unique (hf : UniformContinuous f) {g : Completion α → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g (a : Completion α)) : Completion.extension f = g :=
  cpkg.extend_unique hf hg h

@[simp]
theorem extension_comp_coe {f : Completion α → β} (hf : UniformContinuous f) : Completion.extension (f ∘ coe) = f :=
  cpkg.extend_comp_coe hf

end Extension

section Map

variable {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : Completion α → Completion β :=
  cpkg.map cpkg f

theorem uniform_continuous_map : UniformContinuous (Completion.map f) :=
  cpkg.uniform_continuous_map cpkg f

theorem continuous_map : Continuous (Completion.map f) :=
  cpkg.continuous_map cpkg f

@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : (Completion.map f) a = f a :=
  cpkg.map_coe cpkg hf a

theorem map_unique {f : α → β} {g : Completion α → Completion β} (hg : UniformContinuous g)
    (h : ∀ a : α, ↑(f a) = g a) : Completion.map f = g :=
  cpkg.map_unique cpkg hg h

@[simp]
theorem map_id : Completion.map (@id α) = id :=
  cpkg.map_id

theorem extension_map [CompleteSpace γ] [SeparatedSpace γ] {f : β → γ} {g : α → β} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : Completion.extension f ∘ Completion.map g = Completion.extension (f ∘ g) :=
  Completion.ext (continuous_extension.comp continuous_map) continuous_extension <| by
    intro a <;> simp only [hg, hf, hf.comp hg, (· ∘ ·), map_coe, extension_coe]

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    Completion.map g ∘ Completion.map f = Completion.map (g ∘ f) :=
  extension_map ((uniform_continuous_coe _).comp hg) hf

end Map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section SeparationQuotientCompletion

def completionSeparationQuotientEquiv (α : Type u) [UniformSpace α] :
    Completion (SeparationQuotient α) ≃ Completion α := by
  refine' ⟨completion.extension (separation_quotient.lift (coe : α → completion α)), completion.map Quotientₓ.mk, _, _⟩
  · intro a
    refine' induction_on a (is_closed_eq (continuous_map.comp continuous_extension) continuous_id) _
    rintro ⟨a⟩
    show completion.map Quotientₓ.mk (completion.extension (separation_quotient.lift coe) ↑(⟦a⟧)) = ↑(⟦a⟧)
    rw [extension_coe (separation_quotient.uniform_continuous_lift _),
        separation_quotient.lift_mk (uniform_continuous_coe α), completion.map_coe uniform_continuous_quotient_mk] <;>
      infer_instance
    
  · intro a
    refine' completion.induction_on a (is_closed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => _
    rw [map_coe uniform_continuous_quotient_mk, extension_coe (separation_quotient.uniform_continuous_lift _),
        separation_quotient.lift_mk (uniform_continuous_coe α) _] <;>
      infer_instance
    

theorem uniform_continuous_completion_separation_quotient_equiv :
    UniformContinuous ⇑(completionSeparationQuotientEquiv α) :=
  uniform_continuous_extension

theorem uniform_continuous_completion_separation_quotient_equiv_symm :
    UniformContinuous ⇑(completionSeparationQuotientEquiv α).symm :=
  uniform_continuous_map

end SeparationQuotientCompletion

section Extension₂

variable (f : α → β → γ)

open Function

protected def extension₂ (f : α → β → γ) : Completion α → Completion β → γ :=
  cpkg.extend₂ cpkg f

section SeparatedSpace

variable [SeparatedSpace γ] {f}

@[simp]
theorem extension₂_coe_coe (hf : UniformContinuous₂ f) (a : α) (b : β) : Completion.extension₂ f a b = f a b :=
  cpkg.extension₂_coe_coe cpkg hf a b

end SeparatedSpace

variable [CompleteSpace γ] (f)

theorem uniform_continuous_extension₂ : UniformContinuous₂ (Completion.extension₂ f) :=
  cpkg.uniform_continuous_extension₂ cpkg f

end Extension₂

section Map₂

open Function

protected def map₂ (f : α → β → γ) : Completion α → Completion β → Completion γ :=
  cpkg.map₂ cpkg cpkg f

theorem uniform_continuous_map₂ (f : α → β → γ) : UniformContinuous₂ (Completion.map₂ f) :=
  cpkg.uniform_continuous_map₂ cpkg cpkg f

theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → Completion α} {b : δ → Completion β}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun d : δ => Completion.map₂ f (a d) (b d) :=
  cpkg.continuous_map₂ cpkg cpkg ha hb

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    Completion.map₂ f (a : Completion α) (b : Completion β) = f a b :=
  cpkg.map₂_coe_coe cpkg cpkg a b f hf

end Map₂

end Completion

end UniformSpace

