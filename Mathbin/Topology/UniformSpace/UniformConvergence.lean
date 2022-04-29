/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `at_top`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α`to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `tendsto_uniformly_on F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `tendsto_uniformly F f p`: same notion with `s = univ`.
* `tendsto_uniformly_on.continuous_on`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `tendsto_uniformly.continuous`: a uniform limit of continuous functions is continuous.
* `tendsto_uniformly_on.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `tendsto_uniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

We also define notions where the convergence is locally uniform, called
`tendsto_locally_uniformly_on F f p s` and `tendsto_locally_uniformly F f p`. The previous theorems
all have corresponding versions under locally uniform convergence.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
 -/


noncomputable section

open TopologicalSpace Classical uniformity Filter

open Set Filter

universe u v w

variable {α β γ ι : Type _} [UniformSpace β]

variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {g : ι → α}

/-!
### Different notions of uniform convergence

We define uniform convergence and locally uniform convergence, on a set or in the whole space.
-/


/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
def TendstoUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀, ∀ u ∈ 𝓤 β, ∀, ∀ᶠ n in p, ∀, ∀ x ∈ s, ∀, (f x, F n x) ∈ u

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ 𝓟 s` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `s`.
-/
theorem tendsto_uniformly_on_iff_tendsto {F : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α} :
    TendstoUniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ᶠ 𝓟 s) (𝓤 β) :=
  forall₂_congrₓ fun u u_in => by
    simp [mem_map, Filter.Eventually, mem_prod_principal]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
def TendstoUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀, ∀ u ∈ 𝓤 β, ∀, ∀ᶠ n in p, ∀ x, (f x, F n x) ∈ u

theorem tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe :
    TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun x : s => F i x) (f ∘ coe) p :=
  forall₂_congrₓ fun V hV => by
    simp

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ ⊤` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
theorem tendsto_uniformly_iff_tendsto {F : ι → α → β} {f : α → β} {p : Filter ι} :
    TendstoUniformly F f p ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ᶠ ⊤) (𝓤 β) :=
  forall₂_congrₓ fun u u_in => by
    simp [mem_map, Filter.Eventually, mem_prod_top]

/-- Uniform converence implies pointwise convergence. -/
theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) : Tendsto (fun n => F n x) p <| 𝓝 (f x) :=
  Uniform.tendsto_nhds_right.mpr fun u hu =>
    mem_map.mpr <| by
      filter_upwards [h u hu]
      tauto

theorem tendsto_uniformly_on_univ : TendstoUniformlyOn F f p Univ ↔ TendstoUniformly F f p := by
  simp [TendstoUniformlyOn, TendstoUniformly]

theorem TendstoUniformlyOn.mono {s' : Set α} (h : TendstoUniformlyOn F f p s) (h' : s' ⊆ s) :
    TendstoUniformlyOn F f p s' := fun u hu => (h u hu).mono fun n hn x hx => hn x (h' hx)

protected theorem TendstoUniformly.tendsto_uniformly_on (h : TendstoUniformly F f p) : TendstoUniformlyOn F f p s :=
  (tendsto_uniformly_on_univ.2 h).mono (subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a set -/
theorem TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ → α) :
    TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' s) := fun u hu => (h u hu).mono fun i hi => fun a => hi (g a)

/-- Composing on the right by a function preserves uniform convergence -/
theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ → α) :
    TendstoUniformly (fun n => F n ∘ g) (f ∘ g) p := fun u hu => (h u hu).mono fun i hi => fun a => hi (g a)

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set -/
theorem TendstoUniformlyOn.comp' [UniformSpace γ] {g : β → γ} (h : TendstoUniformlyOn F f p s)
    (hg : UniformContinuous g) : TendstoUniformlyOn (fun i => g ∘ F i) (g ∘ f) p s := fun u hu => h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves uniform convergence -/
theorem TendstoUniformly.comp' [UniformSpace γ] {g : β → γ} (h : TendstoUniformly F f p) (hg : UniformContinuous g) :
    TendstoUniformly (fun i => g ∘ F i) (g ∘ f) p := fun u hu => h _ (hg hu)

theorem TendstoUniformlyOn.prod_map {ι' α' β' : Type _} [UniformSpace β'] {F' : ι' → α' → β'} {f' : α' → β'}
    {p' : Filter ι'} {s' : Set α'} (h : TendstoUniformlyOn F f p s) (h' : TendstoUniformlyOn F' f' p' s') :
    TendstoUniformlyOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p.Prod p') (s ×ˢ s') := by
  intro u hu
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  exact
    mem_prod_iff.mpr
      ⟨_, h v hv, _, h' w hw, fun i hi a ha => hvw (show (_, _) ∈ v ×ˢ w from ⟨hi.1 a.1 ha.1, hi.2 a.2 ha.2⟩)⟩

theorem TendstoUniformly.prod_map {ι' α' β' : Type _} [UniformSpace β'] {F' : ι' → α' → β'} {f' : α' → β'}
    {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p.Prod p') := by
  rw [← tendsto_uniformly_on_univ, ← univ_prod_univ] at *
  exact h.prod_map h'

theorem TendstoUniformlyOn.prod {ι' β' : Type _} [UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'} {p' : Filter ι'}
    (h : TendstoUniformlyOn F f p s) (h' : TendstoUniformlyOn F' f' p' s) :
    TendstoUniformlyOn (fun a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p.Prod p') s :=
  (congr_argₓ _ s.inter_self).mp ((h.prod_map h').comp fun a => (a, a))

theorem TendstoUniformly.prod {ι' β' : Type _} [UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'} {p' : Filter ι'}
    (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p.Prod p') :=
  (h.prod_map h').comp fun a => (a, a)

/-- Uniform convergence to a constant function is equivalent to convergence in `p ×ᶠ ⊤`. -/
theorem tendsto_prod_top_iff {c : β} : Tendsto (↿F) (p ×ᶠ ⊤) (𝓝 c) ↔ TendstoUniformly F (fun _ => c) p :=
  let j : β → β × β := Prod.mk c
  calc
    Tendsto (↿F) (p ×ᶠ ⊤) (𝓝 c) ↔ map (↿F) (p ×ᶠ ⊤) ≤ 𝓝 c := Iff.rfl
    _ ↔ map (↿F) (p ×ᶠ ⊤) ≤ comap j (𝓤 β) := by
      rw [nhds_eq_comap_uniformity]
    _ ↔ map j (map (↿F) (p ×ᶠ ⊤)) ≤ 𝓤 β := map_le_iff_le_comap.symm
    _ ↔ map (j ∘ ↿F) (p ×ᶠ ⊤) ≤ 𝓤 β := by
      rw [map_map]
    _ ↔ ∀, ∀ V ∈ 𝓤 β, ∀, { x | (c, (↿F) x) ∈ V } ∈ p ×ᶠ (⊤ : Filter α) := Iff.rfl
    _ ↔ ∀, ∀ V ∈ 𝓤 β, ∀, { i | ∀ a, (c, F i a) ∈ V } ∈ p := by
      simpa [mem_prod_top]
    

theorem UniformContinuousOn.tendsto_uniformly [UniformSpace α] [UniformSpace γ] {x : α} {U : Set α} (hU : U ∈ 𝓝 x)
    {F : α → β → γ} (hF : UniformContinuousOn (↿F) (U ×ˢ (Univ : Set β))) : TendstoUniformly F (F x) (𝓝 x) := by
  let φ := fun q : α × β => ((x, q.2), q)
  rw [tendsto_uniformly_iff_tendsto,
    show (fun q : α × β => (F x q.2, F q.1 q.2)) = Prod.map (↿F) ↿F ∘ φ by
      ext <;> simpa]
  apply hF.comp (tendsto_inf.mpr ⟨_, _⟩)
  · rw [uniformity_prod, tendsto_inf, tendsto_comap_iff, tendsto_comap_iff,
      show (fun p : (α × β) × α × β => (p.1.1, p.2.1)) ∘ φ = (fun a => (x, a)) ∘ Prod.fst by
        ext
        simp ,
      show (fun p : (α × β) × α × β => (p.1.2, p.2.2)) ∘ φ = (fun b => (b, b)) ∘ Prod.snd by
        ext
        simp ]
    exact ⟨tendsto_left_nhds_uniformity.comp tendsto_fst, (tendsto_diag_uniformity id ⊤).comp tendsto_top⟩
    
  · rw [tendsto_principal]
    apply mem_of_superset (prod_mem_prod hU (mem_top.mpr rfl)) fun q h => _
    simp [h.1, mem_of_mem_nhds hU]
    

theorem UniformContinuous₂.tendsto_uniformly [UniformSpace α] [UniformSpace γ] {f : α → β → γ}
    (h : UniformContinuous₂ f) {x : α} : TendstoUniformly f (f x) (𝓝 x) :=
  UniformContinuousOn.tendsto_uniformly univ_mem <| by
    rwa [univ_prod_univ, uniform_continuous_on_univ]

section SeqTendsto

theorem tendsto_uniformly_on_of_seq_tendsto_uniformly_on {l : Filter ι} [l.IsCountablyGenerated]
    (h : ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s) :
    TendstoUniformlyOn F f l s := by
  rw [tendsto_uniformly_on_iff_tendsto, tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendsto_uniformly_on_iff_tendsto] at h
  have :
    (fun q : ι × α => (f q.snd, F q.fst q.snd)) ∘ u =
      (fun q : ℕ × α => (f q.snd, F ((fun n : ℕ => (u n).fst) q.fst) q.snd)) ∘ fun n => (n, (u n).snd) :=
    by
    ext1 n
    simp
  rw [this]
  refine' tendsto.comp h _
  rw [tendsto_prod_iff']
  exact ⟨tendsto_id, hu.2⟩

theorem TendstoUniformlyOn.seq_tendsto_uniformly_on {l : Filter ι} (h : TendstoUniformlyOn F f l s) (u : ℕ → ι)
    (hu : Tendsto u atTop l) : TendstoUniformlyOn (fun n => F (u n)) f atTop s := by
  rw [tendsto_uniformly_on_iff_tendsto] at h⊢
  have :
    (fun q : ℕ × α => (f q.snd, F (u q.fst) q.snd)) =
      (fun q : ι × α => (f q.snd, F q.fst q.snd)) ∘ fun p : ℕ × α => (u p.fst, p.snd) :=
    by
    ext1 x
    simp
  rw [this]
  refine' h.comp _
  rw [tendsto_prod_iff']
  exact ⟨hu.comp tendsto_fst, tendsto_snd⟩

theorem tendsto_uniformly_on_iff_seq_tendsto_uniformly_on {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformlyOn F f l s ↔ ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s :=
  ⟨TendstoUniformlyOn.seq_tendsto_uniformly_on, tendsto_uniformly_on_of_seq_tendsto_uniformly_on⟩

theorem tendsto_uniformly_iff_seq_tendsto_uniformly {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformly F f l ↔ ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformly (fun n => F (u n)) f atTop := by
  simp_rw [← tendsto_uniformly_on_univ]
  exact tendsto_uniformly_on_iff_seq_tendsto_uniformly_on

end SeqTendsto

variable [TopologicalSpace α]

/-- A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limiting function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for any `x ∈ s`, one
has `p`-eventually `(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x` in `s`. -/
def TendstoLocallyUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀, ∀ u ∈ 𝓤 β, ∀, ∀, ∀ x ∈ s, ∀, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, (f y, F n y) ∈ u

/-- A sequence of functions `Fₙ` converges locally uniformly to a limiting function `f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has `p`-eventually
`(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x`. -/
def TendstoLocallyUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀, ∀ u ∈ 𝓤 β, ∀, ∀ x : α, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, (f y, F n y) ∈ u

theorem tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe :
    TendstoLocallyUniformlyOn F f p s ↔ TendstoLocallyUniformly (fun x : s => F i x) (f ∘ coe) p := by
  refine' forall₂_congrₓ fun V hV => _
  simp only [exists_prop, Function.comp_app, SetCoe.forall, Subtype.coe_mk]
  refine' forall₂_congrₓ fun x hx => ⟨_, _⟩
  · rintro ⟨t, ht₁, ht₂⟩
    obtain ⟨u, hu₁, hu₂⟩ := mem_nhds_within_iff_exists_mem_nhds_inter.mp ht₁
    exact
      ⟨coe ⁻¹' u, (mem_nhds_subtype _ _ _).mpr ⟨u, hu₁, rfl.subset⟩,
        ht₂.mono fun i hi y hy₁ hy₂ => hi y (hu₂ ⟨hy₂, hy₁⟩)⟩
    
  · rintro ⟨t, ht₁, ht₂⟩
    obtain ⟨u, hu₁, hu₂⟩ := (mem_nhds_subtype _ _ _).mp ht₁
    exact
      ⟨u ∩ s, mem_nhds_within_iff_exists_mem_nhds_inter.mpr ⟨u, hu₁, rfl.subset⟩,
        ht₂.mono fun i hi y hy =>
          hi y hy.2
            (hu₂
              (by
                simp [hy.1]))⟩
    

theorem tendsto_locally_uniformly_iff_forall_tendsto :
    TendstoLocallyUniformly F f p ↔ ∀ x, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ᶠ 𝓝 x) (𝓤 β) := by
  simp only [TendstoLocallyUniformly, Filter.forall_in_swap, tendsto_def, mem_prod_iff, Set.prod_subset_iff]
  refine' forall₃_congrₓ fun x u hu => ⟨_, _⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨_, hp, n, hn, fun i hi a ha => hi a ha⟩
    
  · rintro ⟨I, hI, n, hn, hu⟩
    exact
      ⟨n, hn, by
        filter_upwards [hI] using hu⟩
    

protected theorem TendstoUniformlyOn.tendsto_locally_uniformly_on (h : TendstoUniformlyOn F f p s) :
    TendstoLocallyUniformlyOn F f p s := fun u hu x hx => ⟨s, self_mem_nhds_within, h u hu⟩

protected theorem TendstoUniformly.tendsto_locally_uniformly (h : TendstoUniformly F f p) :
    TendstoLocallyUniformly F f p := fun u hu x =>
  ⟨Univ, univ_mem, by
    simpa using h u hu⟩

theorem TendstoLocallyUniformlyOn.mono (h : TendstoLocallyUniformlyOn F f p s) (h' : s' ⊆ s) :
    TendstoLocallyUniformlyOn F f p s' := by
  intro u hu x hx
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩
  exact ⟨t, nhds_within_mono x h' ht, H.mono fun n => id⟩

theorem tendsto_locally_uniformly_on_univ : TendstoLocallyUniformlyOn F f p Univ ↔ TendstoLocallyUniformly F f p := by
  simp [TendstoLocallyUniformlyOn, TendstoLocallyUniformly, nhds_within_univ]

protected theorem TendstoLocallyUniformly.tendsto_locally_uniformly_on (h : TendstoLocallyUniformly F f p) :
    TendstoLocallyUniformlyOn F f p s :=
  (tendsto_locally_uniformly_on_univ.mpr h).mono (subset_univ _)

/-- On a compact space, locally uniform convergence is just uniform convergence. -/
theorem tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space [CompactSpace α] :
    TendstoLocallyUniformly F f p ↔ TendstoUniformly F f p := by
  refine' ⟨fun h V hV => _, TendstoUniformly.tendsto_locally_uniformly⟩
  choose U hU using h V hV
  obtain ⟨t, ht⟩ := compact_univ.elim_nhds_subcover' (fun k hk => U k) fun k hk => (hU k).1
  replace hU := fun x : t => (hU x).2
  rw [← eventually_all] at hU
  refine' hU.mono fun i hi x => _
  specialize ht (mem_univ x)
  simp only [exists_prop, mem_Union, SetCoe.exists, exists_and_distrib_right, Subtype.coe_mk] at ht
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := ht
  exact hi ⟨⟨y, hy₁⟩, hy₂⟩ x hy₃

/-- For a compact set `s`, locally uniform convergence on `s` is just uniform convergence on `s`. -/
theorem tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact (hs : IsCompact s) :
    TendstoLocallyUniformlyOn F f p s ↔ TendstoUniformlyOn F f p s := by
  have : CompactSpace s := is_compact_iff_compact_space.mp hs
  refine' ⟨fun h => _, TendstoUniformlyOn.tendsto_locally_uniformly_on⟩
  rwa [tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe,
    tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space, ←
    tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe] at h

theorem TendstoLocallyUniformlyOn.comp [TopologicalSpace γ] {t : Set γ} (h : TendstoLocallyUniformlyOn F f p s)
    (g : γ → α) (hg : MapsTo g t s) (cg : ContinuousOn g t) :
    TendstoLocallyUniformlyOn (fun n => F n ∘ g) (f ∘ g) p t := by
  intro u hu x hx
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩
  have : g ⁻¹' a ∈ 𝓝[t] x := (cg x hx).preimage_mem_nhds_within' (nhds_within_mono (g x) hg.image_subset ha)
  exact ⟨g ⁻¹' a, this, H.mono fun n hn y hy => hn _ hy⟩

theorem TendstoLocallyUniformly.comp [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p) (g : γ → α)
    (cg : Continuous g) : TendstoLocallyUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [← tendsto_locally_uniformly_on_univ] at h⊢
  rw [continuous_iff_continuous_on_univ] at cg
  exact h.comp _ (maps_to_univ _ _) cg

/-!
### Uniform approximation

In this section, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`. -/


/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
theorem continuous_within_at_of_locally_uniform_approx_of_continuous_within_at (hx : x ∈ s)
    (L : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝[s] x, ∃ F : α → β, ContinuousWithinAt F s x ∧ ∀, ∀ y ∈ t, ∀, (f y, F y) ∈ u) :
    ContinuousWithinAt f s x := by
  apply Uniform.continuous_within_at_iff'_left.2 fun u₀ hu₀ => _
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : Set (β × β))(H : u ∈ 𝓤 β), CompRel u u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ :
    ∃ (u : Set (β × β))(H : u ∈ 𝓤 β), (∀ {a b}, (a, b) ∈ u → (b, a) ∈ u) ∧ CompRel u u ⊆ u₁ :=
    comp_symm_of_uniformity h₁
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩
  have A : ∀ᶠ y in 𝓝[s] x, (f y, F y) ∈ u₂ := eventually.mono tx hF
  have B : ∀ᶠ y in 𝓝[s] x, (F y, F x) ∈ u₂ := Uniform.continuous_within_at_iff'_left.1 hFc h₂
  have C : ∀ᶠ y in 𝓝[s] x, (f y, F x) ∈ u₁ := (A.and B).mono fun y hy => u₂₁ (prod_mk_mem_comp_rel hy.1 hy.2)
  have : (F x, f x) ∈ u₁ := u₂₁ (prod_mk_mem_comp_rel (refl_mem_uniformity h₂) (hsymm (A.self_of_nhds_within hx)))
  exact C.mono fun y hy => u₁₀ (prod_mk_mem_comp_rel hy this)

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
theorem continuous_at_of_locally_uniform_approx_of_continuous_at
    (L : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀, ∀ y ∈ t, ∀, (f y, F y) ∈ u) : ContinuousAt f x := by
  rw [← continuous_within_at_univ]
  apply continuous_within_at_of_locally_uniform_approx_of_continuous_within_at (mem_univ _) _
  simpa only [exists_prop, nhds_within_univ, continuous_within_at_univ] using L

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
theorem continuous_on_of_locally_uniform_approx_of_continuous_within_at
    (L : ∀, ∀ x ∈ s, ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝[s] x, ∃ F, ContinuousWithinAt F s x ∧ ∀, ∀ y ∈ t, ∀, (f y, F y) ∈ u) :
    ContinuousOn f s := fun x hx => continuous_within_at_of_locally_uniform_approx_of_continuous_within_at hx (L x hx)

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
theorem continuous_on_of_uniform_approx_of_continuous_on
    (L : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ F, ContinuousOn F s ∧ ∀, ∀ y ∈ s, ∀, (f y, F y) ∈ u) : ContinuousOn f s :=
  continuous_on_of_locally_uniform_approx_of_continuous_within_at fun x hx u hu =>
    ⟨s, self_mem_nhds_within, (L u hu).imp fun F hF => ⟨hF.1.ContinuousWithinAt hx, hF.2⟩⟩

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_locally_uniform_approx_of_continuous_at
    (L : ∀ x : α, ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝 x, ∃ F, ContinuousAt F x ∧ ∀, ∀ y ∈ t, ∀, (f y, F y) ∈ u) : Continuous f :=
  continuous_iff_continuous_at.2 fun x => continuous_at_of_locally_uniform_approx_of_continuous_at (L x)

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
theorem continuous_of_uniform_approx_of_continuous (L : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ F, Continuous F ∧ ∀ y, (f y, F y) ∈ u) :
    Continuous f :=
  continuous_iff_continuous_on_univ.mpr <|
    continuous_on_of_uniform_approx_of_continuous_on <| by
      simpa [continuous_iff_continuous_on_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/


/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
protected theorem TendstoLocallyUniformlyOn.continuous_on (h : TendstoLocallyUniformlyOn F f p s)
    (hc : ∀ᶠ n in p, ContinuousOn (F n) s) [NeBot p] : ContinuousOn f s := by
  apply continuous_on_of_locally_uniform_approx_of_continuous_within_at fun x hx u hu => _
  rcases h u hu x hx with ⟨t, ht, H⟩
  rcases(hc.and H).exists with ⟨n, hFc, hF⟩
  exact ⟨t, ht, ⟨F n, hFc.continuous_within_at hx, hF⟩⟩

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
protected theorem TendstoUniformlyOn.continuous_on (h : TendstoUniformlyOn F f p s)
    (hc : ∀ᶠ n in p, ContinuousOn (F n) s) [NeBot p] : ContinuousOn f s :=
  h.TendstoLocallyUniformlyOn.ContinuousOn hc

/-- A locally uniform limit of continuous functions is continuous. -/
protected theorem TendstoLocallyUniformly.continuous (h : TendstoLocallyUniformly F f p)
    (hc : ∀ᶠ n in p, Continuous (F n)) [NeBot p] : Continuous f :=
  continuous_iff_continuous_on_univ.mpr <|
    h.TendstoLocallyUniformlyOn.ContinuousOn <| hc.mono fun n hn => hn.ContinuousOn

/-- A uniform limit of continuous functions is continuous. -/
protected theorem TendstoUniformly.continuous (h : TendstoUniformly F f p) (hc : ∀ᶠ n in p, Continuous (F n))
    [NeBot p] : Continuous f :=
  h.TendstoLocallyUniformly.Continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/


/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s `, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit_within (h : ContinuousWithinAt f s x) (hg : Tendsto g p (𝓝[s] x))
    (hunif : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  apply Uniform.tendsto_nhds_right.2 fun u₀ hu₀ => _
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : Set (β × β))(H : u ∈ 𝓤 β), CompRel u u ⊆ u₀ := comp_mem_uniformity_sets hu₀
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩
  have A : ∀ᶠ n in p, g n ∈ s := hg sx
  have B : ∀ᶠ n in p, (f x, f (g n)) ∈ u₁ := hg (Uniform.continuous_within_at_iff'_right.1 h h₁)
  refine' ((hs.and A).And B).mono fun y hy => _
  rcases hy with ⟨⟨H1, H2⟩, H3⟩
  exact u₁₀ (prod_mk_mem_comp_rel H3 (H1 _ H2))

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
theorem tendsto_comp_of_locally_uniform_limit (h : ContinuousAt f x) (hg : Tendsto g p (𝓝 x))
    (hunif : ∀, ∀ u ∈ 𝓤 β, ∀, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀, ∀ y ∈ t, ∀, (f y, F n y) ∈ u) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) := by
  rw [← continuous_within_at_univ] at h
  rw [← nhds_within_univ] at hunif hg
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
theorem TendstoLocallyUniformlyOn.tendsto_comp (h : TendstoLocallyUniformlyOn F f p s) (hf : ContinuousWithinAt f s x)
    (hx : x ∈ s) (hg : Tendsto g p (𝓝[s] x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => h u hu x hx

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`. -/
theorem TendstoUniformlyOn.tendsto_comp (h : TendstoUniformlyOn F f p s) (hf : ContinuousWithinAt f s x)
    (hg : Tendsto g p (𝓝[s] x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit_within hf hg fun u hu => ⟨s, self_mem_nhds_within, h u hu⟩

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem TendstoLocallyUniformly.tendsto_comp (h : TendstoLocallyUniformly F f p) (hf : ContinuousAt f x)
    (hg : Tendsto g p (𝓝 x)) : Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  tendsto_comp_of_locally_uniform_limit hf hg fun u hu => h u hu x

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
theorem TendstoUniformly.tendsto_comp (h : TendstoUniformly F f p) (hf : ContinuousAt f x) (hg : Tendsto g p (𝓝 x)) :
    Tendsto (fun n => F n (g n)) p (𝓝 (f x)) :=
  h.TendstoLocallyUniformly.tendsto_comp hf hg

