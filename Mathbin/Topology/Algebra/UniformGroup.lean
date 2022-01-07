import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.CompleteSeparated
import Mathbin.Topology.Algebra.Group
import Mathbin.Tactic.Abel

/-!
# Uniform structure on topological groups

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)
-/


noncomputable section

open_locale Classical uniformity TopologicalSpace Filter

section UniformAddGroup

open Filter Set

variable {α : Type _} {β : Type _}

/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class UniformAddGroup (α : Type _) [UniformSpace α] [AddGroupₓ α] : Prop where
  uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

theorem UniformAddGroup.mk' {α} [UniformSpace α] [AddGroupₓ α] (h₁ : UniformContinuous fun p : α × α => p.1 + p.2)
    (h₂ : UniformContinuous fun p : α => -p) : UniformAddGroup α :=
  ⟨by
    simpa only [sub_eq_add_neg] using h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩

variable [UniformSpace α] [AddGroupₓ α] [UniformAddGroup α]

theorem uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2 :=
  UniformAddGroup.uniform_continuous_sub

theorem UniformContinuous.sub [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x - g x :=
  uniform_continuous_sub.comp (hf.prod_mk hg)

theorem UniformContinuous.neg [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => -f x := by
  have : UniformContinuous fun x => 0 - f x := uniform_continuous_const.sub hf
  simp_all

theorem uniform_continuous_neg : UniformContinuous fun x : α => -x :=
  uniform_continuous_id.neg

theorem UniformContinuous.add [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x + g x := by
  have : UniformContinuous fun x => f x - -g x := hf.sub hg.neg
  simp_all [sub_eq_add_neg]

theorem uniform_continuous_add : UniformContinuous fun p : α × α => p.1 + p.2 :=
  uniform_continuous_fst.add uniform_continuous_snd

instance (priority := 10) UniformAddGroup.to_topological_add_group : TopologicalAddGroup α where
  continuous_add := uniform_continuous_add.Continuous
  continuous_neg := uniform_continuous_neg.Continuous

instance [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β] : UniformAddGroup (α × β) :=
  ⟨((uniform_continuous_fst.comp uniform_continuous_fst).sub
          (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).sub (uniform_continuous_snd.comp uniform_continuous_snd))⟩

theorem uniformity_translate (a : α) : ((𝓤 α).map fun x : α × α => (x.1 + a, x.2 + a)) = 𝓤 α :=
  le_antisymmₓ (uniform_continuous_id.add uniform_continuous_const)
    (calc
      𝓤 α = ((𝓤 α).map fun x : α × α => (x.1 + -a, x.2 + -a)).map fun x : α × α => (x.1 + a, x.2 + a) := by
        simp [Filter.map_map, · ∘ ·] <;> exact filter.map_id.symm
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 + a, x.2 + a) :=
        Filter.map_mono (uniform_continuous_id.add uniform_continuous_const)
      )

-- ././Mathport/Syntax/Translate/Tactic/Lean3.lean:98:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ , ]»([1]) }
theorem uniform_embedding_translate (a : α) : UniformEmbedding fun x : α => x + a :=
  { comap_uniformity := by
      rw [← uniformity_translate a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp (config := { contextual := true })[Prod.eq_iff_fst_eq_snd_eq],
    inj := add_left_injective a }

section

variable (α)

theorem uniformity_eq_comap_nhds_zero : 𝓤 α = comap (fun x : α × α => x.2 - x.1) (𝓝 (0 : α)) := by
  rw [nhds_eq_comap_uniformity, Filter.comap_comap]
  refine' le_antisymmₓ (Filter.map_le_iff_le_comap.1 _) _
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_sub hs with ⟨t, ht, hts⟩
    refine' mem_map.2 (mem_of_superset ht _)
    rintro ⟨a, b⟩
    simpa [subset_def] using hts a b a
    
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_add hs with ⟨t, ht, hts⟩
    refine' ⟨_, ht, _⟩
    rintro ⟨a, b⟩
    simpa [subset_def] using hts 0 (b - a) a
    

end

theorem group_separation_rel (x y : α) : (x, y) ∈ SeparationRel α ↔ x - y ∈ Closure ({0} : Set α) :=
  have : Embedding fun a => a + (y - x) := (uniform_embedding_translate (y - x)).Embedding
  show (x, y) ∈ ⋂₀(𝓤 α).Sets ↔ x - y ∈ Closure ({0} : Set α) by
    rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_zero α, sInter_comap_sets]
    simp [mem_closure_iff_nhds, inter_singleton_nonempty, sub_eq_add_neg, add_assocₓ]

theorem uniform_continuous_of_tendsto_zero [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β] {f : α →+ β}
    (h : tendsto f (𝓝 0) (𝓝 0)) : UniformContinuous f := by
  have : ((fun x : β × β => x.2 - x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α => f (x.2 - x.1) := by
    simp only [f.map_sub]
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero α, uniformity_eq_comap_nhds_zero β, tendsto_comap_iff, this]
  exact tendsto.comp h tendsto_comap

theorem AddMonoidHom.uniform_continuous_of_continuous_at_zero [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β]
    (f : α →+ β) (hf : ContinuousAt f 0) : UniformContinuous f :=
  uniform_continuous_of_tendsto_zero
    (by
      simpa using hf.tendsto)

theorem uniform_continuous_of_continuous [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β] {f : α →+ β}
    (h : Continuous f) : UniformContinuous f :=
  uniform_continuous_of_tendsto_zero $
    suffices tendsto f (𝓝 0) (𝓝 (f 0)) by
      rwa [f.map_zero] at this
    h.tendsto 0

theorem CauchySeq.add {ι : Type _} [SemilatticeSup ι] {u v : ι → α} (hu : CauchySeq u) (hv : CauchySeq v) :
    CauchySeq (u + v) :=
  uniform_continuous_add.comp_cauchy_seq (hu.prod hv)

end UniformAddGroup

section TopologicalAddCommGroup

universe u v w x

open Filter

variable {G : Type u} [AddCommGroupₓ G] [TopologicalSpace G] [TopologicalAddGroup G]

variable (G)

/-- The right uniformity on a topological group. -/
def TopologicalAddGroup.toUniformSpace : UniformSpace G where
  uniformity := comap (fun p : G × G => p.2 - p.1) (𝓝 0)
  refl := by
    refine' map_le_iff_le_comap.1 (le_transₓ _ (pure_le_nhds 0)) <;>
      simp (config := { contextual := true })[Set.subset_def]
  symm := by
    suffices tendsto ((fun p => -p) ∘ fun p : G × G => p.2 - p.1) (comap (fun p : G × G => p.2 - p.1) (𝓝 0)) (𝓝 (-0)) by
      simpa [· ∘ ·, tendsto_comap_iff]
    exact tendsto.comp (tendsto.neg tendsto_id) tendsto_comap
  comp := by
    intro D H
    rw [mem_lift'_sets]
    · rcases H with ⟨U, U_nhds, U_sub⟩
      rcases exists_nhds_zero_half U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩
      exists (fun p : G × G => p.2 - p.1) ⁻¹' V
      have H : (fun p : G × G => p.2 - p.1) ⁻¹' V ∈ comap (fun p : G × G => p.2 - p.1) (𝓝 (0 : G)) := by
        exists V, V_nhds <;> rfl
      exists H
      have comp_rel_sub :
        CompRel ((fun p : G × G => p.2 - p.1) ⁻¹' V) ((fun p => p.2 - p.1) ⁻¹' V) ⊆
          (fun p : G × G => p.2 - p.1) ⁻¹' U :=
        by
        intro p p_comp_rel
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩
        simpa [sub_eq_add_neg, add_commₓ, add_left_commₓ] using V_sum _ Hz1 _ Hz2
      exact Set.Subset.trans comp_rel_sub U_sub
      
    · exact monotone_comp_rel monotone_id monotone_id
      
  is_open_uniformity := by
    intro S
    let S' := fun x => { p : G × G | p.1 = x → p.2 ∈ S }
    show IsOpen S ↔ ∀ x : G, x ∈ S → S' x ∈ comap (fun p : G × G => p.2 - p.1) (𝓝 (0 : G))
    rw [is_open_iff_mem_nhds]
    refine' forall_congrₓ fun a => forall_congrₓ fun ha => _
    rw [← nhds_translation_sub, mem_comap, mem_comap]
    refine' exists_congr fun t => exists_congr fun ht => _
    show (fun y : G => y - a) ⁻¹' t ⊆ S ↔ (fun p : G × G => p.snd - p.fst) ⁻¹' t ⊆ S' a
    constructor
    · rintro h ⟨x, y⟩ hx rfl
      exact h hx
      
    · rintro h x hx
      exact @h (a, x) hx rfl
      

section

attribute [local instance] TopologicalAddGroup.toUniformSpace

theorem uniformity_eq_comap_nhds_zero' : 𝓤 G = comap (fun p : G × G => p.2 - p.1) (𝓝 (0 : G)) :=
  rfl

variable {G}

theorem topological_add_group_is_uniform : UniformAddGroup G := by
  have :
    tendsto ((fun p : G × G => p.1 - p.2) ∘ fun p : (G × G) × G × G => (p.1.2 - p.1.1, p.2.2 - p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 - p.1.1, p.2.2 - p.2.1)) ((𝓝 0).Prod (𝓝 0))) (𝓝 (0 - 0)) :=
    (tendsto_fst.sub tendsto_snd).comp tendsto_comap
  constructor
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_zero' G, tendsto_comap_iff,
    prod_comap_comap_eq]
  simpa [· ∘ ·, sub_eq_add_neg, add_commₓ, add_left_commₓ] using this

attribute [local instance] topological_add_group_is_uniform

open Set

theorem TopologicalAddGroup.separated_iff_zero_closed : SeparatedSpace G ↔ IsClosed ({0} : Set G) := by
  rw [separated_space_iff, ← closure_eq_iff_is_closed]
  constructor <;> intro h
  · apply subset.antisymm
    · intro x x_in
      have := group_separation_rel x 0
      rw [sub_zero] at this
      rw [← this, h] at x_in
      change x = 0 at x_in
      simp [x_in]
      
    · exact subset_closure
      
    
  · ext p
    cases' p with x y
    rw [group_separation_rel x, h, mem_singleton_iff, sub_eq_zero]
    rfl
    

theorem TopologicalAddGroup.separated_of_zero_sep (H : ∀ x : G, x ≠ 0 → ∃ U ∈ nhds (0 : G), x ∉ U) : SeparatedSpace G :=
  by
  rw [TopologicalAddGroup.separated_iff_zero_closed, ← is_open_compl_iff, is_open_iff_mem_nhds]
  intro x x_not
  have : x ≠ 0 := mem_compl_singleton_iff.mp x_not
  rcases H x this with ⟨U, U_in, xU⟩
  rw [← nhds_zero_symm G] at U_in
  rcases U_in with ⟨W, W_in, UW⟩
  rw [← nhds_translation_add_neg]
  use W, W_in
  rw [subset_compl_comm]
  suffices -x ∉ W by
    simpa
  exact fun h => xU (UW h)

end

theorem to_uniform_space_eq {G : Type _} [u : UniformSpace G] [AddCommGroupₓ G] [UniformAddGroup G] :
    TopologicalAddGroup.toUniformSpace G = u := by
  ext : 1
  show @uniformity G (TopologicalAddGroup.toUniformSpace G) = 𝓤 G
  rw [uniformity_eq_comap_nhds_zero' G, uniformity_eq_comap_nhds_zero G]

end TopologicalAddCommGroup

open AddCommGroupₓ Filter Set Function

section

variable {α : Type _} {β : Type _}

variable [TopologicalSpace α] [AddCommGroupₓ α] [TopologicalAddGroup α]

variable [TopologicalSpace β] [AddCommGroupₓ β]

variable {e : β →+ α} (de : DenseInducing e)

include de

theorem tendsto_sub_comap_self (x₀ : α) :
    tendsto (fun t : β × β => t.2 - t.1) ((comap fun p : β × β => (e p.1, e p.2)) $ 𝓝 (x₀, x₀)) (𝓝 0) := by
  have comm : ((fun x : α × α => x.2 - x.1) ∘ fun t : β × β => (e t.1, e t.2)) = e ∘ fun t : β × β => t.2 - t.1 := by
    ext t
    change e t.2 - e t.1 = e (t.2 - t.1)
    rwa [← e.map_sub t.2 t.1]
  have lim : tendsto (fun x : α × α => x.2 - x.1) (𝓝 (x₀, x₀)) (𝓝 (e 0)) := by
    simpa using (continuous_sub.comp (@continuous_swap α α _ _)).Tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds limₓ comm

end

namespace DenseInducing

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {G : Type _}

variable [TopologicalSpace α] [AddCommGroupₓ α] [TopologicalAddGroup α]

variable [TopologicalSpace β] [AddCommGroupₓ β] [TopologicalAddGroup β]

variable [TopologicalSpace γ] [AddCommGroupₓ γ] [TopologicalAddGroup γ]

variable [TopologicalSpace δ] [AddCommGroupₓ δ] [TopologicalAddGroup δ]

variable [UniformSpace G] [AddCommGroupₓ G] [UniformAddGroup G] [SeparatedSpace G] [CompleteSpace G]

variable {e : β →+ α} (de : DenseInducing e)

variable {f : δ →+ γ} (df : DenseInducing f)

variable {φ : β →+ δ →+ G}

local notation "Φ" => fun p : β × δ => φ p.1 p.2

variable (hφ : Continuous Φ)

include de df hφ

variable {W' : Set G} (W'_nhd : W' ∈ 𝓝 (0 : G))

include W'_nhd

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x x' «expr ∈ » U₂)
private theorem extend_Z_bilin_aux (x₀ : α) (y₁ : δ) :
    ∃ U₂ ∈ comap e (𝓝 x₀), ∀ x x' _ : x ∈ U₂ _ : x' ∈ U₂, Φ (x' - x, y₁) ∈ W' := by
  let Nx := 𝓝 x₀
  let ee := fun u : β × β => (e u.1, e u.2)
  have lim1 : tendsto (fun a : β × β => (a.2 - a.1, y₁)) (comap e Nx ×ᶠ comap e Nx) (𝓝 (0, y₁)) := by
    have :=
      tendsto.prod_mk (tendsto_sub_comap_self de x₀)
        (tendsto_const_nhds : tendsto (fun p : β × β => y₁) (comap ee $ 𝓝 (x₀, x₀)) (𝓝 y₁))
    rw [nhds_prod_eq, prod_comap_comap_eq, ← nhds_prod_eq]
    exact (this : _)
  have lim2 : tendsto Φ (𝓝 (0, y₁)) (𝓝 0) := by
    simpa using hφ.tendsto (0, y₁)
  have lim := lim2.comp lim1
  rw [tendsto_prod_self_iff] at lim
  exact limₓ W' W'_nhd

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x x' «expr ∈ » U₁)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (y y' «expr ∈ » V₁)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (x x' «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (y y' «expr ∈ » V)
private theorem extend_Z_bilin_key (x₀ : α) (y₀ : γ) :
    ∃ U ∈ comap e (𝓝 x₀),
      ∃ V ∈ comap f (𝓝 y₀), ∀ x x' _ : x ∈ U _ : x' ∈ U, ∀ y y' _ : y ∈ V _ : y' ∈ V, Φ (x', y') - Φ (x, y) ∈ W' :=
  by
  let Nx := 𝓝 x₀
  let Ny := 𝓝 y₀
  let dp := DenseInducing.prod de df
  let ee := fun u : β × β => (e u.1, e u.2)
  let ff := fun u : δ × δ => (f u.1, f u.2)
  have lim_φ : Filter.Tendsto Φ (𝓝 (0, 0)) (𝓝 0) := by
    simpa using hφ.tendsto (0, 0)
  have lim_φ_sub_sub :
    tendsto (fun p : (β × β) × δ × δ => Φ (p.1.2 - p.1.1, p.2.2 - p.2.1))
      ((comap ee $ 𝓝 (x₀, x₀)) ×ᶠ (comap ff $ 𝓝 (y₀, y₀))) (𝓝 0) :=
    by
    have lim_sub_sub :
      tendsto (fun p : (β × β) × δ × δ => (p.1.2 - p.1.1, p.2.2 - p.2.1))
        (comap ee (𝓝 (x₀, x₀)) ×ᶠ comap ff (𝓝 (y₀, y₀))) (𝓝 0 ×ᶠ 𝓝 0) :=
      by
      have := Filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)
      rwa [prod_map_map_eq] at this
    rw [← nhds_prod_eq] at lim_sub_sub
    exact tendsto.comp lim_φ lim_sub_sub
  rcases exists_nhds_zero_quarter W'_nhd with ⟨W, W_nhd, W4⟩
  have :
    ∃ U₁ ∈ comap e (𝓝 x₀),
      ∃ V₁ ∈ comap f (𝓝 y₀), ∀ x x' _ : x ∈ U₁ _ : x' ∈ U₁, ∀ y y' _ : y ∈ V₁ _ : y' ∈ V₁, Φ (x' - x, y' - y) ∈ W :=
    by
    have := tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd
    repeat'
      rw [nhds_prod_eq, ← prod_comap_comap_eq] at this
    rcases this with ⟨U, U_in, V, V_in, H⟩
    rw [mem_prod_same_iff] at U_in V_in
    rcases U_in with ⟨U₁, U₁_in, HU₁⟩
    rcases V_in with ⟨V₁, V₁_in, HV₁⟩
    exists U₁, U₁_in, V₁, V₁_in
    intro x x' x_in x'_in y y' y_in y'_in
    exact H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))
  rcases this with ⟨U₁, U₁_nhd, V₁, V₁_nhd, H⟩
  obtain ⟨x₁, x₁_in⟩ : U₁.nonempty := (de.comap_nhds_ne_bot _).nonempty_of_mem U₁_nhd
  obtain ⟨y₁, y₁_in⟩ : V₁.nonempty := (df.comap_nhds_ne_bot _).nonempty_of_mem V₁_nhd
  have cont_flip : Continuous fun p : δ × β => φ.flip p.1 p.2 := by
    show Continuous (Φ ∘ Prod.swap)
    exact hφ.comp continuous_swap
  rcases extend_Z_bilin_aux de df hφ W_nhd x₀ y₁ with ⟨U₂, U₂_nhd, HU⟩
  rcases extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁ with ⟨V₂, V₂_nhd, HV⟩
  exists U₁ ∩ U₂, inter_mem U₁_nhd U₂_nhd, V₁ ∩ V₂, inter_mem V₁_nhd V₂_nhd
  rintro x x' ⟨xU₁, xU₂⟩ ⟨x'U₁, x'U₂⟩ y y' ⟨yV₁, yV₂⟩ ⟨y'V₁, y'V₂⟩
  have key_formula : φ x' y' - φ x y = φ (x' - x) y₁ + φ (x' - x) (y' - y₁) + φ x₁ (y' - y) + φ (x - x₁) (y' - y) := by
    simp
    abel
  rw [key_formula]
  have h₁ := HU x x' xU₂ x'U₂
  have h₂ := H x x' xU₁ x'U₁ y₁ y' y₁_in y'V₁
  have h₃ := HV y y' yV₂ y'V₂
  have h₄ := H x₁ x x₁_in xU₁ y y' yV₁ y'V₁
  exact W4 h₁ h₂ h₃ h₄

omit W'_nhd

open DenseInducing

/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin : Continuous (extend (de.prod df) Φ) := by
  refine' continuous_extend_of_cauchy _ _
  rintro ⟨x₀, y₀⟩
  constructor
  · apply ne_bot.map
    apply comap_ne_bot
    intro U h
    rcases mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h with ⟨x, x_in, ⟨z, z_x⟩⟩
    exists z
    cc
    
  · suffices
      map (fun p : (β × δ) × β × δ => Φ p.2 - Φ p.1)
          (comap (fun p : (β × δ) × β × δ => ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2))) (𝓝 (x₀, y₀) ×ᶠ 𝓝 (x₀, y₀))) ≤
        𝓝 0
      by
      rwa [uniformity_eq_comap_nhds_zero G, prod_map_map_eq, ← map_le_iff_le_comap, Filter.map_map, prod_comap_comap_eq]
    intro W' W'_nhd
    have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀
    rcases key with ⟨U, U_nhd, V, V_nhd, h⟩
    rw [mem_comap] at U_nhd
    rcases U_nhd with ⟨U', U'_nhd, U'_sub⟩
    rw [mem_comap] at V_nhd
    rcases V_nhd with ⟨V', V'_nhd, V'_sub⟩
    rw [mem_map, mem_comap, nhds_prod_eq]
    exists Set.Prod (Set.Prod U' V') (Set.Prod U' V')
    rw [mem_prod_same_iff]
    simp only [exists_prop]
    constructor
    · change U' ∈ 𝓝 x₀ at U'_nhd
      change V' ∈ 𝓝 y₀ at V'_nhd
      have := prod_mem_prod U'_nhd V'_nhd
      tauto
      
    · intro p h'
      simp only [Set.mem_preimage, Set.prod_mk_mem_set_prod_eq] at h'
      rcases p with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
      apply h <;> tauto
      
    

end DenseInducing

