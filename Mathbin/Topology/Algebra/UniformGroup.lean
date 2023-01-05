/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.uniform_group
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.CompleteSeparated
import Mathbin.Topology.UniformSpace.Compact
import Mathbin.Topology.Algebra.Group.Basic
import Mathbin.Tactic.Abel

/-!
# Uniform structure on topological groups

This file defines uniform groups and its additive counterpart. These typeclasses should be
preferred over using `[topological_space α] [topological_group α]` since every topological
group naturally induces a uniform structure.

## Main declarations
* `uniform_group` and `uniform_add_group`: Multiplicative and additive uniform groups, that
  i.e., groups with uniformly continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`.

## Main results

* `topological_add_group.to_uniform_space` and `topological_add_comm_group_is_uniform` can be used
  to construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)

* `quotient_group.complete_space` and `quotient_add_group.complete_space` guarantee that quotients
  of first countable topological groups by normal subgroups are themselves complete. In particular,
  the quotient of a Banach space by a subspace is complete.
-/


noncomputable section

open Classical uniformity TopologicalSpace Filter Pointwise

section UniformGroup

open Filter Set

variable {α : Type _} {β : Type _}

/-- A uniform group is a group in which multiplication and inversion are uniformly continuous. -/
class UniformGroup (α : Type _) [UniformSpace α] [Group α] : Prop where
  uniform_continuous_div : UniformContinuous fun p : α × α => p.1 / p.2
#align uniform_group UniformGroup

/-- A uniform additive group is an additive group in which addition
  and negation are uniformly continuous.-/
class UniformAddGroup (α : Type _) [UniformSpace α] [AddGroup α] : Prop where
  uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2
#align uniform_add_group UniformAddGroup

attribute [to_additive] UniformGroup

@[to_additive]
theorem UniformGroup.mk' {α} [UniformSpace α] [Group α]
    (h₁ : UniformContinuous fun p : α × α => p.1 * p.2) (h₂ : UniformContinuous fun p : α => p⁻¹) :
    UniformGroup α :=
  ⟨by
    simpa only [div_eq_mul_inv] using
      h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩
#align uniform_group.mk' UniformGroup.mk'

variable [UniformSpace α] [Group α] [UniformGroup α]

@[to_additive]
theorem uniform_continuous_div : UniformContinuous fun p : α × α => p.1 / p.2 :=
  UniformGroup.uniform_continuous_div
#align uniform_continuous_div uniform_continuous_div

@[to_additive]
theorem UniformContinuous.div [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x / g x :=
  uniform_continuous_div.comp (hf.prod_mk hg)
#align uniform_continuous.div UniformContinuous.div

@[to_additive]
theorem UniformContinuous.inv [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    UniformContinuous fun x => (f x)⁻¹ :=
  by
  have : UniformContinuous fun x => 1 / f x := uniform_continuous_const.div hf
  simp_all
#align uniform_continuous.inv UniformContinuous.inv

@[to_additive]
theorem uniform_continuous_inv : UniformContinuous fun x : α => x⁻¹ :=
  uniform_continuous_id.inv
#align uniform_continuous_inv uniform_continuous_inv

@[to_additive]
theorem UniformContinuous.mul [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun x => f x * g x :=
  by
  have : UniformContinuous fun x => f x / (g x)⁻¹ := hf.div hg.inv
  simp_all
#align uniform_continuous.mul UniformContinuous.mul

@[to_additive]
theorem uniform_continuous_mul : UniformContinuous fun p : α × α => p.1 * p.2 :=
  uniform_continuous_fst.mul uniform_continuous_snd
#align uniform_continuous_mul uniform_continuous_mul

@[to_additive UniformContinuous.const_nsmul]
theorem UniformContinuous.pow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℕ, UniformContinuous fun x => f x ^ n
  | 0 => by
    simp_rw [pow_zero]
    exact uniform_continuous_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact hf.mul (UniformContinuous.pow_const n)
#align uniform_continuous.pow_const UniformContinuous.pow_const

@[to_additive uniform_continuous_const_nsmul]
theorem uniform_continuous_pow_const (n : ℕ) : UniformContinuous fun x : α => x ^ n :=
  uniform_continuous_id.pow_const n
#align uniform_continuous_pow_const uniform_continuous_pow_const

@[to_additive UniformContinuous.const_zsmul]
theorem UniformContinuous.zpow_const [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
    ∀ n : ℤ, UniformContinuous fun x => f x ^ n
  | (n : ℕ) => by
    simp_rw [zpow_ofNat]
    exact hf.pow_const _
  | -[n+1] => by
    simp_rw [zpow_negSucc]
    exact (hf.pow_const _).inv
#align uniform_continuous.zpow_const UniformContinuous.zpow_const

@[to_additive uniform_continuous_const_zsmul]
theorem uniform_continuous_zpow_const (n : ℤ) : UniformContinuous fun x : α => x ^ n :=
  uniform_continuous_id.zpow_const n
#align uniform_continuous_zpow_const uniform_continuous_zpow_const

@[to_additive]
instance (priority := 10) UniformGroup.to_topological_group : TopologicalGroup α
    where
  continuous_mul := uniform_continuous_mul.Continuous
  continuous_inv := uniform_continuous_inv.Continuous
#align uniform_group.to_topological_group UniformGroup.to_topological_group

@[to_additive]
instance [UniformSpace β] [Group β] [UniformGroup β] : UniformGroup (α × β) :=
  ⟨((uniform_continuous_fst.comp uniform_continuous_fst).div
          (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).div
        (uniform_continuous_snd.comp uniform_continuous_snd))⟩

@[to_additive]
theorem uniformity_translate_mul (a : α) : ((𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a)) = 𝓤 α :=
  le_antisymm (uniform_continuous_id.mul uniform_continuous_const)
    (calc
      𝓤 α =
          ((𝓤 α).map fun x : α × α => (x.1 * a⁻¹, x.2 * a⁻¹)).map fun x : α × α =>
            (x.1 * a, x.2 * a) :=
        by simp [Filter.map_map, (· ∘ ·)] <;> exact filter.map_id.symm
      _ ≤ (𝓤 α).map fun x : α × α => (x.1 * a, x.2 * a) :=
        Filter.map_mono (uniform_continuous_id.mul uniform_continuous_const)
      )
#align uniformity_translate_mul uniformity_translate_mul

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([1]) } -/
@[to_additive]
theorem uniform_embedding_translate_mul (a : α) : UniformEmbedding fun x : α => x * a :=
  { comap_uniformity := by
      rw [← uniformity_translate_mul a, comap_map]
      rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      simp (config := { contextual := true }) [Prod.eq_iff_fst_eq_snd_eq]
    inj := mul_left_injective a }
#align uniform_embedding_translate_mul uniform_embedding_translate_mul

namespace MulOpposite

@[to_additive]
instance : UniformGroup αᵐᵒᵖ :=
  ⟨uniform_continuous_op.comp
      ((uniform_continuous_unop.comp uniform_continuous_snd).inv.mul <|
        uniform_continuous_unop.comp uniform_continuous_fst)⟩

end MulOpposite

namespace Subgroup

@[to_additive]
instance (S : Subgroup α) : UniformGroup S :=
  ⟨uniform_continuous_comap'
      (uniform_continuous_div.comp <|
        uniform_continuous_subtype_val.prod_map uniform_continuous_subtype_val)⟩

end Subgroup

section LatticeOps

variable [Group β]

@[to_additive]
theorem uniform_group_Inf {us : Set (UniformSpace β)} (h : ∀ u ∈ us, @UniformGroup β u _) :
    @UniformGroup β (infₛ us) _ :=
  {
    uniform_continuous_div :=
      uniform_continuous_Inf_rng fun u hu =>
        uniform_continuous_Inf_dom₂ hu hu (@UniformGroup.uniform_continuous_div β u _ (h u hu)) }
#align uniform_group_Inf uniform_group_Inf

@[to_additive]
theorem uniform_group_infi {ι : Sort _} {us' : ι → UniformSpace β}
    (h' : ∀ i, @UniformGroup β (us' i) _) : @UniformGroup β (⨅ i, us' i) _ :=
  by
  rw [← infₛ_range]
  exact uniform_group_Inf (set.forall_range_iff.mpr h')
#align uniform_group_infi uniform_group_infi

@[to_additive]
theorem uniform_group_inf {u₁ u₂ : UniformSpace β} (h₁ : @UniformGroup β u₁ _)
    (h₂ : @UniformGroup β u₂ _) : @UniformGroup β (u₁ ⊓ u₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' uniform_group_infi fun b => _
  cases b <;> assumption
#align uniform_group_inf uniform_group_inf

@[to_additive]
theorem uniform_group_comap {γ : Type _} [Group γ] {u : UniformSpace γ} [UniformGroup γ]
    {F : Type _} [MonoidHomClass F β γ] (f : F) : @UniformGroup β (u.comap f) _ :=
  {
    uniform_continuous_div := by
      letI : UniformSpace β := u.comap f
      refine' uniform_continuous_comap' _
      simp_rw [Function.comp, map_div]
      change UniformContinuous ((fun p : γ × γ => p.1 / p.2) ∘ Prod.map f f)
      exact
        uniform_continuous_div.comp (uniform_continuous_comap.prod_map uniform_continuous_comap) }
#align uniform_group_comap uniform_group_comap

end LatticeOps

section

variable (α)

@[to_additive]
theorem uniformity_eq_comap_nhds_one : 𝓤 α = comap (fun x : α × α => x.2 / x.1) (𝓝 (1 : α)) :=
  by
  rw [nhds_eq_comap_uniformity, Filter.comap_comap]
  refine' le_antisymm (Filter.map_le_iff_le_comap.1 _) _
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_div hs with
      ⟨t, ht, hts⟩
    refine' mem_map.2 (mem_of_superset ht _)
    rintro ⟨a, b⟩
    simpa [subset_def] using hts a b a
  · intro s hs
    rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_mul hs with
      ⟨t, ht, hts⟩
    refine' ⟨_, ht, _⟩
    rintro ⟨a, b⟩
    simpa [subset_def] using hts 1 (b / a) a
#align uniformity_eq_comap_nhds_one uniformity_eq_comap_nhds_one

@[to_additive]
theorem uniformity_eq_comap_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.1 / x.2) (𝓝 (1 : α)) :=
  by
  rw [← comap_swap_uniformity, uniformity_eq_comap_nhds_one, comap_comap, (· ∘ ·)]
  rfl
#align uniformity_eq_comap_nhds_one_swapped uniformity_eq_comap_nhds_one_swapped

@[to_additive]
theorem UniformGroup.ext {G : Type _} [Group G] {u v : UniformSpace G} (hu : @UniformGroup G u _)
    (hv : @UniformGroup G v _)
    (h : @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1) : u = v :=
  by
  refine' uniform_space_eq _
  change @uniformity _ u = @uniformity _ v
  rw [@uniformity_eq_comap_nhds_one _ u _ hu, @uniformity_eq_comap_nhds_one _ v _ hv, h]
#align uniform_group.ext UniformGroup.ext

@[to_additive]
theorem UniformGroup.ext_iff {G : Type _} [Group G] {u v : UniformSpace G}
    (hu : @UniformGroup G u _) (hv : @UniformGroup G v _) :
    u = v ↔ @nhds _ u.toTopologicalSpace 1 = @nhds _ v.toTopologicalSpace 1 :=
  ⟨fun h => h ▸ rfl, hu.ext hv⟩
#align uniform_group.ext_iff UniformGroup.ext_iff

variable {α}

@[to_additive]
theorem UniformGroup.uniformity_countably_generated [(𝓝 (1 : α)).IsCountablyGenerated] :
    (𝓤 α).IsCountablyGenerated :=
  by
  rw [uniformity_eq_comap_nhds_one]
  exact Filter.comap.is_countably_generated _ _
#align uniform_group.uniformity_countably_generated UniformGroup.uniformity_countably_generated

open MulOpposite

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one :
    𝓤 α = comap (fun x : α × α => x.1⁻¹ * x.2) (𝓝 (1 : α)) :=
  by
  rw [← comap_uniformity_mul_opposite, uniformity_eq_comap_nhds_one, ← op_one, ← comap_unop_nhds,
    comap_comap, comap_comap]
  simp [(· ∘ ·)]
#align uniformity_eq_comap_inv_mul_nhds_one uniformity_eq_comap_inv_mul_nhds_one

@[to_additive]
theorem uniformity_eq_comap_inv_mul_nhds_one_swapped :
    𝓤 α = comap (fun x : α × α => x.2⁻¹ * x.1) (𝓝 (1 : α)) :=
  by
  rw [← comap_swap_uniformity, uniformity_eq_comap_inv_mul_nhds_one, comap_comap, (· ∘ ·)]
  rfl
#align uniformity_eq_comap_inv_mul_nhds_one_swapped uniformity_eq_comap_inv_mul_nhds_one_swapped

end

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2 / x.1 ∈ U i } :=
  by
  rw [uniformity_eq_comap_nhds_one]
  exact h.comap _
#align filter.has_basis.uniformity_of_nhds_one Filter.HasBasis.uniformity_of_nhds_one

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1⁻¹ * x.2 ∈ U i } :=
  by
  rw [uniformity_eq_comap_inv_mul_nhds_one]
  exact h.comap _
#align
  filter.has_basis.uniformity_of_nhds_one_inv_mul Filter.HasBasis.uniformity_of_nhds_one_inv_mul

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.1 / x.2 ∈ U i } :=
  by
  rw [uniformity_eq_comap_nhds_one_swapped]
  exact h.comap _
#align
  filter.has_basis.uniformity_of_nhds_one_swapped Filter.HasBasis.uniformity_of_nhds_one_swapped

@[to_additive]
theorem Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped {ι} {p : ι → Prop} {U : ι → Set α}
    (h : (𝓝 (1 : α)).HasBasis p U) : (𝓤 α).HasBasis p fun i => { x : α × α | x.2⁻¹ * x.1 ∈ U i } :=
  by
  rw [uniformity_eq_comap_inv_mul_nhds_one_swapped]
  exact h.comap _
#align
  filter.has_basis.uniformity_of_nhds_one_inv_mul_swapped Filter.HasBasis.uniformity_of_nhds_one_inv_mul_swapped

@[to_additive]
theorem group_separation_rel (x y : α) : (x, y) ∈ separationRel α ↔ x / y ∈ closure ({1} : Set α) :=
  have : Embedding fun a => a * (y / x) := (uniform_embedding_translate_mul (y / x)).Embedding
  show (x, y) ∈ ⋂₀ (𝓤 α).sets ↔ x / y ∈ closure ({1} : Set α)
    by
    rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_one α, sInter_comap_sets]
    simp [mem_closure_iff_nhds, inter_singleton_nonempty, sub_eq_add_neg, add_assoc]
#align group_separation_rel group_separation_rel

@[to_additive]
theorem uniform_continuous_of_tendsto_one {hom : Type _} [UniformSpace β] [Group β] [UniformGroup β]
    [MonoidHomClass hom α β] {f : hom} (h : Tendsto f (𝓝 1) (𝓝 1)) : UniformContinuous f :=
  by
  have :
    ((fun x : β × β => x.2 / x.1) ∘ fun x : α × α => (f x.1, f x.2)) = fun x : α × α =>
      f (x.2 / x.1) :=
    by simp only [map_div]
  rw [UniformContinuous, uniformity_eq_comap_nhds_one α, uniformity_eq_comap_nhds_one β,
    tendsto_comap_iff, this]
  exact tendsto.comp h tendsto_comap
#align uniform_continuous_of_tendsto_one uniform_continuous_of_tendsto_one

/-- A group homomorphism (a bundled morphism of a type that implements `monoid_hom_class`) between
two uniform groups is uniformly continuous provided that it is continuous at one. See also
`continuous_of_continuous_at_one`. -/
@[to_additive
      "An additive group homomorphism (a bundled morphism of a type that implements\n`add_monoid_hom_class`) between two uniform additive groups is uniformly continuous provided that it\nis continuous at zero. See also `continuous_of_continuous_at_zero`."]
theorem uniform_continuous_of_continuous_at_one {hom : Type _} [UniformSpace β] [Group β]
    [UniformGroup β] [MonoidHomClass hom α β] (f : hom) (hf : ContinuousAt f 1) :
    UniformContinuous f :=
  uniform_continuous_of_tendsto_one (by simpa using hf.tendsto)
#align uniform_continuous_of_continuous_at_one uniform_continuous_of_continuous_at_one

@[to_additive]
theorem MonoidHom.uniform_continuous_of_continuous_at_one [UniformSpace β] [Group β]
    [UniformGroup β] (f : α →* β) (hf : ContinuousAt f 1) : UniformContinuous f :=
  uniform_continuous_of_continuous_at_one f hf
#align
  monoid_hom.uniform_continuous_of_continuous_at_one MonoidHom.uniform_continuous_of_continuous_at_one

/-- A homomorphism from a uniform group to a discrete uniform group is continuous if and only if
its kernel is open. -/
@[to_additive
      "A homomorphism from a uniform additive group to a discrete uniform additive group is\ncontinuous if and only if its kernel is open."]
theorem UniformGroup.uniform_continuous_iff_open_ker {hom : Type _} [UniformSpace β]
    [DiscreteTopology β] [Group β] [UniformGroup β] [MonoidHomClass hom α β] {f : hom} :
    UniformContinuous f ↔ IsOpen ((f : α →* β).ker : Set α) :=
  by
  refine' ⟨fun hf => _, fun hf => _⟩
  · apply (is_open_discrete ({1} : Set β)).Preimage (UniformContinuous.continuous hf)
  · apply uniform_continuous_of_continuous_at_one
    rw [ContinuousAt, nhds_discrete β, map_one, tendsto_pure]
    exact hf.mem_nhds (map_one f)
#align uniform_group.uniform_continuous_iff_open_ker UniformGroup.uniform_continuous_iff_open_ker

@[to_additive]
theorem uniform_continuous_monoid_hom_of_continuous {hom : Type _} [UniformSpace β] [Group β]
    [UniformGroup β] [MonoidHomClass hom α β] {f : hom} (h : Continuous f) : UniformContinuous f :=
  uniform_continuous_of_tendsto_one <|
    suffices Tendsto f (𝓝 1) (𝓝 (f 1)) by rwa [map_one] at this
    h.Tendsto 1
#align uniform_continuous_monoid_hom_of_continuous uniform_continuous_monoid_hom_of_continuous

@[to_additive]
theorem CauchySeq.mul {ι : Type _} [SemilatticeSup ι] {u v : ι → α} (hu : CauchySeq u)
    (hv : CauchySeq v) : CauchySeq (u * v) :=
  uniform_continuous_mul.comp_cauchy_seq (hu.Prod hv)
#align cauchy_seq.mul CauchySeq.mul

@[to_additive]
theorem CauchySeq.mul_const {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => u n * x :=
  (uniform_continuous_id.mul uniform_continuous_const).comp_cauchy_seq hu
#align cauchy_seq.mul_const CauchySeq.mul_const

@[to_additive]
theorem CauchySeq.const_mul {ι : Type _} [SemilatticeSup ι] {u : ι → α} {x : α} (hu : CauchySeq u) :
    CauchySeq fun n => x * u n :=
  (uniform_continuous_const.mul uniform_continuous_id).comp_cauchy_seq hu
#align cauchy_seq.const_mul CauchySeq.const_mul

@[to_additive]
theorem CauchySeq.inv {ι : Type _} [SemilatticeSup ι] {u : ι → α} (h : CauchySeq u) :
    CauchySeq u⁻¹ :=
  uniform_continuous_inv.comp_cauchy_seq h
#align cauchy_seq.inv CauchySeq.inv

@[to_additive]
theorem totally_bounded_iff_subset_finite_Union_nhds_one {s : Set α} :
    TotallyBounded s ↔ ∀ U ∈ 𝓝 (1 : α), ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, y • U :=
  (𝓝 (1 : α)).basis_sets.uniformity_of_nhds_one_inv_mul_swapped.totally_bounded_iff.trans <| by
    simp [← preimage_smul_inv, preimage]
#align
  totally_bounded_iff_subset_finite_Union_nhds_one totally_bounded_iff_subset_finite_Union_nhds_one

section UniformConvergence

variable {ι : Type _} {l : Filter ι} {l' : Filter β} {f f' : ι → β → α} {g g' : β → α} {s : Set β}

@[to_additive]
theorem TendstoUniformlyOnFilter.mul (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f * f') (g * g') l l' :=
  fun u hu =>
  ((uniform_continuous_mul.comp_tendsto_uniformly_on_filter (hf.Prod hf')) u hu).diag_of_prod_left
#align tendsto_uniformly_on_filter.mul TendstoUniformlyOnFilter.mul

@[to_additive]
theorem TendstoUniformlyOnFilter.div (hf : TendstoUniformlyOnFilter f g l l')
    (hf' : TendstoUniformlyOnFilter f' g' l l') : TendstoUniformlyOnFilter (f / f') (g / g') l l' :=
  fun u hu =>
  ((uniform_continuous_div.comp_tendsto_uniformly_on_filter (hf.Prod hf')) u hu).diag_of_prod_left
#align tendsto_uniformly_on_filter.div TendstoUniformlyOnFilter.div

@[to_additive]
theorem TendstoUniformlyOn.mul (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f * f') (g * g') l s := fun u hu =>
  ((uniform_continuous_mul.comp_tendsto_uniformly_on (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly_on.mul TendstoUniformlyOn.mul

@[to_additive]
theorem TendstoUniformlyOn.div (hf : TendstoUniformlyOn f g l s)
    (hf' : TendstoUniformlyOn f' g' l s) : TendstoUniformlyOn (f / f') (g / g') l s := fun u hu =>
  ((uniform_continuous_div.comp_tendsto_uniformly_on (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly_on.div TendstoUniformlyOn.div

@[to_additive]
theorem TendstoUniformly.mul (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f * f') (g * g') l := fun u hu =>
  ((uniform_continuous_mul.comp_tendsto_uniformly (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly.mul TendstoUniformly.mul

@[to_additive]
theorem TendstoUniformly.div (hf : TendstoUniformly f g l) (hf' : TendstoUniformly f' g' l) :
    TendstoUniformly (f / f') (g / g') l := fun u hu =>
  ((uniform_continuous_div.comp_tendsto_uniformly (hf.Prod hf')) u hu).diag_of_prod
#align tendsto_uniformly.div TendstoUniformly.div

@[to_additive]
theorem UniformCauchySeqOn.mul (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f * f') l s := fun u hu => by
  simpa using (uniform_continuous_mul.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu
#align uniform_cauchy_seq_on.mul UniformCauchySeqOn.mul

@[to_additive]
theorem UniformCauchySeqOn.div (hf : UniformCauchySeqOn f l s) (hf' : UniformCauchySeqOn f' l s) :
    UniformCauchySeqOn (f / f') l s := fun u hu => by
  simpa using (uniform_continuous_div.comp_uniform_cauchy_seq_on (hf.prod' hf')) u hu
#align uniform_cauchy_seq_on.div UniformCauchySeqOn.div

end UniformConvergence

end UniformGroup

section TopologicalGroup

open Filter

variable (G : Type _) [Group G] [TopologicalSpace G] [TopologicalGroup G]

/-- The right uniformity on a topological group (as opposed to the left uniformity).

Warning: in general the right and left uniformities do not coincide and so one does not obtain a
`uniform_group` structure. Two important special cases where they _do_ coincide are for
commutative groups (see `topological_comm_group_is_uniform`) and for compact groups (see
`topological_group_is_uniform_of_compact_space`). -/
@[to_additive
      "The right uniformity on a topological additive group (as opposed to the left\nuniformity).\n\nWarning: in general the right and left uniformities do not coincide and so one does not obtain a\n`uniform_add_group` structure. Two important special cases where they _do_ coincide are for\ncommutative additive groups (see `topological_add_comm_group_is_uniform`) and for compact\nadditive groups (see `topological_add_comm_group_is_uniform_of_compact_space`)."]
def TopologicalGroup.toUniformSpace : UniformSpace G
    where
  uniformity := comap (fun p : G × G => p.2 / p.1) (𝓝 1)
  refl := by
    refine' map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 1)) <;>
      simp (config := { contextual := true }) [Set.subset_def]
  symm :=
    by
    suffices
      tendsto (fun p : G × G => (p.2 / p.1)⁻¹) (comap (fun p : G × G => p.2 / p.1) (𝓝 1)) (𝓝 1⁻¹) by
      simpa [tendsto_comap_iff]
    exact tendsto.comp (tendsto.inv tendsto_id) tendsto_comap
  comp := by
    intro D H
    rw [mem_lift'_sets]
    · rcases H with ⟨U, U_nhds, U_sub⟩
      rcases exists_nhds_one_split U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩
      exists (fun p : G × G => p.2 / p.1) ⁻¹' V
      have H :
        (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) := by
        exists V, V_nhds <;> rfl
      exists H
      have comp_rel_sub :
        compRel ((fun p : G × G => p.2 / p.1) ⁻¹' V) ((fun p => p.2 / p.1) ⁻¹' V) ⊆
          (fun p : G × G => p.2 / p.1) ⁻¹' U :=
        by
        intro p p_comp_rel
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩
        simpa using V_sum _ Hz2 _ Hz1
      exact Set.Subset.trans comp_rel_sub U_sub
    · exact monotone_comp_rel monotone_id monotone_id
  is_open_uniformity := by
    intro S
    let S' x := { p : G × G | p.1 = x → p.2 ∈ S }
    show IsOpen S ↔ ∀ x : G, x ∈ S → S' x ∈ comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G))
    rw [is_open_iff_mem_nhds]
    refine' forall₂_congr fun a ha => _
    rw [← nhds_translation_div, mem_comap, mem_comap]
    refine' exists₂_congr fun t ht => _
    show (fun y : G => y / a) ⁻¹' t ⊆ S ↔ (fun p : G × G => p.snd / p.fst) ⁻¹' t ⊆ S' a
    constructor
    · rintro h ⟨x, y⟩ hx rfl
      exact h hx
    · rintro h x hx
      exact @h (a, x) hx rfl
#align topological_group.to_uniform_space TopologicalGroup.toUniformSpace

attribute [local instance] TopologicalGroup.toUniformSpace

@[to_additive]
theorem uniformity_eq_comap_nhds_one' : 𝓤 G = comap (fun p : G × G => p.2 / p.1) (𝓝 (1 : G)) :=
  rfl
#align uniformity_eq_comap_nhds_one' uniformity_eq_comap_nhds_one'

@[to_additive]
theorem topological_group_is_uniform_of_compact_space [CompactSpace G] : UniformGroup G :=
  ⟨by
    apply CompactSpace.uniform_continuous_of_continuous
    exact continuous_div'⟩
#align topological_group_is_uniform_of_compact_space topological_group_is_uniform_of_compact_space

variable {G}

@[to_additive]
instance Subgroup.is_closed_of_discrete [T2Space G] {H : Subgroup G} [DiscreteTopology H] :
    IsClosed (H : Set G) :=
  by
  obtain ⟨V, V_in, VH⟩ : ∃ (V : Set G)(hV : V ∈ 𝓝 (1 : G)), V ∩ (H : Set G) = {1}
  exact nhds_inter_eq_singleton_of_mem_discrete H.one_mem
  haveI : SeparatedSpace G := separated_iff_t2.mpr ‹_›
  have : (fun p : G × G => p.2 / p.1) ⁻¹' V ∈ 𝓤 G := preimage_mem_comap V_in
  apply is_closed_of_spaced_out this
  intro h h_in h' h'_in
  contrapose!
  rintro (hyp : h' / h ∈ V)
  have : h' / h ∈ ({1} : Set G) := VH ▸ Set.mem_inter hyp (H.div_mem h'_in h_in)
  exact (eq_of_div_eq_one this).symm
#align subgroup.is_closed_of_discrete Subgroup.is_closed_of_discrete

@[to_additive]
theorem TopologicalGroup.tendsto_uniformly_iff {ι α : Type _} (F : ι → α → G) (f : α → G)
    (p : Filter ι) :
    @TendstoUniformly α G ι (TopologicalGroup.toUniformSpace G) F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun i hi a => hv (hi a)⟩
#align topological_group.tendsto_uniformly_iff TopologicalGroup.tendsto_uniformly_iff

@[to_additive]
theorem TopologicalGroup.tendsto_uniformly_on_iff {ι α : Type _} (F : ι → α → G) (f : α → G)
    (p : Filter ι) (s : Set α) :
    @TendstoUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ᶠ i in p, ∀ a ∈ s, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ =>
    mem_of_superset (h u hu) fun i hi a ha => hv (hi a ha)⟩
#align topological_group.tendsto_uniformly_on_iff TopologicalGroup.tendsto_uniformly_on_iff

@[to_additive]
theorem TopologicalGroup.tendsto_locally_uniformly_iff {ι α : Type _} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) :
    @TendstoLocallyUniformly α G ι (TopologicalGroup.toUniformSpace G) _ F f p ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    Exists.imp (fun a => Exists.imp fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha))
      (h u hu x)⟩
#align
  topological_group.tendsto_locally_uniformly_iff TopologicalGroup.tendsto_locally_uniformly_iff

@[to_additive]
theorem TopologicalGroup.tendsto_locally_uniformly_on_iff {ι α : Type _} [TopologicalSpace α]
    (F : ι → α → G) (f : α → G) (p : Filter ι) (s : Set α) :
    @TendstoLocallyUniformlyOn α G ι (TopologicalGroup.toUniformSpace G) _ F f p s ↔
      ∀ u ∈ 𝓝 (1 : G), ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ i in p, ∀ a ∈ t, F i a / f a ∈ u :=
  ⟨fun h u hu => h _ ⟨u, hu, fun _ => id⟩, fun h v ⟨u, hu, hv⟩ x =>
    (Exists.imp fun a => Exists.imp fun ha hp => mem_of_superset hp fun i hi a ha => hv (hi a ha)) ∘
      h u hu x⟩
#align
  topological_group.tendsto_locally_uniformly_on_iff TopologicalGroup.tendsto_locally_uniformly_on_iff

end TopologicalGroup

section TopologicalCommGroup

universe u v w x

open Filter

variable (G : Type _) [CommGroup G] [TopologicalSpace G] [TopologicalGroup G]

section

attribute [local instance] TopologicalGroup.toUniformSpace

variable {G}

@[to_additive]
theorem topological_comm_group_is_uniform : UniformGroup G :=
  by
  have :
    Tendsto
      ((fun p : G × G => p.1 / p.2) ∘ fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 / p.1.1, p.2.2 / p.2.1)) ((𝓝 1).Prod (𝓝 1)))
      (𝓝 (1 / 1)) :=
    (tendsto_fst.div' tendsto_snd).comp tendsto_comap
  constructor
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_one' G,
    tendsto_comap_iff, prod_comap_comap_eq]
  simpa [(· ∘ ·), div_eq_mul_inv, mul_comm, mul_left_comm] using this
#align topological_comm_group_is_uniform topological_comm_group_is_uniform

open Set

@[to_additive]
theorem TopologicalGroup.t2_space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  by
  haveI : UniformGroup G := topological_comm_group_is_uniform
  rw [← separated_iff_t2, separated_space_iff, ← closure_eq_iff_is_closed]
  constructor <;> intro h
  · apply subset.antisymm
    · intro x x_in
      have := group_separation_rel x 1
      rw [div_one] at this
      rw [← this, h] at x_in
      change x = 1 at x_in
      simp [x_in]
    · exact subset_closure
  · ext p
    cases' p with x y
    rw [group_separation_rel x, h, mem_singleton_iff, div_eq_one]
    rfl
#align topological_group.t2_space_iff_one_closed TopologicalGroup.t2_space_iff_one_closed

@[to_additive]
theorem TopologicalGroup.t2SpaceOfOneSep (H : ∀ x : G, x ≠ 1 → ∃ U ∈ nhds (1 : G), x ∉ U) :
    T2Space G :=
  by
  rw [TopologicalGroup.t2_space_iff_one_closed, ← is_open_compl_iff, is_open_iff_mem_nhds]
  intro x x_not
  have : x ≠ 1 := mem_compl_singleton_iff.mp x_not
  rcases H x this with ⟨U, U_in, xU⟩
  rw [← nhds_one_symm G] at U_in
  rcases U_in with ⟨W, W_in, UW⟩
  rw [← nhds_translation_mul_inv]
  use W, W_in
  rw [subset_compl_comm]
  suffices x⁻¹ ∉ W by simpa
  exact fun h => xU (UW h)
#align topological_group.t2_space_of_one_sep TopologicalGroup.t2SpaceOfOneSep

end

@[to_additive]
theorem UniformGroup.to_uniform_space_eq {G : Type _} [u : UniformSpace G] [Group G]
    [UniformGroup G] : TopologicalGroup.toUniformSpace G = u :=
  by
  ext : 1
  show @uniformity G (TopologicalGroup.toUniformSpace G) = 𝓤 G
  rw [uniformity_eq_comap_nhds_one' G, uniformity_eq_comap_nhds_one G]
#align uniform_group.to_uniform_space_eq UniformGroup.to_uniform_space_eq

end TopologicalCommGroup

open Filter Set Function

section

variable {α : Type _} {β : Type _} {hom : Type _}

variable [TopologicalSpace α] [Group α] [TopologicalGroup α]

-- β is a dense subgroup of α, inclusion is denoted by e
variable [TopologicalSpace β] [Group β]

variable [MonoidHomClass hom β α] {e : hom} (de : DenseInducing e)

include de

@[to_additive]
theorem tendsto_div_comap_self (x₀ : α) :
    Tendsto (fun t : β × β => t.2 / t.1) ((comap fun p : β × β => (e p.1, e p.2)) <| 𝓝 (x₀, x₀))
      (𝓝 1) :=
  by
  have comm :
    ((fun x : α × α => x.2 / x.1) ∘ fun t : β × β => (e t.1, e t.2)) =
      e ∘ fun t : β × β => t.2 / t.1 :=
    by
    ext t
    change e t.2 / e t.1 = e (t.2 / t.1)
    rwa [← map_div e t.2 t.1]
  have lim : tendsto (fun x : α × α => x.2 / x.1) (𝓝 (x₀, x₀)) (𝓝 (e 1)) := by
    simpa using (continuous_div'.comp (@continuous_swap α α _ _)).Tendsto (x₀, x₀)
  simpa using de.tendsto_comap_nhds_nhds lim comm
#align tendsto_div_comap_self tendsto_div_comap_self

end

namespace DenseInducing

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {G : Type _}

-- β is a dense subgroup of α, inclusion is denoted by e
-- δ is a dense subgroup of γ, inclusion is denoted by f
variable [TopologicalSpace α] [AddCommGroup α] [TopologicalAddGroup α]

variable [TopologicalSpace β] [AddCommGroup β] [TopologicalAddGroup β]

variable [TopologicalSpace γ] [AddCommGroup γ] [TopologicalAddGroup γ]

variable [TopologicalSpace δ] [AddCommGroup δ] [TopologicalAddGroup δ]

variable [UniformSpace G] [AddCommGroup G] [UniformAddGroup G] [SeparatedSpace G] [CompleteSpace G]

variable {e : β →+ α} (de : DenseInducing e)

variable {f : δ →+ γ} (df : DenseInducing f)

variable {φ : β →+ δ →+ G}

-- mathport name: exprΦ
local notation "Φ" => fun p : β × δ => φ p.1 p.2

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.variable
     "variable"
     [(Term.explicitBinder
       "("
       [`hφ]
       [":" (Term.app `Continuous [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")])]
       []
       ")")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Continuous [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'DenseInducing.Topology.Algebra.UniformGroup.termΦ._@.Topology.Algebra.UniformGroup._hyg.32'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'-/-- failed to format: format: uncaught backtrack exception
variable ( hφ : Continuous Φ )

include de df hφ

variable {W' : Set G} (W'_nhd : W' ∈ 𝓝 (0 : G))

include W'_nhd

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x x' «expr ∈ » U₂) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_Z_bilin_aux [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x₀] [":" `α] [] ")")
        (Term.explicitBinder "(" [`y₁] [":" `δ] [] ")")]
       (Term.typeSpec
        ":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `U₂)
         («binderTerm∈_»
          "∈"
          (Term.app `comap [`e (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])]))
         ","
         (Term.forall
          "∀"
          [(Term.explicitBinder "(" [`x] [] [] ")")
           (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `U₂)] [] ")")
           (Term.explicitBinder "(" [`x'] [] [] ")")
           (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x' "∈" `U₂)] [] ")")]
          []
          ","
          («term_∈_»
           (Term.app
            (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
            [(Term.tuple "(" [(«term_-_» `x' "-" `x) "," [`y₁]] ")")])
           "∈"
           `W')))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Nx
              []
              []
              ":="
              (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `ee
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`u]
                [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                "=>"
                (Term.tuple
                 "("
                 [(Term.app `e [(Term.proj `u "." (fieldIdx "1"))])
                  ","
                  [(Term.app `e [(Term.proj `u "." (fieldIdx "2"))])]]
                 ")"))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim1 []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                    "=>"
                    (Term.tuple
                     "("
                     [(«term_-_»
                       (Term.proj `a "." (fieldIdx "2"))
                       "-"
                       (Term.proj `a "." (fieldIdx "1")))
                      ","
                      [`y₁]]
                     ")")))
                  (Filter.Order.Filter.Prod.filter.prod
                   (Term.app `comap [`e `Nx])
                   " ×ᶠ "
                   (Term.app `comap [`e `Nx]))
                  (Term.app
                   (TopologicalSpace.Topology.Basic.nhds "𝓝")
                   [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      `tendsto.prod_mk
                      [(Term.app `tendsto_sub_comap_self [`de `x₀])
                       (Term.typeAscription
                        "("
                        `tendsto_const_nhds
                        ":"
                        [(Term.app
                          `tendsto
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`p]
                             [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                             "=>"
                             `y₁))
                           («term_<|_»
                            (Term.app `comap [`ee])
                            "<|"
                            (Term.app
                             (TopologicalSpace.Topology.Basic.nhds "𝓝")
                             [(Term.tuple "(" [`x₀ "," [`x₀]] ")")]))
                           (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₁])])]
                        ")")]))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `nhds_prod_eq)
                     ","
                     (Tactic.rwRule [] `prod_comap_comap_eq)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.typeAscription "(" `this ":" [(Term.hole "_")] ")"))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim2 []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                  (Term.app
                   (TopologicalSpace.Topology.Basic.nhds "𝓝")
                   [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    []
                    ["using"
                     (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`lim []] [] ":=" (Term.app `lim2.comp [`lim1]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_prod_self_iff)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`lim] []))])
           []
           (Mathlib.Tactic.tacticSimp_rw__
            "simp_rw"
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ball_mem_comm)] "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `lim [`W' `W'_nhd]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Nx
             []
             []
             ":="
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `ee
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`u]
               [(Term.typeSpec ":" («term_×_» `β "×" `β))]
               "=>"
               (Term.tuple
                "("
                [(Term.app `e [(Term.proj `u "." (fieldIdx "1"))])
                 ","
                 [(Term.app `e [(Term.proj `u "." (fieldIdx "2"))])]]
                ")"))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim1 []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                   "=>"
                   (Term.tuple
                    "("
                    [(«term_-_»
                      (Term.proj `a "." (fieldIdx "2"))
                      "-"
                      (Term.proj `a "." (fieldIdx "1")))
                     ","
                     [`y₁]]
                    ")")))
                 (Filter.Order.Filter.Prod.filter.prod
                  (Term.app `comap [`e `Nx])
                  " ×ᶠ "
                  (Term.app `comap [`e `Nx]))
                 (Term.app
                  (TopologicalSpace.Topology.Basic.nhds "𝓝")
                  [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     `tendsto.prod_mk
                     [(Term.app `tendsto_sub_comap_self [`de `x₀])
                      (Term.typeAscription
                       "("
                       `tendsto_const_nhds
                       ":"
                       [(Term.app
                         `tendsto
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`p]
                            [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                            "=>"
                            `y₁))
                          («term_<|_»
                           (Term.app `comap [`ee])
                           "<|"
                           (Term.app
                            (TopologicalSpace.Topology.Basic.nhds "𝓝")
                            [(Term.tuple "(" [`x₀ "," [`x₀]] ")")]))
                          (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₁])])]
                       ")")]))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `nhds_prod_eq)
                    ","
                    (Tactic.rwRule [] `prod_comap_comap_eq)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.typeAscription "(" `this ":" [(Term.hole "_")] ")"))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim2 []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                 (Term.app
                  (TopologicalSpace.Topology.Basic.nhds "𝓝")
                  [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   []
                   ["using"
                    (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`lim []] [] ":=" (Term.app `lim2.comp [`lim1]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_prod_self_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`lim] []))])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ball_mem_comm)] "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `lim [`W' `W'_nhd]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `lim [`W' `W'_nhd]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lim [`W' `W'_nhd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `W'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `W'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ball_mem_comm)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ball_mem_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `tendsto_prod_self_iff)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`lim] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `tendsto_prod_self_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`lim []] [] ":=" (Term.app `lim2.comp [`lim1]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lim2.comp [`lim1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lim1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lim2.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`lim2 []]
         [(Term.typeSpec
           ":"
           (Term.app
            `tendsto
            [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
             (Term.app
              (TopologicalSpace.Topology.Basic.nhds "𝓝")
              [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               []
               []
               ["using"
                (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            []
            []
            ["using" (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        []
        []
        ["using" (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hφ.tendsto [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(num "0") "," [`y₁]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hφ.tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `tendsto
       [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
        (Term.app
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
        (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [(num "0") "," [`y₁]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
      [(Term.tuple "(" [(num "0") "," [`y₁]] ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'DenseInducing.Topology.Algebra.UniformGroup.termΦ._@.Topology.Algebra.UniformGroup._hyg.32'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem
    extend_Z_bilin_aux
    ( x₀ : α ) ( y₁ : δ )
      : ∃ U₂ ∈ comap e 𝓝 x₀ , ∀ ( x ) ( _ : x ∈ U₂ ) ( x' ) ( _ : x' ∈ U₂ ) , Φ ( x' - x , y₁ ) ∈ W'
    :=
      by
        let Nx := 𝓝 x₀
          let ee := fun u : β × β => ( e u . 1 , e u . 2 )
          have
            lim1
              :
                tendsto
                  fun a : β × β => ( a . 2 - a . 1 , y₁ ) comap e Nx ×ᶠ comap e Nx 𝓝 ( 0 , y₁ )
              :=
              by
                have
                    :=
                      tendsto.prod_mk
                        tendsto_sub_comap_self de x₀
                          (
                            tendsto_const_nhds
                            :
                            tendsto fun p : β × β => y₁ comap ee <| 𝓝 ( x₀ , x₀ ) 𝓝 y₁
                            )
                  rw [ nhds_prod_eq , prod_comap_comap_eq , ← nhds_prod_eq ]
                  exact ( this : _ )
          have lim2 : tendsto Φ 𝓝 ( 0 , y₁ ) 𝓝 0 := by simpa using hφ.tendsto ( 0 , y₁ )
          have lim := lim2.comp lim1
          rw [ tendsto_prod_self_iff ] at lim
          simp_rw [ ball_mem_comm ]
          exact lim W' W'_nhd
#align dense_inducing.extend_Z_bilin_aux dense_inducing.extend_Z_bilin_aux

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x x' «expr ∈ » U₁) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y y' «expr ∈ » V₁) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x x' «expr ∈ » U) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y y' «expr ∈ » V) -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.private "private")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_Z_bilin_key [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x₀] [":" `α] [] ")")
        (Term.explicitBinder "(" [`y₀] [":" `γ] [] ")")]
       (Term.typeSpec
        ":"
        (Std.ExtendedBinder.«term∃__,_»
         "∃"
         (Lean.binderIdent `U)
         («binderTerm∈_»
          "∈"
          (Term.app `comap [`e (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])]))
         ","
         (Std.ExtendedBinder.«term∃__,_»
          "∃"
          (Lean.binderIdent `V)
          («binderTerm∈_»
           "∈"
           (Term.app `comap [`f (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀])]))
          ","
          (Term.forall
           "∀"
           [(Term.explicitBinder "(" [`x] [] [] ")")
            (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `U)] [] ")")
            (Term.explicitBinder "(" [`x'] [] [] ")")
            (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x' "∈" `U)] [] ")")]
           []
           ","
           (Term.forall
            "∀"
            [(Term.explicitBinder "(" [`y] [] [] ")")
             (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `y "∈" `V)] [] ")")
             (Term.explicitBinder "(" [`y'] [] [] ")")
             (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `y' "∈" `V)] [] ")")]
            []
            ","
            («term_∈_»
             («term_-_»
              (Term.app
               (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
               [(Term.tuple "(" [`x' "," [`y']] ")")])
              "-"
              (Term.app
               (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
               [(Term.tuple "(" [`x "," [`y]] ")")]))
             "∈"
             `W')))))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Nx
              []
              []
              ":="
              (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `Ny
              []
              []
              ":="
              (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `dp [] [] ":=" (Term.app `DenseInducing.prod [`de `df]))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `ee
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`u]
                [(Term.typeSpec ":" («term_×_» `β "×" `β))]
                "=>"
                (Term.tuple
                 "("
                 [(Term.app `e [(Term.proj `u "." (fieldIdx "1"))])
                  ","
                  [(Term.app `e [(Term.proj `u "." (fieldIdx "2"))])]]
                 ")"))))))
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `ff
              []
              []
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`u]
                [(Term.typeSpec ":" («term_×_» `δ "×" `δ))]
                "=>"
                (Term.tuple
                 "("
                 [(Term.app `f [(Term.proj `u "." (fieldIdx "1"))])
                  ","
                  [(Term.app `f [(Term.proj `u "." (fieldIdx "2"))])]]
                 ")"))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim_φ []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `Filter.Tendsto
                 [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                  (Term.app
                   (TopologicalSpace.Topology.Basic.nhds "𝓝")
                   [(Term.tuple "(" [(num "0") "," [(num "0")]] ")")])
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.Simpa.simpa
                   "simpa"
                   []
                   []
                   (Std.Tactic.Simpa.simpaArgsRest
                    []
                    []
                    []
                    []
                    ["using"
                     (Term.app
                      `hφ.tendsto
                      [(Term.tuple "(" [(num "0") "," [(num "0")]] ")")])]))]))))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`lim_φ_sub_sub []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `tendsto
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`p]
                    [(Term.typeSpec
                      ":"
                      («term_×_» («term_×_» `β "×" `β) "×" («term_×_» `δ "×" `δ)))]
                    "=>"
                    (Term.app
                     (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                     [(Term.tuple
                       "("
                       [(«term_-_»
                         (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))
                         "-"
                         (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1")))
                        ","
                        [(«term_-_»
                          (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))
                          "-"
                          (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                       ")")])))
                  (Filter.Order.Filter.Prod.filter.prod
                   («term_<|_»
                    (Term.app `comap [`ee])
                    "<|"
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.tuple "(" [`x₀ "," [`x₀]] ")")]))
                   " ×ᶠ "
                   («term_<|_»
                    (Term.app `comap [`ff])
                    "<|"
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.tuple "(" [`y₀ "," [`y₀]] ")")])))
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`lim_sub_sub []]
                     [(Term.typeSpec
                       ":"
                       (Term.app
                        `tendsto
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`p]
                           [(Term.typeSpec
                             ":"
                             («term_×_» («term_×_» `β "×" `β) "×" («term_×_» `δ "×" `δ)))]
                           "=>"
                           (Term.tuple
                            "("
                            [(«term_-_»
                              (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))
                              "-"
                              (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1")))
                             ","
                             [(«term_-_»
                               (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))
                               "-"
                               (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                            ")")))
                         (Filter.Order.Filter.Prod.filter.prod
                          (Term.app
                           `comap
                           [`ee
                            (Term.app
                             (TopologicalSpace.Topology.Basic.nhds "𝓝")
                             [(Term.tuple "(" [`x₀ "," [`x₀]] ")")])])
                          " ×ᶠ "
                          (Term.app
                           `comap
                           [`ff
                            (Term.app
                             (TopologicalSpace.Topology.Basic.nhds "𝓝")
                             [(Term.tuple "(" [`y₀ "," [`y₀]] ")")])]))
                         (Filter.Order.Filter.Prod.filter.prod
                          (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])
                          " ×ᶠ "
                          (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))]))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.tacticHave_
                          "have"
                          (Term.haveDecl
                           (Term.haveIdDecl
                            []
                            []
                            ":="
                            (Term.app
                             `Filter.prod_mono
                             [(Term.app `tendsto_sub_comap_self [`de `x₀])
                              (Term.app `tendsto_sub_comap_self [`df `y₀])]))))
                         []
                         (Std.Tactic.tacticRwa__
                          "rwa"
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_map_map_eq)] "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`lim_sub_sub] []))])
                  []
                  (Tactic.exact "exact" (Term.app `tendsto.comp [`lim_φ `lim_sub_sub]))]))))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `exists_nhds_zero_quarter [`W'_nhd]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W_nhd)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W4)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Std.ExtendedBinder.«term∃__,_»
                 "∃"
                 (Lean.binderIdent `U₁)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `comap
                   [`e (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])]))
                 ","
                 (Std.ExtendedBinder.«term∃__,_»
                  "∃"
                  (Lean.binderIdent `V₁)
                  («binderTerm∈_»
                   "∈"
                   (Term.app
                    `comap
                    [`f (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀])]))
                  ","
                  (Term.forall
                   "∀"
                   [(Term.explicitBinder "(" [`x] [] [] ")")
                    (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `U₁)] [] ")")
                    (Term.explicitBinder "(" [`x'] [] [] ")")
                    (Term.explicitBinder
                     "("
                     [(Term.hole "_")]
                     [":" («term_∈_» `x' "∈" `U₁)]
                     []
                     ")")]
                   []
                   ","
                   (Term.forall
                    "∀"
                    [(Term.explicitBinder "(" [`y] [] [] ")")
                     (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `y "∈" `V₁)] [] ")")
                     (Term.explicitBinder "(" [`y'] [] [] ")")
                     (Term.explicitBinder
                      "("
                      [(Term.hole "_")]
                      [":" («term_∈_» `y' "∈" `V₁)]
                      []
                      ")")]
                    []
                    ","
                    («term_∈_»
                     (Term.app
                      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                      [(Term.tuple "(" [(«term_-_» `x' "-" `x) "," [(«term_-_» `y' "-" `y)]] ")")])
                     "∈"
                     `W))))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     []
                     []
                     ":="
                     (Term.app
                      (Term.proj `tendsto_prod_iff "." (fieldIdx "1"))
                      [`lim_φ_sub_sub `W `W_nhd]))))
                  []
                  (Std.Tactic.tacticRepeat'_
                   "repeat'"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `nhds_prod_eq)
                         ","
                         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_comap_comap_eq)]
                        "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `this)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_in)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_in)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`U_in `V_in] []))])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `U_in)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `U₁_in)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HU₁)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `V_in)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.one `V₁_in)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HV₁)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.«tacticExists_,,» "exists" [`U₁ "," `U₁_in "," `V₁ "," `V₁_in])
                  []
                  (Tactic.intro "intro" [`x `x_in `x' `x'_in `y `y_in `y' `y'_in])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `H
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app `HU₁ [(Term.app `mk_mem_prod [`x_in `x'_in])])
                     (Term.app `HV₁ [(Term.app `mk_mem_prod [`y_in `y'_in])])]))]))))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] `this)]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁_nhd)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁_nhd)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                   [])]
                 "⟩")])
              [])])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁_in)])
                  [])]
                "⟩")])]
            [":" `U₁.nonempty]
            [":="
             [(Term.app
               (Term.proj (Term.app `de.comap_nhds_ne_bot [(Term.hole "_")]) "." `nonempty_of_mem)
               [`U₁_nhd])]])
           []
           (Std.Tactic.obtain
            "obtain"
            [(Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₁_in)])
                  [])]
                "⟩")])]
            [":" `V₁.nonempty]
            [":="
             [(Term.app
               (Term.proj (Term.app `df.comap_nhds_ne_bot [(Term.hole "_")]) "." `nonempty_of_mem)
               [`V₁_nhd])]])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`cont_flip []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `Continuous
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`p]
                    [(Term.typeSpec ":" («term_×_» `δ "×" `β))]
                    "=>"
                    (Term.app
                     `φ.flip
                     [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])))]))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticShow_
                   "show"
                   (Term.app
                    `Continuous
                    [(«term_∘_»
                      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                      "∘"
                      `Prod.swap)]))
                  []
                  (Tactic.exact "exact" (Term.app `hφ.comp [`continuous_swap]))]))))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `extend_Z_bilin_aux [`de `df `hφ `W_nhd `x₀ `y₁]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂_nhd)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HU)])
                   [])]
                 "⟩")])
              [])])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app `extend_Z_bilin_aux [`df `de `cont_flip `W_nhd `y₀ `x₁]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂_nhd)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HV)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.«tacticExists_,,»
            "exists"
            [(«term_∩_» `U₁ "∩" `U₂)
             ","
             (Term.app `inter_mem [`U₁_nhd `U₂_nhd])
             ","
             («term_∩_» `V₁ "∩" `V₂)
             ","
             (Term.app `inter_mem [`V₁_nhd `V₂_nhd])])
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₂)])
                 [])]
               "⟩"))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x'))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₂)])
                 [])]
               "⟩"))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₂)])
                 [])]
               "⟩"))
             (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y'))
             (Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₂)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`key_formula []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 («term_-_» (Term.app `φ [`x' `y']) "-" (Term.app `φ [`x `y]))
                 "="
                 («term_+_»
                  («term_+_»
                   («term_+_»
                    (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
                    "+"
                    (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
                   "+"
                   (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
                  "+"
                  (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.abel "abel" [] [])]))))))
           []
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `key_formula)] "]") [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `HU [`x `xU₂ `x' `x'U₂]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₂ []]
              []
              ":="
              (Term.app `H [`x `xU₁ `x' `x'U₁ `y₁ `y₁_in `y' `y'V₁]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`h₃ []] [] ":=" (Term.app `HV [`y `yV₂ `y' `y'V₂]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h₄ []]
              []
              ":="
              (Term.app `H [`x₁ `x₁_in `x `xU₁ `y `yV₁ `y' `y'V₁]))))
           []
           (Tactic.exact "exact" (Term.app `W4 [`h₁ `h₂ `h₃ `h₄]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Nx
             []
             []
             ":="
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `Ny
             []
             []
             ":="
             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `dp [] [] ":=" (Term.app `DenseInducing.prod [`de `df]))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `ee
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`u]
               [(Term.typeSpec ":" («term_×_» `β "×" `β))]
               "=>"
               (Term.tuple
                "("
                [(Term.app `e [(Term.proj `u "." (fieldIdx "1"))])
                 ","
                 [(Term.app `e [(Term.proj `u "." (fieldIdx "2"))])]]
                ")"))))))
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl
            (Term.letIdDecl
             `ff
             []
             []
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`u]
               [(Term.typeSpec ":" («term_×_» `δ "×" `δ))]
               "=>"
               (Term.tuple
                "("
                [(Term.app `f [(Term.proj `u "." (fieldIdx "1"))])
                 ","
                 [(Term.app `f [(Term.proj `u "." (fieldIdx "2"))])]]
                ")"))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim_φ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `Filter.Tendsto
                [(DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                 (Term.app
                  (TopologicalSpace.Topology.Basic.nhds "𝓝")
                  [(Term.tuple "(" [(num "0") "," [(num "0")]] ")")])
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Simpa.simpa
                  "simpa"
                  []
                  []
                  (Std.Tactic.Simpa.simpaArgsRest
                   []
                   []
                   []
                   []
                   ["using"
                    (Term.app
                     `hφ.tendsto
                     [(Term.tuple "(" [(num "0") "," [(num "0")]] ")")])]))]))))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`lim_φ_sub_sub []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`p]
                   [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `β) "×" («term_×_» `δ "×" `δ)))]
                   "=>"
                   (Term.app
                    (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                    [(Term.tuple
                      "("
                      [(«term_-_»
                        (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))
                        "-"
                        (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1")))
                       ","
                       [(«term_-_»
                         (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))
                         "-"
                         (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                      ")")])))
                 (Filter.Order.Filter.Prod.filter.prod
                  («term_<|_»
                   (Term.app `comap [`ee])
                   "<|"
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.tuple "(" [`x₀ "," [`x₀]] ")")]))
                  " ×ᶠ "
                  («term_<|_»
                   (Term.app `comap [`ff])
                   "<|"
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.tuple "(" [`y₀ "," [`y₀]] ")")])))
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`lim_sub_sub []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `tendsto
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`p]
                          [(Term.typeSpec
                            ":"
                            («term_×_» («term_×_» `β "×" `β) "×" («term_×_» `δ "×" `δ)))]
                          "=>"
                          (Term.tuple
                           "("
                           [(«term_-_»
                             (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))
                             "-"
                             (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1")))
                            ","
                            [(«term_-_»
                              (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))
                              "-"
                              (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1")))]]
                           ")")))
                        (Filter.Order.Filter.Prod.filter.prod
                         (Term.app
                          `comap
                          [`ee
                           (Term.app
                            (TopologicalSpace.Topology.Basic.nhds "𝓝")
                            [(Term.tuple "(" [`x₀ "," [`x₀]] ")")])])
                         " ×ᶠ "
                         (Term.app
                          `comap
                          [`ff
                           (Term.app
                            (TopologicalSpace.Topology.Basic.nhds "𝓝")
                            [(Term.tuple "(" [`y₀ "," [`y₀]] ")")])]))
                        (Filter.Order.Filter.Prod.filter.prod
                         (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])
                         " ×ᶠ "
                         (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))]))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.tacticHave_
                         "have"
                         (Term.haveDecl
                          (Term.haveIdDecl
                           []
                           []
                           ":="
                           (Term.app
                            `Filter.prod_mono
                            [(Term.app `tendsto_sub_comap_self [`de `x₀])
                             (Term.app `tendsto_sub_comap_self [`df `y₀])]))))
                        []
                        (Std.Tactic.tacticRwa__
                         "rwa"
                         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `prod_map_map_eq)] "]")
                         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])]))))))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`lim_sub_sub] []))])
                 []
                 (Tactic.exact "exact" (Term.app `tendsto.comp [`lim_φ `lim_sub_sub]))]))))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `exists_nhds_zero_quarter [`W'_nhd]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W_nhd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `W4)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Std.ExtendedBinder.«term∃__,_»
                "∃"
                (Lean.binderIdent `U₁)
                («binderTerm∈_»
                 "∈"
                 (Term.app `comap [`e (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])]))
                ","
                (Std.ExtendedBinder.«term∃__,_»
                 "∃"
                 (Lean.binderIdent `V₁)
                 («binderTerm∈_»
                  "∈"
                  (Term.app
                   `comap
                   [`f (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀])]))
                 ","
                 (Term.forall
                  "∀"
                  [(Term.explicitBinder "(" [`x] [] [] ")")
                   (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `U₁)] [] ")")
                   (Term.explicitBinder "(" [`x'] [] [] ")")
                   (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x' "∈" `U₁)] [] ")")]
                  []
                  ","
                  (Term.forall
                   "∀"
                   [(Term.explicitBinder "(" [`y] [] [] ")")
                    (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `y "∈" `V₁)] [] ")")
                    (Term.explicitBinder "(" [`y'] [] [] ")")
                    (Term.explicitBinder
                     "("
                     [(Term.hole "_")]
                     [":" («term_∈_» `y' "∈" `V₁)]
                     []
                     ")")]
                   []
                   ","
                   («term_∈_»
                    (Term.app
                     (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                     [(Term.tuple "(" [(«term_-_» `x' "-" `x) "," [(«term_-_» `y' "-" `y)]] ")")])
                    "∈"
                    `W))))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    []
                    []
                    ":="
                    (Term.app
                     (Term.proj `tendsto_prod_iff "." (fieldIdx "1"))
                     [`lim_φ_sub_sub `W `W_nhd]))))
                 []
                 (Std.Tactic.tacticRepeat'_
                  "repeat'"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `nhds_prod_eq)
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `prod_comap_comap_eq)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])))
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `this)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_in)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_in)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`U_in `V_in] []))])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `U_in)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁_in)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HU₁)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Std.Tactic.rcases
                  "rcases"
                  [(Tactic.casesTarget [] `V_in)]
                  ["with"
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁_in)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HV₁)])
                         [])]
                       "⟩")])
                    [])])
                 []
                 (Tactic.«tacticExists_,,» "exists" [`U₁ "," `U₁_in "," `V₁ "," `V₁_in])
                 []
                 (Tactic.intro "intro" [`x `x_in `x' `x'_in `y `y_in `y' `y'_in])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `H
                   [(Term.hole "_")
                    (Term.hole "_")
                    (Term.app `HU₁ [(Term.app `mk_mem_prod [`x_in `x'_in])])
                    (Term.app `HV₁ [(Term.app `mk_mem_prod [`y_in `y'_in])])]))]))))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `this)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₁_nhd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₁_nhd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₁_in)])
                 [])]
               "⟩")])]
           [":" `U₁.nonempty]
           [":="
            [(Term.app
              (Term.proj (Term.app `de.comap_nhds_ne_bot [(Term.hole "_")]) "." `nonempty_of_mem)
              [`U₁_nhd])]])
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₁)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₁_in)])
                 [])]
               "⟩")])]
           [":" `V₁.nonempty]
           [":="
            [(Term.app
              (Term.proj (Term.app `df.comap_nhds_ne_bot [(Term.hole "_")]) "." `nonempty_of_mem)
              [`V₁_nhd])]])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`cont_flip []]
             [(Term.typeSpec
               ":"
               (Term.app
                `Continuous
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`p]
                   [(Term.typeSpec ":" («term_×_» `δ "×" `β))]
                   "=>"
                   (Term.app
                    `φ.flip
                    [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])))]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.tacticShow_
                  "show"
                  (Term.app
                   `Continuous
                   [(«term_∘_»
                     (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                     "∘"
                     `Prod.swap)]))
                 []
                 (Tactic.exact "exact" (Term.app `hφ.comp [`continuous_swap]))]))))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `extend_Z_bilin_aux [`de `df `hφ `W_nhd `x₀ `y₁]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂_nhd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HU)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app `extend_Z_bilin_aux [`df `de `cont_flip `W_nhd `y₀ `x₁]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂_nhd)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HV)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.«tacticExists_,,»
           "exists"
           [(«term_∩_» `U₁ "∩" `U₂)
            ","
            (Term.app `inter_mem [`U₁_nhd `U₂_nhd])
            ","
            («term_∩_» `V₁ "∩" `V₂)
            ","
            (Term.app `inter_mem [`V₁_nhd `V₂_nhd])])
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₂)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x'))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₂)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₂)])
                [])]
              "⟩"))
            (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y'))
            (Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₁)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₂)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`key_formula []]
             [(Term.typeSpec
               ":"
               («term_=_»
                («term_-_» (Term.app `φ [`x' `y']) "-" (Term.app `φ [`x `y]))
                "="
                («term_+_»
                 («term_+_»
                  («term_+_»
                   (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
                   "+"
                   (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
                  "+"
                  (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
                 "+"
                 (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)]))))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.abel "abel" [] [])]))))))
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `key_formula)] "]") [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `HU [`x `xU₂ `x' `x'U₂]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₂ []]
             []
             ":="
             (Term.app `H [`x `xU₁ `x' `x'U₁ `y₁ `y₁_in `y' `y'V₁]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`h₃ []] [] ":=" (Term.app `HV [`y `yV₂ `y' `y'V₂]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h₄ []]
             []
             ":="
             (Term.app `H [`x₁ `x₁_in `x `xU₁ `y `yV₁ `y' `y'V₁]))))
          []
          (Tactic.exact "exact" (Term.app `W4 [`h₁ `h₂ `h₃ `h₄]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `W4 [`h₁ `h₂ `h₃ `h₄]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `W4 [`h₁ `h₂ `h₃ `h₄])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₄
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₃
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `W4
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [`h₄ []] [] ":=" (Term.app `H [`x₁ `x₁_in `x `xU₁ `y `yV₁ `y' `y'V₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`x₁ `x₁_in `x `xU₁ `y `yV₁ `y' `y'V₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y'V₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `yV₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xU₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x₁_in
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`h₃ []] [] ":=" (Term.app `HV [`y `yV₂ `y' `y'V₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HV [`y `yV₂ `y' `y'V₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y'V₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `yV₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HV
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl [`h₂ []] [] ":=" (Term.app `H [`x `xU₁ `x' `x'U₁ `y₁ `y₁_in `y' `y'V₁]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`x `xU₁ `x' `x'U₁ `y₁ `y₁_in `y' `y'V₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y'V₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₁_in
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'U₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xU₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`h₁ []] [] ":=" (Term.app `HU [`x `xU₂ `x' `x'U₂]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `HU [`x `xU₂ `x' `x'U₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x'U₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `xU₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `HU
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `key_formula)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key_formula
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`key_formula []]
         [(Term.typeSpec
           ":"
           («term_=_»
            («term_-_» (Term.app `φ [`x' `y']) "-" (Term.app `φ [`x `y]))
            "="
            («term_+_»
             («term_+_»
              («term_+_»
               (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
               "+"
               (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
              "+"
              (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
             "+"
             (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)]))))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.abel "abel" [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" [] [] [] [] []) [] (Tactic.abel "abel" [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.abel "abel" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       («term_-_» (Term.app `φ [`x' `y']) "-" (Term.app `φ [`x `y]))
       "="
       («term_+_»
        («term_+_»
         («term_+_»
          (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
          "+"
          (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
         "+"
         (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
        "+"
        (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       («term_+_»
        («term_+_»
         (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
         "+"
         (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
        "+"
        (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
       "+"
       (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [(«term_-_» `x "-" `x₁) («term_-_» `y' "-" `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `y' "-" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `y' "-" `y) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» `x "-" `x₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₁
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `x "-" `x₁) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       («term_+_»
        (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
        "+"
        (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
       "+"
       (Term.app `φ [`x₁ («term_-_» `y' "-" `y)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`x₁ («term_-_» `y' "-" `y)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `y' "-" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `y' "-" `y) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_+_»
       (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
       "+"
       (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [(«term_-_» `x' "-" `x) («term_-_» `y' "-" `y₁)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» `y' "-" `y₁)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `y' "-" `y₁) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» `x' "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `x' "-" `x) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `φ [(«term_-_» `x' "-" `x) `y₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» `x' "-" `x)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_-_» `x' "-" `x) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 65, (some 66, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_-_» (Term.app `φ [`x' `y']) "-" (Term.app `φ [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `φ [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `φ [`x' `y'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `φ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 66, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₁)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `xU₂)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x'))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₁)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x'U₂)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₁)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `yV₂)])
            [])]
          "⟩"))
        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y'))
        (Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₁)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y'V₂)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tacticExists_,,»
       "exists"
       [(«term_∩_» `U₁ "∩" `U₂)
        ","
        (Term.app `inter_mem [`U₁_nhd `U₂_nhd])
        ","
        («term_∩_» `V₁ "∩" `V₂)
        ","
        (Term.app `inter_mem [`V₁_nhd `V₂_nhd])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inter_mem [`V₁_nhd `V₂_nhd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V₂_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `V₁_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inter_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» `V₁ "∩" `V₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V₂
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `V₁
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inter_mem [`U₁_nhd `U₂_nhd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U₂_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U₁_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inter_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∩_» `U₁ "∩" `U₂)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U₂
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `U₁
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `extend_Z_bilin_aux [`df `de `cont_flip `W_nhd `y₀ `x₁]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V₂_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HV)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `extend_Z_bilin_aux [`df `de `cont_flip `W_nhd `y₀ `x₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `W_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `cont_flip
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `de
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `df
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extend_Z_bilin_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `extend_Z_bilin_aux [`de `df `hφ `W_nhd `x₀ `y₁]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U₂_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `HU)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `extend_Z_bilin_aux [`de `df `hφ `W_nhd `x₀ `y₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `W_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `df
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `de
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extend_Z_bilin_aux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cont_flip []]
         [(Term.typeSpec
           ":"
           (Term.app
            `Continuous
            [(Term.fun
              "fun"
              (Term.basicFun
               [`p]
               [(Term.typeSpec ":" («term_×_» `δ "×" `β))]
               "=>"
               (Term.app
                `φ.flip
                [(Term.proj `p "." (fieldIdx "1")) (Term.proj `p "." (fieldIdx "2"))])))]))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticShow_
              "show"
              (Term.app
               `Continuous
               [(«term_∘_»
                 (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                 "∘"
                 `Prod.swap)]))
             []
             (Tactic.exact "exact" (Term.app `hφ.comp [`continuous_swap]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticShow_
           "show"
           (Term.app
            `Continuous
            [(«term_∘_» (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ") "∘" `Prod.swap)]))
          []
          (Tactic.exact "exact" (Term.app `hφ.comp [`continuous_swap]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hφ.comp [`continuous_swap]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hφ.comp [`continuous_swap])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_swap
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hφ.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticShow_
       "show"
       (Term.app
        `Continuous
        [(«term_∘_» (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ") "∘" `Prod.swap)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Continuous
       [(«term_∘_» (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ") "∘" `Prod.swap)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∘_» (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ") "∘" `Prod.swap)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Prod.swap
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'DenseInducing.Topology.Algebra.UniformGroup.termΦ._@.Topology.Algebra.UniformGroup._hyg.32'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
private
  theorem
    extend_Z_bilin_key
    ( x₀ : α ) ( y₀ : γ )
      :
        ∃
          U
          ∈ comap e 𝓝 x₀
          ,
          ∃
            V
            ∈ comap f 𝓝 y₀
            ,
            ∀
              ( x ) ( _ : x ∈ U ) ( x' ) ( _ : x' ∈ U )
              ,
              ∀ ( y ) ( _ : y ∈ V ) ( y' ) ( _ : y' ∈ V ) , Φ ( x' , y' ) - Φ ( x , y ) ∈ W'
    :=
      by
        let Nx := 𝓝 x₀
          let Ny := 𝓝 y₀
          let dp := DenseInducing.prod de df
          let ee := fun u : β × β => ( e u . 1 , e u . 2 )
          let ff := fun u : δ × δ => ( f u . 1 , f u . 2 )
          have lim_φ : Filter.Tendsto Φ 𝓝 ( 0 , 0 ) 𝓝 0 := by simpa using hφ.tendsto ( 0 , 0 )
          have
            lim_φ_sub_sub
              :
                tendsto
                  fun p : β × β × δ × δ => Φ ( p . 1 . 2 - p . 1 . 1 , p . 2 . 2 - p . 2 . 1 )
                    comap ee <| 𝓝 ( x₀ , x₀ ) ×ᶠ comap ff <| 𝓝 ( y₀ , y₀ )
                    𝓝 0
              :=
              by
                have
                    lim_sub_sub
                      :
                        tendsto
                          fun p : β × β × δ × δ => ( p . 1 . 2 - p . 1 . 1 , p . 2 . 2 - p . 2 . 1 )
                            comap ee 𝓝 ( x₀ , x₀ ) ×ᶠ comap ff 𝓝 ( y₀ , y₀ )
                            𝓝 0 ×ᶠ 𝓝 0
                      :=
                      by
                        have
                            :=
                              Filter.prod_mono
                                tendsto_sub_comap_self de x₀ tendsto_sub_comap_self df y₀
                          rwa [ prod_map_map_eq ] at this
                  rw [ ← nhds_prod_eq ] at lim_sub_sub
                  exact tendsto.comp lim_φ lim_sub_sub
          rcases exists_nhds_zero_quarter W'_nhd with ⟨ W , W_nhd , W4 ⟩
          have
            :
                ∃
                  U₁
                  ∈ comap e 𝓝 x₀
                  ,
                  ∃
                    V₁
                    ∈ comap f 𝓝 y₀
                    ,
                    ∀
                      ( x ) ( _ : x ∈ U₁ ) ( x' ) ( _ : x' ∈ U₁ )
                      ,
                      ∀ ( y ) ( _ : y ∈ V₁ ) ( y' ) ( _ : y' ∈ V₁ ) , Φ ( x' - x , y' - y ) ∈ W
              :=
              by
                have := tendsto_prod_iff . 1 lim_φ_sub_sub W W_nhd
                  repeat' rw [ nhds_prod_eq , ← prod_comap_comap_eq ] at this
                  rcases this with ⟨ U , U_in , V , V_in , H ⟩
                  rw [ mem_prod_same_iff ] at U_in V_in
                  rcases U_in with ⟨ U₁ , U₁_in , HU₁ ⟩
                  rcases V_in with ⟨ V₁ , V₁_in , HV₁ ⟩
                  exists U₁ , U₁_in , V₁ , V₁_in
                  intro x x_in x' x'_in y y_in y' y'_in
                  exact H _ _ HU₁ mk_mem_prod x_in x'_in HV₁ mk_mem_prod y_in y'_in
          rcases this with ⟨ U₁ , U₁_nhd , V₁ , V₁_nhd , H ⟩
          obtain ⟨ x₁ , x₁_in ⟩ : U₁.nonempty := de.comap_nhds_ne_bot _ . nonempty_of_mem U₁_nhd
          obtain ⟨ y₁ , y₁_in ⟩ : V₁.nonempty := df.comap_nhds_ne_bot _ . nonempty_of_mem V₁_nhd
          have
            cont_flip
              : Continuous fun p : δ × β => φ.flip p . 1 p . 2
              :=
              by show Continuous Φ ∘ Prod.swap exact hφ.comp continuous_swap
          rcases extend_Z_bilin_aux de df hφ W_nhd x₀ y₁ with ⟨ U₂ , U₂_nhd , HU ⟩
          rcases extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁ with ⟨ V₂ , V₂_nhd , HV ⟩
          exists U₁ ∩ U₂ , inter_mem U₁_nhd U₂_nhd , V₁ ∩ V₂ , inter_mem V₁_nhd V₂_nhd
          rintro x ⟨ xU₁ , xU₂ ⟩ x' ⟨ x'U₁ , x'U₂ ⟩ y ⟨ yV₁ , yV₂ ⟩ y' ⟨ y'V₁ , y'V₂ ⟩
          have
            key_formula
              : φ x' y' - φ x y = φ x' - x y₁ + φ x' - x y' - y₁ + φ x₁ y' - y + φ x - x₁ y' - y
              :=
              by simp abel
          rw [ key_formula ]
          have h₁ := HU x xU₂ x' x'U₂
          have h₂ := H x xU₁ x' x'U₁ y₁ y₁_in y' y'V₁
          have h₃ := HV y yV₂ y' y'V₂
          have h₄ := H x₁ x₁_in x xU₁ y yV₁ y' y'V₁
          exact W4 h₁ h₂ h₃ h₄
#align dense_inducing.extend_Z_bilin_key dense_inducing.extend_Z_bilin_key

omit W'_nhd

open DenseInducing

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Bourbaki GT III.6.5 Theorem I:\nℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.\nNote: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `extend_Z_bilin [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.app
           `extend
           [(Term.app (Term.proj `de "." `Prod) [`df])
            (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app `continuous_extend_of_cauchy [(Term.hole "_") (Term.hole "_")]))
           []
           (Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.constructor "constructor")
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply "apply" `ne_bot.map)
             []
             (Tactic.apply "apply" `comap_ne_bot)
             []
             (Tactic.intro "intro" [`U `h])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj `mem_closure_iff_nhds "." (fieldIdx "1"))
                 [(Term.app
                   (Term.proj (Term.app `de.prod [`df]) "." `dense)
                   [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
                  `U
                  `h]))]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_in)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_x)])
                          [])]
                        "⟩")])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.«tacticExists_,,» "exists" [`z])
             []
             (Tactic.cc "cc")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_≤_»
                (Term.app
                 `map
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`p]
                    [(Term.typeSpec
                      ":"
                      («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
                    "=>"
                    («term_-_»
                     (Term.app
                      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                      [(Term.proj `p "." (fieldIdx "2"))])
                     "-"
                     (Term.app
                      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                      [(Term.proj `p "." (fieldIdx "1"))]))))
                  (Term.app
                   `comap
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`p]
                      [(Term.typeSpec
                        ":"
                        («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
                      "=>"
                      (Term.tuple
                       "("
                       [(Term.tuple
                         "("
                         [(Term.app
                           `e
                           [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                          ","
                          [(Term.app
                            `f
                            [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
                         ")")
                        ","
                        [(Term.tuple
                          "("
                          [(Term.app
                            `e
                            [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                           ","
                           [(Term.app
                             `f
                             [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                          ")")]]
                       ")")))
                    (Filter.Order.Filter.Prod.filter.prod
                     (Term.app
                      (TopologicalSpace.Topology.Basic.nhds "𝓝")
                      [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
                     " ×ᶠ "
                     (Term.app
                      (TopologicalSpace.Topology.Basic.nhds "𝓝")
                      [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
                "≤"
                (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] (Term.app `uniformity_eq_comap_nhds_zero [`G]))
                      ","
                      (Tactic.rwRule [] `prod_map_map_eq)
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_le_iff_le_comap)
                      ","
                      (Tactic.rwRule [] `Filter.map_map)
                      ","
                      (Tactic.rwRule [] `prod_comap_comap_eq)]
                     "]")
                    [])])))))
             []
             (Tactic.intro "intro" [`W' `W'_nhd])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`key []]
                []
                ":="
                (Term.app `extend_Z_bilin_key [`de `df `hφ `W'_nhd `x₀ `y₀]))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `key)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_nhd)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_nhd)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`U_nhd] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `U_nhd)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_nhd)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_sub)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`V_nhd] []))])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `V_nhd)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_nhd)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_sub)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mem_map)
                ","
                (Tactic.rwRule [] `mem_comap)
                ","
                (Tactic.rwRule [] `nhds_prod_eq)]
               "]")
              [])
             []
             (Tactic.«tacticExists_,,»
              "exists"
              [(LowerSet.Order.UpperLower.lower_set.prod
                (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
                " ×ˢ "
                (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V'))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]")
              [])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `exists_prop)] "]"]
              [])
             []
             (Tactic.constructor "constructor")
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.change
                "change"
                («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
                [(Tactic.location "at" (Tactic.locationHyp [`U'_nhd] []))])
               []
               (Tactic.change
                "change"
                («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
                [(Tactic.location "at" (Tactic.locationHyp [`V'_nhd] []))])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl [] [] ":=" (Term.app `prod_mem_prod [`U'_nhd `V'_nhd]))))
               []
               (Mathlib.Tactic.Tauto.tauto "tauto" [])])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`p `h'])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Set.mem_preimage)
                  ","
                  (Tactic.simpLemma [] [] `Set.prod_mk_mem_set_prod_eq)]
                 "]"]
                [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `p)]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                            [])]
                          "⟩")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                            [])]
                          "⟩")])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.«tactic_<;>_»
                (Tactic.apply "apply" `h)
                "<;>"
                (Mathlib.Tactic.Tauto.tauto "tauto" []))])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app `continuous_extend_of_cauchy [(Term.hole "_") (Term.hole "_")]))
          []
          (Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x₀)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.constructor "constructor")
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply "apply" `ne_bot.map)
            []
            (Tactic.apply "apply" `comap_ne_bot)
            []
            (Tactic.intro "intro" [`U `h])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj `mem_closure_iff_nhds "." (fieldIdx "1"))
                [(Term.app
                  (Term.proj (Term.app `de.prod [`df]) "." `dense)
                  [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
                 `U
                 `h]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x_in)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z_x)])
                         [])]
                       "⟩")])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.«tacticExists_,,» "exists" [`z])
            []
            (Tactic.cc "cc")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_≤_»
               (Term.app
                `map
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`p]
                   [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
                   "=>"
                   («term_-_»
                    (Term.app
                     (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                     [(Term.proj `p "." (fieldIdx "2"))])
                    "-"
                    (Term.app
                     (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                     [(Term.proj `p "." (fieldIdx "1"))]))))
                 (Term.app
                  `comap
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`p]
                     [(Term.typeSpec
                       ":"
                       («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
                     "=>"
                     (Term.tuple
                      "("
                      [(Term.tuple
                        "("
                        [(Term.app
                          `e
                          [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                         ","
                         [(Term.app
                           `f
                           [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
                        ")")
                       ","
                       [(Term.tuple
                         "("
                         [(Term.app
                           `e
                           [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                          ","
                          [(Term.app
                            `f
                            [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                         ")")]]
                      ")")))
                   (Filter.Order.Filter.Prod.filter.prod
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
                    " ×ᶠ "
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
               "≤"
               (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Std.Tactic.tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `uniformity_eq_comap_nhds_zero [`G]))
                     ","
                     (Tactic.rwRule [] `prod_map_map_eq)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_le_iff_le_comap)
                     ","
                     (Tactic.rwRule [] `Filter.map_map)
                     ","
                     (Tactic.rwRule [] `prod_comap_comap_eq)]
                    "]")
                   [])])))))
            []
            (Tactic.intro "intro" [`W' `W'_nhd])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`key []]
               []
               ":="
               (Term.app `extend_Z_bilin_key [`de `df `hφ `W'_nhd `x₀ `y₀]))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `key)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_nhd)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_nhd)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`U_nhd] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `U_nhd)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_nhd)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_sub)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`V_nhd] []))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `V_nhd)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_nhd)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_sub)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mem_map)
               ","
               (Tactic.rwRule [] `mem_comap)
               ","
               (Tactic.rwRule [] `nhds_prod_eq)]
              "]")
             [])
            []
            (Tactic.«tacticExists_,,»
             "exists"
             [(LowerSet.Order.UpperLower.lower_set.prod
               (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
               " ×ˢ "
               (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V'))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]")
             [])
            []
            (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `exists_prop)] "]"] [])
            []
            (Tactic.constructor "constructor")
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.change
               "change"
               («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
               [(Tactic.location "at" (Tactic.locationHyp [`U'_nhd] []))])
              []
              (Tactic.change
               "change"
               («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
               [(Tactic.location "at" (Tactic.locationHyp [`V'_nhd] []))])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl [] [] ":=" (Term.app `prod_mem_prod [`U'_nhd `V'_nhd]))))
              []
              (Mathlib.Tactic.Tauto.tauto "tauto" [])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`p `h'])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Set.mem_preimage)
                 ","
                 (Tactic.simpLemma [] [] `Set.prod_mk_mem_set_prod_eq)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `p)]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                           [])]
                         "⟩")])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.«tactic_<;>_»
               (Tactic.apply "apply" `h)
               "<;>"
               (Mathlib.Tactic.Tauto.tauto "tauto" []))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_≤_»
           (Term.app
            `map
            [(Term.fun
              "fun"
              (Term.basicFun
               [`p]
               [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
               "=>"
               («term_-_»
                (Term.app
                 (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                 [(Term.proj `p "." (fieldIdx "2"))])
                "-"
                (Term.app
                 (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
                 [(Term.proj `p "." (fieldIdx "1"))]))))
             (Term.app
              `comap
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`p]
                 [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
                 "=>"
                 (Term.tuple
                  "("
                  [(Term.tuple
                    "("
                    [(Term.app
                      `e
                      [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                     ","
                     [(Term.app
                       `f
                       [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
                    ")")
                   ","
                   [(Term.tuple
                     "("
                     [(Term.app
                       `e
                       [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                      ","
                      [(Term.app
                        `f
                        [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                     ")")]]
                  ")")))
               (Filter.Order.Filter.Prod.filter.prod
                (Term.app
                 (TopologicalSpace.Topology.Basic.nhds "𝓝")
                 [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
                " ×ᶠ "
                (Term.app
                 (TopologicalSpace.Topology.Basic.nhds "𝓝")
                 [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
           "≤"
           (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `uniformity_eq_comap_nhds_zero [`G]))
                 ","
                 (Tactic.rwRule [] `prod_map_map_eq)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_le_iff_le_comap)
                 ","
                 (Tactic.rwRule [] `Filter.map_map)
                 ","
                 (Tactic.rwRule [] `prod_comap_comap_eq)]
                "]")
               [])])))))
        []
        (Tactic.intro "intro" [`W' `W'_nhd])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`key []]
           []
           ":="
           (Term.app `extend_Z_bilin_key [`de `df `hφ `W'_nhd `x₀ `y₀]))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `key)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_nhd)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_nhd)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`U_nhd] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `U_nhd)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U')])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_nhd)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_sub)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`V_nhd] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `V_nhd)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_nhd)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_sub)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `mem_map)
           ","
           (Tactic.rwRule [] `mem_comap)
           ","
           (Tactic.rwRule [] `nhds_prod_eq)]
          "]")
         [])
        []
        (Tactic.«tacticExists_,,»
         "exists"
         [(LowerSet.Order.UpperLower.lower_set.prod
           (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
           " ×ˢ "
           (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V'))])
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]") [])
        []
        (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `exists_prop)] "]"] [])
        []
        (Tactic.constructor "constructor")
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.change
           "change"
           («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
           [(Tactic.location "at" (Tactic.locationHyp [`U'_nhd] []))])
          []
          (Tactic.change
           "change"
           («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
           [(Tactic.location "at" (Tactic.locationHyp [`V'_nhd] []))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `prod_mem_prod [`U'_nhd `V'_nhd]))))
          []
          (Mathlib.Tactic.Tauto.tauto "tauto" [])])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`p `h'])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Set.mem_preimage)
             ","
             (Tactic.simpLemma [] [] `Set.prod_mk_mem_set_prod_eq)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `p)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                       [])]
                     "⟩")])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.«tactic_<;>_»
           (Tactic.apply "apply" `h)
           "<;>"
           (Mathlib.Tactic.Tauto.tauto "tauto" []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`p `h'])
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Set.mem_preimage)
           ","
           (Tactic.simpLemma [] [] `Set.prod_mk_mem_set_prod_eq)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `p)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                     [])]
                   "⟩")])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                     [])]
                   "⟩")])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.«tactic_<;>_»
         (Tactic.apply "apply" `h)
         "<;>"
         (Mathlib.Tactic.Tauto.tauto "tauto" []))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_» (Tactic.apply "apply" `h) "<;>" (Mathlib.Tactic.Tauto.tauto "tauto" []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Tauto.tauto "tauto" [])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Tactic.apply "apply" `h)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `p)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                   [])]
                 "⟩")])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Set.mem_preimage)
         ","
         (Tactic.simpLemma [] [] `Set.prod_mk_mem_set_prod_eq)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.prod_mk_mem_set_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Set.mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`p `h'])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.change
         "change"
         («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
         [(Tactic.location "at" (Tactic.locationHyp [`U'_nhd] []))])
        []
        (Tactic.change
         "change"
         («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
         [(Tactic.location "at" (Tactic.locationHyp [`V'_nhd] []))])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `prod_mem_prod [`U'_nhd `V'_nhd]))))
        []
        (Mathlib.Tactic.Tauto.tauto "tauto" [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Tauto.tauto "tauto" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `prod_mem_prod [`U'_nhd `V'_nhd]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `prod_mem_prod [`U'_nhd `V'_nhd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `U'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `prod_mem_prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
       [(Tactic.location "at" (Tactic.locationHyp [`V'_nhd] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `V' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`y₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `V'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
       [(Tactic.location "at" (Tactic.locationHyp [`U'_nhd] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `U' "∈" (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `U'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] ["only"] ["[" [(Tactic.simpLemma [] [] `exists_prop)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_prop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_prod_same_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_prod_same_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tacticExists_,,»
       "exists"
       [(LowerSet.Order.UpperLower.lower_set.prod
         (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
         " ×ˢ "
         (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V'))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod
       (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
       " ×ˢ "
       (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V'))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V'
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      `U'
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 82 >? 82, (some 82, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V'
[PrettyPrinter.parenthesize] ...precedences are 82 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 82, term))
      `U'
[PrettyPrinter.parenthesize] ...precedences are 83 >? 1024, (none, [anonymous]) <=? (some 82, term)
[PrettyPrinter.parenthesize] ...precedences are 83 >? 82, (some 82, term) <=? (some 82, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (LowerSet.Order.UpperLower.lower_set.prod `U' " ×ˢ " `V')
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 82, (some 82, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mem_map)
         ","
         (Tactic.rwRule [] `mem_comap)
         ","
         (Tactic.rwRule [] `nhds_prod_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nhds_prod_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `V_nhd)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_sub)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V_nhd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`V_nhd] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `V_nhd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `U_nhd)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U')])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U'_sub)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U_nhd
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_comap)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`U_nhd] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U_nhd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `key)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_nhd)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `key
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`key []]
         []
         ":="
         (Term.app `extend_Z_bilin_key [`de `df `hφ `W'_nhd `x₀ `y₀]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `extend_Z_bilin_key [`de `df `hφ `W'_nhd `x₀ `y₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `W'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hφ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `df
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `de
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extend_Z_bilin_key
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`W' `W'_nhd])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `W'_nhd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `W'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        («term_≤_»
         (Term.app
          `map
          [(Term.fun
            "fun"
            (Term.basicFun
             [`p]
             [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
             "=>"
             («term_-_»
              (Term.app
               (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
               [(Term.proj `p "." (fieldIdx "2"))])
              "-"
              (Term.app
               (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
               [(Term.proj `p "." (fieldIdx "1"))]))))
           (Term.app
            `comap
            [(Term.fun
              "fun"
              (Term.basicFun
               [`p]
               [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
               "=>"
               (Term.tuple
                "("
                [(Term.tuple
                  "("
                  [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                   ","
                   [(Term.app
                     `f
                     [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
                  ")")
                 ","
                 [(Term.tuple
                   "("
                   [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                    ","
                    [(Term.app
                      `f
                      [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                   ")")]]
                ")")))
             (Filter.Order.Filter.Prod.filter.prod
              (Term.app
               (TopologicalSpace.Topology.Basic.nhds "𝓝")
               [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
              " ×ᶠ "
              (Term.app
               (TopologicalSpace.Topology.Basic.nhds "𝓝")
               [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
         "≤"
         (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `uniformity_eq_comap_nhds_zero [`G]))
               ","
               (Tactic.rwRule [] `prod_map_map_eq)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_le_iff_le_comap)
               ","
               (Tactic.rwRule [] `Filter.map_map)
               ","
               (Tactic.rwRule [] `prod_comap_comap_eq)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `uniformity_eq_comap_nhds_zero [`G]))
         ","
         (Tactic.rwRule [] `prod_map_map_eq)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_le_iff_le_comap)
         ","
         (Tactic.rwRule [] `Filter.map_map)
         ","
         (Tactic.rwRule [] `prod_comap_comap_eq)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_comap_comap_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Filter.map_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_le_iff_le_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `prod_map_map_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `uniformity_eq_comap_nhds_zero [`G])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `G
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `uniformity_eq_comap_nhds_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_≤_»
       (Term.app
        `map
        [(Term.fun
          "fun"
          (Term.basicFun
           [`p]
           [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
           "=>"
           («term_-_»
            (Term.app
             (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
             [(Term.proj `p "." (fieldIdx "2"))])
            "-"
            (Term.app
             (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
             [(Term.proj `p "." (fieldIdx "1"))]))))
         (Term.app
          `comap
          [(Term.fun
            "fun"
            (Term.basicFun
             [`p]
             [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
             "=>"
             (Term.tuple
              "("
              [(Term.tuple
                "("
                [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                 ","
                 [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
                ")")
               ","
               [(Term.tuple
                 "("
                 [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                  ","
                  [(Term.app
                    `f
                    [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                 ")")]]
              ")")))
           (Filter.Order.Filter.Prod.filter.prod
            (Term.app
             (TopologicalSpace.Topology.Basic.nhds "𝓝")
             [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
            " ×ᶠ "
            (Term.app
             (TopologicalSpace.Topology.Basic.nhds "𝓝")
             [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
       "≤"
       (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `map
       [(Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
          "=>"
          («term_-_»
           (Term.app
            (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
            [(Term.proj `p "." (fieldIdx "2"))])
           "-"
           (Term.app
            (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
            [(Term.proj `p "." (fieldIdx "1"))]))))
        (Term.app
         `comap
         [(Term.fun
           "fun"
           (Term.basicFun
            [`p]
            [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
            "=>"
            (Term.tuple
             "("
             [(Term.tuple
               "("
               [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
                ","
                [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
               ")")
              ","
              [(Term.tuple
                "("
                [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
                 ","
                 [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
                ")")]]
             ")")))
          (Filter.Order.Filter.Prod.filter.prod
           (Term.app
            (TopologicalSpace.Topology.Basic.nhds "𝓝")
            [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
           " ×ᶠ "
           (Term.app
            (TopologicalSpace.Topology.Basic.nhds "𝓝")
            [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `comap
       [(Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
          "=>"
          (Term.tuple
           "("
           [(Term.tuple
             "("
             [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
              ","
              [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
             ")")
            ","
            [(Term.tuple
              "("
              [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
               ","
               [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
              ")")]]
           ")")))
        (Filter.Order.Filter.Prod.filter.prod
         (Term.app
          (TopologicalSpace.Topology.Basic.nhds "𝓝")
          [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
         " ×ᶠ "
         (Term.app
          (TopologicalSpace.Topology.Basic.nhds "𝓝")
          [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Prod.filter.prod', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Prod.filter.prod', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.Prod.filter.prod
       (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
       " ×ᶠ "
       (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`x₀ "," [`y₀]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 61 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 60, term))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.tuple', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple "(" [`x₀ "," [`y₀]] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 60 >? 1022, (some 1023, term) <=? (some 60, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 60, (some 61, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Filter.Order.Filter.Prod.filter.prod
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
      " ×ᶠ "
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
        "=>"
        (Term.tuple
         "("
         [(Term.tuple
           "("
           [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
            ","
            [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
           ")")
          ","
          [(Term.tuple
            "("
            [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
             ","
             [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
            ")")]]
         ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.tuple
         "("
         [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
          ","
          [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
         ")")
        ","
        [(Term.tuple
          "("
          [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
           ","
           [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
          ")")]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
        ","
        [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.tuple
       "("
       [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
        ","
        [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_×_» `β "×" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      («term_×_» `β "×" `δ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `δ
[PrettyPrinter.parenthesize] ...precedences are 35 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `β
[PrettyPrinter.parenthesize] ...precedences are 36 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 35, (some 35, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_×_» `β "×" `δ) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`p]
       [(Term.typeSpec
         ":"
         («term_×_» (Term.paren "(" («term_×_» `β "×" `δ) ")") "×" («term_×_» `β "×" `δ)))]
       "=>"
       (Term.tuple
        "("
        [(Term.tuple
          "("
          [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
           ","
           [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
          ")")
         ","
         [(Term.tuple
           "("
           [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
            ","
            [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
           ")")]]
        ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `comap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `comap
      [(Term.paren
        "("
        (Term.fun
         "fun"
         (Term.basicFun
          [`p]
          [(Term.typeSpec
            ":"
            («term_×_» (Term.paren "(" («term_×_» `β "×" `δ) ")") "×" («term_×_» `β "×" `δ)))]
          "=>"
          (Term.tuple
           "("
           [(Term.tuple
             "("
             [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "1"))])
              ","
              [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "1")) "." (fieldIdx "2"))])]]
             ")")
            ","
            [(Term.tuple
              "("
              [(Term.app `e [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "1"))])
               ","
               [(Term.app `f [(Term.proj (Term.proj `p "." (fieldIdx "2")) "." (fieldIdx "2"))])]]
              ")")]]
           ")")))
        ")")
       (Term.paren
        "("
        (Filter.Order.Filter.Prod.filter.prod
         (Term.app
          (TopologicalSpace.Topology.Basic.nhds "𝓝")
          [(Term.tuple "(" [`x₀ "," [`y₀]] ")")])
         " ×ᶠ "
         (Term.app
          (TopologicalSpace.Topology.Basic.nhds "𝓝")
          [(Term.tuple "(" [`x₀ "," [`y₀]] ")")]))
        ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`p]
        [(Term.typeSpec ":" («term_×_» («term_×_» `β "×" `δ) "×" («term_×_» `β "×" `δ)))]
        "=>"
        («term_-_»
         (Term.app
          (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
          [(Term.proj `p "." (fieldIdx "2"))])
         "-"
         (Term.app
          (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
          [(Term.proj `p "." (fieldIdx "1"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_»
       (Term.app
        (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
        [(Term.proj `p "." (fieldIdx "2"))])
       "-"
       (Term.app
        (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
        [(Term.proj `p "." (fieldIdx "1"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
       [(Term.proj `p "." (fieldIdx "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `p "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (DenseInducing.Topology.Algebra.UniformGroup.termΦ "Φ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'DenseInducing.Topology.Algebra.UniformGroup.termΦ', expected 'DenseInducing.Topology.Algebra.UniformGroup.termΦ._@.Topology.Algebra.UniformGroup._hyg.32'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Bourbaki GT III.6.5 Theorem I:
    ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
    Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
  theorem
    extend_Z_bilin
    : Continuous extend de . Prod df Φ
    :=
      by
        refine' continuous_extend_of_cauchy _ _
          rintro ⟨ x₀ , y₀ ⟩
          constructor
          ·
            apply ne_bot.map
              apply comap_ne_bot
              intro U h
              rcases
                mem_closure_iff_nhds . 1 de.prod df . dense ( x₀ , y₀ ) U h
                with ⟨ x , x_in , ⟨ z , z_x ⟩ ⟩
              exists z
              cc
          ·
            suffices
                map
                      fun p : β × δ × β × δ => Φ p . 2 - Φ p . 1
                        comap
                          fun
                              p
                                : β × δ × β × δ
                                =>
                                ( ( e p . 1 . 1 , f p . 1 . 2 ) , ( e p . 2 . 1 , f p . 2 . 2 ) )
                            𝓝 ( x₀ , y₀ ) ×ᶠ 𝓝 ( x₀ , y₀ )
                    ≤
                    𝓝 0
                  by
                    rwa
                      [
                        uniformity_eq_comap_nhds_zero G
                          ,
                          prod_map_map_eq
                          ,
                          ← map_le_iff_le_comap
                          ,
                          Filter.map_map
                          ,
                          prod_comap_comap_eq
                        ]
              intro W' W'_nhd
              have key := extend_Z_bilin_key de df hφ W'_nhd x₀ y₀
              rcases key with ⟨ U , U_nhd , V , V_nhd , h ⟩
              rw [ mem_comap ] at U_nhd
              rcases U_nhd with ⟨ U' , U'_nhd , U'_sub ⟩
              rw [ mem_comap ] at V_nhd
              rcases V_nhd with ⟨ V' , V'_nhd , V'_sub ⟩
              rw [ mem_map , mem_comap , nhds_prod_eq ]
              exists U' ×ˢ V' ×ˢ U' ×ˢ V'
              rw [ mem_prod_same_iff ]
              simp only [ exists_prop ]
              constructor
              ·
                change U' ∈ 𝓝 x₀ at U'_nhd
                  change V' ∈ 𝓝 y₀ at V'_nhd
                  have := prod_mem_prod U'_nhd V'_nhd
                  tauto
              ·
                intro p h'
                  simp only [ Set.mem_preimage , Set.prod_mk_mem_set_prod_eq ] at h'
                  rcases p with ⟨ ⟨ x , y ⟩ , ⟨ x' , y' ⟩ ⟩
                  apply h <;> tauto
#align dense_inducing.extend_Z_bilin DenseInducing.extend_Z_bilin

end DenseInducing

section CompleteQuotient

universe u

open TopologicalSpace Classical

/-- The quotient `G ⧸ N` of a complete first countable topological group `G` by a normal subgroup
is itself complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Because a topological group is not equipped with a `uniform_space` instance by default, we must
explicitly provide it in order to consider completeness. See `quotient_group.complete_space` for a
version in which `G` is already equipped with a uniform structure. -/
@[to_additive
      "The quotient `G ⧸ N` of a complete first countable topological additive group\n`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by\nsubspaces are complete. [N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]\n\nBecause an additive topological group is not equipped with a `uniform_space` instance by default,\nwe must explicitly provide it in order to consider completeness. See\n`quotient_add_group.complete_space` for a version in which `G` is already equipped with a uniform\nstructure."]
instance QuotientGroup.complete_space' (G : Type u) [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [FirstCountableTopology G] (N : Subgroup G) [N.normal]
    [@CompleteSpace G (TopologicalGroup.toUniformSpace G)] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) :=
  by
  /- Since `G ⧸ N` is a topological group it is a uniform space, and since `G` is first countable
    the uniformities of both `G` and `G ⧸ N` are countably generated. Moreover, we may choose a
    sequential antitone neighborhood basis `u` for `𝓝 (1 : G)` so that `(u (n + 1)) ^ 2 ⊆ u n`, and
    this descends to an antitone neighborhood basis `v` for `𝓝 (1 : G ⧸ N)`. Since `𝓤 (G ⧸ N)` is
    countably generated, it suffices to show any Cauchy sequence `x` converges. -/
  letI : UniformSpace (G ⧸ N) := TopologicalGroup.toUniformSpace (G ⧸ N)
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  haveI : (𝓤 (G ⧸ N)).IsCountablyGenerated := comap.is_countably_generated _ _
  obtain ⟨u, hu, u_mul⟩ := TopologicalGroup.exists_antitone_basis_nhds_one G
  obtain ⟨hv, v_anti⟩ := @has_antitone_basis.map _ _ _ _ _ _ (coe : G → G ⧸ N) hu
  rw [← QuotientGroup.nhds_eq N 1, QuotientGroup.coe_one] at hv
  refine' UniformSpace.complete_of_cauchy_seq_tendsto fun x hx => _
  /- Given `n : ℕ`, for sufficiently large `a b : ℕ`, given any lift of `x b`, we can find a lift
    of `x a` such that the quotient of the lifts lies in `u n`. -/
  have key₀ :
    ∀ i j : ℕ,
      ∃ M : ℕ,
        j < M ∧ ∀ a b : ℕ, M ≤ a → M ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u i ∧ x a = g' :=
    by
    have h𝓤GN : (𝓤 (G ⧸ N)).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst ∈ coe '' u i } :=
      by simpa [uniformity_eq_comap_nhds_one'] using hv.comap _
    simp only [h𝓤GN.cauchy_seq_iff, ge_iff_le, mem_set_of_eq, forall_true_left, mem_image] at hx
    intro i j
    rcases hx i with ⟨M, hM⟩
    refine' ⟨max j M + 1, (le_max_left _ _).trans_lt (lt_add_one _), fun a b ha hb g hg => _⟩
    obtain ⟨y, y_mem, hy⟩ :=
      hM a (((le_max_right j _).trans (lt_add_one _).le).trans ha) b
        (((le_max_right j _).trans (lt_add_one _).le).trans hb)
    refine'
      ⟨y⁻¹ * g, by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left] using y_mem, _⟩
    rw [QuotientGroup.coe_mul, QuotientGroup.coe_inv, hy, hg, inv_div, div_mul_cancel']
  /- Inductively construct a subsequence `φ : ℕ → ℕ` using `key₀` so that if `a b : ℕ` exceed
    `φ (n + 1)`, then we may find lifts whose quotients lie within `u n`. -/
  set φ : ℕ → ℕ := fun n => Nat.recOn n (some <| key₀ 0 0) fun k yk => some <| key₀ (k + 1) yk
  have hφ :
    ∀ n : ℕ,
      φ n < φ (n + 1) ∧
        ∀ a b : ℕ,
          φ (n + 1) ≤ a →
            φ (n + 1) ≤ b → ∀ g : G, x b = g → ∃ g' : G, g / g' ∈ u (n + 1) ∧ x a = g' :=
    fun n => some_spec (key₀ (n + 1) (φ n))
  /- Inductively construct a sequence `x' n : G` of lifts of `x (φ (n + 1))` such that quotients of
    successive terms lie in `x' n / x' (n + 1) ∈ u (n + 1)`. We actually need the proofs that each
    term is a lift to construct the next term, so we use a Σ-type. -/
  set x' : ∀ n, PSigma fun g : G => x (φ (n + 1)) = g := fun n =>
    Nat.recOn n
      ⟨some (QuotientGroup.mk_surjective (x (φ 1))),
        (some_spec (QuotientGroup.mk_surjective (x (φ 1)))).symm⟩
      fun k hk =>
      ⟨some <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd,
        (some_spec <| (hφ k).2 _ _ (hφ (k + 1)).1.le le_rfl hk.fst hk.snd).2⟩
  have hx' : ∀ n : ℕ, (x' n).fst / (x' (n + 1)).fst ∈ u (n + 1) := fun n =>
    (some_spec <| (hφ n).2 _ _ (hφ (n + 1)).1.le le_rfl (x' n).fst (x' n).snd).1
  /- The sequence `x'` is Cauchy. This is where we exploit the condition on `u`. The key idea
    is to show by decreasing induction that `x' m / x' n ∈ u m` if `m ≤ n`. -/
  have x'_cauchy : CauchySeq fun n => (x' n).fst :=
    by
    have h𝓤G : (𝓤 G).HasBasis (fun _ => True) fun i => { x | x.snd / x.fst ∈ u i } := by
      simpa [uniformity_eq_comap_nhds_one'] using hu.to_has_basis.comap _
    simp only [h𝓤G.cauchy_seq_iff', ge_iff_le, mem_set_of_eq, forall_true_left]
    exact fun m =>
      ⟨m, fun n hmn =>
        Nat.decreasingInduction'
          (fun k hkn hkm hk => u_mul k ⟨_, _, hx' k, hk, div_mul_div_cancel' _ _ _⟩) hmn
          (by simpa only [div_self'] using mem_of_mem_nhds (hu.mem _))⟩
  /- Since `G` is complete, `x'` converges to some `x₀`, and so the image of this sequence under
    the quotient map converges to `↑x₀`. The image of `x'` is a convergent subsequence of `x`, and
    since `x` is Cauchy, this implies it converges. -/
  rcases cauchy_seq_tendsto_of_complete x'_cauchy with ⟨x₀, hx₀⟩
  refine'
    ⟨↑x₀,
      tendsto_nhds_of_cauchy_seq_of_subseq hx
        (strictMono_nat_of_lt_succ fun n => (hφ (n + 1)).1).tendsto_at_top _⟩
  convert ((continuous_coinduced_rng : Continuous (coe : G → G ⧸ N)).Tendsto x₀).comp hx₀
  exact funext fun n => (x' n).snd
#align quotient_group.complete_space' QuotientGroup.complete_space'

/-- The quotient `G ⧸ N` of a complete first countable uniform group `G` by a normal subgroup
is itself complete. In constrast to `quotient_group.complete_space'`, in this version `G` is
already equipped with a uniform structure.
[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]

Even though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a
uniform structure, so it is still provided manually via `topological_group.to_uniform_space`.
In the most common use cases, this coincides (definitionally) with the uniform structure on the
quotient obtained via other means.  -/
@[to_additive
      "The quotient `G ⧸ N` of a complete first countable uniform additive group\n`G` by a normal additive subgroup is itself complete. Consequently, quotients of Banach spaces by\nsubspaces are complete. In constrast to `quotient_add_group.complete_space'`, in this version\n`G` is already equipped with a uniform structure.\n[N. Bourbaki, *General Topology*, IX.3.1 Proposition 4][bourbaki1966b]\n\nEven though `G` is equipped with a uniform structure, the quotient `G ⧸ N` does not inherit a\nuniform structure, so it is still provided manually via `topological_add_group.to_uniform_space`.\nIn the most common use case ─ quotients of normed additive commutative groups by subgroups ─\nsignificant care was taken so that the uniform structure inherent in that setting coincides\n(definitionally) with the uniform structure provided here."]
instance QuotientGroup.complete_space (G : Type u) [Group G] [us : UniformSpace G] [UniformGroup G]
    [FirstCountableTopology G] (N : Subgroup G) [N.normal] [hG : CompleteSpace G] :
    @CompleteSpace (G ⧸ N) (TopologicalGroup.toUniformSpace (G ⧸ N)) :=
  by
  rw [← @UniformGroup.to_uniform_space_eq _ us _ _] at hG
  infer_instance
#align quotient_group.complete_space QuotientGroup.complete_space

end CompleteQuotient

