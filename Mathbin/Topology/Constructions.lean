/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

! This file was ported from Lean 3 source module topology.constructions
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Maps
import Mathbin.Topology.LocallyFinite
import Mathbin.Order.Filter.Pi

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/


noncomputable section

open TopologicalSpace Set Filter Function

open Classical TopologicalSpace Filter

universe u v

variable {α : Type u} {β : Type v} {γ δ ε ζ : Type _}

section Constructions

instance {p : α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Subtype p) :=
  induced coe t

instance {r : α → α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

instance {s : Setoid α} [t : TopologicalSpace α] : TopologicalSpace (Quotient s) :=
  coinduced Quotient.mk'' t

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (α × β) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

instance [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (Sum α β) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (Sigma β) :=
  ⨆ a, coinduced (Sigma.mk a) (t₂ a)

instance PiCat.topologicalSpace {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] :
    TopologicalSpace (∀ a, β a) :=
  ⨅ a, induced (fun f => f a) (t₂ a)
#align Pi.topological_space PiCat.topologicalSpace

instance ULift.topologicalSpace [t : TopologicalSpace α] : TopologicalSpace (ULift.{v, u} α) :=
  t.induced ULift.down
#align ulift.topological_space ULift.topologicalSpace

/-!
### `additive`, `multiplicative`

The topology on those type synonyms is inherited without change.
-/


section

variable [TopologicalSpace α]

open Additive Multiplicative

instance : TopologicalSpace (Additive α) :=
  ‹TopologicalSpace α›

instance : TopologicalSpace (Multiplicative α) :=
  ‹TopologicalSpace α›

instance [DiscreteTopology α] : DiscreteTopology (Additive α) :=
  ‹DiscreteTopology α›

instance [DiscreteTopology α] : DiscreteTopology (Multiplicative α) :=
  ‹DiscreteTopology α›

theorem continuous_of_mul : Continuous (ofMul : α → Additive α) :=
  continuous_id
#align continuous_of_mul continuous_of_mul

theorem continuous_to_mul : Continuous (toMul : Additive α → α) :=
  continuous_id
#align continuous_to_mul continuous_to_mul

theorem continuous_of_add : Continuous (ofAdd : α → Multiplicative α) :=
  continuous_id
#align continuous_of_add continuous_of_add

theorem continuous_to_add : Continuous (toAdd : Multiplicative α → α) :=
  continuous_id
#align continuous_to_add continuous_to_add

theorem is_open_map_of_mul : IsOpenMap (ofMul : α → Additive α) :=
  IsOpenMap.id
#align is_open_map_of_mul is_open_map_of_mul

theorem is_open_map_to_mul : IsOpenMap (toMul : Additive α → α) :=
  IsOpenMap.id
#align is_open_map_to_mul is_open_map_to_mul

theorem is_open_map_of_add : IsOpenMap (ofAdd : α → Multiplicative α) :=
  IsOpenMap.id
#align is_open_map_of_add is_open_map_of_add

theorem is_open_map_to_add : IsOpenMap (toAdd : Multiplicative α → α) :=
  IsOpenMap.id
#align is_open_map_to_add is_open_map_to_add

theorem is_closed_map_of_mul : IsClosedMap (ofMul : α → Additive α) :=
  IsClosedMap.id
#align is_closed_map_of_mul is_closed_map_of_mul

theorem is_closed_map_to_mul : IsClosedMap (toMul : Additive α → α) :=
  IsClosedMap.id
#align is_closed_map_to_mul is_closed_map_to_mul

theorem is_closed_map_of_add : IsClosedMap (ofAdd : α → Multiplicative α) :=
  IsClosedMap.id
#align is_closed_map_of_add is_closed_map_of_add

theorem is_closed_map_to_add : IsClosedMap (toAdd : Multiplicative α → α) :=
  IsClosedMap.id
#align is_closed_map_to_add is_closed_map_to_add

theorem nhds_of_mul (a : α) : 𝓝 (ofMul a) = map ofMul (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_of_mul nhds_of_mul

theorem nhds_of_add (a : α) : 𝓝 (ofAdd a) = map ofAdd (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_of_add nhds_of_add

theorem nhds_to_mul (a : Additive α) : 𝓝 (toMul a) = map toMul (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_to_mul nhds_to_mul

theorem nhds_to_add (a : Multiplicative α) : 𝓝 (toAdd a) = map toAdd (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_to_add nhds_to_add

end

/-!
### Order dual

The topology on this type synonym is inherited without change.
-/


section

variable [TopologicalSpace α]

open OrderDual

instance : TopologicalSpace αᵒᵈ :=
  ‹TopologicalSpace α›

instance [DiscreteTopology α] : DiscreteTopology αᵒᵈ :=
  ‹DiscreteTopology α›

theorem continuous_to_dual : Continuous (toDual : α → αᵒᵈ) :=
  continuous_id
#align continuous_to_dual continuous_to_dual

theorem continuous_of_dual : Continuous (ofDual : αᵒᵈ → α) :=
  continuous_id
#align continuous_of_dual continuous_of_dual

theorem is_open_map_to_dual : IsOpenMap (toDual : α → αᵒᵈ) :=
  IsOpenMap.id
#align is_open_map_to_dual is_open_map_to_dual

theorem is_open_map_of_dual : IsOpenMap (ofDual : αᵒᵈ → α) :=
  IsOpenMap.id
#align is_open_map_of_dual is_open_map_of_dual

theorem is_closed_map_to_dual : IsClosedMap (toDual : α → αᵒᵈ) :=
  IsClosedMap.id
#align is_closed_map_to_dual is_closed_map_to_dual

theorem is_closed_map_of_dual : IsClosedMap (ofDual : αᵒᵈ → α) :=
  IsClosedMap.id
#align is_closed_map_of_dual is_closed_map_of_dual

theorem nhds_to_dual (a : α) : 𝓝 (toDual a) = map toDual (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_to_dual nhds_to_dual

theorem nhds_of_dual (a : α) : 𝓝 (ofDual a) = map ofDual (𝓝 a) := by
  unfold nhds
  rfl
#align nhds_of_dual nhds_of_dual

end

theorem Quotient.preimage_mem_nhds [TopologicalSpace α] [s : Setoid α] {V : Set <| Quotient s}
    {a : α} (hs : V ∈ 𝓝 (Quotient.mk'' a)) : Quotient.mk'' ⁻¹' V ∈ 𝓝 a :=
  preimage_nhds_coinduced hs
#align quotient.preimage_mem_nhds Quotient.preimage_mem_nhds

/-- The image of a dense set under `quotient.mk` is a dense set. -/
theorem Dense.quotient [Setoid α] [TopologicalSpace α] {s : Set α} (H : Dense s) :
    Dense (Quotient.mk'' '' s) :=
  (surjective_quotient_mk α).DenseRange.dense_image continuous_coinduced_rng H
#align dense.quotient Dense.quotient

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoid α] [TopologicalSpace α] {f : β → α} (hf : DenseRange f) :
    DenseRange (Quotient.mk'' ∘ f) :=
  (surjective_quotient_mk α).DenseRange.comp hf continuous_coinduced_rng
#align dense_range.quotient DenseRange.quotient

instance {p : α → Prop} [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique fun s hs =>
      ⟨coe '' s, is_open_discrete _, Set.preimage_image_eq _ Subtype.coe_injective⟩⟩

instance Sum.discrete_topology [TopologicalSpace α] [TopologicalSpace β] [hα : DiscreteTopology α]
    [hβ : DiscreteTopology β] : DiscreteTopology (Sum α β) :=
  ⟨by unfold Sum.topologicalSpace <;> simp [hα.eq_bot, hβ.eq_bot]⟩
#align sum.discrete_topology Sum.discrete_topology

instance Sigma.discrete_topology {β : α → Type v} [∀ a, TopologicalSpace (β a)]
    [h : ∀ a, DiscreteTopology (β a)] : DiscreteTopology (Sigma β) :=
  ⟨by 
    unfold Sigma.topologicalSpace
    simp [fun a => (h a).eq_bot]⟩
#align sigma.discrete_topology Sigma.discrete_topology

section Topα

variable [TopologicalSpace α]

/-
The 𝓝 filter and the subspace topology.
-/
theorem mem_nhds_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    t ∈ 𝓝 a ↔ ∃ u ∈ 𝓝 (a : α), coe ⁻¹' u ⊆ t :=
  mem_nhds_induced coe a t
#align mem_nhds_subtype mem_nhds_subtype

theorem nhds_subtype (s : Set α) (a : { x // x ∈ s }) : 𝓝 a = comap coe (𝓝 (a : α)) :=
  nhds_induced coe a
#align nhds_subtype nhds_subtype

theorem nhds_within_subtype_eq_bot_iff {s t : Set α} {x : s} :
    𝓝[(coe : s → α) ⁻¹' t] x = ⊥ ↔ 𝓝[t] (x : α) ⊓ 𝓟 s = ⊥ := by
  rw [inf_principal_eq_bot_iff_comap, nhdsWithin, nhdsWithin, comap_inf, comap_principal,
    nhds_induced]
#align nhds_within_subtype_eq_bot_iff nhds_within_subtype_eq_bot_iff

theorem nhds_ne_subtype_eq_bot_iff {S : Set α} {x : S} :
    𝓝[{x}ᶜ] x = ⊥ ↔ 𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S = ⊥ := by
  rw [← nhds_within_subtype_eq_bot_iff, preimage_compl, ← image_singleton,
    subtype.coe_injective.preimage_image]
#align nhds_ne_subtype_eq_bot_iff nhds_ne_subtype_eq_bot_iff

theorem nhds_ne_subtype_ne_bot_iff {S : Set α} {x : S} :
    (𝓝[{x}ᶜ] x).ne_bot ↔ (𝓝[{x}ᶜ] (x : α) ⊓ 𝓟 S).ne_bot := by
  rw [ne_bot_iff, ne_bot_iff, not_iff_not, nhds_ne_subtype_eq_bot_iff]
#align nhds_ne_subtype_ne_bot_iff nhds_ne_subtype_ne_bot_iff

theorem discrete_topology_subtype_iff {S : Set α} :
    DiscreteTopology S ↔ ∀ x ∈ S, 𝓝[≠] x ⊓ 𝓟 S = ⊥ := by
  simp_rw [discrete_topology_iff_nhds_ne, SetCoe.forall', nhds_ne_subtype_eq_bot_iff]
#align discrete_topology_subtype_iff discrete_topology_subtype_iff

end Topα

/-- A type synonym equiped with the topology whose open sets are the empty set and the sets with
finite complements. -/
def CofiniteTopology (α : Type _) :=
  α
#align cofinite_topology CofiniteTopology

namespace CofiniteTopology

/-- The identity equivalence between `α` and `cofinite_topology α`. -/
def of : α ≃ CofiniteTopology α :=
  Equiv.refl α
#align cofinite_topology.of CofiniteTopology.of

instance [Inhabited α] : Inhabited (CofiniteTopology α) where default := of default

instance :
    TopologicalSpace
      (CofiniteTopology
        α) where 
  IsOpen s := s.Nonempty → Set.Finite (sᶜ)
  is_open_univ := by simp
  is_open_inter s t := by 
    rintro hs ht ⟨x, hxs, hxt⟩
    rw [compl_inter]
    exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
  is_open_sUnion := by 
    rintro s h ⟨x, t, hts, hzt⟩
    rw [Set.compl_sUnion]
    exact Set.Finite.sInter (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

theorem is_open_iff {s : Set (CofiniteTopology α)} : IsOpen s ↔ s.Nonempty → sᶜ.Finite :=
  Iff.rfl
#align cofinite_topology.is_open_iff CofiniteTopology.is_open_iff

theorem is_open_iff' {s : Set (CofiniteTopology α)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Finite := by
  simp only [is_open_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]
#align cofinite_topology.is_open_iff' CofiniteTopology.is_open_iff'

theorem is_closed_iff {s : Set (CofiniteTopology α)} : IsClosed s ↔ s = univ ∨ s.Finite := by
  simp [← is_open_compl_iff, is_open_iff']
#align cofinite_topology.is_closed_iff CofiniteTopology.is_closed_iff

theorem nhds_eq (a : CofiniteTopology α) : 𝓝 a = pure a ⊔ cofinite := by
  ext U
  rw [mem_nhds_iff]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    exact mem_sup.mpr ⟨hVU haV, mem_of_superset (V_op ⟨_, haV⟩) hVU⟩
  · rintro ⟨hU : a ∈ U, hU' : Uᶜ.Finite⟩
    exact ⟨U, subset.rfl, fun h => hU', hU⟩
#align cofinite_topology.nhds_eq CofiniteTopology.nhds_eq

theorem mem_nhds_iff {a : CofiniteTopology α} {s : Set (CofiniteTopology α)} :
    s ∈ 𝓝 a ↔ a ∈ s ∧ sᶜ.Finite := by simp [nhds_eq]
#align cofinite_topology.mem_nhds_iff CofiniteTopology.mem_nhds_iff

end CofiniteTopology

end Constructions

section Prod

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
  [TopologicalSpace ε] [TopologicalSpace ζ]

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst α β) :=
  continuous_inf_dom_left continuous_induced_dom
#align continuous_fst continuous_fst

/-- Postcomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).1 :=
  continuous_fst.comp hf
#align continuous.fst Continuous.fst

/-- Precomposing `f` with `prod.fst` is continuous -/
theorem Continuous.fst' {f : α → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.fst :=
  hf.comp continuous_fst
#align continuous.fst' Continuous.fst'

theorem continuous_at_fst {p : α × β} : ContinuousAt Prod.fst p :=
  continuous_fst.ContinuousAt
#align continuous_at_fst continuous_at_fst

/-- Postcomposing `f` with `prod.fst` is continuous at `x` -/
theorem ContinuousAt.fst {f : α → β × γ} {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun a : α => (f a).1) x :=
  continuous_at_fst.comp hf
#align continuous_at.fst ContinuousAt.fst

/-- Precomposing `f` with `prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : α → γ} {x : α} {y : β} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : α × β => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuous_at_fst
#align continuous_at.fst' ContinuousAt.fst'

/-- Precomposing `f` with `prod.fst` is continuous at `x : α × β` -/
theorem ContinuousAt.fst'' {f : α → γ} {x : α × β} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : α × β => f x.fst) x :=
  hf.comp continuous_at_fst
#align continuous_at.fst'' ContinuousAt.fst''

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd α β) :=
  continuous_inf_dom_right continuous_induced_dom
#align continuous_snd continuous_snd

/-- Postcomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).2 :=
  continuous_snd.comp hf
#align continuous.snd Continuous.snd

/-- Precomposing `f` with `prod.snd` is continuous -/
theorem Continuous.snd' {f : β → γ} (hf : Continuous f) : Continuous fun x : α × β => f x.snd :=
  hf.comp continuous_snd
#align continuous.snd' Continuous.snd'

theorem continuous_at_snd {p : α × β} : ContinuousAt Prod.snd p :=
  continuous_snd.ContinuousAt
#align continuous_at_snd continuous_at_snd

/-- Postcomposing `f` with `prod.snd` is continuous at `x` -/
theorem ContinuousAt.snd {f : α → β × γ} {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun a : α => (f a).2) x :=
  continuous_at_snd.comp hf
#align continuous_at.snd ContinuousAt.snd

/-- Precomposing `f` with `prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : β → γ} {x : α} {y : β} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : α × β => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuous_at_snd
#align continuous_at.snd' ContinuousAt.snd'

/-- Precomposing `f` with `prod.snd` is continuous at `x : α × β` -/
theorem ContinuousAt.snd'' {f : β → γ} {x : α × β} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : α × β => f x.snd) x :=
  hf.comp continuous_at_snd
#align continuous_at.snd'' ContinuousAt.snd''

@[continuity]
theorem Continuous.prod_mk {f : γ → α} {g : γ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_inf_rng.2 ⟨continuous_induced_rng.2 hf, continuous_induced_rng.2 hg⟩
#align continuous.prod_mk Continuous.prod_mk

@[simp]
theorem continuous_prod_mk {f : α → β} {g : α → γ} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod_mk h.2⟩
#align continuous_prod_mk continuous_prod_mk

@[continuity]
theorem Continuous.Prod.mk (a : α) : Continuous fun b : β => (a, b) :=
  continuous_const.prod_mk continuous_id'
#align continuous.prod.mk Continuous.Prod.mk

@[continuity]
theorem Continuous.Prod.mk_left (b : β) : Continuous fun a : α => (a, b) :=
  continuous_id'.prod_mk continuous_const
#align continuous.prod.mk_left Continuous.Prod.mk_left

theorem Continuous.comp₂ {g : α × β → γ} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) : Continuous fun x => g (e x, f x) :=
  hg.comp <| he.prod_mk hf
#align continuous.comp₂ Continuous.comp₂

theorem Continuous.comp₃ {g : α × β × γ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) {k : δ → γ} (hk : Continuous k) :
    Continuous fun x => g (e x, f x, k x) :=
  hg.comp₂ he <| hf.prod_mk hk
#align continuous.comp₃ Continuous.comp₃

theorem Continuous.comp₄ {g : α × β × γ × ζ → ε} (hg : Continuous g) {e : δ → α} (he : Continuous e)
    {f : δ → β} (hf : Continuous f) {k : δ → γ} (hk : Continuous k) {l : δ → ζ}
    (hl : Continuous l) : Continuous fun x => g (e x, f x, k x, l x) :=
  hg.comp₃ he hf <| hk.prod_mk hl
#align continuous.comp₄ Continuous.comp₄

theorem Continuous.prod_map {f : γ → α} {g : δ → β} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x : γ × δ => (f x.1, g x.2) :=
  hf.fst'.prod_mk hg.snd'
#align continuous.prod_map Continuous.prod_map

/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α}
    {tb1 tb2 : TopologicalSpace β} {tc1 : TopologicalSpace γ}
    (h : by haveI := ta1 <;> haveI := tb1 <;> exact Continuous fun p : α × β => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2 <;> haveI := tb1 ⊓ tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_left₂ continuous_inf_dom_left₂

/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ta1 ta2 : TopologicalSpace α}
    {tb1 tb2 : TopologicalSpace β} {tc1 : TopologicalSpace γ}
    (h : by haveI := ta2 <;> haveI := tb2 <;> exact Continuous fun p : α × β => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2 <;> haveI := tb1 ⊓ tb2 <;> exact Continuous fun p : α × β => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id
#align continuous_inf_dom_right₂ continuous_inf_dom_right₂

/-- A version of `continuous_Inf_dom` for binary functions -/
theorem continuous_Inf_dom₂ {α β γ} {f : α → β → γ} {tas : Set (TopologicalSpace α)}
    {tbs : Set (TopologicalSpace β)} {ta : TopologicalSpace α} {tb : TopologicalSpace β}
    {tc : TopologicalSpace γ} (ha : ta ∈ tas) (hb : tb ∈ tbs)
    (hf : Continuous fun p : α × β => f p.1 p.2) : by
    haveI := Inf tas <;> haveI := Inf tbs <;>
      exact @Continuous _ _ _ tc fun p : α × β => f p.1 p.2 :=
  by 
  let t : TopologicalSpace (α × β) := Prod.topologicalSpace
  have ha := continuous_Inf_dom ha continuous_id
  have hb := continuous_Inf_dom hb continuous_id
  have h_continuous_id := @Continuous.prod_map _ _ _ _ ta tb (Inf tas) (Inf tbs) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id
#align continuous_Inf_dom₂ continuous_Inf_dom₂

theorem Filter.Eventually.prod_inl_nhds {p : α → Prop} {a : α} (h : ∀ᶠ x in 𝓝 a, p x) (b : β) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).1 :=
  continuous_at_fst h
#align filter.eventually.prod_inl_nhds Filter.Eventually.prod_inl_nhds

theorem Filter.Eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠ x in 𝓝 b, p x) (a : α) :
    ∀ᶠ x in 𝓝 (a, b), p (x : α × β).2 :=
  continuous_at_snd h
#align filter.eventually.prod_inr_nhds Filter.Eventually.prod_inr_nhds

theorem Filter.Eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠ x in 𝓝 a, pa x) {pb : β → Prop}
    {b} (hb : ∀ᶠ y in 𝓝 b, pb y) : ∀ᶠ p in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl_nhds b).And (hb.prod_inr_nhds a)
#align filter.eventually.prod_mk_nhds Filter.Eventually.prod_mk_nhds

theorem continuous_swap : Continuous (Prod.swap : α × β → β × α) :=
  continuous_snd.prod_mk continuous_fst
#align continuous_swap continuous_swap

theorem continuous_uncurry_left {f : α → β → γ} (a : α) (h : Continuous (uncurry f)) :
    Continuous (f a) :=
  show Continuous (uncurry f ∘ fun b => (a, b)) from h.comp (by continuity)
#align continuous_uncurry_left continuous_uncurry_left

theorem continuous_uncurry_right {f : α → β → γ} (b : β) (h : Continuous (uncurry f)) :
    Continuous fun a => f a b :=
  show Continuous (uncurry f ∘ fun a => (a, b)) from h.comp (by continuity)
#align continuous_uncurry_right continuous_uncurry_right

theorem continuous_curry {g : α × β → γ} (a : α) (h : Continuous g) : Continuous (curry g a) :=
  show Continuous (g ∘ fun b => (a, b)) from h.comp (by continuity)
#align continuous_curry continuous_curry

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsOpen.prod {s : Set α} {t : Set β} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.Preimage continuous_fst).inter (ht.Preimage continuous_snd)
#align is_open.prod IsOpen.prod

theorem nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b := by
  rw [Filter.prod, Prod.topologicalSpace, nhds_inf, nhds_induced, nhds_induced]
#align nhds_prod_eq nhds_prod_eq

/-- If a function `f x y` is such that `y ↦ f x y` is continuous for all `x`, and `x` lives in a
discrete space, then `f` is continuous. -/
theorem continuous_uncurry_of_discrete_topology [DiscreteTopology α] {f : α → β → γ}
    (hf : ∀ a, Continuous (f a)) : Continuous (uncurry f) := by
  apply continuous_iff_continuous_at.2
  rintro ⟨a, x⟩
  change map _ _ ≤ _
  rw [nhds_prod_eq, nhds_discrete, Filter.map_pure_prod]
  exact (hf a).ContinuousAt
#align continuous_uncurry_of_discrete_topology continuous_uncurry_of_discrete_topology

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_nhds_prod_iff {a : α} {b : β} {s : Set (α × β)} :
    s ∈ 𝓝 (a, b) ↔ ∃ u ∈ 𝓝 a, ∃ v ∈ 𝓝 b, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]
#align mem_nhds_prod_iff mem_nhds_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_nhds_prod_iff' {a : α} {b : β} {s : Set (α × β)} :
    s ∈ 𝓝 (a, b) ↔ ∃ (u : Set α)(v : Set β), IsOpen u ∧ a ∈ u ∧ IsOpen v ∧ b ∈ v ∧ u ×ˢ v ⊆ s := by
  rw [mem_nhds_prod_iff]
  constructor
  · rintro ⟨u, Hu, v, Hv, h⟩
    rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩
    rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩
    exact ⟨u', v', u'_open, Hu', v'_open, Hv', (Set.prod_mono u'u v'v).trans h⟩
  · rintro ⟨u, v, u_open, au, v_open, bv, huv⟩
    exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩
#align mem_nhds_prod_iff' mem_nhds_prod_iff'

theorem Prod.tendsto_iff {α} (seq : α → β × γ) {f : Filter α} (x : β × γ) :
    Tendsto seq f (𝓝 x) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 x.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 x.snd) :=
  by 
  cases x
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']
#align prod.tendsto_iff Prod.tendsto_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.HasBasis.prod_nhds {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop}
    {sa : ιa → Set α} {sb : ιb → Set β} {a : α} {b : β} (ha : (𝓝 a).HasBasis pa sa)
    (hb : (𝓝 b).HasBasis pb sb) :
    (𝓝 (a, b)).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 := by
  rw [nhds_prod_eq]
  exact ha.prod hb
#align filter.has_basis.prod_nhds Filter.HasBasis.prod_nhds

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.HasBasis.prod_nhds' {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop}
    {sa : ιa → Set α} {sb : ιb → Set β} {ab : α × β} (ha : (𝓝 ab.1).HasBasis pa sa)
    (hb : (𝓝 ab.2).HasBasis pb sb) :
    (𝓝 ab).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 := by
  cases ab
  exact ha.prod_nhds hb
#align filter.has_basis.prod_nhds' Filter.HasBasis.prod_nhds'

instance [DiscreteTopology α] [DiscreteTopology β] : DiscreteTopology (α × β) :=
  ⟨eq_of_nhds_eq_nhds fun ⟨a, b⟩ => by
      rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_bot, Filter.prod_pure_pure]⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mem_nhds_iff {s : Set α} {t : Set β} {a : α} {b : β} :
    s ×ˢ t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b := by rw [nhds_prod_eq, prod_mem_prod_iff]
#align prod_mem_nhds_iff prod_mem_nhds_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mem_nhds {s : Set α} {t : Set β} {a : α} {b : β} (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) :
    s ×ˢ t ∈ 𝓝 (a, b) :=
  prod_mem_nhds_iff.2 ⟨ha, hb⟩
#align prod_mem_nhds prod_mem_nhds

theorem Filter.Eventually.prod_nhds {p : α → Prop} {q : β → Prop} {a : α} {b : β}
    (ha : ∀ᶠ x in 𝓝 a, p x) (hb : ∀ᶠ y in 𝓝 b, q y) : ∀ᶠ z : α × β in 𝓝 (a, b), p z.1 ∧ q z.2 :=
  prod_mem_nhds ha hb
#align filter.eventually.prod_nhds Filter.Eventually.prod_nhds

theorem nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq] <;> rfl
#align nhds_swap nhds_swap

theorem Filter.Tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : Filter γ} {ma : γ → α} {mb : γ → β}
    (ha : Tendsto ma f (𝓝 a)) (hb : Tendsto mb f (𝓝 b)) :
    Tendsto (fun c => (ma c, mb c)) f (𝓝 (a, b)) := by
  rw [nhds_prod_eq] <;> exact Filter.Tendsto.prod_mk ha hb
#align filter.tendsto.prod_mk_nhds Filter.Tendsto.prod_mk_nhds

theorem Filter.Eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry
#align filter.eventually.curry_nhds Filter.Eventually.curry_nhds

theorem ContinuousAt.prod {f : α → β} {g : α → γ} {x : α} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg
#align continuous_at.prod ContinuousAt.prod

theorem ContinuousAt.prod_map {f : α → γ} {g : β → δ} {p : α × β} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) p :=
  hf.fst''.Prod hg.snd''
#align continuous_at.prod_map ContinuousAt.prod_map

theorem ContinuousAt.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) (x, y) :=
  hf.fst'.Prod hg.snd'
#align continuous_at.prod_map' ContinuousAt.prod_map'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_generate_from_generate_from_eq {α β : Type _} {s : Set (Set α)} {t : Set (Set β)}
    (hs : ⋃₀s = univ) (ht : ⋃₀t = univ) :
    @Prod.topologicalSpace α β (generateFrom s) (generateFrom t) =
      generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v } :=
  let G := generateFrom { g | ∃ u ∈ s, ∃ v ∈ t, g = u ×ˢ v }
  le_antisymm
    (le_generate_from fun g ⟨u, hu, v, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generate_from fun u hu =>
          have : (⋃ v ∈ t, u ×ˢ v) = Prod.fst ⁻¹' u := by
            simp_rw [← prod_Union, ← sUnion_eq_bUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by 
            rw [← this]
            exact
              is_open_Union fun v =>
                is_open_Union fun hv => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generate_from fun v hv =>
          have : (⋃ u ∈ s, u ×ˢ v) = Prod.snd ⁻¹' v := by
            simp_rw [← Union_prod_const, ← sUnion_eq_bUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by 
            rw [← this]
            exact
              is_open_Union fun u =>
                is_open_Union fun hu => generate_open.basic _ ⟨_, hu, _, hv, rfl⟩))
#align prod_generate_from_generate_from_eq prod_generate_from_generate_from_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_generate_from :
    Prod.topologicalSpace =
      generateFrom { g | ∃ (s : Set α)(t : Set β), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generate_from fun g ⟨s, t, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.Prod ht)
    (le_inf
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _ ⟨t, univ, by simpa [Set.prod_eq] using ht⟩)
      (ball_image_of_ball fun t ht =>
        GenerateOpen.basic _ ⟨univ, t, by simpa [Set.prod_eq] using ht⟩))
#align prod_eq_generate_from prod_eq_generate_from

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem is_open_prod_iff {s : Set (α × β)} :
    IsOpen s ↔
      ∀ a b,
        (a, b) ∈ s → ∃ (u : Set α)(v : Set β), IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  by 
  rw [is_open_iff_nhds]
  simp_rw [le_principal_iff, Prod.forall,
    ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, Prod.exists, exists_prop]
  simp only [and_assoc', and_left_comm]
#align is_open_prod_iff is_open_prod_iff

/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced {α γ : Type _} (f : α → β) (g : γ → δ) :
    @Prod.topologicalSpace α γ (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) Prod.topologicalSpace :=
  by simp_rw [Prod.topologicalSpace, induced_inf, induced_compose]
#align prod_induced_induced prod_induced_induced

theorem continuous_uncurry_of_discrete_topology_left [DiscreteTopology α] {f : α → β → γ}
    (h : ∀ a, Continuous (f a)) : Continuous (uncurry f) :=
  continuous_iff_continuous_at.2 fun ⟨a, b⟩ => by
    simp only [ContinuousAt, nhds_prod_eq, nhds_discrete α, pure_prod, tendsto_map'_iff, (· ∘ ·),
      uncurry, (h a).Tendsto]
#align continuous_uncurry_of_discrete_topology_left continuous_uncurry_of_discrete_topology_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx
#align exists_nhds_square exists_nhds_square

/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhds_within (x : α × β) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine' le_antisymm (continuous_at_fst.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl
#align map_fst_nhds_within map_fst_nhds_within

@[simp]
theorem map_fst_nhds (x : α × β) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuous_at_fst <| (map_fst_nhds_within x).symm.trans_le (map_mono inf_le_left)
#align map_fst_nhds map_fst_nhds

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_fst : IsOpenMap (@Prod.fst α β) :=
  is_open_map_iff_nhds_le.2 fun x => (map_fst_nhds x).ge
#align is_open_map_fst is_open_map_fst

/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhds_within (x : α × β) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine' le_antisymm (continuous_at_snd.mono_left inf_le_left) fun s hs => _
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl
#align map_snd_nhds_within map_snd_nhds_within

@[simp]
theorem map_snd_nhds (x : α × β) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuous_at_snd <| (map_snd_nhds_within x).symm.trans_le (map_mono inf_le_left)
#align map_snd_nhds map_snd_nhds

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_snd : IsOpenMap (@Prod.snd α β) :=
  is_open_map_iff_nhds_le.2 fun x => (map_snd_nhds x).ge
#align is_open_map_snd is_open_map_snd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem is_open_prod_iff' {s : Set α} {t : Set β} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.nonempty ∧ t.nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine' Or.inl ⟨_, _⟩
      show IsOpen s
      · rw [← fst_image_prod s st.2]
        exact is_open_map_fst _ H
      show IsOpen t
      · rw [← snd_image_prod st.1 t]
        exact is_open_map_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false_iff] at H
      exact H.1.Prod H.2
#align is_open_prod_iff' is_open_prod_iff'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem closure_prod_eq {s : Set α} {t : Set β} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  Set.ext fun ⟨a, b⟩ => by
    have : (𝓝 a ×ᶠ 𝓝 b) ⊓ 𝓟 (s ×ˢ t) = 𝓝 a ⊓ 𝓟 s ×ᶠ 𝓝 b ⊓ 𝓟 t := by
      rw [← prod_inf_prod, prod_principal_principal]
    simp [closure_eq_cluster_pts, ClusterPt, nhds_prod_eq, this] <;> exact prod_ne_bot
#align closure_prod_eq closure_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interior_prod_eq (s : Set α) (t : Set β) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  Set.ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]
#align interior_prod_eq interior_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem frontier_prod_eq (s : Set α) (t : Set β) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]
#align frontier_prod_eq frontier_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem frontier_prod_univ_eq (s : Set α) : frontier (s ×ˢ (univ : Set β)) = frontier s ×ˢ univ :=
  by simp [frontier_prod_eq]
#align frontier_prod_univ_eq frontier_prod_univ_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem frontier_univ_prod_eq (s : Set β) : frontier ((univ : Set α) ×ˢ s) = univ ×ˢ frontier s :=
  by simp [frontier_prod_eq]
#align frontier_univ_prod_eq frontier_univ_prod_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_mem_closure₂ {f : α → β → γ} {a : α} {b : β} {s : Set α} {t : Set β} {u : Set γ}
    (hf : Continuous (uncurry f)) (ha : a ∈ closure s) (hb : b ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f a b ∈ closure u :=
  have H₁ : (a, b) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod ha hb
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁
#align map_mem_closure₂ map_mem_closure₂

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsClosed.prod {s₁ : Set α} {s₂ : Set β} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_is_closed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]
#align is_closed.prod IsClosed.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set α} {t : Set β} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by 
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩
#align dense.prod Dense.prod

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
theorem DenseRange.prod_map {ι : Type _} {κ : Type _} {f : ι → β} {g : κ → γ} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using hf.prod hg
#align dense_range.prod_map DenseRange.prod_map

theorem Inducing.prod_mk {f : α → β} {g : γ → δ} (hf : Inducing f) (hg : Inducing g) :
    Inducing fun x : α × γ => (f x.1, g x.2) :=
  ⟨by
    rw [Prod.topologicalSpace, Prod.topologicalSpace, hf.induced, hg.induced, induced_compose,
      induced_compose, induced_inf, induced_compose, induced_compose]⟩
#align inducing.prod_mk Inducing.prod_mk

theorem Embedding.prod_mk {f : α → β} {g : γ → δ} (hf : Embedding f) (hg : Embedding g) :
    Embedding fun x : α × γ => (f x.1, g x.2) :=
  { hf.to_inducing.prod_mk hg.to_inducing with
    inj := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => by simp <;> exact fun h₁ h₂ => ⟨hf.inj h₁, hg.inj h₂⟩ }
#align embedding.prod_mk Embedding.prod_mk

protected theorem IsOpenMap.prod {f : α → β} {g : γ → δ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap fun p : α × γ => (f p.1, g p.2) := by
  rw [is_open_map_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq]
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)
#align is_open_map.prod IsOpenMap.prod

protected theorem OpenEmbedding.prod {f : α → β} {g : γ → δ} (hf : OpenEmbedding f)
    (hg : OpenEmbedding g) : OpenEmbedding fun x : α × γ => (f x.1, g x.2) :=
  open_embedding_of_embedding_open (hf.1.prod_mk hg.1) (hf.IsOpenMap.Prod hg.IsOpenMap)
#align open_embedding.prod OpenEmbedding.prod

theorem embedding_graph {f : α → β} (hf : Continuous f) : Embedding fun x => (x, f x) :=
  embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id
#align embedding_graph embedding_graph

end Prod

section Sum

open Sum

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

@[continuity]
theorem continuous_inl : Continuous (@inl α β) :=
  continuous_sup_rng_left continuous_coinduced_rng
#align continuous_inl continuous_inl

@[continuity]
theorem continuous_inr : Continuous (@inr α β) :=
  continuous_sup_rng_right continuous_coinduced_rng
#align continuous_inr continuous_inr

theorem is_open_sum_iff {s : Set (Sum α β)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl
#align is_open_sum_iff is_open_sum_iff

theorem is_open_map_inl : IsOpenMap (@inl α β) := fun u hu => by
  simpa [is_open_sum_iff, preimage_image_eq u Sum.inl_injective]
#align is_open_map_inl is_open_map_inl

theorem is_open_map_inr : IsOpenMap (@inr α β) := fun u hu => by
  simpa [is_open_sum_iff, preimage_image_eq u Sum.inr_injective]
#align is_open_map_inr is_open_map_inr

theorem open_embedding_inl : OpenEmbedding (@inl α β) :=
  open_embedding_of_continuous_injective_open continuous_inl inl_injective is_open_map_inl
#align open_embedding_inl open_embedding_inl

theorem open_embedding_inr : OpenEmbedding (@inr α β) :=
  open_embedding_of_continuous_injective_open continuous_inr inr_injective is_open_map_inr
#align open_embedding_inr open_embedding_inr

theorem embedding_inl : Embedding (@inl α β) :=
  open_embedding_inl.1
#align embedding_inl embedding_inl

theorem embedding_inr : Embedding (@inr α β) :=
  open_embedding_inr.1
#align embedding_inr embedding_inr

theorem is_open_range_inl : IsOpen (range (inl : α → Sum α β)) :=
  open_embedding_inl.2
#align is_open_range_inl is_open_range_inl

theorem is_open_range_inr : IsOpen (range (inr : β → Sum α β)) :=
  open_embedding_inr.2
#align is_open_range_inr is_open_range_inr

theorem is_closed_range_inl : IsClosed (range (inl : α → Sum α β)) := by
  rw [← is_open_compl_iff, compl_range_inl]
  exact is_open_range_inr
#align is_closed_range_inl is_closed_range_inl

theorem is_closed_range_inr : IsClosed (range (inr : β → Sum α β)) := by
  rw [← is_open_compl_iff, compl_range_inr]
  exact is_open_range_inl
#align is_closed_range_inr is_closed_range_inr

theorem closed_embedding_inl : ClosedEmbedding (inl : α → Sum α β) :=
  ⟨embedding_inl, is_closed_range_inl⟩
#align closed_embedding_inl closed_embedding_inl

theorem closed_embedding_inr : ClosedEmbedding (inr : β → Sum α β) :=
  ⟨embedding_inr, is_closed_range_inr⟩
#align closed_embedding_inr closed_embedding_inr

theorem nhds_inl (x : α) : 𝓝 (inl x : Sum α β) = map inl (𝓝 x) :=
  (open_embedding_inl.map_nhds_eq _).symm
#align nhds_inl nhds_inl

theorem nhds_inr (x : β) : 𝓝 (inr x : Sum α β) = map inr (𝓝 x) :=
  (open_embedding_inr.map_nhds_eq _).symm
#align nhds_inr nhds_inr

theorem continuous_sum_elim {f : α → γ} {g : β → γ} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g := by
  simp only [continuous_sup_dom, continuous_coinduced_dom, Sum.elim_comp_inl, Sum.elim_comp_inr]
#align continuous_sum_elim continuous_sum_elim

@[continuity]
theorem Continuous.sum_elim {f : α → γ} {g : β → γ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sum_elim.2 ⟨hf, hg⟩
#align continuous.sum_elim Continuous.sum_elim

@[simp]
theorem continuous_sum_map {f : α → β} {g : γ → δ} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_elim.trans <|
    embedding_inl.continuous_iff.symm.And embedding_inr.continuous_iff.symm
#align continuous_sum_map continuous_sum_map

@[continuity]
theorem Continuous.sum_map {f : α → β} {g : γ → δ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sum_map.2 ⟨hf, hg⟩
#align continuous.sum_map Continuous.sum_map

theorem is_open_map_sum {f : Sum α β → γ} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [is_open_map_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map]
#align is_open_map_sum is_open_map_sum

@[simp]
theorem is_open_map_sum_elim {f : α → γ} {g : β → γ} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [is_open_map_sum, elim_inl, elim_inr]
#align is_open_map_sum_elim is_open_map_sum_elim

theorem IsOpenMap.sum_elim {f : α → γ} {g : β → γ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  is_open_map_sum_elim.2 ⟨hf, hg⟩
#align is_open_map.sum_elim IsOpenMap.sum_elim

end Sum

section Subtype

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {p : α → Prop}

theorem inducing_coe {b : Set β} : Inducing (coe : b → β) :=
  ⟨rfl⟩
#align inducing_coe inducing_coe

theorem Inducing.of_cod_restrict {f : α → β} {b : Set β} (hb : ∀ a, f a ∈ b)
    (h : Inducing (b.codRestrict f hb)) : Inducing f :=
  inducing_coe.comp h
#align inducing.of_cod_restrict Inducing.of_cod_restrict

theorem embedding_subtype_coe : Embedding (coe : Subtype p → α) :=
  ⟨⟨rfl⟩, Subtype.coe_injective⟩
#align embedding_subtype_coe embedding_subtype_coe

theorem closed_embedding_subtype_coe (h : IsClosed { a | p a }) :
    ClosedEmbedding (coe : Subtype p → α) :=
  ⟨embedding_subtype_coe, by rwa [Subtype.range_coe_subtype]⟩
#align closed_embedding_subtype_coe closed_embedding_subtype_coe

@[continuity]
theorem continuous_subtype_val : Continuous (@Subtype.val α p) :=
  continuous_induced_dom
#align continuous_subtype_val continuous_subtype_val

theorem continuous_subtype_coe : Continuous (coe : Subtype p → α) :=
  continuous_subtype_val
#align continuous_subtype_coe continuous_subtype_coe

theorem Continuous.subtype_coe {f : β → Subtype p} (hf : Continuous f) :
    Continuous fun x => (f x : α) :=
  continuous_subtype_coe.comp hf
#align continuous.subtype_coe Continuous.subtype_coe

theorem IsOpen.open_embedding_subtype_coe {s : Set α} (hs : IsOpen s) :
    OpenEmbedding (coe : s → α) :=
  { induced := rfl
    inj := Subtype.coe_injective
    open_range := (Subtype.range_coe : range coe = s).symm ▸ hs }
#align is_open.open_embedding_subtype_coe IsOpen.open_embedding_subtype_coe

theorem IsOpen.is_open_map_subtype_coe {s : Set α} (hs : IsOpen s) : IsOpenMap (coe : s → α) :=
  hs.open_embedding_subtype_coe.IsOpenMap
#align is_open.is_open_map_subtype_coe IsOpen.is_open_map_subtype_coe

theorem IsOpenMap.restrict {f : α → β} (hf : IsOpenMap f) {s : Set α} (hs : IsOpen s) :
    IsOpenMap (s.restrict f) :=
  hf.comp hs.is_open_map_subtype_coe
#align is_open_map.restrict IsOpenMap.restrict

theorem IsClosed.closed_embedding_subtype_coe {s : Set α} (hs : IsClosed s) :
    ClosedEmbedding (coe : { x // x ∈ s } → α) :=
  { induced := rfl
    inj := Subtype.coe_injective
    closed_range := (Subtype.range_coe : range coe = s).symm ▸ hs }
#align is_closed.closed_embedding_subtype_coe IsClosed.closed_embedding_subtype_coe

@[continuity]
theorem Continuous.subtype_mk {f : β → α} (h : Continuous f) (hp : ∀ x, p (f x)) :
    Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng.2 h
#align continuous.subtype_mk Continuous.subtype_mk

theorem Continuous.subtype_map {f : α → β} (h : Continuous f) {q : β → Prop}
    (hpq : ∀ x, p x → q (f x)) : Continuous (Subtype.map f hpq) :=
  (h.comp continuous_subtype_coe).subtype_mk _
#align continuous.subtype_map Continuous.subtype_map

theorem continuous_inclusion {s t : Set α} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_id.subtypeMap h
#align continuous_inclusion continuous_inclusion

theorem continuous_at_subtype_coe {p : α → Prop} {a : Subtype p} :
    ContinuousAt (coe : Subtype p → α) a :=
  continuous_iff_continuous_at.mp continuous_subtype_coe _
#align continuous_at_subtype_coe continuous_at_subtype_coe

theorem Subtype.dense_iff {s : Set α} {t : Set s} : Dense t ↔ s ⊆ closure (coe '' t) := by
  rw [inducing_coe.dense_iff, SetCoe.forall]
  rfl
#align subtype.dense_iff Subtype.dense_iff

theorem map_nhds_subtype_coe_eq {a : α} (ha : p a) (h : { a | p a } ∈ 𝓝 a) :
    map (coe : Subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
  map_nhds_induced_of_mem <| by simpa only [Subtype.coe_mk, Subtype.range_coe] using h
#align map_nhds_subtype_coe_eq map_nhds_subtype_coe_eq

theorem nhds_subtype_eq_comap {a : α} {h : p a} : 𝓝 (⟨a, h⟩ : Subtype p) = comap coe (𝓝 a) :=
  nhds_induced _ _
#align nhds_subtype_eq_comap nhds_subtype_eq_comap

theorem tendsto_subtype_rng {β : Type _} {p : α → Prop} {b : Filter β} {f : β → Subtype p} :
    ∀ {a : Subtype p}, Tendsto f b (𝓝 a) ↔ Tendsto (fun x => (f x : α)) b (𝓝 (a : α))
  | ⟨a, ha⟩ => by rw [nhds_subtype_eq_comap, tendsto_comap_iff, Subtype.coe_mk]
#align tendsto_subtype_rng tendsto_subtype_rng

theorem continuous_subtype_nhds_cover {ι : Sort _} {f : α → β} {c : ι → α → Prop}
    (c_cover : ∀ x : α, ∃ i, { x | c i x } ∈ 𝓝 x)
    (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) : Continuous f :=
  continuous_iff_continuous_at.mpr fun x =>
    let ⟨i, (c_sets : { x | c i x } ∈ 𝓝 x)⟩ := c_cover x
    let x' : Subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩
    calc
      map f (𝓝 x) = map f (map coe (𝓝 x')) :=
        congr_arg (map f) (map_nhds_subtype_coe_eq _ <| c_sets).symm
      _ = map (fun x : Subtype (c i) => f x) (𝓝 x') := rfl
      _ ≤ 𝓝 (f x) := continuous_iff_continuous_at.mp (f_cont i) x'
      
#align continuous_subtype_nhds_cover continuous_subtype_nhds_cover

theorem continuous_subtype_is_closed_cover {ι : Sort _} {f : α → β} (c : ι → α → Prop)
    (h_lf : LocallyFinite fun i => { x | c i x }) (h_is_closed : ∀ i, IsClosed { x | c i x })
    (h_cover : ∀ x, ∃ i, c i x) (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) :
    Continuous f :=
  continuous_iff_is_closed.mpr fun s hs => by
    have : ∀ i, IsClosed ((coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) := fun i =>
      (closed_embedding_subtype_coe (h_is_closed _)).IsClosedMap _ (hs.Preimage (f_cont i))
    have : IsClosed (⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s)) :=
      LocallyFinite.is_closed_Union (h_lf.Subset fun i x ⟨⟨x', hx'⟩, _, HEq⟩ => HEq ▸ hx') this
    have : f ⁻¹' s = ⋃ i, (coe : { x | c i x } → α) '' (f ∘ coe ⁻¹' s) := by
      apply Set.ext
      have : ∀ x : α, f x ∈ s ↔ ∃ i : ι, c i x ∧ f x ∈ s := fun x =>
        ⟨fun hx =>
          let ⟨i, hi⟩ := h_cover x
          ⟨i, hi, hx⟩,
          fun ⟨i, hi, hx⟩ => hx⟩
      simpa [and_comm, @and_left_comm (c _ _), ← exists_and_right]
    rwa [this]
#align continuous_subtype_is_closed_cover continuous_subtype_is_closed_cover

theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
    x ∈ closure s ↔ (x : α) ∈ closure ((coe : _ → α) '' s) :=
  closure_induced
#align closure_subtype closure_subtype

theorem continuous_at_cod_restrict_iff {f : α → β} {t : Set β} (h1 : ∀ x, f x ∈ t) {x : α} :
    ContinuousAt (codRestrict f t h1) x ↔ ContinuousAt f x := by
  simp_rw [inducing_coe.continuous_at_iff, Function.comp, coe_cod_restrict_apply]
#align continuous_at_cod_restrict_iff continuous_at_cod_restrict_iff

alias continuous_at_cod_restrict_iff ↔ _ ContinuousAt.cod_restrict

theorem ContinuousAt.restrict {f : α → β} {s : Set α} {t : Set β} (h1 : MapsTo f s t) {x : s}
    (h2 : ContinuousAt f x) : ContinuousAt (h1.restrict f s t) x :=
  (h2.comp continuous_at_subtype_coe).codRestrict _
#align continuous_at.restrict ContinuousAt.restrict

theorem ContinuousAt.restrict_preimage {f : α → β} {s : Set β} {x : f ⁻¹' s}
    (h : ContinuousAt f x) : ContinuousAt (s.restrictPreimage f) x :=
  h.restrict _
#align continuous_at.restrict_preimage ContinuousAt.restrict_preimage

@[continuity]
theorem Continuous.cod_restrict {f : α → β} {s : Set β} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :
    Continuous (s.codRestrict f hs) :=
  hf.subtype_mk hs
#align continuous.cod_restrict Continuous.cod_restrict

theorem Inducing.cod_restrict {e : α → β} (he : Inducing e) {s : Set β} (hs : ∀ x, e x ∈ s) :
    Inducing (codRestrict e s hs) :=
  inducing_of_inducing_compose (he.Continuous.codRestrict hs) continuous_subtype_coe he
#align inducing.cod_restrict Inducing.cod_restrict

theorem Embedding.cod_restrict {e : α → β} (he : Embedding e) (s : Set β) (hs : ∀ x, e x ∈ s) :
    Embedding (codRestrict e s hs) :=
  embedding_of_embedding_compose (he.Continuous.codRestrict hs) continuous_subtype_coe he
#align embedding.cod_restrict Embedding.cod_restrict

end Subtype

section Quotient

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable {r : α → α → Prop} {s : Setoid α}

theorem quotient_map_quot_mk : QuotientMap (@Quot.mk α r) :=
  ⟨Quot.exists_rep, rfl⟩
#align quotient_map_quot_mk quotient_map_quot_mk

@[continuity]
theorem continuous_quot_mk : Continuous (@Quot.mk α r) :=
  continuous_coinduced_rng
#align continuous_quot_mk continuous_quot_mk

@[continuity]
theorem continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
    Continuous (Quot.lift f hr : Quot r → β) :=
  continuous_coinduced_dom.2 h
#align continuous_quot_lift continuous_quot_lift

theorem quotient_map_quotient_mk : QuotientMap (@Quotient.mk'' α s) :=
  quotient_map_quot_mk
#align quotient_map_quotient_mk quotient_map_quotient_mk

theorem continuous_quotient_mk : Continuous (@Quotient.mk'' α s) :=
  continuous_coinduced_rng
#align continuous_quotient_mk continuous_quotient_mk

theorem Continuous.quotient_lift {f : α → β} (h : Continuous f) (hs : ∀ a b, a ≈ b → f a = f b) :
    Continuous (Quotient.lift f hs : Quotient s → β) :=
  continuous_coinduced_dom.2 h
#align continuous.quotient_lift Continuous.quotient_lift

theorem Continuous.quotient_lift_on' {f : α → β} (h : Continuous f)
    (hs : ∀ a b, @Setoid.r _ s a b → f a = f b) :
    Continuous (fun x => Quotient.liftOn' x f hs : Quotient s → β) :=
  h.quotient_lift hs
#align continuous.quotient_lift_on' Continuous.quotient_lift_on'

theorem Continuous.quotient_map' {t : Setoid β} {f : α → β} (hf : Continuous f)
    (H : (s.R ⇒ t.R) f f) : Continuous (Quotient.map' f H) :=
  (continuous_quotient_mk.comp hf).quotient_lift _
#align continuous.quotient_map' Continuous.quotient_map'

end Quotient

section Pi

variable {ι : Type _} {π : ι → Type _} {κ : Type _} [TopologicalSpace α]
  [∀ i, TopologicalSpace (π i)] {f : α → ∀ i : ι, π i}

theorem continuous_pi_iff : Continuous f ↔ ∀ i, Continuous fun a => f a i := by
  simp only [continuous_infi_rng, continuous_induced_rng]
#align continuous_pi_iff continuous_pi_iff

@[continuity]
theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_pi_iff.2 h
#align continuous_pi continuous_pi

@[continuity]
theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_infi_dom continuous_induced_dom
#align continuous_apply continuous_apply

@[continuity]
theorem continuous_apply_apply {ρ : κ → ι → Type _} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)
    (i : ι) : Continuous fun p : ∀ j, ∀ i, ρ j i => p j i :=
  (continuous_apply i).comp (continuous_apply j)
#align continuous_apply_apply continuous_apply_apply

theorem continuous_at_apply (i : ι) (x : ∀ i, π i) : ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).ContinuousAt
#align continuous_at_apply continuous_at_apply

theorem Filter.Tendsto.apply {l : Filter β} {f : β → ∀ i, π i} {x : ∀ i, π i}
    (h : Tendsto f l (𝓝 x)) (i : ι) : Tendsto (fun a => f a i) l (𝓝 <| x i) :=
  (continuous_at_apply i _).Tendsto.comp h
#align filter.tendsto.apply Filter.Tendsto.apply

theorem nhds_pi {a : ∀ i, π i} : 𝓝 a = pi fun i => 𝓝 (a i) := by
  simp only [nhds_infi, nhds_induced, Filter.pi]
#align nhds_pi nhds_pi

theorem tendsto_pi_nhds {f : β → ∀ i, π i} {g : ∀ i, π i} {u : Filter β} :
    Tendsto f u (𝓝 g) ↔ ∀ x, Tendsto (fun i => f i x) u (𝓝 (g x)) := by
  rw [nhds_pi, Filter.tendsto_pi]
#align tendsto_pi_nhds tendsto_pi_nhds

theorem continuous_at_pi {f : α → ∀ i, π i} {x : α} :
    ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi_nhds
#align continuous_at_pi continuous_at_pi

theorem Filter.Tendsto.update [DecidableEq ι] {l : Filter β} {f : β → ∀ i, π i} {x : ∀ i, π i}
    (hf : Tendsto f l (𝓝 x)) (i : ι) {g : β → π i} {xi : π i} (hg : Tendsto g l (𝓝 xi)) :
    Tendsto (fun a => update (f a) i (g a)) l (𝓝 <| update x i xi) :=
  tendsto_pi_nhds.2 fun j => by rcases em (j = i) with (rfl | hj) <;> simp [*, hf.apply]
#align filter.tendsto.update Filter.Tendsto.update

theorem ContinuousAt.update [DecidableEq ι] {a : α} (hf : ContinuousAt f a) (i : ι) {g : α → π i}
    (hg : ContinuousAt g a) : ContinuousAt (fun a => update (f a) i (g a)) a :=
  hf.update i hg
#align continuous_at.update ContinuousAt.update

theorem Continuous.update [DecidableEq ι] (hf : Continuous f) (i : ι) {g : α → π i}
    (hg : Continuous g) : Continuous fun a => update (f a) i (g a) :=
  continuous_iff_continuous_at.2 fun x => hf.ContinuousAt.update i hg.ContinuousAt
#align continuous.update Continuous.update

/-- `update f i x` is continuous in `(f, x)`. -/
@[continuity]
theorem continuous_update [DecidableEq ι] (i : ι) :
    Continuous fun f : (∀ j, π j) × π i => update f.1 i f.2 :=
  continuous_fst.update i continuous_snd
#align continuous_update continuous_update

theorem Filter.Tendsto.fin_insert_nth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : β → π i} {l : Filter β} {x : π i} (hf : Tendsto f l (𝓝 x))
    {g : β → ∀ j : Fin n, π (i.succAbove j)} {y : ∀ j, π (i.succAbove j)} (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun a => i.insertNth (f a) (g a)) l (𝓝 <| i.insertNth x y) :=
  tendsto_pi_nhds.2 fun j => Fin.succAboveCases i (by simpa) (by simpa using tendsto_pi_nhds.1 hg) j
#align filter.tendsto.fin_insert_nth Filter.Tendsto.fin_insert_nth

theorem ContinuousAt.fin_insert_nth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : α → π i} {a : α} (hf : ContinuousAt f a)
    {g : α → ∀ j : Fin n, π (i.succAbove j)} (hg : ContinuousAt g a) :
    ContinuousAt (fun a => i.insertNth (f a) (g a)) a :=
  hf.fin_insert_nth i hg
#align continuous_at.fin_insert_nth ContinuousAt.fin_insert_nth

theorem Continuous.fin_insert_nth {n} {π : Fin (n + 1) → Type _} [∀ i, TopologicalSpace (π i)]
    (i : Fin (n + 1)) {f : α → π i} (hf : Continuous f) {g : α → ∀ j : Fin n, π (i.succAbove j)}
    (hg : Continuous g) : Continuous fun a => i.insertNth (f a) (g a) :=
  continuous_iff_continuous_at.2 fun a => hf.ContinuousAt.fin_insert_nth i hg.ContinuousAt
#align continuous.fin_insert_nth Continuous.fin_insert_nth

theorem is_open_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hi : i.Finite)
    (hs : ∀ a ∈ i, IsOpen (s a)) : IsOpen (pi i s) := by
  rw [pi_def] <;> exact (is_open_bInter hi) fun a ha => (hs _ ha).Preimage (continuous_apply _)
#align is_open_set_pi is_open_set_pi

theorem is_closed_set_pi {i : Set ι} {s : ∀ a, Set (π a)} (hs : ∀ a ∈ i, IsClosed (s a)) :
    IsClosed (pi i s) := by
  rw [pi_def] <;>
    exact is_closed_Inter fun a => is_closed_Inter fun ha => (hs _ ha).Preimage (continuous_apply _)
#align is_closed_set_pi is_closed_set_pi

theorem mem_nhds_of_pi_mem_nhds {I : Set ι} {s : ∀ i, Set (π i)} (a : ∀ i, π i) (hs : I.pi s ∈ 𝓝 a)
    {i : ι} (hi : i ∈ I) : s i ∈ 𝓝 (a i) := by
  rw [nhds_pi] at hs
  exact mem_of_pi_mem_pi hs hi
#align mem_nhds_of_pi_mem_nhds mem_nhds_of_pi_mem_nhds

theorem set_pi_mem_nhds {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : i.Finite)
    (hs : ∀ a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x := by
  rw [pi_def, bInter_mem hi]
  exact fun a ha => (continuous_apply a).ContinuousAt (hs a ha)
#align set_pi_mem_nhds set_pi_mem_nhds

theorem set_pi_mem_nhds_iff {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} (a : ∀ i, π i) :
    I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) := by
  rw [nhds_pi, pi_mem_pi_iff hI]
  infer_instance
#align set_pi_mem_nhds_iff set_pi_mem_nhds_iff

theorem interior_pi_set {I : Set ι} (hI : I.Finite) {s : ∀ i, Set (π i)} :
    interior (pi I s) = I.pi fun i => interior (s i) := by
  ext a
  simp only [Set.mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff hI]
#align interior_pi_set interior_pi_set

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] {s : Set (∀ a, π a)} {x : ∀ a, π a}
    (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s := by
  simp only [nhds_pi, Filter.mem_pi'] at hs
  rcases hs with ⟨I, t, htx, hts⟩
  refine' ⟨I, hts fun i hi => _⟩
  simpa [Finset.mem_coe.1 hi] using mem_of_mem_nhds (htx i)
#align exists_finset_piecewise_mem_of_mem_nhds exists_finset_piecewise_mem_of_mem_nhds

theorem pi_eq_generate_from :
    PiCat.topologicalSpace =
      generateFrom
        { g | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, IsOpen (s a)) ∧ g = pi (↑i) s } :=
  le_antisymm
    (le_generate_from fun g ⟨s, i, hi, Eq⟩ => Eq.symm ▸ is_open_set_pi (Finset.finite_to_set _) hi)
    (le_infᵢ fun a s ⟨t, ht, s_eq⟩ =>
      GenerateOpen.basic _ <|
        ⟨update (fun a => univ) a t, {a}, by simpa using ht, s_eq ▸ by ext f <;> simp [Set.pi]⟩)
#align pi_eq_generate_from pi_eq_generate_from

theorem pi_generate_from_eq {π : ι → Type _} {g : ∀ a, Set (Set (π a))} :
    (@PiCat.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom
        { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s } :=
  by 
  let G := { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a ∈ i, s a ∈ g a) ∧ t = pi (↑i) s }
  rw [pi_eq_generate_from]
  refine' le_antisymm (generate_from_mono _) (le_generate_from _)
  exact fun s ⟨t, i, ht, Eq⟩ => ⟨t, i, fun a ha => generate_open.basic _ (ht a ha), Eq⟩
  · rintro s ⟨t, i, hi, rfl⟩
    rw [pi_def]
    apply is_open_bInter (Finset.finite_to_set _)
    intro a ha
    show ((generate_from G).coinduced fun f : ∀ a, π a => f a).IsOpen (t a)
    refine' le_generate_from _ _ (hi a ha)
    exact fun s hs => generate_open.basic _ ⟨update (fun a => univ) a s, {a}, by simp [hs]⟩
#align pi_generate_from_eq pi_generate_from_eq

theorem pi_generate_from_eq_finite {π : ι → Type _} {g : ∀ a, Set (Set (π a))} [Finite ι]
    (hg : ∀ a, ⋃₀g a = univ) :
    (@PiCat.topologicalSpace ι π fun a => generateFrom (g a)) =
      generateFrom { t | ∃ s : ∀ a, Set (π a), (∀ a, s a ∈ g a) ∧ t = pi univ s } :=
  by 
  cases nonempty_fintype ι
  rw [pi_generate_from_eq]
  refine' le_antisymm (generate_from_mono _) (le_generate_from _)
  exact fun s ⟨t, ht, Eq⟩ => ⟨t, Finset.univ, by simp [ht, Eq]⟩
  · rintro s ⟨t, i, ht, rfl⟩
    apply is_open_iff_forall_mem_open.2 _
    intro f hf
    choose c hc using
      show ∀ a, ∃ s, s ∈ g a ∧ f a ∈ s by 
        intro a
        have : f a ∈ ⋃₀g a := by 
          rw [hg]
          apply mem_univ
        simpa
    refine' ⟨pi univ fun a => if a ∈ i then t a else (c : ∀ a, Set (π a)) a, _, _, _⟩
    · simp [pi_if]
    · refine' generate_open.basic _ ⟨_, fun a => _, rfl⟩
      by_cases a ∈ i <;> simp_all [Set.pi]
    · have : f ∈ pi { a | a ∉ i } c := by simp_all [Set.pi]
      simpa [pi_if, hf]
#align pi_generate_from_eq_finite pi_generate_from_eq_finite

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_infi_to_pi {X : Type _} (f : ∀ i, X → π i) :
    @Inducing X (∀ i, π i) (⨅ i, induced (f i) inferInstance) _ fun x i => f i x := by
  constructor
  erw [induced_infi]
  congr 1
  funext
  erw [induced_compose]
#align inducing_infi_to_pi inducing_infi_to_pi

variable [Finite ι] [∀ i, DiscreteTopology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance PiCat.discrete_topology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp fun x => by
    rw [show {x} = ⋂ i, { y : ∀ i, π i | y i = x i } by ext;
        simp only [funext_iff, Set.mem_singleton_iff, Set.mem_Inter, Set.mem_setOf_eq]]
    exact
      is_open_Inter fun i => (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i})
#align Pi.discrete_topology PiCat.discrete_topology

end Pi

section Sigma

variable {ι κ : Type _} {σ : ι → Type _} {τ : κ → Type _} [∀ i, TopologicalSpace (σ i)]
  [∀ k, TopologicalSpace (τ k)] [TopologicalSpace α]

@[continuity]
theorem continuous_sigma_mk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_supr_rng continuous_coinduced_rng
#align continuous_sigma_mk continuous_sigma_mk

theorem is_open_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) := by
  simp only [is_open_supr_iff, is_open_coinduced]
#align is_open_sigma_iff is_open_sigma_iff

theorem is_closed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) :=
  by simp only [← is_open_compl_iff, is_open_sigma_iff, preimage_compl]
#align is_closed_sigma_iff is_closed_sigma_iff

theorem is_open_map_sigma_mk {i : ι} : IsOpenMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [is_open_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigma_mk_of_ne hne]
    exact is_open_empty
#align is_open_map_sigma_mk is_open_map_sigma_mk

theorem is_open_range_sigma_mk {i : ι} : IsOpen (Set.range (@Sigma.mk ι σ i)) :=
  is_open_map_sigma_mk.is_open_range
#align is_open_range_sigma_mk is_open_range_sigma_mk

theorem is_closed_map_sigma_mk {i : ι} : IsClosedMap (@Sigma.mk ι σ i) := by
  intro s hs
  rw [is_closed_sigma_iff]
  intro j
  rcases eq_or_ne j i with (rfl | hne)
  · rwa [Set.preimage_image_eq _ sigma_mk_injective]
  · rw [preimage_image_sigma_mk_of_ne hne]
    exact is_closed_empty
#align is_closed_map_sigma_mk is_closed_map_sigma_mk

theorem is_closed_range_sigma_mk {i : ι} : IsClosed (Set.range (@Sigma.mk ι σ i)) :=
  is_closed_map_sigma_mk.closed_range
#align is_closed_range_sigma_mk is_closed_range_sigma_mk

theorem open_embedding_sigma_mk {i : ι} : OpenEmbedding (@Sigma.mk ι σ i) :=
  open_embedding_of_continuous_injective_open continuous_sigma_mk sigma_mk_injective
    is_open_map_sigma_mk
#align open_embedding_sigma_mk open_embedding_sigma_mk

theorem closed_embedding_sigma_mk {i : ι} : ClosedEmbedding (@Sigma.mk ι σ i) :=
  closed_embedding_of_continuous_injective_closed continuous_sigma_mk sigma_mk_injective
    is_closed_map_sigma_mk
#align closed_embedding_sigma_mk closed_embedding_sigma_mk

theorem embedding_sigma_mk {i : ι} : Embedding (@Sigma.mk ι σ i) :=
  closed_embedding_sigma_mk.1
#align embedding_sigma_mk embedding_sigma_mk

theorem Sigma.nhds_mk (i : ι) (x : σ i) : 𝓝 (⟨i, x⟩ : Sigma σ) = map (Sigma.mk i) (𝓝 x) :=
  (open_embedding_sigma_mk.map_nhds_eq x).symm
#align sigma.nhds_mk Sigma.nhds_mk

theorem Sigma.nhds_eq (x : Sigma σ) : 𝓝 x = map (Sigma.mk x.1) (𝓝 x.2) := by
  cases x
  apply Sigma.nhds_mk
#align sigma.nhds_eq Sigma.nhds_eq

theorem comap_sigma_mk_nhds (i : ι) (x : σ i) : comap (Sigma.mk i) (𝓝 ⟨i, x⟩) = 𝓝 x :=
  (embedding_sigma_mk.to_inducing.nhds_eq_comap _).symm
#align comap_sigma_mk_nhds comap_sigma_mk_nhds

theorem is_open_sigma_fst_preimage (s : Set ι) : IsOpen (Sigma.fst ⁻¹' s : Set (Σa, σ a)) := by
  rw [← bUnion_of_singleton s, preimage_Union₂]
  simp only [← range_sigma_mk]
  exact is_open_bUnion fun _ _ => is_open_range_sigma_mk
#align is_open_sigma_fst_preimage is_open_sigma_fst_preimage

/-- A map out of a sum type is continuous iff its restriction to each summand is. -/
@[simp]
theorem continuous_sigma_iff {f : Sigma σ → α} : Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ :=
  by simp only [continuous_supr_dom, continuous_coinduced_dom]
#align continuous_sigma_iff continuous_sigma_iff

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
theorem continuous_sigma {f : Sigma σ → α} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :
    Continuous f :=
  continuous_sigma_iff.2 hf
#align continuous_sigma continuous_sigma

@[simp]
theorem continuous_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    Continuous (Sigma.map f₁ f₂) ↔ ∀ i, Continuous (f₂ i) :=
  continuous_sigma_iff.trans <| by simp only [Sigma.map, embedding_sigma_mk.continuous_iff]
#align continuous_sigma_map continuous_sigma_map

@[continuity]
theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :
    Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma_map.2 hf
#align continuous.sigma_map Continuous.sigma_map

theorem is_open_map_sigma {f : Sigma σ → α} : IsOpenMap f ↔ ∀ i, IsOpenMap fun a => f ⟨i, a⟩ := by
  simp only [is_open_map_iff_nhds_le, Sigma.forall, Sigma.nhds_eq, map_map]
#align is_open_map_sigma is_open_map_sigma

theorem is_open_map_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} :
    IsOpenMap (Sigma.map f₁ f₂) ↔ ∀ i, IsOpenMap (f₂ i) :=
  is_open_map_sigma.trans <|
    forall_congr' fun i => (@open_embedding_sigma_mk _ _ _ (f₁ i)).is_open_map_iff.symm
#align is_open_map_sigma_map is_open_map_sigma_map

theorem inducing_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h₁ : Injective f₁) :
    Inducing (Sigma.map f₁ f₂) ↔ ∀ i, Inducing (f₂ i) := by
  simp only [inducing_iff_nhds, Sigma.forall, Sigma.nhds_mk, Sigma.map, ← map_sigma_mk_comap h₁,
    map_inj sigma_mk_injective]
#align inducing_sigma_map inducing_sigma_map

theorem embedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    Embedding (Sigma.map f₁ f₂) ↔ ∀ i, Embedding (f₂ i) := by
  simp only [embedding_iff, injective.sigma_map, inducing_sigma_map h, forall_and, h.sigma_map_iff]
#align embedding_sigma_map embedding_sigma_map

theorem open_embedding_sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (h : Injective f₁) :
    OpenEmbedding (Sigma.map f₁ f₂) ↔ ∀ i, OpenEmbedding (f₂ i) := by
  simp only [open_embedding_iff_embedding_open, is_open_map_sigma_map, embedding_sigma_map h,
    forall_and]
#align open_embedding_sigma_map open_embedding_sigma_map

end Sigma

section ULift

@[continuity]
theorem continuous_ulift_down [TopologicalSpace α] : Continuous (ULift.down : ULift.{v, u} α → α) :=
  continuous_induced_dom
#align continuous_ulift_down continuous_ulift_down

@[continuity]
theorem continuous_ulift_up [TopologicalSpace α] : Continuous (ULift.up : α → ULift.{v, u} α) :=
  continuous_induced_rng.2 continuous_id
#align continuous_ulift_up continuous_ulift_up

end ULift

