/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/
import Tactic.ApplyFun
import Topology.UniformSpace.Basic
import Topology.Separation

#align_import topology.uniform_space.separation from "leanprover-community/mathlib"@"0c1f285a9f6e608ae2bdffa3f993eafb01eba829"

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is T₃, hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/


open Filter TopologicalSpace Set Classical Function UniformSpace

open scoped Classical Topology uniformity Filter

noncomputable section

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/


#print UniformSpace.to_regularSpace /-
instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  RegularSpace.of_hasBasis
    (fun a => by rw [nhds_eq_comap_uniformity]; exact uniformity_has_basis_closed.comap _)
    fun a V hV => hV.2.Preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.to_regular_space UniformSpace.to_regularSpace
-/

/- warning: separation_rel clashes with inseparable -> Inseparable
Case conversion may be inaccurate. Consider using '#align separation_rel Inseparableₓ'. -/
#print Inseparable /-
/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def Inseparable (α : Type u) [u : UniformSpace α] :=
  ⋂₀ (𝓤 α).sets
#align separation_rel Inseparable
-/

scoped[uniformity] notation "𝓢" => Inseparable

theorem separated_equiv : Equivalence fun x y => (x, y) ∈ 𝓢 α :=
  ⟨fun x => fun s => refl_mem_uniformity, fun x y => fun h (s : Set (α × α)) hs =>
    have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
    h _ this,
    fun x y z (hxy : (x, y) ∈ 𝓢 α) (hyz : (y, z) ∈ 𝓢 α) s (hs : s ∈ 𝓤 α) =>
    let ⟨t, ht, (h_ts : compRel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs
    h_ts <| show (x, z) ∈ compRel t t from ⟨y, hxy t ht, hyz t ht⟩⟩
#align separated_equiv separated_equiv

#print Filter.HasBasis.inseparable_iff_uniformity /-
theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort _} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {a : α × α} : a ∈ 𝓢 α ↔ ∀ i, p i → a ∈ s i :=
  h.forall_mem_mem
#align filter.has_basis.mem_separation_rel Filter.HasBasis.inseparable_iff_uniformity
-/

/- warning: separation_rel_iff_specializes clashes with specializes_iff_inseparable -> specializes_iff_inseparable
Case conversion may be inaccurate. Consider using '#align separation_rel_iff_specializes specializes_iff_inseparableₓ'. -/
#print specializes_iff_inseparable /-
theorem specializes_iff_inseparable {a b : α} : (a, b) ∈ 𝓢 α ↔ a ⤳ b := by
  simp only [(𝓤 α).basis_sets.inseparable_iff_uniformity, id, mem_set_of_eq,
    (nhds_basis_uniformity (𝓤 α).basis_sets).specializes_iff]
#align separation_rel_iff_specializes specializes_iff_inseparable
-/

theorem inseparable_iff_inseparable {a b : α} : (a, b) ∈ 𝓢 α ↔ Inseparable a b :=
  specializes_iff_inseparable.trans specializes_iff_inseparable
#align separation_rel_iff_inseparable inseparable_iff_inseparable

/- warning: separated_space clashes with t0_space -> T0Space
Case conversion may be inaccurate. Consider using '#align separated_space T0Spaceₓ'. -/
#print T0Space /-
/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class T0Space (α : Type u) [UniformSpace α] : Prop where
  out : 𝓢 α = idRel
#align separated_space T0Space
-/

#print t0Space_iff_ker_uniformity /-
theorem t0Space_iff_ker_uniformity {α : Type u} [UniformSpace α] : T0Space α ↔ 𝓢 α = idRel :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align separated_space_iff t0Space_iff_ker_uniformity
-/

#print t0Space_iff_uniformity /-
theorem t0Space_iff_uniformity {α : Type u} [UniformSpace α] :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp [t0Space_iff_ker_uniformity, idRel_subset.2 separated_equiv.1, subset.antisymm_iff] <;>
    simp [subset_def, Inseparable]
#align separated_def t0Space_iff_uniformity
-/

#print t0Space_iff_uniformity' /-
theorem t0Space_iff_uniformity' {α : Type u} [UniformSpace α] :
    T0Space α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
  t0Space_iff_uniformity.trans <|
    forall₂_congr fun x y => by rw [← not_imp_not] <;> simp [Classical.not_forall]
#align separated_def' t0Space_iff_uniformity'
-/

#print eq_of_uniformity /-
theorem eq_of_uniformity {α : Type _} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y fun _ => h
#align eq_of_uniformity eq_of_uniformity
-/

#print eq_of_uniformity_basis /-
theorem eq_of_uniformity_basis {α : Type _} [UniformSpace α] [T0Space α] {ι : Type _} {p : ι → Prop}
    {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α} (h : ∀ {i}, p i → (x, y) ∈ s i) :
    x = y :=
  eq_of_uniformity fun V V_in =>
    let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in
    H (h hi)
#align eq_of_uniformity_basis eq_of_uniformity_basis
-/

#print eq_of_forall_symmetric /-
theorem eq_of_forall_symmetric {α : Type _} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa [and_imp] using fun _ => h)
#align eq_of_forall_symmetric eq_of_forall_symmetric
-/

#print eq_of_clusterPt_uniformity /-
theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  eq_of_uniformity_basis uniformity_hasBasis_closed fun V ⟨hV, hVc⟩ =>
    isClosed_iff_clusterPt.1 hVc _ <| h.mono <| le_principal_iff.2 hV
#align eq_of_cluster_pt_uniformity eq_of_clusterPt_uniformity
-/

/- warning: id_rel_sub_separation_relation clashes with inseparable.rfl -> Inseparable.rfl
Case conversion may be inaccurate. Consider using '#align id_rel_sub_separation_relation Inseparable.rflₓ'. -/
#print Inseparable.rfl /-
theorem Inseparable.rfl (α : Type _) [UniformSpace α] : idRel ⊆ 𝓢 α :=
  by
  unfold Inseparable
  rw [idRel_subset]
  intro x
  suffices ∀ t ∈ 𝓤 α, (x, x) ∈ t by simpa only [refl_mem_uniformity]
  exact fun t => refl_mem_uniformity
#align id_rel_sub_separation_relation Inseparable.rfl
-/

/- warning: separation_rel_comap clashes with inducing.inseparable_iff -> Inducing.inseparable_iff
Case conversion may be inaccurate. Consider using '#align separation_rel_comap Inducing.inseparable_iffₓ'. -/
#print Inducing.inseparable_iff /-
theorem Inducing.inseparable_iff {f : α → β}
    (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) : 𝓢 α = Prod.map f f ⁻¹' 𝓢 β :=
  by
  subst h
  dsimp [Inseparable]
  simp_rw [uniformity_comap, (Filter.comap_hasBasis (Prod.map f f) (𝓤 β)).ker, ← preimage_Inter,
    sInter_eq_bInter]
  rfl
#align separation_rel_comap Inducing.inseparable_iff
-/

/- warning: filter.has_basis.separation_rel clashes with filter.has_basis.sInter_sets -> Filter.HasBasis.ker
Case conversion may be inaccurate. Consider using '#align filter.has_basis.separation_rel Filter.HasBasis.kerₓ'. -/
#print Filter.HasBasis.ker /-
protected theorem Filter.HasBasis.ker {ι : Sort _} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p s) : 𝓢 α = ⋂ (i) (hi : p i), s i := by unfold Inseparable;
  rw [h.sInter_sets]
#align filter.has_basis.separation_rel Filter.HasBasis.ker
-/

theorem inseparable_eq_inter_closure : 𝓢 α = ⋂₀ (closure '' (𝓤 α).sets) := by
  simp [uniformity_has_basis_closure.separation_rel]
#align separation_rel_eq_inter_closure inseparable_eq_inter_closure

/- warning: is_closed_separation_rel clashes with is_closed_set_of_inseparable -> isClosed_setOf_inseparable
Case conversion may be inaccurate. Consider using '#align is_closed_separation_rel isClosed_setOf_inseparableₓ'. -/
#print isClosed_setOf_inseparable /-
theorem isClosed_setOf_inseparable : IsClosed (𝓢 α) :=
  by
  rw [inseparable_eq_inter_closure]
  apply isClosed_sInter
  rintro _ ⟨t, t_in, rfl⟩
  exact isClosed_closure
#align is_closed_separation_rel isClosed_setOf_inseparable
-/

#print R1Space.t2Space_iff_t0Space /-
theorem R1Space.t2Space_iff_t0Space : T0Space α ↔ T2Space α := by
  classical
  constructor <;> intro h
  · rw [t2_iff_isClosed_diagonal, ← show 𝓢 α = diagonal α from h.1]
    exact isClosed_setOf_inseparable
  · rw [t0Space_iff_uniformity']
    intro x y hxy
    rcases t2_separation hxy with ⟨u, v, uo, vo, hx, hy, h⟩
    rcases isOpen_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩
    exact ⟨r, hrU, fun H => h.le_bot ⟨hr H, hy⟩⟩
#align separated_iff_t2 R1Space.t2Space_iff_t0Space
-/

#print RegularSpace.t3Space_iff_t0Space /-
-- see Note [lower instance priority]
instance (priority := 100) RegularSpace.t3Space_iff_t0Space [T0Space α] : T3Space α :=
  haveI := separated_iff_t2.mp ‹_›
  ⟨⟩
#align separated_t3 RegularSpace.t3Space_iff_t0Space
-/

/- warning: subtype.separated_space clashes with subtype.t0_space -> Subtype.t0Space
Case conversion may be inaccurate. Consider using '#align subtype.separated_space Subtype.t0Spaceₓ'. -/
#print Subtype.t0Space /-
instance Subtype.t0Space [T0Space α] (s : Set α) : T0Space s :=
  R1Space.t2Space_iff_t0Space.mpr Subtype.t2Space
#align subtype.separated_space Subtype.t0Space
-/

#print isClosed_of_spaced_out /-
theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s :=
  by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in V_symm
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
#align is_closed_of_spaced_out isClosed_of_spaced_out
-/

#print isClosed_range_of_spaced_out /-
theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h; exact hf (ne_of_apply_ne f h)
#align is_closed_range_of_spaced_out isClosed_range_of_spaced_out
-/

/-!
### Separation quotient
-/


namespace UniformSpace

/- warning: uniform_space.separation_setoid clashes with inseparable_setoid -> inseparableSetoid
Case conversion may be inaccurate. Consider using '#align uniform_space.separation_setoid inseparableSetoidₓ'. -/
#print inseparableSetoid /-
/-- The separation relation of a uniform space seen as a setoid. -/
def inseparableSetoid (α : Type u) [UniformSpace α] : Setoid α :=
  ⟨fun x y => (x, y) ∈ 𝓢 α, separated_equiv⟩
#align uniform_space.separation_setoid inseparableSetoid
-/

attribute [local instance] separation_setoid

instance inseparableSetoid.uniformSpace {α : Type u} [u : UniformSpace α] :
    UniformSpace (Quotient (inseparableSetoid α))
    where
  toTopologicalSpace := u.toTopologicalSpace.coinduced fun x => ⟦x⟧
  uniformity := map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) u.uniformity
  refl := le_trans (by simp [Quotient.exists_rep]) (Filter.map_mono refl_le_uniformity)
  symm :=
    tendsto_map' <| by simp [Prod.swap, (· ∘ ·)] <;> exact tendsto_map.comp tendsto_swap_uniformity
  comp :=
    calc
      ((map (fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) u.uniformity).lift' fun s => compRel s s) =
          u.uniformity.lift' ((fun s => compRel s s) ∘ image fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) :=
        map_lift'_eq2 <| monotone_id.compRel monotone_id
      _ ≤
          u.uniformity.lift'
            ((image fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ∘ fun s : Set (α × α) =>
              compRel s (compRel s s)) :=
        (lift'_mono' fun s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩ =>
          by
          simp at a_eq
          simp at b_eq
          have h : ⟦a₂⟧ = ⟦b₁⟧ := by rw [a_eq.right, b_eq.left]
          have h : (a₂, b₁) ∈ 𝓢 α := Quotient.exact h
          simp [Function.comp, Set.image, compRel, and_comm, and_left_comm, and_assoc]
          exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩)
      _ =
          map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧))
            (u.uniformity.lift' fun s : Set (α × α) => compRel s (compRel s s)) :=
        by rw [map_lift'_eq] <;> exact monotone_id.comp_rel (monotone_id.comp_rel monotone_id)
      _ ≤ map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) u.uniformity := map_mono comp_le_uniformity3
  isOpen_uniformity s :=
    by
    have :
      ∀ a,
        ⟦a⟧ ∈ s →
          ({p : α × α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α ↔ {p : α × α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ 𝓤 α) :=
      fun a ha =>
      ⟨fun h =>
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h
        have hts : ∀ {a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s := fun a₁ a₂ ha₁ ha₂ =>
          @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl
        have ht' : ∀ {a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t := fun a₁ a₂ h => sInter_subset_of_mem ht h
        u.uniformity.sets_of_superset ht fun ⟨a₁, a₂⟩ h₁ h₂ => hts (ht' <| Setoid.symm h₂) h₁,
        fun h => u.uniformity.sets_of_superset h <| by simp (config := { contextual := true })⟩
    simp only [isOpen_coinduced, isOpen_uniformity, uniformity, Quotient.forall, mem_preimage,
      mem_map, preimage_set_of_eq, Quotient.eq']
    exact ⟨fun h a ha => (this a ha).mp <| h a ha, fun h a ha => (this a ha).mpr <| h a ha⟩
#align uniform_space.separation_setoid.uniform_space inseparableSetoid.uniformSpace

#print SeparationQuotient.uniformity_eq /-
theorem uniformity_eq :
    𝓤 (Quotient (inseparableSetoid α)) = (𝓤 α).map fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
  rfl
#align uniform_space.uniformity_quotient SeparationQuotient.uniformity_eq
-/

#print SeparationQuotient.uniformContinuous_mk /-
theorem uniformContinuous_mk :
    UniformContinuous (Quotient.mk' : α → Quotient (inseparableSetoid α)) :=
  le_rfl
#align uniform_space.uniform_continuous_quotient_mk SeparationQuotient.uniformContinuous_mk
-/

#print SeparationQuotient.uniformContinuous_dom /-
theorem uniformContinuous_dom {f : Quotient (inseparableSetoid α) → β}
    (hf : UniformContinuous fun x => f ⟦x⟧) : UniformContinuous f :=
  hf
#align uniform_space.uniform_continuous_quotient SeparationQuotient.uniformContinuous_dom
-/

#print SeparationQuotient.uniformContinuous_lift /-
theorem uniformContinuous_lift {f : α → β} {h : ∀ a b, (a, b) ∈ 𝓢 α → f a = f b}
    (hf : UniformContinuous f) : UniformContinuous fun a => Quotient.lift f h a :=
  uniformContinuous_dom hf
#align uniform_space.uniform_continuous_quotient_lift SeparationQuotient.uniformContinuous_lift
-/

#print SeparationQuotient.uniformContinuous_uncurry_lift₂ /-
theorem uniformContinuous_uncurry_lift₂ {f : α → β → γ}
    {h : ∀ a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
    (hf : UniformContinuous fun p : α × β => f p.1 p.2) :
    UniformContinuous fun p : _ × _ => Quotient.lift₂ f h p.1 p.2 :=
  by
  rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    Filter.prod_map_map_eq, Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
  rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf
#align uniform_space.uniform_continuous_quotient_lift₂ SeparationQuotient.uniformContinuous_uncurry_lift₂
-/

theorem comap_quotient_le_uniformity :
    ((𝓤 <| Quotient <| inseparableSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ≤ 𝓤 α :=
  fun t' ht' =>
  let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht'
  let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht
  ⟨(fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) '' s, (𝓤 α).sets_of_superset hs fun x hx => ⟨x, hx, rfl⟩,
    fun ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩ =>
    have : ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧ := Prod.mk.inj ab_eq
    have : b₁ ≈ a₁ ∧ b₂ ≈ a₂ := And.imp Quotient.exact Quotient.exact this
    have ab₁ : (a₁, b₁) ∈ t := (Setoid.symm this.left) t ht
    have ba₂ : (b₂, a₂) ∈ s := this.right s hs
    tt_t'
      ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t from ab₁, ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s from hb, ba₂⟩⟩⟩
#align uniform_space.comap_quotient_le_uniformity UniformSpace.comap_quotient_le_uniformity

#print SeparationQuotient.comap_mk_uniformity /-
theorem comap_mk_uniformity :
    ((𝓤 <| Quotient <| inseparableSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
  le_antisymm comap_quotient_le_uniformity le_comap_map
#align uniform_space.comap_quotient_eq_uniformity SeparationQuotient.comap_mk_uniformity
-/

#print SeparationQuotient.instT0Space /-
instance instT0Space : T0Space (Quotient (inseparableSetoid α)) :=
  ⟨Set.ext fun ⟨a, b⟩ =>
      Quotient.induction_on₂ a b fun a b =>
        ⟨fun h =>
          have : a ≈ b := fun s hs =>
            have :
              s ∈ (𝓤 <| Quotient <| inseparableSetoid α).comap fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
              comap_quotient_le_uniformity hs
            let ⟨t, ht, hts⟩ := this
            hts (by dsimp [preimage]; exact h t ht)
          show ⟦a⟧ = ⟦b⟧ from Quotient.sound this,
          fun heq : ⟦a⟧ = ⟦b⟧ => fun h hs => HEq ▸ refl_mem_uniformity hs⟩⟩
#align uniform_space.separated_separation SeparationQuotient.instT0Space
-/

/- warning: uniform_space.separated_of_uniform_continuous clashes with inseparable.map -> Inseparable.map
Case conversion may be inaccurate. Consider using '#align uniform_space.separated_of_uniform_continuous Inseparable.mapₓ'. -/
#print Inseparable.map /-
theorem map {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) : f x ≈ f y := fun _ h' =>
  h _ (H h')
#align uniform_space.separated_of_uniform_continuous Inseparable.map
-/

theorem eq_of_separated_of_uniformContinuous [T0Space β] {f : α → β} {x y : α}
    (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  t0Space_iff_uniformity.1 (by infer_instance) _ _ <| map H h
#align uniform_space.eq_of_separated_of_uniform_continuous UniformSpace.eq_of_separated_of_uniformContinuous

/- warning: uniform_space.separation_quotient clashes with separation_quotient -> SeparationQuotient
Case conversion may be inaccurate. Consider using '#align uniform_space.separation_quotient SeparationQuotientₓ'. -/
#print SeparationQuotient /-
/-- The maximal separated quotient of a uniform space `α`. -/
def SeparationQuotient (α : Type _) [UniformSpace α] :=
  Quotient (inseparableSetoid α)
#align uniform_space.separation_quotient SeparationQuotient
-/

namespace SeparationQuotient

instance : UniformSpace (SeparationQuotient α) :=
  inseparableSetoid.uniformSpace

instance : T0Space (SeparationQuotient α) :=
  SeparationQuotient.instT0Space

instance [Inhabited α] : Inhabited (SeparationQuotient α) :=
  Quotient.inhabited (inseparableSetoid α)

/- warning: uniform_space.separation_quotient.mk_eq_mk clashes with separation_quotient.mk_eq_mk -> SeparationQuotient.mk_eq_mk
Case conversion may be inaccurate. Consider using '#align uniform_space.separation_quotient.mk_eq_mk SeparationQuotient.mk_eq_mkₓ'. -/
#print SeparationQuotient.mk_eq_mk /-
theorem SeparationQuotient.mk_eq_mk {x y : α} :
    (⟦x⟧ : SeparationQuotient α) = ⟦y⟧ ↔ Inseparable x y :=
  Quotient.eq''.trans inseparable_iff_inseparable
#align uniform_space.separation_quotient.mk_eq_mk SeparationQuotient.mk_eq_mk
-/

#print SeparationQuotient.lift' /-
/-- Factoring functions to a separated space through the separation quotient. -/
def SeparationQuotient.lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if h : UniformContinuous f then Quotient.lift f fun x y => eq_of_separated_of_uniformContinuous h
  else fun x => f (Nonempty.some ⟨x.out⟩)
#align uniform_space.separation_quotient.lift SeparationQuotient.lift'
-/

#print SeparationQuotient.lift'_mk /-
theorem SeparationQuotient.lift'_mk [T0Space β] {f : α → β} (h : UniformContinuous f) (a : α) :
    SeparationQuotient.lift' f ⟦a⟧ = f a := by rw [lift, dif_pos h] <;> rfl
#align uniform_space.separation_quotient.lift_mk SeparationQuotient.lift'_mk
-/

#print SeparationQuotient.uniformContinuous_lift' /-
theorem SeparationQuotient.uniformContinuous_lift' [T0Space β] (f : α → β) :
    UniformContinuous (SeparationQuotient.lift' f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [lift, dif_pos hf]; exact uniform_continuous_quotient_lift hf
  · rw [lift, dif_neg hf]; exact uniformContinuous_of_const fun a b => rfl
#align uniform_space.separation_quotient.uniform_continuous_lift SeparationQuotient.uniformContinuous_lift'
-/

#print SeparationQuotient.map /-
/-- The separation quotient functor acting on functions. -/
def SeparationQuotient.map (f : α → β) : SeparationQuotient α → SeparationQuotient β :=
  SeparationQuotient.lift' (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.map SeparationQuotient.map
-/

#print SeparationQuotient.map_mk /-
theorem SeparationQuotient.map_mk {f : α → β} (h : UniformContinuous f) (a : α) :
    SeparationQuotient.map f ⟦a⟧ = ⟦f a⟧ := by
  rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]
#align uniform_space.separation_quotient.map_mk SeparationQuotient.map_mk
-/

#print SeparationQuotient.uniformContinuous_map /-
theorem SeparationQuotient.uniformContinuous_map (f : α → β) :
    UniformContinuous (SeparationQuotient.map f) :=
  SeparationQuotient.uniformContinuous_lift' (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.uniform_continuous_map SeparationQuotient.uniformContinuous_map
-/

#print SeparationQuotient.map_unique /-
theorem SeparationQuotient.map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : Quotient.mk' ∘ f = g ∘ Quotient.mk') :
    SeparationQuotient.map f = g := by
  ext ⟨a⟩ <;>
    calc
      map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
      _ = g ⟦a⟧ := congr_fun comm a
#align uniform_space.separation_quotient.map_unique SeparationQuotient.map_unique
-/

#print SeparationQuotient.map_id /-
theorem SeparationQuotient.map_id : SeparationQuotient.map (@id α) = id :=
  SeparationQuotient.map_unique uniformContinuous_id rfl
#align uniform_space.separation_quotient.map_id SeparationQuotient.map_id
-/

#print SeparationQuotient.map_comp /-
theorem SeparationQuotient.map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) :
    SeparationQuotient.map g ∘ SeparationQuotient.map f = SeparationQuotient.map (g ∘ f) :=
  (SeparationQuotient.map_unique (hg.comp hf) <| by simp only [(· ∘ ·), map_mk, hf, hg]).symm
#align uniform_space.separation_quotient.map_comp SeparationQuotient.map_comp
-/

end SeparationQuotient

/- warning: uniform_space.separation_prod clashes with inseparable_prod -> inseparable_prod
Case conversion may be inaccurate. Consider using '#align uniform_space.separation_prod inseparable_prodₓ'. -/
#print inseparable_prod /-
theorem inseparable_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
  by
  constructor
  · intro h
    exact
      ⟨separated_of_uniform_continuous uniformContinuous_fst h,
        separated_of_uniform_continuous uniformContinuous_snd h⟩
  · rintro ⟨eqv_α, eqv_β⟩ r r_in
    rw [uniformity_prod] at r_in
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, rfl⟩
    let p_α := fun p : (α × β) × α × β => (p.1.1, p.2.1)
    let p_β := fun p : (α × β) × α × β => (p.1.2, p.2.2)
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α := by simp [p_α, eqv_α r_α r_α_in]
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β := by simp [p_β, eqv_β r_β r_β_in]
    exact ⟨h_α key_α, h_β key_β⟩
#align uniform_space.separation_prod inseparable_prod
-/

#print Prod.instT0Space /-
instance Prod.instT0Space [T0Space α] [T0Space β] : T0Space (α × β) :=
  t0Space_iff_uniformity.2 fun x y H =>
    Prod.ext (eq_of_separated_of_uniformContinuous uniformContinuous_fst H)
      (eq_of_separated_of_uniformContinuous uniformContinuous_snd H)
#align uniform_space.separated.prod Prod.instT0Space
-/

end UniformSpace

