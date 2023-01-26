/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module topology.order.lower_topology
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Lattice

/-!
# Lower topology

This file introduces the lower topology on a preorder as the topology generated by the complements
of the closed intervals to infinity.

## Main statements

- `lower_topology.t0_space` - the lower topology on a partial order is T₀
- `is_topological_basis.is_topological_basis` - the complements of the upper closures of finite
  subsets form a basis for the lower topology
- `lower_topology.to_has_continuous_inf` - the inf map is continuous with respect to the lower
  topology

## Implementation notes

A type synonym `with_lower_topology` is introduced and for a preorder `α`, `with_lower_topology α`
is made an instance of `topological_space` by the topology generated by the complements of the
closed intervals to infinity.

We define a mixin class `lower_topology` for the class of types which are both a preorder and a
topology and where the topology is generated by the complements of the closed intervals to infinity.
It is shown that `with_lower_topology α` is an instance of `lower_topology`.

## Motivation

The lower topology is used with the `Scott` topology to define the Lawson topology. The restriction
of the lower topology to the spectrum of a complete lattice coincides with the hull-kernel topology.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

lower topology, preorder
-/


variable (α β : Type _)

open Set TopologicalSpace

/-- Type synonym for a preorder equipped with the lower topology
-/
def WithLowerTopology :=
  α
#align with_lower_topology WithLowerTopology

variable {α β}

namespace WithLowerTopology

/-- `to_lower` is the identity function to the `with_lower_topology` of a type.  -/
@[match_pattern]
def toLower : α ≃ WithLowerTopology α :=
  Equiv.refl _
#align with_lower_topology.to_lower WithLowerTopology.toLower

/-- `of_lower` is the identity function from the `with_lower_topology` of a type.  -/
@[match_pattern]
def ofLower : WithLowerTopology α ≃ α :=
  Equiv.refl _
#align with_lower_topology.of_lower WithLowerTopology.ofLower

@[simp]
theorem to_withLowerTopology_symm_eq : (@toLower α).symm = of_lower :=
  rfl
#align with_lower_topology.to_with_lower_topology_symm_eq WithLowerTopology.to_withLowerTopology_symm_eq

@[simp]
theorem of_withLowerTopology_symm_eq : (@ofLower α).symm = to_lower :=
  rfl
#align with_lower_topology.of_with_lower_topology_symm_eq WithLowerTopology.of_withLowerTopology_symm_eq

@[simp]
theorem toLower_ofLower (a : WithLowerTopology α) : toLower (ofLower a) = a :=
  rfl
#align with_lower_topology.to_lower_of_lower WithLowerTopology.toLower_ofLower

@[simp]
theorem ofLower_toLower (a : α) : ofLower (toLower a) = a :=
  rfl
#align with_lower_topology.of_lower_to_lower WithLowerTopology.ofLower_toLower

@[simp]
theorem toLower_inj {a b : α} : toLower a = toLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.to_lower_inj WithLowerTopology.toLower_inj

@[simp]
theorem ofLower_inj {a b : WithLowerTopology α} : ofLower a = ofLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.of_lower_inj WithLowerTopology.ofLower_inj

/-- A recursor for `with_lower_topology`. Use as `induction x using with_lower_topology.rec`. -/
protected def rec {β : WithLowerTopology α → Sort _} (h : ∀ a, β (toLower a)) : ∀ a, β a := fun a =>
  h (ofLower a)
#align with_lower_topology.rec WithLowerTopology.rec

instance [Nonempty α] : Nonempty (WithLowerTopology α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithLowerTopology α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLowerTopology α) :=
  ‹Preorder α›

instance : TopologicalSpace (WithLowerTopology α) :=
  generateFrom { s | ∃ a, Ici aᶜ = s }

theorem isOpen_preimage_ofLower (S : Set α) :
    IsOpen (WithLowerTopology.ofLower ⁻¹' S) ↔
      (generateFrom { s : Set α | ∃ a : α, Ici aᶜ = s }).IsOpen S :=
  Iff.rfl
#align with_lower_topology.is_open_preimage_of_lower WithLowerTopology.isOpen_preimage_ofLower

theorem isOpen_def (T : Set (WithLowerTopology α)) :
    IsOpen T ↔
      (generateFrom { s : Set α | ∃ a : α, Ici aᶜ = s }).IsOpen (WithLowerTopology.toLower ⁻¹' T) :=
  Iff.rfl
#align with_lower_topology.is_open_def WithLowerTopology.isOpen_def

end WithLowerTopology

/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`topology_eq_lower_topology] [] -/
/--
The lower topology is the topology generated by the complements of the closed intervals to infinity.
-/
class LowerTopology (α : Type _) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lower_topology : t = generateFrom { s | ∃ a, Ici aᶜ = s }
#align lower_topology LowerTopology

instance [Preorder α] : LowerTopology (WithLowerTopology α) :=
  ⟨rfl⟩

namespace LowerTopology

/-- The complements of the upper closures of finite sets are a collection of lower sets
which form a basis for the lower topology. -/
def lowerBasis (α : Type _) [Preorder α] :=
  { s : Set α | ∃ t : Set α, t.Finite ∧ (upperClosure t : Set α)ᶜ = s }
#align lower_topology.lower_basis LowerTopology.lowerBasis

section Preorder

variable [Preorder α] [TopologicalSpace α] [LowerTopology α] {s : Set α}

/-- If `α` is equipped with the lower topology, then it is homeomorphic to `with_lower_topology α`.
-/
def withLowerTopologyHomeomorph : WithLowerTopology α ≃ₜ α :=
  {
    WithLowerTopology.ofLower with
    continuous_to_fun := by
      convert continuous_id
      apply topology_eq_lower_topology
    continuous_inv_fun := by
      convert ← continuous_id
      apply topology_eq_lower_topology }
#align lower_topology.with_lower_topology_homeomorph LowerTopology.withLowerTopologyHomeomorph

theorem isOpen_iff_generate_ici_compl : IsOpen s ↔ GenerateOpen { t | ∃ a, Ici aᶜ = t } s := by
  rw [topology_eq_lower_topology α] <;> rfl
#align lower_topology.is_open_iff_generate_Ici_compl LowerTopology.isOpen_iff_generate_ici_compl

/-- Left-closed right-infinite intervals [a, ∞) are closed in the lower topology. -/
theorem isClosed_ici (a : α) : IsClosed (Ici a) :=
  isOpen_compl_iff.1 <| isOpen_iff_generate_ici_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩
#align lower_topology.is_closed_Ici LowerTopology.isClosed_ici

/-- The upper closure of a finite set is closed in the lower topology. -/
theorem isClosed_upperClosure (h : s.Finite) : IsClosed (upperClosure s : Set α) :=
  by
  simp only [← UpperSet.infᵢ_ici, UpperSet.coe_infᵢ]
  exact isClosed_bUnion h fun a h₁ => isClosed_ici a
#align lower_topology.is_closed_upper_closure LowerTopology.isClosed_upperClosure

/-- Every set open in the lower topology is a lower set. -/
theorem isLowerSet_of_isOpen (h : IsOpen s) : IsLowerSet s :=
  by
  rw [is_open_iff_generate_Ici_compl] at h
  induction h
  case basic u h => obtain ⟨a, rfl⟩ := h; exact (isUpperSet_ici a).compl
  case univ => exact isLowerSet_univ
  case inter u v hu1 hv1 hu2 hv2 => exact hu2.inter hv2
  case sUnion _ _ ih => exact isLowerSet_unionₛ ih
#align lower_topology.is_lower_set_of_is_open LowerTopology.isLowerSet_of_isOpen

theorem isUpperSet_of_isClosed (h : IsClosed s) : IsUpperSet s :=
  isLowerSet_compl.1 <| isLowerSet_of_isOpen h.is_open_compl
#align lower_topology.is_upper_set_of_is_closed LowerTopology.isUpperSet_of_isClosed

/--
The closure of a singleton `{a}` in the lower topology is the left-closed right-infinite interval
[a, ∞).
-/
@[simp]
theorem closure_singleton (a : α) : closure {a} = Ici a :=
  subset_antisymm ((closure_minimal fun b h => h.ge) <| isClosed_ici a) <|
    (isUpperSet_of_isClosed isClosed_closure).Ici_subset <| subset_closure rfl
#align lower_topology.closure_singleton LowerTopology.closure_singleton

protected theorem isTopologicalBasis : IsTopologicalBasis (lowerBasis α) :=
  by
  convert is_topological_basis_of_subbasis (topology_eq_lower_topology α)
  simp_rw [lower_basis, coe_upperClosure, compl_Union]
  ext s
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine' ⟨(fun a => Ici aᶜ) '' F, ⟨hF.image _, image_subset_iff.2 fun _ _ => ⟨_, rfl⟩⟩, _⟩
    rw [sInter_image]
  · rintro ⟨F, ⟨hF, hs⟩, rfl⟩
    haveI := hF.to_subtype
    rw [subset_def, Subtype.forall'] at hs
    choose f hf using hs
    exact ⟨_, finite_range f, by simp_rw [bInter_range, hf, sInter_eq_Inter]⟩
#align lower_topology.is_topological_basis LowerTopology.isTopologicalBasis

end Preorder

section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [LowerTopology α]

-- see Note [lower instance priority]
/-- The lower topology on a partial order is T₀.
-/
instance (priority := 90) : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h =>
    Ici_injective <| by simpa only [inseparable_iff_closure_eq, closure_singleton] using h

end PartialOrder

end LowerTopology

instance [Preorder α] [TopologicalSpace α] [LowerTopology α] [OrderBot α] [Preorder β]
    [TopologicalSpace β] [LowerTopology β] [OrderBot β] : LowerTopology (α × β)
    where topology_eq_lower_topology :=
    by
    refine' le_antisymm (le_generateFrom _) _
    · rintro _ ⟨x, rfl⟩
      exact ((LowerTopology.isClosed_ici _).Prod <| LowerTopology.isClosed_ici _).is_open_compl
    rw [(lower_topology.is_topological_basis.prod
          LowerTopology.isTopologicalBasis).eq_generate_from,
      le_generateFrom_iff_subset_isOpen, image2_subset_iff]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    dsimp
    simp_rw [coe_upperClosure, compl_Union, prod_eq, preimage_Inter, preimage_compl]
    -- Note: `refine` doesn't work here because it tries using `prod.topological_space`.
    apply (isOpen_bInter hs fun a _ => _).inter (isOpen_bInter ht fun b _ => _)
    · exact generate_open.basic _ ⟨(a, ⊥), by simp [Ici_prod_eq, prod_univ]⟩
    · exact generate_open.basic _ ⟨(⊥, b), by simp [Ici_prod_eq, univ_prod]⟩
    all_goals infer_instance

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [LowerTopology α]
  [TopologicalSpace β] [LowerTopology β]

theorem InfHom.continuous (f : InfHom α β) : Continuous f :=
  by
  convert continuous_generated_from _
  · exact LowerTopology.topology_eq_lowerTopology β
  rintro _ ⟨b, rfl⟩
  rw [preimage_compl, isOpen_compl_iff]
  convert LowerTopology.isClosed_ici (Inf <| f ⁻¹' Ici b)
  refine' subset_antisymm (fun a => infₛ_le) fun a ha => le_trans _ <| OrderHomClass.mono f ha
  simp [map_Inf]
#align Inf_hom.continuous InfHom.continuous

-- see Note [lower instance priority]
instance (priority := 90) LowerTopology.to_hasContinuousInf : HasContinuousInf α :=
  ⟨(infInfHom : InfHom (α × α) α).Continuous⟩
#align lower_topology.to_has_continuous_inf LowerTopology.to_hasContinuousInf

end CompleteLattice

